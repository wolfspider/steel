(* Main.ml — switchable queue (steel vs local), same forensic modes *)

open Prims
open Eio.Std
open Sqlite3
(* open Memtrace *)
module TLQ = TwoLockQueue

let ( >! ) a b = Prims.op_GreaterThan (Prims.of_int a) (Prims.of_int b)

(* --- Local, minimal two-lock queue that cannot be shadowed --- *)
module QLocal = struct
  type 'a node = { mutable data : 'a option; mutable next : 'a node option }

  type 'a t = {
    head_mu : Mutex.t;
    tail_mu : Mutex.t;
    mutable head : 'a node;
    mutable tail : 'a node;
  }

  let new_queue seed =
    let d = { data = Some seed; next = None } in
    print_endline "[QLocal] new_queue";
    { head_mu = Mutex.create (); tail_mu = Mutex.create (); head = d; tail = d }

  let enqueue q x =
    let n = { data = Some x; next = None } in
    Mutex.lock q.tail_mu;
    q.tail.next <- Some n;
    q.tail <- n;
    Mutex.unlock q.tail_mu;
    print_endline "[QLocal] enqueue"

  let dequeue q =
    Mutex.lock q.head_mu;
    let r =
      match q.head.next with
      | None ->
          Mutex.unlock q.head_mu;
          print_endline "[QLocal] dequeue -> None";
          None
      | Some n ->
          let old = q.head in
          q.head <- n;
          let v = old.data in
          Mutex.unlock q.head_mu;
          print_endline "[QLocal] dequeue -> Some";
          v
    in
    r
end

(* --- Steel-TLQ wrapper with logs (your existing Qdbg) --- *)
module QSteel = struct
  type 'a t = 'a TLQ.t

  let new_queue = TLQ.new_queue

  let enqueue q (x : 'a) =
    print_endline "[Qdbg] enqueue: begin";
    flush stdout;
    TLQ.enqueue q x;
    print_endline "[Qdbg] enqueue: end";
    flush stdout

  let dequeue q =
    let r = TLQ.dequeue q in
    (match r with
    | None -> print_endline "[Qdbg] dequeue -> None"
    | Some _ -> print_endline "[Qdbg] dequeue -> Some");
    flush stdout;
    r
end

(* --- Local, minimal two-lock queue that cannot be shadowed --- *)

(* Use the local queue *)
module Q = TwoLockQueue

(* ---------- payload types ---------- *)
type t0 = Seed | Work of Prims.int (* use Prims.int so we stay consistent *)
type t1 = Seed1 | Work1 of (unit -> unit)

(* ---------------------- PCM ping→pong protocol ---------------------- *)
let (duat : Duplex_PCM.dprot) =
  Duplex_PCM.bind (Duplex_PCM.send ()) (fun _x ->
      Duplex_PCM.bind (Duplex_PCM.recv ()) (fun _y -> Duplex_PCM.done1))

(* ---------------------- MODE 0: TLQ single-thread ---------------------- *)
let run_mode0 () =
  print_endline "[M0] TLQ single-thread sanity";
  let q = Q.new_queue Seed in
  (* prove which queue we're actually using with a smoke roundtrip *)
  print_endline "[SMOKE] enqueue+dequeue on selected queue";
  Q.enqueue q Seed;
  ignore (Q.dequeue q);

  let d0 = Q.dequeue q in
  (match d0 with
  | None -> print_endline "[M0] first dequeue -> None (expected before enqueue)"
  | Some _ ->
      print_endline "[M0] first dequeue -> Some (unexpected before enqueue)");
  print_endline "[M0] enqueue Work 41";
  Q.enqueue q (Work (Prims.of_int 41));
  let a = Q.dequeue q in
  (match a with
  | Some Seed -> print_endline "[M0] got Seed (dummy head) — OK"
  | Some (Work _v) -> Printf.printf "[M0] got Work (unexpected first)!\n"
  | None -> print_endline "[M0] got None (unexpected)");
  let b = Q.dequeue q in
  match b with
  | Some (Work _v) -> Printf.printf "[M0] got Work — OK\n%!"
  | Some Seed -> print_endline "[M0] got Seed again (unexpected)"
  | None -> print_endline "[M0] got None (unexpected)"

(* ---------------------- MODE 1: TLQ two threads (no PCM) ---------------------- *)
let run_mode1 () =
  print_endline "[M1] TLQ two threads (no PCM)";
  let q = Q.new_queue Seed in
  ignore (Q.dequeue q);

  (* drop dummy like original harness *)
  let stop = ref false in
  let mu = Mutex.create () in
  let get_stop () =
    Mutex.lock mu;
    let v = !stop in
    Mutex.unlock mu;
    v
  in
  let set_stop v =
    Mutex.lock mu;
    stop := v;
    Mutex.unlock mu
  in

  let consumer () =
    let idle = ref 0 in
    let rec loop () =
      match Q.dequeue q with
      | Some Seed ->
          print_endline "[M1] consumer: Seed";
          Thread.yield ();
          loop ()
      | Some (Work _v) ->
          Printf.printf "[M1] consumer: Work\n%!";
          ()
      | None ->
          if get_stop () then (
            incr idle;
            if !idle >! 2048 then ()
            else (
              Thread.delay 0.0005;
              loop ()))
          else (
            Thread.delay 0.0005;
            loop ())
    in
    loop ()
  in

  let cth = Thread.create consumer () in
  Thread.delay 0.010;
  print_endline "[M1] producer: enqueue Work 41";
  Q.enqueue q (Work (Prims.of_int 41));
  Thread.yield ();
  Thread.delay 0.010;
  (* give consumer a scheduling window *)
  set_stop true;
  Thread.join cth;
  print_endline "[M1] done"

(* ---------------------- MODE 2: TLQ two threads + Steel_Reference flag ---------------------- *)
let run_mode2 () =
  print_endline "[M2] TLQ two threads with Steel_Reference flag";
  let q = Q.new_queue Seed1 in
  ignore (Q.dequeue q);
  let flag = Steel_Reference.alloc_pt true in
  let stop = ref false in
  let mu = Mutex.create () in
  let get_stop () =
    Mutex.lock mu;
    let v = !stop in
    Mutex.unlock mu;
    v
  in
  let set_stop v =
    Mutex.lock mu;
    stop := v;
    Mutex.unlock mu
  in

  let consumer () =
    let idle = ref 0 in
    let rec loop () =
      match Q.dequeue q with
      | Some Seed1 ->
          print_endline "[M2] consumer: Seed";
          Thread.yield ();
          loop ()
      | Some (Work1 f) ->
          print_endline "[M2] consumer: run task";
          f ();
          ()
      | None ->
          if get_stop () then (
            incr idle;
            if !idle >! 2048 then ()
            else (
              Thread.delay 0.0005;
              loop ()))
          else (
            Thread.delay 0.0005;
            loop ())
    in
    loop ()
  in
  let cth = Thread.create consumer () in
  Thread.delay 0.010;

  print_endline "[M2] producer: enqueue flag flip";
  Q.enqueue q
    (Work1
       (fun () ->
         print_endline "[M2] task: writing flag=false";
         Steel_Reference.write_pt () flag false));

  Thread.yield ();
  Thread.delay 0.010;
  set_stop true;
  Thread.join cth;

  let v = Steel_Reference.read_pt () () flag in
  Printf.printf "[M2] flag now = %B (expect false)\n%!" v

(* ---------------------- MODE 3: TLQ × PCM with watchdog ---------------------- *)
let run_mode3 () =
  print_endline "[M3] TLQ × PCM forensic";

  let q = Q.new_queue (fun () -> ()) in
  ignore (Q.dequeue q);

  let stop = ref false in
  let mu = Mutex.create () in
  let get_stop () =
    Mutex.lock mu;
    let v = !stop in
    Mutex.unlock mu;
    v
  in
  let set_stop v =
    Mutex.lock mu;
    stop := v;
    Mutex.unlock mu
  in

  let b_started = ref false in
  let a_sent = ref false in
  let b_after_recv = ref false in
  let b_after_send = ref false in

  let watchdog_running = ref true in
  let watchdog () =
    let ticks = ref 0 in
    while !watchdog_running && not (!ticks >! 3000) do
      Thread.delay 0.001;
      incr ticks
    done;
    if !watchdog_running then (
      print_endline "\n[watchdog] TIMEOUT — dumping state:";
      Printf.printf
        "  b_started=%b  a_sent=%b  b_after_recv=%b  b_after_send=%b\n%!"
        !b_started !a_sent !b_after_recv !b_after_send;
      print_endline
        "  (If b_started=false: consumer never saw Work; if a_sent=false: \
         producer never sent.)";
      exit 2)
  in
  let _wd = Thread.create watchdog () in

  let serve_b cB =
    b_started := true;
    print_endline "[B] start";
    flush stdout;
    Thread.delay 0.010;
    print_endline "[B] waiting to recv x";
    let x =
      Duplex_PCM.channel_recv Duplex_PCM.B (Steel_Channel_Protocol.dual duat) cB
    in
    b_after_recv := true;
    print_endline "[B] recv ok";
    flush stdout;
    let xi : Prims.int = (Obj.magic x : Prims.int) in
    let yi : Prims.int = Prims.op_Addition xi (Prims.of_int 42) in
    let stepB =
      Steel_Channel_Protocol.step (Steel_Channel_Protocol.dual duat) x
    in
    Thread.delay 0.010;
    print_endline "[B] sending y";
    Duplex_PCM.channel_send Duplex_PCM.B stepB cB (Obj.magic yi);
    b_after_send := true;
    print_endline "[B] send ok";
    flush stdout
  in

  let consumer () =
    let polls = ref 0 in
    let rec loop () =
      match Q.dequeue q with
      | Some f ->
          print_endline "[Q] DEQ -> run B";
          f ();
          ()
      | None ->
          Thread.delay 0.002;
          incr polls;
          if get_stop () then ()
          else if !polls >! 10000 then (
            print_endline "[Q] too many polls — giving up";
            ())
          else loop ()
    in
    loop ()
  in
  let cth = Thread.create consumer () in

  let pth =
    Thread.create
      (fun () ->
        let cA1, cB1 = Duplex_PCM.new_channel duat in
        print_endline "[A] ENQ B task";
        Q.enqueue q (fun () -> serve_b cB1);
        Thread.yield ();
        Thread.delay 0.010;
        print_endline "[A] sending x=1";
        let x_any = (Obj.magic (Prims.of_int 1) : Obj.t) in
        Duplex_PCM.channel_send Duplex_PCM.A duat cA1 x_any;
        a_sent := true;
        print_endline "[A] send ok";
        let stepA1 = Steel_Channel_Protocol.step duat x_any in
        print_endline "[A] waiting to recv y";
        let _ = Duplex_PCM.channel_recv Duplex_PCM.A stepA1 cA1 in
        print_endline "[A] recv ok")
      ()
  in

  Thread.join pth;
  set_stop true;
  Thread.join cth;

  watchdog_running := false;
  print_endline "[M3] done."

(* ==== Prims <-> OCaml bridges, fully annotated ==== *)
(* helpers only for boundary conversions when you must print a Prims.int *)
(* nat helpers *)
(* === helpers: keep OCaml <-> Prims conversions simple === *)
let nat_of_int (x : int) : Prims.nat = (Obj.magic x : Prims.nat)
let int_of_nat (n : Prims.nat) : int = (Obj.magic n : int)

(* string-bridge to get floats from Prims.int without Zarith fuss *)
let f_of_int (i : Prims.int) : float =
  Stdlib.float_of_string (Prims.string_of_int i)

(* ---------------------- MODE 3S: TLQ × PCM stress (with stats) ---------------------- *)
let run_mode3_stress () =
  (* OCaml ints from env *)
  let producers = try int_of_string (Sys.getenv "PRODUCERS") with _ -> 1 in
  let consumers = try int_of_string (Sys.getenv "CONSUMERS") with _ -> 4 in
  let iters = try int_of_string (Sys.getenv "ITERS") with _ -> 100_000 in

  Printf.printf "[3S] start  producers=%d  consumers=%d  iters/producer=%d\n%!"
    producers consumers iters;

  (* TLQ of unit->unit tasks; drop dummy head element *)
  let q = Q.new_queue (fun () -> ()) in
  ignore (Q.dequeue q);

  (* stop flag (plain OCaml mutex) *)
  let stop = ref false in
  let mu = Mutex.create () in
  let get_stop () =
    Mutex.lock mu;
    let v = !stop in
    Mutex.unlock mu;
    v
  in
  let set_stop v =
    Mutex.lock mu;
    stop := v;
    Mutex.unlock mu
  in

  (* B service: recv x; send y=x+42 *)
  let serve_b (cB : Duplex_PCM.ch) : unit =
    let x =
      Duplex_PCM.channel_recv Duplex_PCM.B (Steel_Channel_Protocol.dual duat) cB
    in
    let xi : Prims.int = (Obj.magic x : Prims.int) in
    let yi : Prims.int = Prims.op_Addition xi (Prims.of_int 42) in
    let stepB =
      Steel_Channel_Protocol.step (Steel_Channel_Protocol.dual duat) x
    in
    Duplex_PCM.channel_send Duplex_PCM.B stepB cB (Obj.magic yi)
  in

  (* per-consumer counts (Prims) to avoid pos/int clashes *)
  (* OCaml-side metrics *)
  let incr_nat (a : Prims.nat array) i =
    let v = int_of_nat a.(i) + Prims.of_int 1 in
    a.(i) <- nat_of_int v
  in

  let counts : Prims.nat array = Array.make consumers (Prims.of_int 0) in

  (* consumers: pop & run B-service tasks *)
  let consumer_loop cid () =
    let idle_spins = ref 0 in
    let rec loop () =
      match Q.dequeue q with
      | Some f ->
          idle_spins := 0;
          incr_nat counts cid;
          f ();
          Thread.yield ();
          loop ()
      | None ->
          if get_stop () then (
            incr idle_spins;
            if !idle_spins >! 4 then () (* all OCaml ints here *)
            else (
              Thread.delay 0.05;
              Thread.yield ();
              loop ()))
          else (
            Thread.delay 0.05;
            Thread.yield ();
            loop ())
    in
    loop ()
  in
  let cons =
    Array.init consumers (fun cid -> Thread.create (consumer_loop cid) ())
  in

  (* producers: each does [iters] channel exchanges *)
  let prod =
    Array.init producers (fun _ ->
        Thread.create
          (fun () ->
            for i = 1 to iters do
              let cA, cB = Duplex_PCM.new_channel duat in
              Q.enqueue q (fun () -> serve_b cB);
              Thread.yield ();
              let x_any = (Obj.magic (Prims.of_int 1) : Obj.t) in
              Duplex_PCM.channel_send Duplex_PCM.A duat cA x_any;
              let stepA = Steel_Channel_Protocol.step duat x_any in
              let _y = Duplex_PCM.channel_recv Duplex_PCM.A stepA cA in
              if i land 0x3FF = 0 then Thread.yield ()
            done)
          ())
  in

  let t0 = Unix.gettimeofday () in
  Array.iter Thread.join prod;
  set_stop true;
  Array.iter Thread.join cons;
  let t1 = Unix.gettimeofday () in

  (* ---- stats in Prims.int (your code above these bindings stays the same) ---- *)
  let total_i : Prims.int =
    Array.fold_left
      (fun acc k_nat -> Prims.op_Addition acc (Obj.magic k_nat : Prims.int))
      (Prims.of_int 0) counts
  in

  let min_i, max_i =
    let first : Prims.int = (Obj.magic counts.(0) : Prims.int) in
    Array.fold_left
      (fun (mn, mx) k_nat ->
        let ki : Prims.int = (Obj.magic k_nat : Prims.int) in
        let mn' = if Prims.op_LessThan ki mn then ki else mn in
        let mx' = if Prims.op_GreaterThan ki mx then ki else mx in
        (mn', mx'))
      (first, first) counts
  in

  (* ---- isolate float math so it can't unify with Prims ---- *)
  let secs, avg_f, imb_f, rate_f =
    let secs : float = t1 -. t0 in
    let avg_f : float = f_of_int total_i /. Stdlib.float_of_int consumers in
    let imb_f : float =
      if Prims.op_Equality max_i (Prims.of_int 0) then 0.0
      else
        f_of_int (Prims.op_Subtraction max_i min_i) /. f_of_int max_i *. 100.0
    in
    let rate_f : float = f_of_int total_i /. secs in
    (secs, avg_f, imb_f, rate_f)
  in

  (* ---- printing ---- *)
  Printf.printf "=== PCM × TwoLockQueue stress ===\n";
  Printf.printf "producers=%d  consumers=%d  iters/producer=%d\n" producers
    consumers iters;

  Array.iteri
    (fun i k_nat ->
      Printf.printf "T%-2d: %s\n" i
        (Prims.string_of_int (Obj.magic k_nat : Prims.int)))
    counts;

  Printf.printf "total=%s  time=%.3fs  throughput=%.0f ops/s\n%!"
    (Prims.string_of_int total_i)
    secs rate_f;
  Printf.printf "min=%s  max=%s  avg=%.1f  imbalance=%.1f%%%%\n%!"
    (Prims.string_of_int min_i)
    (Prims.string_of_int max_i)
    avg_f imb_f;
  ()

type req = Request of { x : Prims.int; reply : Prims.int Eio.Stream.t } | Stop

(* ---------------------- MODE 3E: TLQ × PCM (Eio fibers + multi-domains) ---------------------- *)
let run_mode3_eio () =
  Eio_main.run (fun env ->
      Eio.traceln "Eio backend = %s" (Eio.Stdenv.backend_id env);
      (* let tracer =
        Memtrace.start_tracing ~context:None ~filename:"alloc.ctf"
          ~sampling_rate:1e-8
      in *)

      let clock = env#clock in
      (* keep your >! helper for Prims comparisons when needed *)
      let ( >! ) a b = Prims.op_GreaterThan (Prims.of_int a) (Prims.of_int b) in

      (* Plain OCaml ints from env; rename to avoid clashes *)
      let n_producers =
        try int_of_string (Sys.getenv "PRODUCERS") with _ -> 4
      in
      let n_consumers =
        try int_of_string (Sys.getenv "CONSUMERS") with _ -> 4
      in
      let iters =
        try int_of_string (Sys.getenv "ITERS") with _ -> 1_000_000
      in
      let n_domains =
        try int_of_string (Sys.getenv "DOMAINS")
        with _ -> max 1 (Domain.recommended_domain_count ())
      in

      Printf.printf
        "[3E] domains=%d producers=%d consumers=%d iters/producer=%d\n%!"
        n_domains n_producers n_consumers iters;

      (* Keep Steel TLQ; drop dummy *)
      let q = Q.new_queue (fun () -> ()) in
      ignore (Q.dequeue q);

      (* Stop flag guarded by Eio.Mutex *)
      (* Atomic stop flag *)
      let stop = Atomic.make false in

      (* Same function names as before *)
      let get_stop () = Atomic.get stop in
      let set_stop v  = Atomic.set stop v in

      (* Optional helpers, if useful *)
      let request_stop () : unit =
        ignore (Atomic.exchange stop true) in (* sets to true, discards previous *)
      
      let was_stopped_before_request () : bool =
        Atomic.exchange stop true in          (* sets to true, returns previous *)

      (* Bridges already defined elsewhere:
       val nat_of_int : int -> Prims.nat
       val int_of_nat : Prims.nat -> int
       val f_of_int   : Prims.int -> float
    *)
      let counts : Prims.nat array = Array.make n_consumers (Prims.of_int 0) in
      let incr_nat (a : Prims.nat array) i =
        let v = int_of_nat a.(i) + Prims.of_int 1 in
        a.(i) <- nat_of_int v
      in

      (* PCM service unchanged *)
      let serve_b (cB : Duplex_PCM.ch) : unit =
        let x =
          Duplex_PCM.channel_recv Duplex_PCM.B
            (Steel_Channel_Protocol.dual duat)
            cB
        in
        let xi : Prims.int = (Obj.magic x : Prims.int) in
        let yi : Prims.int = Prims.op_Addition xi (Prims.of_int 42) in
        let stepB =
          Steel_Channel_Protocol.step (Steel_Channel_Protocol.dual duat) x
        in
        Duplex_PCM.channel_send Duplex_PCM.B stepB cB (Obj.magic yi)
      in

      let t0 = Unix.gettimeofday () in

      let served = ref 0 in

      Switch.run @@ fun sw ->
      (* --- Single B-server fed by a request stream --- *)
      (* one request bus on the main Eio scheduler domain *)
      let reqs : req Eio.Stream.t = Eio.Stream.create (max 1 n_consumers) in

      (* 2) One B-server fiber: does full PCM per request *)
      Eio.Fiber.fork ~sw (fun () ->
          let rec serve_loop () =
            match Eio.Stream.take reqs with
            | Request { x; reply } ->
                let cA, cB = Duplex_PCM.new_channel duat in
                let x_any : Obj.t = (Obj.magic x : Obj.t) in
                Duplex_PCM.channel_send Duplex_PCM.A duat cA x_any;
                let stepA = Steel_Channel_Protocol.step duat x_any in
                serve_b cB;
                let y_any = Duplex_PCM.channel_recv Duplex_PCM.A stepA cA in
                Eio.Stream.add reply (Obj.magic y_any : Prims.int);
                serve_loop ()
            | Stop -> () (* graceful exit *)
          in
          serve_loop ());

      (* one gate to guard dequeue only; queue internals unchanged *)
      let deq_gate = Eio.Mutex.create () in

      (* 3) Consumers: pop TLQ and run closures (those closures add to [reqs]) *)
      let cids = Stdlib.List.init n_consumers (fun i -> i) in
      (* Consumers: pop TLQ, execute, then ALWAYS yield *)
      Stdlib.List.iter
        (fun cid ->
          Eio.Fiber.fork ~sw (fun () ->
            let served = ref 0 in
            let rec loop () =
              match Q.dequeue q with
              | Some f ->
                  f ();                      (* do the work first *)
                  incr_nat counts cid;       (* then record it *)
                  incr served;
                  Eio.Fiber.yield ();        (* <- unconditional fairness *)
                  loop ()
              | None ->
                  if get_stop () then () else (Eio.Fiber.yield (); loop ())
            in
            loop ()))
        cids;

      (* ---- Producers spread across domains, no for-loop on spans ---- *)
      let prod_ps =
        List.init n_domains (fun dom_i ->
            Eio.Fiber.fork_promise ~sw (fun () ->
                Eio.Domain_manager.run env#domain_mgr (fun () ->
                    (* shard indices using half-open [start, stop) — all in Prims.int *)
                    let start : Prims.int =
                      Prims.of_int dom_i * Prims.of_int n_producers
                      / Prims.of_int n_domains
                    in
                    let stop_excl : Prims.int =
                      (Prims.of_int dom_i + Prims.of_int 1)
                      * Prims.of_int n_producers / Prims.of_int n_domains
                    in
                    let count_p : Prims.int =
                      Prims.op_Subtraction stop_excl start
                    in

                    (* build span = [start + 0 ; … ; start + (count-1)] with Prims math only *)
                    let rec build_span acc (k : Prims.int) =
                      if Prims.op_GreaterThanOrEqual k count_p then
                        Stdlib.List.rev acc
                      else
                        let elt = Prims.op_Addition start k in
                        build_span (elt :: acc)
                          (Prims.op_Addition k (Prims.of_int 1))
                    in
                    let span : Prims.int list =
                      build_span [] (Prims.of_int 0)
                    in

                    (* iterate each producer in this domain *)
                    Stdlib.List.iter
                      (fun (_p : Prims.int) ->
                        (* 1-slot reply stream for THIS producer, reused every iteration *)
                        (* per-producer, reused *)
                        let reply : Prims.int Eio.Stream.t =
                          Eio.Stream.create 1
                        in
                        for i = 1 to iters do
                          let x = Prims.of_int 1 in
                          Q.enqueue q (fun () ->
                              Eio.Stream.add reqs (Request { x; reply }));
                          let _y = Eio.Stream.take reply in
                          
                          if i land 0x3FF = 0 then Eio.Fiber.yield ();
                        done)
                      span)))
      in

      List.iter (fun p -> ignore (Eio.Promise.await_exn p)) prod_ps;
      (* 1) Send Stop through the same TLQ so it’s ordered after all work *)
      Q.enqueue q (fun () -> Eio.Stream.add reqs Stop);

      (* 2) Now tell consumers they may exit once the queue is empty *)
      set_stop true;

      (* 3) Give the fibers a scheduling turn to process Stop and wind down *)
      Eio.Fiber.yield ();
      Eio.Time.sleep clock 0.05;
      (* Memtrace.stop_tracing tracer; *)
      

      let t1 = Unix.gettimeofday () in

      (* ---- stats identical to 3S ---- *)
      let total_i : Prims.int =
        Array.fold_left
          (fun acc k_nat -> Prims.op_Addition acc (Obj.magic k_nat : Prims.int))
          (Prims.of_int 0) counts
      in
      let min_i, max_i =
        let first : Prims.int = (Obj.magic counts.(0) : Prims.int) in
        Array.fold_left
          (fun (mn, mx) k_nat ->
            let ki : Prims.int = (Obj.magic k_nat : Prims.int) in
            let mn' = if Prims.op_LessThan ki mn then ki else mn in
            let mx' = if Prims.op_GreaterThan ki mx then ki else mx in
            (mn', mx'))
          (first, first) counts
      in
      let secs = t1 -. t0 in
      let avg_f = f_of_int total_i /. float_of_int n_consumers in
      let imb_f =
        if Prims.op_Equality max_i (Prims.of_int 0) then 0.0
        else
          f_of_int (Prims.op_Subtraction max_i min_i) /. f_of_int max_i *. 100.0
      in
      let rate_f = f_of_int total_i /. secs in
      

      Printf.printf "=== PCM × TwoLockQueue (Eio) ===\n";
      Printf.printf "producers=%d  consumers=%d  iters/producer=%d\n"
        n_producers n_consumers iters;
      Array.iteri
        (fun i k_nat ->
          Printf.printf "T%-2d: %s\n" i
            (Prims.string_of_int (Obj.magic k_nat : Prims.int)))
        counts;
      Printf.printf "total=%s  time=%.3fs  throughput=%.0f ops/s\n%!"
        (Prims.string_of_int total_i)
        secs rate_f;
      Printf.printf "min=%s  max=%s  avg=%.1f  imbalance=%.1f%%%%\n%!"
        (Prims.string_of_int min_i)
        (Prims.string_of_int max_i)
        avg_f imb_f)
      
(* ---------------------- MODE 3Q: TLQ × PCM (Eio fibers + multi-domains) + SQLite3 ---------------------- *)
let run_mode3_sqlite () =
  Eio_main.run (fun env ->
      Eio.traceln "Eio backend = %s" (Eio.Stdenv.backend_id env);
      (* let tracer =
        Memtrace.start_tracing ~context:None ~filename:"alloc.ctf"
          ~sampling_rate:1e-8
      in *)

      (* ---- SQLite setup (single connection, single writer fiber) ---- *)

      let db_path =
        try Sys.getenv "SQLITE_PATH" with _ -> "pcm_mode3.sqlite"
      in

      let db = Sqlite3.db_open db_path in
      (* avoid SQLITE_BUSY if something briefly contends (shouldn’t, but harmless) *)
      let () = ignore (Sqlite3.busy_timeout db 5000) in

      (* Reasonable defaults. For max benchmark speed you can relax these later. *)
      let () =
        ignore (Sqlite3.exec db "PRAGMA journal_mode=WAL;");
        ignore (Sqlite3.exec db "PRAGMA synchronous=NORMAL;");
        ignore (Sqlite3.exec db "PRAGMA temp_store=MEMORY;");
        ignore (Sqlite3.exec db
          "CREATE TABLE IF NOT EXISTS pcm_log (\
             step INTEGER PRIMARY KEY, \
             x    INTEGER NOT NULL, \
             y    INTEGER NOT NULL\
           );");
        ignore (Sqlite3.exec db "DELETE FROM pcm_log;")
      in

      (* BIG performance point: wrap inserts in a transaction *)
      let () = ignore (Sqlite3.exec db "BEGIN;") in

      let insert_stmt =
        Sqlite3.prepare db "INSERT INTO pcm_log(step, x, y) VALUES (?, ?, ?)"
      in

      (* In F* extraction, Prims.int is typically Zarith Z.t *)
      let int64_of_prims (z : Prims.int) : int64 =
        Z.to_int64 z
      in

      let stepper = ref 0 in
      let next_step () = incr stepper; !stepper in
      let db_insert ~(step:int) ~(x:Prims.int) ~(y:Prims.int) : unit =
        ignore (Sqlite3.reset insert_stmt);
        ignore (Sqlite3.clear_bindings insert_stmt);
      
        ignore (Sqlite3.bind insert_stmt 1 (Sqlite3.Data.INT (int64_of_prims step)));
        ignore (Sqlite3.bind insert_stmt 2 (Sqlite3.Data.INT (int64_of_prims x)));
        ignore (Sqlite3.bind insert_stmt 3 (Sqlite3.Data.INT (int64_of_prims y)));
      
        match Sqlite3.step insert_stmt with
        | Sqlite3.Rc.DONE -> ()
        | rc -> failwith ("sqlite insert failed: " ^ Sqlite3.Rc.to_string rc)
      in

      let clock = env#clock in
      (* keep your >! helper for Prims comparisons when needed *)
      let ( >! ) a b = Prims.op_GreaterThan (Prims.of_int a) (Prims.of_int b) in

      (* Plain OCaml ints from env; rename to avoid clashes *)
      let n_producers =
        try int_of_string (Sys.getenv "PRODUCERS") with _ -> 8
      in
      let n_consumers =
        try int_of_string (Sys.getenv "CONSUMERS") with _ -> 8
      in
      let iters =
        try int_of_string (Sys.getenv "ITERS") with _ -> 1_000_000
      in
      let n_domains =
        try int_of_string (Sys.getenv "DOMAINS")
        with _ -> max 1 (Domain.recommended_domain_count ())
      in

      Printf.printf
        "[3E] domains=%d producers=%d consumers=%d iters/producer=%d\n%!"
        n_domains n_producers n_consumers iters;

      (* Keep Steel TLQ; drop dummy *)
      let q = Q.new_queue (fun () -> ()) in
      ignore (Q.dequeue q);

      (* Stop flag guarded by Eio.Mutex *)
      (* Atomic stop flag *)
      let stop = Atomic.make false in

      (* Same function names as before *)
      let get_stop () = Atomic.get stop in
      let set_stop v  = Atomic.set stop v in

      (* Optional helpers, if useful *)
      let request_stop () : unit =
        ignore (Atomic.exchange stop true) in (* sets to true, discards previous *)
      
      let was_stopped_before_request () : bool =
        Atomic.exchange stop true in          (* sets to true, returns previous *)

      (* Bridges already defined elsewhere:
       val nat_of_int : int -> Prims.nat
       val int_of_nat : Prims.nat -> int
       val f_of_int   : Prims.int -> float
    *)
      let counts : Prims.nat array = Array.make n_consumers (Prims.of_int 0) in
      let incr_nat (a : Prims.nat array) i =
        let v = int_of_nat a.(i) + Prims.of_int 1 in
        a.(i) <- nat_of_int v
      in

      (* PCM service unchanged *)
      let serve_b (cB : Duplex_PCM.ch) : unit =
        let x =
          Duplex_PCM.channel_recv Duplex_PCM.B
            (Steel_Channel_Protocol.dual duat)
            cB
        in
        let xi : Prims.int = (Obj.magic x : Prims.int) in
      
        (* one global step per received message, in the B-server fiber *)
        let s = next_step () in
      
        (* y becomes 43,44,45,... (since s starts at 1) *)
        let yi : Prims.int = (Prims.of_int s) + (Prims.of_int 42) in
      
        let stepB =
          Steel_Channel_Protocol.step (Steel_Channel_Protocol.dual duat) x
        in
      
        Duplex_PCM.channel_send Duplex_PCM.B stepB cB (Obj.magic yi);
      
        (* insert uses the SAME step value *)
        db_insert ~step:(Prims.of_int s) ~x:xi ~y:yi
      in


      let t0 = Unix.gettimeofday () in

      let served = ref 0 in

      Switch.run @@ fun sw ->
      (* --- Single B-server fed by a request stream --- *)
      (* one request bus on the main Eio scheduler domain *)
      let reqs : req Eio.Stream.t = Eio.Stream.create (max 1 n_consumers) in

      (* 2) One B-server fiber: does full PCM per request *)
      Eio.Fiber.fork ~sw (fun () ->
          let rec serve_loop () =
            match Eio.Stream.take reqs with
            | Request { x; reply } ->
                let cA, cB = Duplex_PCM.new_channel duat in
                let x_any : Obj.t = (Obj.magic x : Obj.t) in
                Duplex_PCM.channel_send Duplex_PCM.A duat cA x_any;
                let stepA = Steel_Channel_Protocol.step duat x_any in
                serve_b cB;
                let y_any = Duplex_PCM.channel_recv Duplex_PCM.A stepA cA in
                Eio.Stream.add reply (Obj.magic y_any : Prims.int);
                serve_loop ()
            | Stop -> () (* graceful exit *)
          in
          serve_loop ());

      (* one gate to guard dequeue only; queue internals unchanged *)
      let deq_gate = Eio.Mutex.create () in

      (* 3) Consumers: pop TLQ and run closures (those closures add to [reqs]) *)
      let cids = Stdlib.List.init n_consumers (fun i -> i) in
      (* Consumers: pop TLQ, execute, then ALWAYS yield *)
      Stdlib.List.iter
        (fun cid ->
          Eio.Fiber.fork ~sw (fun () ->
            let served = ref 0 in
            let rec loop () =
              match Q.dequeue q with
              | Some f ->
                  f ();                      (* do the work first *)
                  incr_nat counts cid;       (* then record it *)
                  incr served;
                  Eio.Fiber.yield ();        (* <- unconditional fairness *)
                  loop ()
              | None ->
                  if get_stop () then () else (Eio.Fiber.yield (); loop ())
            in
            loop ()))
        cids;

      (* ---- Producers spread across domains, no for-loop on spans ---- *)
      let prod_ps =
        List.init n_domains (fun dom_i ->
            Eio.Fiber.fork_promise ~sw (fun () ->
                Eio.Domain_manager.run env#domain_mgr (fun () ->
                    (* shard indices using half-open [start, stop) — all in Prims.int *)
                    let start : Prims.int =
                      Prims.of_int dom_i * Prims.of_int n_producers
                      / Prims.of_int n_domains
                    in
                    let stop_excl : Prims.int =
                      (Prims.of_int dom_i + Prims.of_int 1)
                      * Prims.of_int n_producers / Prims.of_int n_domains
                    in
                    let count_p : Prims.int =
                      Prims.op_Subtraction stop_excl start
                    in

                    (* build span = [start + 0 ; … ; start + (count-1)] with Prims math only *)
                    let rec build_span acc (k : Prims.int) =
                      if Prims.op_GreaterThanOrEqual k count_p then
                        Stdlib.List.rev acc
                      else
                        let elt = Prims.op_Addition start k in
                        build_span (elt :: acc)
                          (Prims.op_Addition k (Prims.of_int 1))
                    in
                    let span : Prims.int list =
                      build_span [] (Prims.of_int 0)
                    in

                    (* iterate each producer in this domain *)
                    Stdlib.List.iter
                      (fun (_p : Prims.int) ->
                        (* 1-slot reply stream for THIS producer, reused every iteration *)
                        (* per-producer, reused *)
                        let reply : Prims.int Eio.Stream.t =
                          Eio.Stream.create 1
                        in
                        for i = 1 to iters do
                          let x = Prims.of_int 1 in
                          Q.enqueue q (fun () ->
                              Eio.Stream.add reqs (Request { x; reply }));
                          let _y = Eio.Stream.take reply in
                          
                          if i land 0x3FF = 0 then Eio.Fiber.yield ();
                        done)
                      span)))
      in

      List.iter (fun p -> ignore (Eio.Promise.await_exn p)) prod_ps;
      (* 1) Send Stop through the same TLQ so it’s ordered after all work *)
      Q.enqueue q (fun () -> Eio.Stream.add reqs Stop);

      (* 2) Now tell consumers they may exit once the queue is empty *)
      set_stop true;

      (* 3) Give the fibers a scheduling turn to process Stop and wind down *)
      Eio.Fiber.yield ();
      Eio.Time.sleep clock 0.05;
      (* after Stop has been processed and before printing final stats *)
      ignore (Sqlite3.exec db "COMMIT;");
      ignore (Sqlite3.finalize insert_stmt);
      ignore (Sqlite3.db_close db);
      (* Memtrace.stop_tracing tracer; *)
      

      let t1 = Unix.gettimeofday () in

      (* ---- stats identical to 3S ---- *)
      let total_i : Prims.int =
        Array.fold_left
          (fun acc k_nat -> Prims.op_Addition acc (Obj.magic k_nat : Prims.int))
          (Prims.of_int 0) counts
      in
      let min_i, max_i =
        let first : Prims.int = (Obj.magic counts.(0) : Prims.int) in
        Array.fold_left
          (fun (mn, mx) k_nat ->
            let ki : Prims.int = (Obj.magic k_nat : Prims.int) in
            let mn' = if Prims.op_LessThan ki mn then ki else mn in
            let mx' = if Prims.op_GreaterThan ki mx then ki else mx in
            (mn', mx'))
          (first, first) counts
      in
      let secs = t1 -. t0 in
      let avg_f = f_of_int total_i /. float_of_int n_consumers in
      let imb_f =
        if Prims.op_Equality max_i (Prims.of_int 0) then 0.0
        else
          f_of_int (Prims.op_Subtraction max_i min_i) /. f_of_int max_i *. 100.0
      in
      let rate_f = f_of_int total_i /. secs in
      

      Printf.printf "=== PCM × TwoLockQueue (Eio) ===\n";
      Printf.printf "producers=%d  consumers=%d  iters/producer=%d\n"
        n_producers n_consumers iters;
      Array.iteri
        (fun i k_nat ->
          Printf.printf "T%-2d: %s\n" i
            (Prims.string_of_int (Obj.magic k_nat : Prims.int)))
        counts;
      Printf.printf "total=%s  time=%.3fs  throughput=%.0f ops/s\n%!"
        (Prims.string_of_int total_i)
        secs rate_f;
      Printf.printf "min=%s  max=%s  avg=%.1f  imbalance=%.1f%%%%\n%!"
        (Prims.string_of_int min_i)
        (Prims.string_of_int max_i)
        avg_f imb_f)
  
(* --------------------- MODE 3T: TLQ x PCM (Eio fibers + multi-domains + tracing) + SQlite3  ----------------------------- *)

type ocaml_int = Stdlib.Int.t

type trace_event = {
  seq : ocaml_int;
  direction : string;
  value : Prims.int;
}

let events_of_trace
    (tr : (Obj.t, Obj.t) Steel_Channel_Protocol.trace)
  : trace_event list =
  let rec walk
      (seq : ocaml_int)
      (acc : trace_event list)
      (tr : (Obj.t, Obj.t) Steel_Channel_Protocol.trace)
    : trace_event list =
    match tr with
    | Steel_Channel_Protocol.Waiting _ ->
        Stdlib.List.rev acc

    | Steel_Channel_Protocol.Message (q, x, _q', tail) ->
        let direction =
          if Duplex_PCM.is_send q then
            "A->B"
          else if Duplex_PCM.is_recv q then
            "B->A"
          else
            "?"
        in

        let value : Prims.int =
          Obj.magic x
        in

        let ev = {
          seq;
          direction;
          value;
        } in

        walk
          Stdlib.(seq + 1)
          (ev :: acc)
          tail
  in

  walk 1 [] tr

module Trace_monitor = struct

  type command =
    | Nop
    | Watch of ocaml_int * Duplex_PCM.ch
    | Stop

  type watched = {
    id : ocaml_int;
    chan : Duplex_PCM.ch;
    mutable seen : ocaml_int;
  }

  type pending_event = {
    channel_id : ocaml_int;
    ev : trace_event;
  }

  type t = {
    commands : command TLQ.t;
    next_id : ocaml_int Atomic.t;
    domain : unit Domain.t;
  }

  (* ------------------------------------------------------------ *)
  (* Start trace-monitor domain                                   *)
  (* ------------------------------------------------------------ *)

  let start db_path =

    (* Control messages use your existing TwoLockQueue. *)
    let commands =
      TLQ.new_queue Nop
    in

    (* Drop TwoLockQueue's dummy first item. *)
    ignore (TLQ.dequeue commands);

    (* Native OCaml integer. Do not use Prims.of_int here. *)
    let next_id : ocaml_int Atomic.t =
      Atomic.make 0
    in

    let domain =
      Domain.spawn
        (fun () ->

          (* ---------------------------------------------------- *)
          (* SQLite belongs exclusively to this monitor domain.   *)
          (* ---------------------------------------------------- *)

          let db =
            Sqlite3.db_open db_path
          in

          ignore
            (Sqlite3.busy_timeout db 5000);

          ignore
            (Sqlite3.exec db
               "PRAGMA journal_mode=WAL;");

          ignore
            (Sqlite3.exec db
               "PRAGMA synchronous=NORMAL;");

          ignore
            (Sqlite3.exec db
               "PRAGMA temp_store=MEMORY;");

          (* ---------------------------------------------------- *)
          (* Schema                                               *)
          (* ---------------------------------------------------- *)

          ignore
            (Sqlite3.exec db
               "CREATE TABLE IF NOT EXISTS pcm_trace (\
                channel_id INTEGER NOT NULL,\
                seq        INTEGER NOT NULL,\
                direction  TEXT    NOT NULL,\
                value      INTEGER NOT NULL,\
                PRIMARY KEY(channel_id, seq)\
                );");

          (* Start each test with an empty trace table. *)
          ignore
            (Sqlite3.exec db
               "DELETE FROM pcm_trace;");

          (* One large transaction for this experiment. *)
          ignore
            (Sqlite3.exec db "BEGIN;");

                    (* ---------------------------------------------------- *)
          (* Batched SQLite writer                                *)
          (* ---------------------------------------------------- *)

          let batch_size : ocaml_int =
            128
          in

          let batch : pending_event option array =
            Array.make batch_size None
          in

          let batch_len : ocaml_int ref =
            ref 0
          in

          let make_values (n : ocaml_int) : string =
            Stdlib.String.concat
              ","
              (Stdlib.List.init
                 n
                 (fun _ -> "(?, ?, ?, ?)"))
          in

          (* Prepare one statement representing exactly one
             complete batch. This gets reused for the entire run. *)
          let batch_stmt =
            let sql =
              "INSERT OR IGNORE INTO pcm_trace \
               (channel_id, seq, direction, value) VALUES "
              ^ make_values batch_size
            in
            Sqlite3.prepare db sql
          in

          let bind_event
              stmt
              (slot : ocaml_int)
              (p : pending_event)
            : unit =

            let base : ocaml_int =
              Stdlib.(slot * 4)
            in

            ignore
              (Sqlite3.bind
                 stmt
                 Stdlib.(base + 1)
                 (Sqlite3.Data.INT
                    (Stdlib.Int64.of_int p.channel_id)));

            ignore
              (Sqlite3.bind
                 stmt
                 Stdlib.(base + 2)
                 (Sqlite3.Data.INT
                    (Stdlib.Int64.of_int p.ev.seq)));

            ignore
              (Sqlite3.bind
                 stmt
                 Stdlib.(base + 3)
                 (Sqlite3.Data.TEXT p.ev.direction));

            ignore
              (Sqlite3.bind
                 stmt
                 Stdlib.(base + 4)
                 (Sqlite3.Data.INT
                    (Z.to_int64 p.ev.value)))
          in

          let step_statement stmt =
            match Sqlite3.step stmt with
            | Sqlite3.Rc.DONE ->
                ()

            | rc ->
                failwith
                  ("sqlite trace batch insert failed: "
                   ^ Sqlite3.Rc.to_string rc)
          in

          (* Full batches reuse batch_stmt, so there is no
             prepare/finalize operation on the hot path. *)
          let flush_full_batch () : unit =
            ignore
              (Sqlite3.reset batch_stmt);

            ignore
              (Sqlite3.clear_bindings batch_stmt);

            for slot = 0 to Stdlib.pred batch_size do
              match batch.(slot) with
              | Some p ->
                  bind_event batch_stmt slot p

              | None ->
                  failwith
                    "trace batch unexpectedly incomplete"
            done;

            step_statement batch_stmt;

            batch_len := 0
          in

          (* At shutdown we may have fewer than [batch_size]
             entries. Prepare one correctly-sized statement for
             that final partial batch. *)
          let flush_partial_batch () : unit =
            let n : ocaml_int =
              !batch_len
            in

            if Stdlib.(n > 0) then begin
              let sql =
                "INSERT OR IGNORE INTO pcm_trace \
                 (channel_id, seq, direction, value) VALUES "
                ^ make_values n
              in

              let stmt =
                Sqlite3.prepare db sql
              in

              for slot = 0 to Stdlib.pred n do
                match batch.(slot) with
                | Some p ->
                    bind_event stmt slot p

                | None ->
                    failwith
                      "trace partial batch unexpectedly incomplete"
              done;

              step_statement stmt;

              ignore
                (Sqlite3.finalize stmt);

              batch_len := 0
            end
          in

          (* This replaces the old immediate SQLite insert. *)
          let insert
              (channel_id : ocaml_int)
              (ev : trace_event)
            : unit =

            let slot : ocaml_int =
              !batch_len
            in

            batch.(slot) <-
              Some {
                channel_id;
                ev;
              };

            batch_len :=
              Stdlib.(slot + 1);

            if Stdlib.(!batch_len = batch_size) then
              flush_full_batch ()
          in

          (* ---------------------------------------------------- *)
          (* Channels currently being watched                    *)
          (* ---------------------------------------------------- *)

          let active : watched list ref =
            ref []
          in

          let stopping =
            ref false
          in

          (* ---------------------------------------------------- *)
          (* Pull control messages from TwoLockQueue              *)
          (* ---------------------------------------------------- *)

          let rec drain_commands () =
            match TLQ.dequeue commands with

            | None ->
                ()

            | Some Nop ->
                drain_commands ()

            | Some (Watch (id, chan)) ->

                active :=
                  {
                    id;
                    chan;
                    seen = 0;
                  }
                  :: !active;

                drain_commands ()

            | Some Stop ->

                stopping := true;

                drain_commands ()
          in

          (* ---------------------------------------------------- *)
          (* Inspect one live Steel trace                         *)
          (*                                                      *)
          (* Returns true once its protocol reaches Return.       *)
          (* ---------------------------------------------------- *)

          let scan
              (w : watched)
            : bool =

            let Prims.Mkdtuple2 (next, tr) =
              Duplex_PCM.trace_snapshot w.chan
            in

            (* Convert Steel's actual trace to sequential events. *)
            let events =
              events_of_trace tr
            in

            (* Insert only events we haven't already materialized. *)
            Stdlib.List.iter
              (fun (ev : trace_event) ->

                if Stdlib.(ev.seq > w.seen) then
                  insert w.id ev)

              events;

            (* Because seq starts at 1, length is also the highest
               message number observed so far. *)
            w.seen <-
              Stdlib.List.length events;

            (* Return true when this endpoint has finished. *)
            Duplex_PCM.is_fin next
          in

          (* ---------------------------------------------------- *)
          (* Scan every currently-live channel                   *)
          (* ---------------------------------------------------- *)

          let scan_active () =

            active :=
              Stdlib.List.filter
                (fun (w : watched) ->

                  try
                    (* Keep channel while it has not finished. *)
                    not (scan w)

                  with exn ->

                    Printf.eprintf
                      "[trace-monitor] channel %d: %s\n%!"
                      w.id
                      (Printexc.to_string exn);

                    (* Keep it so a transient read failure doesn't
                       permanently discard its trace. *)
                    true)

                !active
          in

          (* ---------------------------------------------------- *)
          (* Monitor loop                                         *)
          (* ---------------------------------------------------- *)

          let rec loop () =

            (* Discover newly-created channels. *)
            drain_commands ();

            (* Observe their current cumulative traces. *)
            scan_active ();

            if !stopping then begin
              (* Final trace scan. *)
              scan_active ();

              (* Flush anything left that did not fill a complete batch. *)
              flush_partial_batch ();

              ignore
                (Sqlite3.exec db "COMMIT;");

              (* This is the persistent prepared statement used for full batches. *)
              ignore
                (Sqlite3.finalize batch_stmt);

              ignore
                (Sqlite3.db_close db)
          end
          else begin
            Unix.sleepf 0.001;
            loop ()
          end
          in

          loop ())
    in

    {
      commands;
      next_id;
      domain;
    }

  (* ------------------------------------------------------------ *)
  (* Register a channel                                           *)
  (* ------------------------------------------------------------ *)

  let watch
      (t : t)
      (chan : Duplex_PCM.ch)
    : ocaml_int =

    let id : ocaml_int =
      Atomic.fetch_and_add
        t.next_id
        1
    in

    TLQ.enqueue
      t.commands
      (Watch (id, chan));

    id

  (* ------------------------------------------------------------ *)
  (* Stop monitor and wait for SQLite to be committed             *)
  (* ------------------------------------------------------------ *)

  let stop
      (t : t)
    : unit =

    TLQ.enqueue
      t.commands
      Stop;

    Domain.join
      t.domain
end

let run_mode3_sqlite_trace () =
  Eio_main.run (fun env ->
      Eio.traceln "Eio backend = %s" (Eio.Stdenv.backend_id env);

      (* ------------------------------------------------------------ *)
      (* Trace monitor                                                *)
      (* ------------------------------------------------------------ *)

      let db_path =
        try Sys.getenv "SQLITE_PATH"
        with _ -> "pcm_mode3_trace.sqlite"
      in

      let trace_monitor =
        Trace_monitor.start db_path
      in

      let clock = env#clock in

      (* ------------------------------------------------------------ *)
      (* Configuration                                                *)
      (* ------------------------------------------------------------ *)

      let n_producers =
        try int_of_string (Sys.getenv "PRODUCERS")
        with _ -> 8
      in

      let n_consumers =
        try int_of_string (Sys.getenv "CONSUMERS")
        with _ -> 8
      in

      let iters =
        try int_of_string (Sys.getenv "ITERS")
        with _ -> 1_000_000
      in

      let n_domains =
        try int_of_string (Sys.getenv "DOMAINS")
        with _ ->
          max 1 (Domain.recommended_domain_count ())
      in

      Printf.printf
        "[3T] domains=%d producers=%d consumers=%d iters/producer=%d\n%!"
        n_domains
        n_producers
        n_consumers
        iters;

      (* ------------------------------------------------------------ *)
      (* Work queue                                                   *)
      (* ------------------------------------------------------------ *)

      let q =
        Q.new_queue (fun () -> ())
      in

      (* Drop dummy queue element. *)
      ignore (Q.dequeue q);

      let stop =
        Atomic.make false
      in

      let get_stop () =
        Atomic.get stop
      in

      let set_stop v =
        Atomic.set stop v
      in

      (* ------------------------------------------------------------ *)
      (* Per-consumer statistics                                      *)
      (* ------------------------------------------------------------ *)

      let counts : Prims.nat array =
        Array.make n_consumers (Prims.of_int 0)
      in

      let incr_nat (a : Prims.nat array) i =
        let v =
          int_of_nat a.(i) + Prims.of_int 1
        in
        a.(i) <- nat_of_int v
      in

      (* ------------------------------------------------------------ *)
      (* B endpoint                                                   *)
      (* ------------------------------------------------------------ *)

      let serve_b (cB : Duplex_PCM.ch) : unit =
        let x =
          Duplex_PCM.channel_recv
            Duplex_PCM.B
            (Steel_Channel_Protocol.dual duat)
            cB
        in

        let xi : Prims.int =
          (Obj.magic x : Prims.int)
        in

        let yi : Prims.int =
          Prims.op_Addition
            xi
            (Prims.of_int 42)
        in

        let stepB =
          Steel_Channel_Protocol.step
            (Steel_Channel_Protocol.dual duat)
            x
        in

        Duplex_PCM.channel_send
          Duplex_PCM.B
          stepB
          cB
          (Obj.magic yi)
      in

      let t0 =
        Unix.gettimeofday ()
      in

      (* ------------------------------------------------------------ *)
      (* Eio work                                                     *)
      (* ------------------------------------------------------------ *)

      Switch.run (fun sw ->

        let reqs : req Eio.Stream.t =
          Eio.Stream.create
            (max 1 n_consumers)
        in

        (* ---------------------------------------------------------- *)
        (* PCM server                                                 *)
        (* ---------------------------------------------------------- *)

        Eio.Fiber.fork ~sw (fun () ->
            let rec serve_loop () =
              match Eio.Stream.take reqs with

              | Request { x; reply } ->

                  (* Create a fresh Steel PCM channel. *)
                  let cA, cB =
                    Duplex_PCM.new_channel duat
                  in

                  (* Register A's endpoint with the independent
                     trace-monitor domain before advancing it. *)
                  let _channel_id =
                    Trace_monitor.watch
                      trace_monitor
                      cA
                  in

                  let x_any : Obj.t =
                    (Obj.magic x : Obj.t)
                  in

                  (* A -> B *)
                  Duplex_PCM.channel_send
                    Duplex_PCM.A
                    duat
                    cA
                    x_any;

                  let stepA =
                    Steel_Channel_Protocol.step
                      duat
                      x_any
                  in

                  (* B receives x and sends x + 42. *)
                  serve_b cB;

                  (* B -> A *)
                  let y_any =
                    Duplex_PCM.channel_recv
                      Duplex_PCM.A
                      stepA
                      cA
                  in

                  Eio.Stream.add
                    reply
                    (Obj.magic y_any : Prims.int);

                  serve_loop ()

              | Stop ->
                  ()
            in

            serve_loop ());

        (* ---------------------------------------------------------- *)
        (* Queue consumers                                            *)
        (* ---------------------------------------------------------- *)

        let cids =
          Stdlib.List.init
            n_consumers
            (fun i -> i)
        in

        Stdlib.List.iter
          (fun cid ->
            Eio.Fiber.fork ~sw (fun () ->
                let rec loop () =
                  match Q.dequeue q with

                  | Some f ->
                      f ();

                      incr_nat counts cid;

                      Eio.Fiber.yield ();

                      loop ()

                  | None ->
                      if get_stop () then
                        ()
                      else begin
                        Eio.Fiber.yield ();
                        loop ()
                      end
                in

                loop ()))
          cids;

        (* ---------------------------------------------------------- *)
        (* Producers                                                  *)
        (* ---------------------------------------------------------- *)

        let prod_ps =
          Stdlib.List.init n_domains
            (fun dom_i ->
              Eio.Fiber.fork_promise ~sw (fun () ->
                  Eio.Domain_manager.run
                    env#domain_mgr
                    (fun () ->

                      let start : Prims.int =
                        Prims.of_int dom_i
                        * Prims.of_int n_producers
                        / Prims.of_int n_domains
                      in

                      let stop_excl : Prims.int =
                        (Prims.of_int dom_i + Prims.of_int 1)
                        * Prims.of_int n_producers
                        / Prims.of_int n_domains
                      in

                      let count_p : Prims.int =
                        Prims.op_Subtraction
                          stop_excl
                          start
                      in

                      let rec build_span
                          acc
                          (k : Prims.int) =
                        if
                          Prims.op_GreaterThanOrEqual
                            k
                            count_p
                        then
                          Stdlib.List.rev acc
                        else
                          let elt =
                            Prims.op_Addition
                              start
                              k
                          in

                          build_span
                            (elt :: acc)
                            (Prims.op_Addition
                               k
                               (Prims.of_int 1))
                      in

                      let span : Prims.int list =
                        build_span
                          []
                          (Prims.of_int 0)
                      in

                      Stdlib.List.iter
                        (fun (_p : Prims.int) ->

                          let reply :
                              Prims.int Eio.Stream.t =
                            Eio.Stream.create 1
                          in

                          for i = 1 to iters do
                            let x =
                              Prims.of_int 1
                            in

                            Q.enqueue q
                              (fun () ->
                                Eio.Stream.add
                                  reqs
                                  (Request { x; reply }));

                            let _y =
                              Eio.Stream.take reply
                            in

                            if i land 0x3FF = 0 then
                              Eio.Fiber.yield ()
                          done)
                        span)))
        in

        (* ---------------------------------------------------------- *)
        (* Wait for producers                                         *)
        (* ---------------------------------------------------------- *)

        Stdlib.List.iter
          (fun p ->
            ignore
              (Eio.Promise.await_exn p))
          prod_ps;

        (* ---------------------------------------------------------- *)
        (* Shut down Eio side                                         *)
        (* ---------------------------------------------------------- *)

        (* Put Stop through the same queue after all producer work. *)
        Q.enqueue q
          (fun () ->
            Eio.Stream.add reqs Stop);

        set_stop true;

        Eio.Fiber.yield ();

        Eio.Time.sleep
          clock
          0.05;

        ()
      );

      (* ------------------------------------------------------------ *)
      (* Switch.run has completed.                                    *)
      (* Stop trace domain, perform final scan and commit SQLite.      *)
      (* ------------------------------------------------------------ *)

      Trace_monitor.stop trace_monitor;

      let t1 =
        Unix.gettimeofday ()
      in

      (* ------------------------------------------------------------ *)
      (* Statistics                                                   *)
      (* ------------------------------------------------------------ *)

      let total_i : Prims.int =
        Array.fold_left
          (fun acc k_nat ->
            Prims.op_Addition
              acc
              (Obj.magic k_nat : Prims.int))
          (Prims.of_int 0)
          counts
      in

      let min_i, max_i =
        let first : Prims.int =
          (Obj.magic counts.(0) : Prims.int)
        in

        Array.fold_left
          (fun (mn, mx) k_nat ->
            let ki : Prims.int =
              (Obj.magic k_nat : Prims.int)
            in

            let mn' =
              if Prims.op_LessThan ki mn
              then ki
              else mn
            in

            let mx' =
              if Prims.op_GreaterThan ki mx
              then ki
              else mx
            in

            (mn', mx'))
          (first, first)
          counts
      in

      let secs =
        t1 -. t0
      in

      let avg_f =
        f_of_int total_i
        /. float_of_int n_consumers
      in

      let imb_f =
        if
          Prims.op_Equality
            max_i
            (Prims.of_int 0)
        then
          0.0
        else
          f_of_int
            (Prims.op_Subtraction
               max_i
               min_i)
          /. f_of_int max_i
          *. 100.0
      in

      let rate_f =
        f_of_int total_i /. secs
      in

      Printf.printf
        "=== PCM trace x TwoLockQueue (Eio + SQLite monitor) ===\n";

      Printf.printf
        "producers=%d  consumers=%d  iters/producer=%d\n"
        n_producers
        n_consumers
        iters;

      Array.iteri
        (fun i k_nat ->
          Printf.printf
            "T%-2d: %s\n"
            i
            (Prims.string_of_int
               (Obj.magic k_nat : Prims.int)))
        counts;

      Printf.printf
        "total=%s  time=%.3fs  throughput=%.0f ops/s\n%!"
        (Prims.string_of_int total_i)
        secs
        rate_f;

      Printf.printf
        "min=%s  max=%s  avg=%.1f  imbalance=%.1f%%%%\n%!"
        (Prims.string_of_int min_i)
        (Prims.string_of_int max_i)
        avg_f
        imb_f;

      Printf.printf
        "Steel PCM trace written to %s\n%!"
        db_path)
(* ---------------------- Entry: choose mode ---------------------- *)
let () =
  let mode = try Sys.getenv "MODE" with _ -> "3" in
  print_endline ("[boot] MODE=" ^ mode);
  match mode with
  | "0" -> run_mode0 ()
  | "1" -> run_mode1 ()
  | "2" -> run_mode2 ()
  | "3S" -> run_mode3_stress ()
  | "3E" -> run_mode3_eio ()
  | "3Q" -> run_mode3_sqlite ()
  | "3T" -> run_mode3_sqlite_trace ()
  | "3" | _ -> run_mode3 ()
