(* Main.ml — switchable queue (steel vs local), same forensic modes *)

open Prims
module TLQ = TwoLockQueue

(* ---- Eio glue ---- *)
open Eio.Std

module Eio_util = struct
  (* promise for the result of [f], exceptions captured in the promise *)
  let go ~sw (f : unit -> 'a) : 'a Promise.or_exn =
    Fiber.fork_promise ~sw f

  (* run [fn i] on N domains and wait for all to finish (propagate errors) *)
  let par_domains env n fn =
    Switch.run @@ fun sw ->
      let ps =
        List.init n (fun i ->
          Fiber.fork_promise ~sw (fun () ->
            Eio.Domain_manager.run env#domain_mgr (fun () -> fn i)))
      in
      List.iter (fun p -> ignore (Promise.await_exn p)) ps
end


let ( >! ) a b = Prims.op_GreaterThan (Prims.of_int a) (Prims.of_int b)

(* --- Local, minimal two-lock queue that cannot be shadowed --- *)
module QLocal = struct
  type 'a node = { mutable data : 'a option; mutable next : 'a node option }
  type 'a t = {
    head_mu : Mutex.t; tail_mu : Mutex.t;
    mutable head : 'a node; mutable tail : 'a node;
  }
  let new_queue seed =
    let d = { data = Some seed; next = None } in
    print_endline "[QLocal] new_queue"; { head_mu=Mutex.create (); tail_mu=Mutex.create (); head=d; tail=d }
  let enqueue q x =
    let n = { data = Some x; next = None } in
    Mutex.lock q.tail_mu;
    q.tail.next <- Some n; q.tail <- n;
    Mutex.unlock q.tail_mu;
    print_endline "[QLocal] enqueue"
  let dequeue q =
    Mutex.lock q.head_mu;
    let r =
      match q.head.next with
      | None   -> Mutex.unlock q.head_mu; print_endline "[QLocal] dequeue -> None"; None
      | Some n ->
          let old = q.head in q.head <- n;
          let v = old.data in Mutex.unlock q.head_mu;
          print_endline "[QLocal] dequeue -> Some"; v
    in r
end

(* --- Steel-TLQ wrapper with logs (your existing Qdbg) --- *)
module QSteel = struct
  type 'a t = 'a TLQ.t
  let new_queue = TLQ.new_queue
  let enqueue q (x:'a) =
    print_endline "[Qdbg] enqueue: begin"; flush stdout;
    TLQ.enqueue q x;
    print_endline "[Qdbg] enqueue: end"; flush stdout
  let dequeue q =
    let r = TLQ.dequeue q in
    (match r with
     | None   -> print_endline "[Qdbg] dequeue -> None"
     | Some _ -> print_endline "[Qdbg] dequeue -> Some");
    flush stdout; r
end

(* --- Local, minimal two-lock queue that cannot be shadowed --- *)


(* Use the local queue *)
module Q = TwoLockQueue

(* ---------- payload types ---------- *)
type t0 = Seed | Work of Prims.int  (* use Prims.int so we stay consistent *)
type t1 = Seed1 | Work1 of (unit -> unit)

(* ---------------------- PCM ping→pong protocol ---------------------- *)
let (pingpong : Duplex_PCM.dprot) =
  Duplex_PCM.bind (Duplex_PCM.send ())
    (fun _x -> Duplex_PCM.bind (Duplex_PCM.recv ()) (fun _y -> Duplex_PCM.done1))

(* ---------------------- MODE 0: TLQ single-thread ---------------------- *)
let run_mode0 () =
  print_endline "[M0] TLQ single-thread sanity";
  let q = Q.new_queue Seed in
  (* prove which queue we're actually using with a smoke roundtrip *)
  print_endline "[SMOKE] enqueue+dequeue on selected queue";
  Q.enqueue q Seed; ignore (Q.dequeue q);

  let d0 = Q.dequeue q in
  (match d0 with
   | None   -> print_endline "[M0] first dequeue -> None (expected before enqueue)"
   | Some _ -> print_endline "[M0] first dequeue -> Some (unexpected before enqueue)");
  print_endline "[M0] enqueue Work 41";
  Q.enqueue q (Work (Prims.of_int 41));
  let a = Q.dequeue q in
  (match a with
   | Some Seed -> print_endline "[M0] got Seed (dummy head) — OK"
   | Some (Work _v) -> Printf.printf "[M0] got Work (unexpected first)!\n"
   | None -> print_endline "[M0] got None (unexpected)");
  let b = Q.dequeue q in
  (match b with
   | Some (Work _v) -> Printf.printf "[M0] got Work — OK\n%!"
   | Some Seed -> print_endline "[M0] got Seed again (unexpected)"
   | None -> print_endline "[M0] got None (unexpected)")

(* ---------------------- MODE 1: TLQ two threads (no PCM) ---------------------- *)
let run_mode1 () =
  print_endline "[M1] TLQ two threads (no PCM)";
  let q = Q.new_queue Seed in
  ignore (Q.dequeue q); (* drop dummy like original harness *)

  let stop = ref false in
  let mu = Mutex.create () in
  let get_stop () = Mutex.lock mu; let v = !stop in Mutex.unlock mu; v in
  let set_stop v = Mutex.lock mu; stop := v; Mutex.unlock mu in

  let consumer () =
    let idle = ref 0 in
    let rec loop () =
      match Q.dequeue q with
      | Some Seed -> print_endline "[M1] consumer: Seed"; Thread.yield (); loop ()
      | Some (Work _v) -> Printf.printf "[M1] consumer: Work\n%!"; ()
      | None ->
          if get_stop () then (incr idle; if !idle >! 2048 then () else (Thread.delay 0.0005; loop ()))
          else (Thread.delay 0.0005; loop ())
    in loop ()
  in

  let cth = Thread.create consumer () in
  Thread.delay 0.010;
  print_endline "[M1] producer: enqueue Work 41";
  Q.enqueue q (Work (Prims.of_int 41));
  Thread.yield (); Thread.delay 0.010;  (* give consumer a scheduling window *)
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
  let get_stop () = Mutex.lock mu; let v = !stop in Mutex.unlock mu; v in
  let set_stop v = Mutex.lock mu; stop := v; Mutex.unlock mu in

  let consumer () =
    let idle = ref 0 in
    let rec loop () =
      match Q.dequeue q with
      | Some Seed1 -> print_endline "[M2] consumer: Seed"; Thread.yield (); loop ()
      | Some (Work1 f) -> print_endline "[M2] consumer: run task"; f (); ()
      | None ->
          if get_stop () then (incr idle; if !idle >! 2048 then () else (Thread.delay 0.0005; loop ()))
          else (Thread.delay 0.0005; loop ())
    in loop ()
  in
  let cth = Thread.create consumer () in
  Thread.delay 0.010;

  print_endline "[M2] producer: enqueue flag flip";
  Q.enqueue q (Work1 (fun () ->
    print_endline "[M2] task: writing flag=false";
    Steel_Reference.write_pt () flag false
  ));

  Thread.yield (); Thread.delay 0.010;
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
  let get_stop () = Mutex.lock mu; let v = !stop in Mutex.unlock mu; v in
  let set_stop v   = Mutex.lock mu; stop := v; Mutex.unlock mu in

  let b_started     = ref false in
  let a_sent        = ref false in
  let b_after_recv  = ref false in
  let b_after_send  = ref false in

  let watchdog_running = ref true in
  let watchdog () =
    let ticks = ref 0 in
    while !watchdog_running && (not (!ticks >! 3000)) do
      Thread.delay 0.001; incr ticks
    done;
    if !watchdog_running then begin
      print_endline "\n[watchdog] TIMEOUT — dumping state:";
      Printf.printf "  b_started=%b  a_sent=%b  b_after_recv=%b  b_after_send=%b\n%!"
        !b_started !a_sent !b_after_recv !b_after_send;
      print_endline "  (If b_started=false: consumer never saw Work; if a_sent=false: producer never sent.)";
      exit 2
    end
  in
  let _wd = Thread.create watchdog () in

  let serve_b cB =
    b_started := true; print_endline "[B] start"; flush stdout;
    Thread.delay 0.010;
    print_endline "[B] waiting to recv x";
    let x =
      Duplex_PCM.channel_recv Duplex_PCM.B
        (Steel_Channel_Protocol.dual pingpong) cB
    in
    b_after_recv := true; print_endline "[B] recv ok"; flush stdout;
    let xi : Prims.int = (Obj.magic x : Prims.int) in
    let yi : Prims.int = Prims.op_Addition xi (Prims.of_int 42) in
    let stepB =
      Steel_Channel_Protocol.step (Steel_Channel_Protocol.dual pingpong) x
    in
    Thread.delay 0.010;
    print_endline "[B] sending y";
    Duplex_PCM.channel_send Duplex_PCM.B stepB cB (Obj.magic yi);
    b_after_send := true; print_endline "[B] send ok"; flush stdout
  in

  let consumer () =
    let polls = ref 0 in
    let rec loop () =
      match Q.dequeue q with
      | Some f -> print_endline "[Q] DEQ -> run B"; f (); ()
      | None ->
          Thread.delay 0.002; incr polls;
          if get_stop () then ()
          else if !polls >! 10000 then (print_endline "[Q] too many polls — giving up"; ())
          else loop ()
    in loop ()
  in
  let cth = Thread.create consumer () in

  let pth =
    Thread.create
      (fun () ->
        let (cA1, cB1) = Duplex_PCM.new_channel pingpong in
        print_endline "[A] ENQ B task"; Q.enqueue q (fun () -> serve_b cB1);
        Thread.yield (); Thread.delay 0.010;
        print_endline "[A] sending x=1";
        let x_any = (Obj.magic (Prims.of_int 1) : Obj.t) in
        Duplex_PCM.channel_send Duplex_PCM.A pingpong cA1 x_any;
        a_sent := true; print_endline "[A] send ok";
        let stepA1 = Steel_Channel_Protocol.step pingpong x_any in
        print_endline "[A] waiting to recv y";
        let _ = Duplex_PCM.channel_recv Duplex_PCM.A stepA1 cA1 in
        print_endline "[A] recv ok"
      ) ()
  in

  Thread.join pth;
  set_stop true;
  Thread.join cth;

  watchdog_running := false;
  print_endline "[M3] done."

(* ==== Prims <-> OCaml bridges, fully annotated ==== *)(* helpers only for boundary conversions when you must print a Prims.int *)
(* nat helpers *)
(* === helpers: keep OCaml <-> Prims conversions simple === *)
let nat_of_int (x:int) : Prims.nat = (Obj.magic x : Prims.nat)
let int_of_nat (n:Prims.nat) : int = (Obj.magic n : int)

(* string-bridge to get floats from Prims.int without Zarith fuss *)
let f_of_int (i:Prims.int) : float =
  Stdlib.float_of_string (Prims.string_of_int i)

(* ---------------------- MODE 3S: TLQ × PCM stress (with stats) ---------------------- *)
let run_mode3_stress () =
  (* OCaml ints from env *)
  let producers =
    try int_of_string (Sys.getenv "PRODUCERS") with _ -> 1 in
  let consumers =
    try int_of_string (Sys.getenv "CONSUMERS") with _ -> 4 in
  let iters =
    try int_of_string (Sys.getenv "ITERS") with _ -> 100_000 in

  Printf.printf "[3S] start  producers=%d  consumers=%d  iters/producer=%d\n%!"
    producers consumers iters;

  (* TLQ of unit->unit tasks; drop dummy head element *)
  let q = Q.new_queue (fun () -> ()) in
  ignore (Q.dequeue q);

  (* stop flag (plain OCaml mutex) *)
  let stop = ref false in
  let mu = Mutex.create () in
  let get_stop () = Mutex.lock mu; let v = !stop in Mutex.unlock mu; v in
  let set_stop v  = Mutex.lock mu; stop := v; Mutex.unlock mu in

  (* B service: recv x; send y=x+42 *)
  let serve_b (cB : Duplex_PCM.ch) : unit =
    let x =
      Duplex_PCM.channel_recv Duplex_PCM.B
        (Steel_Channel_Protocol.dual pingpong) cB
    in
    let xi : Prims.int = (Obj.magic x : Prims.int) in
    let yi : Prims.int = Prims.op_Addition xi (Prims.of_int 42) in
    let stepB =
      Steel_Channel_Protocol.step (Steel_Channel_Protocol.dual pingpong) x
    in
    Duplex_PCM.channel_send Duplex_PCM.B stepB cB (Obj.magic yi)
  in

  (* per-consumer counts (Prims) to avoid pos/int clashes *)
  (* OCaml-side metrics *)
  
  let incr_nat (a:Prims.nat array) i =
  let v = int_of_nat a.(i) + (Prims.of_int 1) in
  a.(i) <- nat_of_int v in

  let counts : Prims.nat array = Array.make consumers (Prims.of_int 0) in

  (* consumers: pop & run B-service tasks *)
  let consumer_loop (cid) () =
    let idle_spins = ref 0 in
    let rec loop () =
      match Q.dequeue q with
      | Some f ->
          idle_spins := 0;
          incr_nat counts cid;
          f (); Thread.yield (); loop ()
      | None ->
          if get_stop () then (
            incr idle_spins;
            if !idle_spins >! 4 then ()          (* all OCaml ints here *)
            else (Thread.delay 0.05; Thread.yield (); loop ())
          ) else (Thread.delay 0.05; Thread.yield (); loop ())
    in
    loop ()
  in
  let cons =
    Array.init consumers (fun cid -> Thread.create (consumer_loop cid) ()) in

  (* producers: each does [iters] channel exchanges *)
  let prod =
    Array.init producers (fun _ ->
      Thread.create
        (fun () ->
          for i = 1 to iters do
            let (cA, cB) = Duplex_PCM.new_channel pingpong in
            Q.enqueue q (fun () -> serve_b cB);
            Thread.yield ();
            let x_any = (Obj.magic (Prims.of_int 1) : Obj.t) in
            Duplex_PCM.channel_send Duplex_PCM.A pingpong cA x_any;
            let stepA = Steel_Channel_Protocol.step pingpong x_any in
            let _y = Duplex_PCM.channel_recv Duplex_PCM.A stepA cA in
            if (i land 0x3FF) = 0 then Thread.yield ();
          done)
        ()
    )
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
    (Prims.of_int 0)
    counts
in

let min_i, max_i =
  let first : Prims.int = (Obj.magic counts.(0) : Prims.int) in
  Array.fold_left
    (fun (mn,mx) k_nat ->
       let ki : Prims.int = (Obj.magic k_nat : Prims.int) in
       let mn' = if Prims.op_LessThan ki mn then ki else mn in
       let mx' = if Prims.op_GreaterThan ki mx then ki else mx in
       (mn', mx'))
    (first, first)
    counts
in

(* ---- isolate float math so it can't unify with Prims ---- *)
let secs, avg_f, imb_f, rate_f =
  let secs : float = t1 -. t0 in
  let avg_f  : float = (f_of_int total_i) /. Stdlib.float_of_int consumers in
  let imb_f  : float =
    if Prims.op_Equality max_i (Prims.of_int 0) then 0.0
    else (f_of_int (Prims.op_Subtraction max_i min_i)) /. (f_of_int max_i) *. 100.0
  in
  let rate_f : float =
    (f_of_int total_i) /. secs
  in
  (secs, avg_f, imb_f, rate_f)
in

(* ---- printing ---- *)
Printf.printf "=== PCM × TwoLockQueue stress ===\n";
Printf.printf "producers=%d  consumers=%d  iters/producer=%d\n"
  producers consumers iters;

Array.iteri
  (fun i k_nat ->
     Printf.printf "T%-2d: %s\n" i (Prims.string_of_int (Obj.magic k_nat : Prims.int)))
  counts;

Printf.printf "total=%s  time=%.3fs  throughput=%.0f ops/s\n%!"
  (Prims.string_of_int total_i) secs rate_f;
Printf.printf "min=%s  max=%s  avg=%.1f  imbalance=%.1f%%%%\n%!"
  (Prims.string_of_int min_i)
  (Prims.string_of_int max_i)
  avg_f imb_f;
()

(* ---------------------- MODE 3E: TLQ × PCM (Eio fibers + multi-domains) ---------------------- *)
let run_mode3_eio () =
  Eio_main.run (fun env ->
    let clock = env#clock in
    (* keep your >! helper for Prims comparisons when needed *)
    let ( >! ) a b = Prims.op_GreaterThan (Prims.of_int a) (Prims.of_int b) in

    (* Plain OCaml ints from env; rename to avoid clashes *)
    let n_producers = try int_of_string (Sys.getenv "PRODUCERS") with _ -> 1 in
    let n_consumers = try int_of_string (Sys.getenv "CONSUMERS") with _ -> 4 in
    let iters       = try int_of_string (Sys.getenv "ITERS")     with _ -> 1_000_000 in
    let n_domains   =
      try int_of_string (Sys.getenv "DOMAINS")
      with _ -> max 1 (Domain.recommended_domain_count ())
    in

    Printf.printf "[3E] domains=%d producers=%d consumers=%d iters/producer=%d\n%!"
      n_domains n_producers n_consumers iters;

    (* Keep Steel TLQ; drop dummy *)
    let q = Q.new_queue (fun () -> ()) in
    ignore (Q.dequeue q);

    (* Stop flag guarded by Eio.Mutex *)
    let stop = ref false in
    let mu = Eio.Mutex.create () in
    let get_stop () = Eio.Mutex.use_ro mu (fun () -> !stop) in
    let set_stop v  = Eio.Mutex.use_rw ~protect:true mu (fun () -> stop := v) in

    (* Bridges already defined elsewhere:
       val nat_of_int : int -> Prims.nat
       val int_of_nat : Prims.nat -> int
       val f_of_int   : Prims.int -> float
    *)
    let counts : Prims.nat array = Array.make n_consumers (Prims.of_int 0) in
    let incr_nat (a:Prims.nat array) i =
      let v = int_of_nat a.(i) + (Prims.of_int 1) in
      a.(i) <- nat_of_int v
    in

    (* PCM service unchanged *)
    let serve_b (cB : Duplex_PCM.ch) : unit =
      let x =
        Duplex_PCM.channel_recv Duplex_PCM.B
          (Steel_Channel_Protocol.dual pingpong) cB
      in
      let xi : Prims.int = (Obj.magic x : Prims.int) in
      let yi : Prims.int = Prims.op_Addition xi (Prims.of_int 42) in
      let stepB =
        Steel_Channel_Protocol.step (Steel_Channel_Protocol.dual pingpong) x
      in
      Duplex_PCM.channel_send Duplex_PCM.B stepB cB (Obj.magic yi)
    in

    let t0 = Unix.gettimeofday () in

    let served = ref 0 in

    Switch.run @@ fun sw ->
      (* ---- Consumers as fibers, no for-loop ---- *)
      let cids = List.init n_consumers (fun i -> i) in
      List.iter
        (fun cid ->
           Eio.Fiber.fork ~sw (fun () ->
             let idle = ref 0 in
             let rec loop () =
               match Q.dequeue q with
               | Some f ->
                   idle := 0;
                   incr_nat counts cid;
                   f ();
                   if !served land 0x3F = 0  (* every 64 tasks *)
                   then Eio.Fiber.yield ()
                   else Domain.cpu_relax ();  (* super cheap on hot path *)
                   Eio.Fiber.yield ();
                   loop ()
               | None ->
                   if get_stop () then (
                     incr idle;
                     if !idle >! 16 then ()
                     else (Eio.Fiber.yield (); loop ())
                   ) else (
                     Eio.Fiber.yield (); loop ()
                   )
             in
             loop ()
           ))
        cids;

      (* ---- Producers spread across domains, no for-loop on spans ---- *)
      let prod_ps =
        List.init n_domains (fun dom_i ->
          Eio.Fiber.fork_promise ~sw (fun () ->
            Eio.Domain_manager.run env#domain_mgr (fun () ->
                          (* shard indices using half-open [start, stop) — all in Prims.int *)
            let start : Prims.int =
              (Prims.of_int dom_i) * (Prims.of_int n_producers) / (Prims.of_int n_domains)
            in
            let stop_excl : Prims.int =
              ((Prims.of_int dom_i + Prims.of_int 1) * (Prims.of_int n_producers) / (Prims.of_int n_domains))
            in
            let count_p : Prims.int = Prims.op_Subtraction stop_excl start in
            
            (* build span = [start + 0 ; … ; start + (count-1)] with Prims math only *)
            let rec build_span acc (k : Prims.int) =
              if Prims.op_GreaterThanOrEqual k count_p then Stdlib.List.rev acc
              else
                let elt = Prims.op_Addition start k in
                build_span (elt :: acc) (Prims.op_Addition k (Prims.of_int 1))
            in
            let span : Prims.int list = build_span [] (Prims.of_int 0) in

              (* iterate each producer in this domain *)
              Stdlib.List.iter
                (fun _p ->
                  for i = 1 to iters do
                    (* Make a 1-slot reply stream for this request *)
                    let reply : Prims.int Eio.Stream.t = Eio.Stream.create 1 in
                  
                    (* Enqueue a pure task: compute x+42 and push to reply. No Steel heap here. *)
                    Q.enqueue q (fun () ->
                      let xi = (Prims.of_int 1 : Prims.int) in
                      let yi = Prims.op_Addition xi (Prims.of_int 42) in
                      Eio.Stream.add reply yi
                    );
                    
                    (* Wait for the reply; safe across domains *)
                    let _y : Prims.int = Eio.Stream.take reply in
                    
                    if (i land 0x3FF) = 0 then Domain.cpu_relax ();
                  done
                )
                span
              )))
      in

      List.iter (fun p -> ignore (Eio.Promise.await_exn p)) prod_ps;
      set_stop true;
      Eio.Time.sleep clock 0.005
    ;

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
        (fun (mn,mx) k_nat ->
           let ki : Prims.int = (Obj.magic k_nat : Prims.int) in
           let mn' = if Prims.op_LessThan ki mn then ki else mn in
           let mx' = if Prims.op_GreaterThan ki mx then ki else mx in
           (mn', mx'))
        (first, first) counts
    in
    let secs  = t1 -. t0 in
    let avg_f = (f_of_int total_i) /. float_of_int n_consumers in
    let imb_f =
      if Prims.op_Equality max_i (Prims.of_int 0) then 0.0
      else (f_of_int (Prims.op_Subtraction max_i min_i)) /. (f_of_int max_i) *. 100.0
    in
    let rate_f = (f_of_int total_i) /. secs in

    Printf.printf "=== PCM × TwoLockQueue (Eio) ===\n";
    Printf.printf "producers=%d  consumers=%d  iters/producer=%d\n"
      n_producers n_consumers iters;
    Array.iteri
      (fun i k_nat ->
         Printf.printf "T%-2d: %s\n" i (Prims.string_of_int (Obj.magic k_nat : Prims.int)))
      counts;
    Printf.printf "total=%s  time=%.3fs  throughput=%.0f ops/s\n%!"
      (Prims.string_of_int total_i) secs rate_f;
    Printf.printf "min=%s  max=%s  avg=%.1f  imbalance=%.1f%%%%\n%!"
      (Prims.string_of_int min_i)
      (Prims.string_of_int max_i)
      avg_f imb_f
  )


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
  | "3" | _ -> run_mode3 ()
  
