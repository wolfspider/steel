(* Main.ml — switchable queue (steel vs local), same forensic modes *)

open Prims
module TLQ = TwoLockQueue

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

let ( >! ) a b = Prims.op_GreaterThan (Prims.of_int a) (Prims.of_int b)

(* ---------------------- MODE 3S: TLQ × PCM stress ---------------------- *)
let run_mode3_stress () =
  (* OCaml ints from env; safe to keep as OCaml ints *)
  let producers =
    try int_of_string (Sys.getenv "PRODUCERS") with _ -> 1 in
  let consumers =
    try int_of_string (Sys.getenv "CONSUMERS") with _ -> 4 in
  let iters =
    try int_of_string (Sys.getenv "ITERS") with _ -> 100 in

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

  (* consumers: pop & run B-service tasks *)
  let consumer_loop () =
    let idle_spins = ref 0 in   (* OCaml int *)
    let rec loop () =
      match Q.dequeue q with
      | Some f ->
          idle_spins := 0;
          f (); Thread.yield (); loop ()
      | None ->
          if get_stop () then (
            incr idle_spins;
            (* use >! to compare OCaml int vs a literal using Prims ops *)
            if !idle_spins >! 4 then ()
            else (Thread.delay 0.05; Thread.yield (); loop ())
          ) else (Thread.delay 0.05; Thread.yield (); loop ())
    in
    loop ()
  in
  let cons = Array.init consumers (fun _ -> Thread.create consumer_loop ()) in

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

(* ----- Prims-safe totals + OCaml timing/throughput ----- *)

(* total_exchanges (Prims) -> OCaml int -> floats *)
let total_exchanges_i : Prims.int =
  (Obj.magic
     (Prims.op_Multiply (Prims.of_int producers) (Prims.of_int iters))
   : Prims.int)
in
let total_ocaml : int = (Obj.magic total_exchanges_i : int) in
let secs  : float = Stdlib.( -. ) t1 t0 in
Stdlib.Printf.printf
  "[3S] done  total_exchanges=%s  time=%.3fs\n%!"
  (Prims.string_of_int total_exchanges_i) secs





(* ---------------------- Entry: choose mode ---------------------- *)
let () =
  let mode = try Sys.getenv "MODE" with _ -> "3" in
  print_endline ("[boot] MODE=" ^ mode);
  match mode with
  | "0" -> run_mode0 ()
  | "1" -> run_mode1 ()
  | "2" -> run_mode2 ()
  | "3S" -> run_mode3_stress ()
  | "3" | _ -> run_mode3 ()
  
