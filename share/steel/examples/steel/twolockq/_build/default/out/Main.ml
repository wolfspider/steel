(* out/Main.ml — thread-based stress harness for TwoLockQueue *)
module Q = TwoLockQueue

let () =
  (* ---- knobs ---- *)
  let producers = 1 in
  let consumers =
    try int_of_string (Sys.getenv "CONSUMERS") with _ -> 4
  in
  let tasks_per_producer = 100_000 in
  let drain_spins_after_stop = 4 in
  (* ---------------- *)

  (* queue of unit->unit tasks; drop the dummy head element *)
  let q = Q.new_queue (fun () -> ()) in
  ignore (Q.dequeue q);

  (* stop flag with a mutex so we avoid Atomics *)
  let stop = ref false in
  let stop_mu = Mutex.create () in
  let get_stop () = Mutex.lock stop_mu; let v = !stop in Mutex.unlock stop_mu; v in
  let set_stop v = Mutex.lock stop_mu; stop := v; Mutex.unlock stop_mu in

  let counts = Array.make consumers 0 in

  (* producers: enqueue tasks *)
  let prod =
    Array.init producers (fun pid ->
      Thread.create
        (fun () ->
           for i = 1 to tasks_per_producer do
             let task () =
               if (i land 0x3FFFF) = 0 then ignore (Sys.opaque_identity pid)
             in
             Q.enqueue q task
           done)
        ())
  in

  (* consumers: dequeue & run; after stop=true, exit once queue stays empty *)
  let consumer_loop cid () =
    let idle_spins = ref 0 in
    let rec loop () =
      match Q.dequeue q with
      | Some f ->
          counts.(cid) <- counts.(cid) + 1;
          idle_spins := 0;
          f (); Thread.yield (); loop ()
      | None ->
          if get_stop () then (
            incr idle_spins;
            if !idle_spins > drain_spins_after_stop then ()
            else (Thread.delay 0.05; Thread.yield (); loop ())
          ) else (Thread.delay 0.05; Thread.yield (); loop ())
    in
    loop ()
  in

  let cons =
    Array.init consumers (fun cid -> Thread.create (consumer_loop cid) ())
  in

  let t0 = Unix.gettimeofday () in
  Array.iter Thread.join prod;       (* all tasks submitted *)
  set_stop true;                     (* signal consumers to wind down *)
  Array.iter Thread.join cons;

  let t1 = Unix.gettimeofday () in
  let elapsed = t1 -. t0 in
  let total = Array.fold_left ( + ) 0 counts in
  let minc = Array.fold_left min max_int counts
  and maxc = Array.fold_left max min_int counts in
  let avg = float total /. float consumers in
  let imbalance =
    if maxc = 0 then 0.0 else (float (maxc - minc)) /. float maxc *. 100.0
  in

  Printf.printf "=== TwoLockQueue stress (threads) ===\n";
  Printf.printf "producers=%d  consumers=%d  tasks/producer=%d\n"
    producers consumers tasks_per_producer;
  Array.iteri (fun i k -> Printf.printf "T%-2d: %d\n" i k) counts;
  Printf.printf "total=%d  time=%.3fs  throughput=%.0f ops/s\n"
    total elapsed (float total /. elapsed);
  Printf.printf "min=%d  max=%d  avg=%.1f  imbalance=%.1f%%%%\n%!"
    minc maxc avg imbalance
