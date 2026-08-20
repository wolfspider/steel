(* out/Main.fanout.ml — TwoLockQueue stress with real per-task work.

   The point of this variant is to move the benchmark off the degenerate case.
   In the original the task body is essentially empty:

       let task () = if (i land 0x3FFFF) = 0 then ignore (...)

   so the harness measures scheduling overhead and nothing else -- which is
   exactly what the multithreaded scheduler *adds*, and none of what it exists
   for. Measured on the empty version: V8 0.145s, mqjs standalone 0.501s, mqjs
   4-thread 1.736s. Four threads lose to one, at any item count, because every
   microsecond of work sits inside the serialised engine entry.

   TASK_WORK (default 0) sets how many iterations of arithmetic each task does.

   Read the result carefully. Work done *here* is still inside the engine lock,
   so raising TASK_WORK slows 1 thread and 4 threads by the same amount and
   proves nothing about parallelism -- that is the control. The crossover only
   appears for work performed on the native side, outside the lock, which is
   what a real fan-out does (a socket write, a per-task transform, a Limbo
   insert). See thread_pump --work-us for that arm of the experiment. *)

module Q = TwoLockQueue
module Thread = JSThread_JSQ

let main () =
  (* ---- knobs ---- *)
  let producers = 1 in
  let consumers =
    try int_of_string (Sys.getenv "CONSUMERS") with _ -> 4
  in
  let tasks_per_producer =
    try int_of_string (Sys.getenv "TASKS") with _ -> 100_000
  in
  (* Per-task work, in loop iterations, executed INSIDE the engine. 0 reproduces
     the original harness. This is the control arm. *)
  let task_work =
    try int_of_string (Sys.getenv "TASK_WORK") with _ -> 0
  in
  (* Per-task NATIVE work: hash rounds requested by the task itself through the
     Native effect. The host performs it -- off the engine lock under mquickjs,
     inline under Node -- and the task is resumed with the digest. Unlike
     TASK_WORK this is work the *program* asked for, so it is the same request
     on every host. 0 disables it. *)
  let native_work =
    try int_of_string (Sys.getenv "NATIVE_WORK") with _ -> 0
  in
  let digest_acc = ref 0 in
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
               (* Sys.opaque_identity keeps the accumulator alive so neither
                  the OCaml optimiser nor the JS engine can fold this away --
                  without it the whole loop is dead code and TASK_WORK would
                  silently do nothing. *)
               if task_work > 0 then begin
                 let acc = ref 0 in
                 for j = 1 to task_work do
                   acc := (!acc + j * 2654435761) land 0x3FFFFFFF
                 done;
                 ignore (Sys.opaque_identity !acc)
               end;
               if native_work > 0 then begin
                 (* The digest is folded into an accumulator so nothing can be
                    elided: the result has to be observed for the work to have
                    happened. *)
                 let d = Thread.native
                     (string_of_int native_work ^ ":" ^ string_of_int i) in
                 digest_acc := (!digest_acc + String.length d) land 0xFFFFFF
               end;
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
          (* Backoff is `yield`, not `delay`.

             These meant the same thing while Delay was a disguised yield. They
             do not any more: `yield` is "same logical time, next epoch", which
             is exactly the backoff wanted here, whereas `delay 0.05` parks this
             consumer at a *later* logical time -- and the scheduler only
             advances its clock once nothing at the current time is runnable.
             So a consumer that polls an empty queue before the producer's first
             turn gets benched until every other consumer has finished, and
             takes zero items for the whole run.

             Observed: T0 : 0, the other three 33333 each, at ~1 run in 10. It
             depends on which worker wins the mutex at the first frontier, so it
             is intermittent and looks like a scheduler bug rather than what it
             is -- a delay doing precisely what a delay means. *)
          if get_stop () then (
            incr idle_spins;
            if !idle_spins > drain_spins_after_stop then ()
            else (Thread.yield (); loop ())
          ) else (Thread.yield (); loop ())
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
  Printf.printf
    "producers=%d  consumers=%d  tasks/producer=%d  task_work=%d  native_work=%d\n"
    producers consumers tasks_per_producer task_work native_work;
  Printf.printf "digest_acc=%d\n" !digest_acc;
  Array.iteri (fun i k -> Printf.printf "T%-2d: %d\n" i k) counts;
  Printf.printf "total=%d  time=%.3fs  throughput=%.0f ops/s\n"
    total elapsed (float total /. elapsed);
  Printf.printf "min=%d  max=%d  avg=%.1f  imbalance=%.1f%%%%\n%!"
    minc maxc avg imbalance

let () =
  match Sys.getenv_opt "JSTHREAD_DRIVEN" with
  | Some _ -> Thread.run_driven main   (* embedded: an external driver pumps *)
  | None   -> Thread.run main          (* standalone: unchanged *)
