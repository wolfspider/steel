module TwoLockQueueTest

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

module U32 = FStar.UInt32
module LL  = TwoLockQueue

// Use a type alias, not a value binding
type elt = U32.t

// A tiny “smoke test”: new → enqueue → dequeue x3
let smoke_u32 () : SteelT (option elt * option elt * option elt) emp (fun _ -> emp) =
  // Some convenient constants
  let z   = U32.uint_to_t 0 in
  let one = U32.uint_to_t 1 in
  let two = U32.uint_to_t 2 in

  // Build a queue seeded with 0
  let q = LL.new_queue z in

  // Enqueue 1, then 2
  LL.enqueue q one;
  LL.enqueue q two;

  // Dequeue thrice; we don't assert functional results here since
  // TwoLockQueue only proves memory-safety, not FIFO semantics.
  let r0 = LL.dequeue q in
  let r1 = LL.dequeue q in
  let r2 = LL.dequeue q in

  return (r0, r1, r2)

// A slightly different shape: do one enqueue then one dequeue
let one_step (x:elt) : SteelT (option elt) emp (fun _ -> emp) =
  let q = LL.new_queue x in
  LL.enqueue q x;
  LL.dequeue q

// If you want a very bare-bones “it compiles” unit
let no_op () : SteelT unit emp (fun _ -> emp) =
  let q = LL.new_queue (U32.uint_to_t 42) in
  LL.enqueue q (U32.uint_to_t 7);
  let _ = LL.dequeue q in
  return ()
