open Prims
type elt = FStar_UInt32.t
let (smoke_u32 :
  unit ->
    (elt FStar_Pervasives_Native.option * elt FStar_Pervasives_Native.option
      * elt FStar_Pervasives_Native.option))
  =
  fun uu___ ->
    let z = FStar_UInt32.uint_to_t Prims.int_zero in
    let one = FStar_UInt32.uint_to_t Prims.int_one in
    let two = FStar_UInt32.uint_to_t (Prims.of_int (2)) in
    let q = TwoLockQueue.new_queue z in
    TwoLockQueue.enqueue q one;
    TwoLockQueue.enqueue q two;
    (let r0 = TwoLockQueue.dequeue q in
     let r1 = TwoLockQueue.dequeue q in
     let r2 = TwoLockQueue.dequeue q in
     Steel_Effect_Atomic.return () () (r0, r1, r2))
let (one_step : elt -> elt FStar_Pervasives_Native.option) =
  fun x ->
    let q = TwoLockQueue.new_queue x in
    TwoLockQueue.enqueue q x; TwoLockQueue.dequeue q
let (no_op : unit -> unit) =
  fun _ ->
    let q = TwoLockQueue.new_queue (FStar_UInt32.uint_to_t (Prims.of_int 42)) in
    TwoLockQueue.enqueue q (FStar_UInt32.uint_to_t (Prims.of_int 7));
    (match TwoLockQueue.dequeue q with
     | FStar_Pervasives_Native.None ->
         FStar_IO.print_string "dequeue: None\n"
     | FStar_Pervasives_Native.Some v ->
         FStar_IO.print_string ("dequeue: " ^ Z.to_string (FStar_UInt32.v v) ^ "\n"));
    FStar_IO.print_string "TwoLockQueueTest.no_op ran (OCaml)\n"

