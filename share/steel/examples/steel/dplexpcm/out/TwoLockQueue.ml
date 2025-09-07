open Prims
let fst : 'uuuuu 'uuuuu1 . ('uuuuu * 'uuuuu1) -> 'uuuuu =
  fun x -> FStar_Pervasives_Native.fst x
let snd : 'uuuuu 'uuuuu1 . ('uuuuu * 'uuuuu1) -> 'uuuuu1 =
  fun x -> FStar_Pervasives_Native.snd x
type 'a q_ptr =
  {
  ptr: 'a Queue_Def.t Steel_Reference.ref ;
  ghost: unit ;
  lock: unit Steel_SpinLock.lock }


let __proj__Mkq_ptr__item__ptr :
  'a . 'a q_ptr -> 'a Queue_Def.t Steel_Reference.ref =
  fun projectee -> match projectee with | { ptr; ghost; lock;_} -> ptr
let __proj__Mkq_ptr__item__lock : 'a . 'a q_ptr -> unit Steel_SpinLock.lock =
  fun projectee -> match projectee with | { ptr; ghost; lock;_} -> lock
type 'a t = {
  head: 'a q_ptr ;
  tail: 'a q_ptr ;
  inv: unit }
let __proj__Mkt__item__head : 'a . 'a t -> 'a q_ptr =
  fun projectee -> match projectee with | { head; tail; inv;_} -> head
let __proj__Mkt__item__tail : 'a . 'a t -> 'a q_ptr =
  fun projectee -> match projectee with | { head; tail; inv;_} -> tail
let __proj__Mkt__item__inv : 'a . 'a t -> unit = fun projectee -> ()
let new_qptr : 'a . 'a Queue_Def.t -> 'a q_ptr =
  fun q ->
    let ptr = Steel_Reference.alloc_pt q in
    let lock = Obj.magic (Steel_SpinLock.new_lock ()) in
    { ptr; ghost = (); lock }
let new_queue : 'a . 'a -> 'a t =
  fun x ->
    let hd = Queue.new_queue x in
    let head =
      let ptr = Steel_Reference.alloc_pt hd in
      let lock = Obj.magic (Steel_SpinLock.new_lock ()) in
      { ptr; ghost = (); lock } in
    let tail =
      let ptr = Steel_Reference.alloc_pt hd in
      let lock = Obj.magic (Steel_SpinLock.new_lock ()) in
      { ptr; ghost = (); lock } in
    Steel_Effect_Atomic.return () () { head; tail; inv = () }
let enqueue : 'a . 'a t -> 'a -> unit =
  fun hdl ->
    fun x ->
      Steel_SpinLock.acquire () (Obj.magic (hdl.tail).lock);
      (let cell =
         { Queue_Def.data = x; Queue_Def.next = (NullCompat.S.null ()) } in
       let tl = Steel_Reference.read_pt () () (hdl.tail).ptr in
       let node = Steel_Reference.alloc_pt cell in
       let enqueue_core u = fun uu___1 -> Queue.enqueue () () tl () node in
       (enqueue_core ()) ();
       Steel_Reference.write_pt () (hdl.tail).ptr node;
       Steel_SpinLock.release () (Obj.magic (hdl.tail).lock))
let dequeue_core :
  'a .
    unit ->
      'a t ->
        'a Queue_Def.t ->
          unit -> 'a Queue_Def.t FStar_Pervasives_Native.option
  =
  fun u ->
    fun hdl ->
      fun hd ->
        fun uu___ ->
          let o = Queue.dequeue () () hd in
          match o with
          | FStar_Pervasives_Native.None ->
              Steel_Effect_Atomic.return () () o
          | FStar_Pervasives_Native.Some p ->
              Steel_Effect_Atomic.return () () o
let dequeue : 'a . 'a t -> 'a FStar_Pervasives_Native.option =
  fun hdl ->
    Steel_SpinLock.acquire () (Obj.magic (hdl.head).lock);
    (let hd = Steel_Reference.read_pt () () (hdl.head).ptr in
     let o = (dequeue_core () hdl hd) () in
     match o with
     | FStar_Pervasives_Native.None ->
         (Steel_SpinLock.release () (Obj.magic (hdl.head).lock);
          FStar_Pervasives_Native.None)
     | FStar_Pervasives_Native.Some next ->
        (Steel_Reference.write_pt () (hdl.head).ptr next;
         Steel_SpinLock.release () (Obj.magic (hdl.head).lock);
         (* Read the *new* head node (which was old_head.next) and return its data *)
         let c_next = Steel_Reference.read_pt () () next in
         let v = c_next.Queue_Def.data in
         FStar_Pervasives_Native.Some v))
