(* match Steel_Memory’s “iname = Prims.nat” without importing it *)
type iname = Prims.nat
type nmst_state = Steel_Heap.heap * iname

let _st : nmst_state ref =
  ref (Steel_Heap.empty_heap, (Prims.of_int 0 : iname))
  (* or: ref (Steel_Heap.empty_heap, (Prims.int_zero : iname)) *)

let get () : nmst_state = !_st
let put (s : nmst_state) : unit = _st := s

(* Keep recall side-effecty and returning unit *)
let witness () = Obj.magic ()
let recall  (_w:Obj.t) : unit = ()
let sample () = false
