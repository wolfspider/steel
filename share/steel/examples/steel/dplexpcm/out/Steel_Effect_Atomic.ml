let return _ _ x = x

(* Do NOT put back here; inner actions (lift_tot_action, etc.) already do NMST get/put *)
let as_atomic_action _ _ _
    (f : Steel_Heap.full_heap -> ('a, Steel_Heap.full_heap) Prims.dtuple2) =
  let h0, _ctr0 = FStar_NMSTTotal.get () in
  let (Prims.Mkdtuple2 (x, _h1)) = f h0 in
  x

let as_atomic_unobservable_action = as_atomic_action
