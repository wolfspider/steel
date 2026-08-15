open Prims

module FStar_Witnessed_Core = struct
  type ('state, 'rel, 'p) witnessed = unit
end

type lock_state = Invariant of unit

let (uu___is_Invariant : lock_state -> Prims.bool) = fun projectee -> true

type lock_store = lock_state Prims.list
type mem = { ctr : Prims.nat; heap : Steel_Heap.heap; locks : lock_store }

let (__proj__Mkmem__item__ctr : mem -> Prims.nat) =
 fun projectee -> match projectee with { ctr; heap; locks; _ } -> ctr

let (__proj__Mkmem__item__heap : mem -> Steel_Heap.heap) =
 fun projectee -> match projectee with { ctr; heap; locks; _ } -> heap

let (__proj__Mkmem__item__locks : mem -> lock_store) =
 fun projectee -> match projectee with { ctr; heap; locks; _ } -> locks

let (heap_of_mem : mem -> Steel_Heap.heap) = fun x -> x.heap

let (mem_of_heap : Steel_Heap.heap -> mem) =
 fun h -> { ctr = Prims.int_zero; heap = h; locks = [] }

let (mem_set_heap : mem -> Steel_Heap.heap -> mem) =
 fun m -> fun h -> { ctr = m.ctr; heap = h; locks = m.locks }

let (core_mem : mem -> mem) = fun m -> mem_of_heap (heap_of_mem m)

type ('m0, 'm1) disjoint = unit

let (join : mem -> mem -> mem) =
 fun m0 ->
  fun m1 ->
   { ctr = m0.ctr; heap = Steel_Heap.join m0.heap m1.heap; locks = m0.locks }

type slprop = unit
type ('p, 'm) interp = ('p, Obj.t) Steel_Heap.interp
type 'p hmem = mem
type ('p1, 'p2) equiv = unit
type ('p1, 'p2) slimp = unit
type core_ref = Steel_Heap.core_ref
type ('a, 'pcm) ref = core_ref

let (core_ref_null : core_ref) = Steel_Heap.core_ref_null
let null : 'a. 'a FStar_PCM.pcm -> ('a, Obj.t) ref = fun pcm -> core_ref_null

let (core_ref_is_null : core_ref -> Prims.bool) =
 fun r -> Steel_Heap.core_ref_is_null r

let is_null : 'a. 'a FStar_PCM.pcm -> ('a, Obj.t) ref -> Prims.bool =
 fun pcm -> fun r -> core_ref_is_null r

type iname = Prims.nat
type inames = unit

let (lock_i : iname -> lock_store -> lock_state) =
 fun i ->
  fun l ->
   let ix = FStar_List_Tot_Base.length l - i - Prims.int_one in
   FStar_List_Tot_Base.index l ix

type ('i, 'p, 'l) iname_for_p = unit
type ('l1, 'l2) lock_store_evolves = unit
type ('e, 'l) inames_in = unit
type ('e, 'm) inames_ok = unit

let (extend_lock_store :
      unit -> lock_store -> unit -> (iname, lock_store) Prims.dtuple2) =
 fun e ->
  fun l ->
   fun p -> Prims.Mkdtuple2 (FStar_List_Tot_Base.length l, Invariant () :: l)

type ('ctr, 'h) heap_ctr_valid = ('h, 'ctr) Steel_Heap.free_above_addr
type 'm full_mem_pred = Obj.t Steel_Heap.full_heap_pred
type full_mem = mem
type ('e, 'fp) hmem_with_inv_except = full_mem
type 'fp hmem_with_inv = (Obj.t, 'fp) hmem_with_inv_except
type ('sl, 'f) mem_prop_is_affine = unit
type 'sl a_mem_prop = unit
type ('sl, 'f, 'uuuuu) a_mem_prop_as_a_heap_prop = unit
type ('s, 'f, 'h) dep_hprop = unit
type ('s, 'f) dep_slprop_is_affine = unit
type 'fp mprop = unit
type ('a, 'fpupre, 'fpupost) mprop2 = unit
type ('m0, 'm1) mem_evolves = unit
type ('a, 'except, 'expects, 'provides) action_except = unit -> 'a

type ('a, 'except, 'expects, 'provides, 'req, 'ens) action_except_full =
  unit -> 'a

type ('e, 'pre, 'post, 'm0, 'm1) preserves_frame = unit

type ('e, 'fp, 'a, 'fpu) tot_pre_action_nf_except =
  ('e, 'fp) hmem_with_inv_except ->
  ('a, ('e, 'fpu) hmem_with_inv_except) Prims.dtuple2

type ('fp, 'a, 'fpu) tot_pre_action_nf =
  (Obj.t, 'fp, 'a, 'fpu) tot_pre_action_nf_except

type ('e, 'a, 'fp, 'fpu, 'f) is_frame_preserving = unit

type ('e, 'fp, 'a, 'fpu) tot_action_nf_except =
  ('e, 'fp, 'a, 'fpu) tot_pre_action_nf_except

type ('fp, 'a, 'fpu) tot_action_nf = (Obj.t, 'fp, 'a, 'fpu) tot_action_nf_except

let (hheap_of_hmem :
      unit ->
      unit ->
      (Obj.t, Obj.t) hmem_with_inv_except ->
      Obj.t Steel_Heap.hheap) =
 fun fp ->
  fun e ->
   fun m ->
    let h = heap_of_mem m in
    h

let (hmem_of_hheap :
      unit ->
      unit ->
      unit ->
      (Obj.t, Obj.t) hmem_with_inv_except ->
      Obj.t Steel_Heap.full_hheap ->
      (Obj.t, Obj.t) hmem_with_inv_except) =
 fun e ->
  fun fp0 ->
   fun fp1 ->
    fun m ->
     fun h ->
      let m1 = { ctr = m.ctr; heap = h; locks = m.locks } in
      m1

type ('m, 'e, 'fp) with_inv_except = (Obj.t, 'm) interp
type ('frame, 'mp, 'uuuuu) as_hprop = 'mp

let (lift_heap_action :
      unit ->
      unit ->
      unit ->
      unit ->
      (Obj.t, Obj.t, Obj.t) Steel_Heap.action ->
      (Obj.t, Obj.t, Obj.t, Obj.t) tot_action_nf_except) =
 fun fp ->
  fun a ->
   fun fp' ->
    fun e ->
     fun f ->
      let g m =
        let h0 = hheap_of_hmem () () m in
        let uu___ = f h0 in
        match uu___ with
        | Prims.Mkdtuple2 (x, h') ->
            Prims.Mkdtuple2 (x, hmem_of_hheap () () () m h')
      in
      g

let lift_tot_action_nf :
    'a.
    unit -> unit -> unit -> (Obj.t, Obj.t, 'a, Obj.t) tot_action_nf_except -> 'a
    =
 fun _e _fp _fp' f ->
  let h, ctr = FStar_NMSTTotal.get () in
  let m0 : full_mem = { ctr; heap = h; locks = [] } in
  let (Prims.Mkdtuple2 (x, m1)) = f m0 in
  FStar_NMSTTotal.put (m1.heap, m1.ctr);
  x

let lift_tot_action :
    'a.
    unit ->
    unit ->
    unit ->
    (Obj.t, Obj.t, 'a, Obj.t) tot_action_nf_except ->
    unit ->
    'a =
 fun e ->
  fun fp ->
   fun fp' ->
    fun f ->
     fun frame ->
      let m0 = FStar_NMSTTotal.get () in
      lift_tot_action_nf () () () f

type ('e, 'fp, 'a, 'fpu) tot_action_with_frame_except =
  unit ->
  ('e, Obj.t) hmem_with_inv_except ->
  ('a, ('e, Obj.t) hmem_with_inv_except) Prims.dtuple2

type ('fp, 'a, 'fpu) tot_action_with_frame =
  (Obj.t, 'fp, 'a, 'fpu) tot_action_with_frame_except

let (lift_heap_action_with_frame :
      unit ->
      unit ->
      unit ->
      unit ->
      (Obj.t, Obj.t, Obj.t) Steel_Heap.action_with_frame ->
      (Obj.t, Obj.t, Obj.t, Obj.t) tot_action_with_frame_except) =
 fun fp ->
  fun a ->
   fun fp' ->
    fun e ->
     fun f ->
      fun frame ->
       fun m0 ->
        let h0 = hheap_of_hmem () () m0 in
        let uu___ = f () h0 in
        match uu___ with
        | Prims.Mkdtuple2 (x, h1) ->
            let m1 = hmem_of_hheap () () () m0 h1 in
            Prims.Mkdtuple2 (x, m1)

let lift_tot_action_with_frame :
    'a.
    unit ->
    unit ->
    unit ->
    (Obj.t, Obj.t, 'a, Obj.t) tot_action_with_frame_except ->
    unit ->
    'a =
 fun e ->
  fun fp ->
   fun fp' ->
    fun f ->
     fun frame ->
      let ((h, ctr) : Steel_Heap.heap * iname) = FStar_NMSTTotal.get () in
      let m0 : full_mem = { ctr; heap = h; locks = [] } in
      let (Prims.Mkdtuple2 (x, m1)) = f () m0 in
      FStar_NMSTTotal.put (m1.heap, m1.ctr);
      x

let sel_action :
    'a.
    'a FStar_PCM.pcm ->
    unit ->
    ('a, Obj.t) ref ->
    unit ->
    ('a, Obj.t, Obj.t, Obj.t) action_except =
 fun pcm ->
  fun e ->
   fun r ->
    fun v0 ->
     lift_tot_action () () ()
       (Obj.magic
          (lift_heap_action () () () ()
             (Obj.magic (Steel_Heap.sel_action pcm r ()))))

let upd_action :
    'a.
    'a FStar_PCM.pcm ->
    unit ->
    ('a, Obj.t) ref ->
    unit ->
    'a ->
    (unit, Obj.t, Obj.t, Obj.t) action_except =
 fun pcm ->
  fun e ->
   fun r ->
    fun v0 ->
     fun v1 ->
      lift_tot_action () () ()
        (Obj.magic
           (lift_heap_action () () () ()
              (Obj.magic (Steel_Heap.upd_action pcm r () v1))))

let free_action :
    'a.
    'a FStar_PCM.pcm ->
    unit ->
    ('a, Obj.t) ref ->
    unit ->
    (unit, Obj.t, Obj.t, Obj.t) action_except =
 fun pcm ->
  fun e ->
   fun r ->
    fun v0 ->
     lift_tot_action () () ()
       (Obj.magic
          (lift_heap_action () () () ()
             (Obj.magic (Steel_Heap.free_action pcm r ()))))

let split_action :
    'a.
    'a FStar_PCM.pcm ->
    unit ->
    ('a, Obj.t) ref ->
    unit ->
    unit ->
    (unit, Obj.t, Obj.t, Obj.t) action_except =
 fun pcm ->
  fun e ->
   fun r ->
    fun v0 ->
     fun v1 ->
      lift_tot_action () () ()
        (Obj.magic
           (lift_heap_action () () () ()
              (Obj.magic (Steel_Heap.split_action pcm r () ()))))

let gather_action :
    'a.
    'a FStar_PCM.pcm ->
    unit ->
    ('a, Obj.t) ref ->
    unit ->
    unit ->
    (unit, Obj.t, Obj.t, Obj.t) action_except =
 fun pcm ->
  fun e ->
   fun r ->
    fun v0 ->
     fun v1 ->
      lift_tot_action () () ()
        (Obj.magic
           (lift_heap_action () () () ()
              (Obj.magic (Steel_Heap.gather_action pcm r () ()))))

let (weaken :
      unit -> unit -> unit -> Obj.t Steel_Heap.hheap -> Obj.t Steel_Heap.hheap)
    =
 fun p -> fun q -> fun r -> fun h -> h

let (inc_ctr :
      unit ->
      unit ->
      (Obj.t, Obj.t) hmem_with_inv_except ->
      (Obj.t, Obj.t) hmem_with_inv_except) =
 fun p ->
  fun e ->
   fun m ->
    let m' = { ctr = m.ctr + Prims.int_one; heap = m.heap; locks = m.locks } in
    let m'1 = m' in
    m'1

type ('fp0, 'fp1, 'e, 'm0, 'm1) frame_related_mems = unit

type ('e, 'fp0, 'a, 'fp1) refined_pre_action =
  ('e, 'fp0) hmem_with_inv_except ->
  ('a, ('e, 'fp1) hmem_with_inv_except) Prims.dtuple2

let (refined_pre_action_as_action :
      unit ->
      unit ->
      unit ->
      unit ->
      (Obj.t, Obj.t, Obj.t, Obj.t) refined_pre_action ->
      (Obj.t, Obj.t, Obj.t, Obj.t) tot_action_nf_except) =
 fun fp0 ->
  fun a ->
   fun fp1 ->
    fun e ->
     fun f ->
      let g m = f m in
      g

let alloc_action :
    'a.
    'a FStar_PCM.pcm ->
    unit ->
    'a ->
    (('a, Obj.t) ref, Obj.t, Obj.t, Obj.t) action_except =
 fun pcm ->
  fun e ->
   fun x ->
    let f m0 =
      let h = hheap_of_hmem () () m0 in
      let uu___ = Steel_Heap.extend pcm x m0.ctr h in
      match uu___ with
      | Prims.Mkdtuple2 (r, h') ->
          let m' = inc_ctr () () m0 in
          let h'1 = weaken () () () h' in
          let m1 = hmem_of_hheap () () () m' h'1 in
          Prims.Mkdtuple2 (r, m1)
    in
    lift_tot_action () () ()
      (Obj.magic (refined_pre_action_as_action () () () () (Obj.magic f)))

let select_refine :
    'a.
    'a FStar_PCM.pcm ->
    unit ->
    ('a, Obj.t) ref ->
    unit ->
    unit ->
    ('a, Obj.t, Obj.t, Obj.t) action_except =
 fun p ->
  fun e ->
   fun r ->
    fun x ->
     fun f ->
      lift_tot_action () () ()
        (Obj.magic
           (lift_heap_action () () () ()
              (Obj.magic (Steel_Heap.select_refine p r () ()))))

let upd_gen :
    'a.
    'a FStar_PCM.pcm ->
    unit ->
    ('a, Obj.t) ref ->
    unit ->
    unit ->
    ('a, Obj.t, Obj.t, Obj.t) FStar_PCM.frame_preserving_upd ->
    (unit, Obj.t, Obj.t, Obj.t) action_except =
 fun p ->
  fun e ->
   fun r ->
    fun x ->
     fun y ->
      fun f ->
       lift_tot_action () () ()
         (Obj.magic
            (lift_heap_action () () () ()
               (Obj.magic (Steel_Heap.upd_gen_action p r () () f))))

type 'a property = unit
type ('a, 'pcm, 'r, 'fact, 'm) witnessed_ref = unit

type ('a, 'pcm, 'r, 'fact) witnessed =
  (full_mem, unit, unit) FStar_Witnessed_Core.witnessed

type ('a, 'pcm) stable_property = unit

(* in out/Steel_Memory.ml *)
let witness :
    'a.
    'a FStar_PCM.pcm ->
    unit ->
    unit ->
    unit ->
    unit ->
    unit ->
    (('a, Obj.t, Obj.t, Obj.t) witnessed, Obj.t, Obj.t, Obj.t) action_except =
 fun _pcm _e _r _fact _v _u -> fun _frame -> FStar_NMSTTotal.witness ()

let recall :
    'a.
    'a FStar_PCM.pcm ->
    unit ->
    unit ->
    unit ->
    unit ->
    ('a, Obj.t, Obj.t, Obj.t) witnessed ->
    (unit, Obj.t, Obj.t, Obj.t) action_except =
 fun _pcm ->
  fun _fact ->
   fun _e ->
    fun _r ->
     fun _v ->
      fun w ->
       fun _frame ->
        let _ = FStar_NMSTTotal.get () in
        ignore (FStar_NMSTTotal.recall (Obj.magic w));
        ()

type ('i, 'p, 'm) iname_for_p_mem = unit

type ('i, 'p) op_Greater_Subtraction_Subtraction_Greater =
  (full_mem, unit, unit) FStar_Witnessed_Core.witnessed

let (new_invariant_tot_action :
      unit ->
      unit ->
      (Obj.t, Obj.t) hmem_with_inv_except ->
      iname * (Obj.t, Obj.t) hmem_with_inv_except) =
 fun e ->
  fun p ->
   fun m0 ->
    let uu___ = extend_lock_store () m0.locks () in
    match uu___ with
    | Prims.Mkdtuple2 (i, l1) ->
        let m1 = { ctr = m0.ctr; heap = m0.heap; locks = l1 } in
        let m11 = m1 in
        (i, m11)

type ('i, 'm0) name_is_ok = unit

type 'i witnessed_name_is_ok =
  (full_mem, unit, unit) FStar_Witnessed_Core.witnessed

type pre_inv = (unit, Obj.t witnessed_name_is_ok) Prims.dtuple2

type 'p inv =
  ( unit,
    Obj.t witnessed_name_is_ok,
    (Obj.t, 'p) op_Greater_Subtraction_Subtraction_Greater )
  FStar_Pervasives.dtuple3

let (pre_inv_of_inv : unit -> unit -> pre_inv) =
 fun p ->
  fun i ->
   match Obj.magic () with
   | FStar_Pervasives.Mkdtuple3 (i1, w, uu___1) -> Prims.Mkdtuple2 ((), w)

type ('ctx, 'i) fresh_wrt = unit

let rec (recall_all : pre_inv Prims.list -> unit) =
 fun ctx ->
  match ctx with
  | [] -> ()
  | hd :: tl ->
      (* hd : Prims.dtuple2<_, _> *)
      let i = FStar_Pervasives.dsnd hd in
      ignore (FStar_NMSTTotal.recall (Obj.magic i));
      recall_all tl

let (fresh_invariant :
      unit ->
      unit ->
      pre_inv Prims.list ->
      (unit, Obj.t, Obj.t, Obj.t) action_except) =
 fun _e ->
  fun _p ->
   fun ctx ->
    fun _frame ->
     (* adapt NMST (heap, iname) -> full_mem *)
     let ((h, ctr) : Steel_Heap.heap * iname) = FStar_NMSTTotal.get () in
     let m0 : full_mem = { ctr; heap = h; locks = [] } in

     (* recall any tokens in ctx; ignore their result *)
     recall_all ctx;

     (* run the Steel allocator for a new invariant *)
     let i, m1 = new_invariant_tot_action () () m0 in

     (* store back to NMST as (heap, iname), not as a full_mem *)
     FStar_NMSTTotal.put (m1.heap, m1.ctr);

     (* produce two witness tokens; shapes don’t matter in the stub *)
     let w = FStar_NMSTTotal.witness () in
     let w0 = FStar_NMSTTotal.witness () in
     Obj.magic (FStar_Pervasives.Mkdtuple3 ((), w0, w))

let (new_invariant : unit -> unit -> (unit, Obj.t, Obj.t, Obj.t) action_except)
    =
 fun e -> fun p -> fun frame -> fresh_invariant () () [] ()

let (token_of_inv :
      unit -> unit -> (Obj.t, Obj.t) op_Greater_Subtraction_Subtraction_Greater)
    =
 fun p ->
  fun i ->
   match Obj.magic () with
   | FStar_Pervasives.Mkdtuple3 (uu___1, uu___2, tok) -> tok

let with_invariant :
    'a.
    unit ->
    unit ->
    unit ->
    unit ->
    unit ->
    ('a, Obj.t, Obj.t, Obj.t) action_except ->
    ('a, Obj.t, Obj.t, Obj.t) action_except =
 fun _fp ->
  fun _fp' ->
   fun _opened_invariants ->
    fun _p ->
     fun _i ->
      fun f ->
       fun _frame ->
        let _ = FStar_NMSTTotal.get () in
        (* recall the token; coerce arg, ignore result *)
        ignore (FStar_NMSTTotal.recall (Obj.magic (token_of_inv () ())));
        let r = f () in
        let _ = FStar_NMSTTotal.get () in
        ignore (FStar_NMSTTotal.recall (Obj.magic (token_of_inv () ())));
        r

let frame :
    'a.
    unit ->
    unit ->
    unit ->
    unit ->
    unit ->
    unit ->
    ('a, Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) action_except_full ->
    ('a, Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) action_except_full =
 fun opened_invariants ->
  fun pre ->
   fun post ->
    fun req ->
     fun ens ->
      fun frame1 ->
       fun f ->
        fun frame0 ->
         let m0 = FStar_NMSTTotal.get () in
         let x = f () in
         let m1 = FStar_NMSTTotal.get () in
         x

let (change_slprop :
      unit -> unit -> unit -> unit -> (unit, Obj.t, Obj.t, Obj.t) action_except)
    =
 fun opened_invariants ->
  fun p ->
   fun q ->
    fun proof ->
     lift_tot_action () () ()
       (Obj.magic
          (lift_heap_action () () () ()
             (Obj.magic (Steel_Heap.change_slprop () () ()))))

type ('a, 'p) is_frame_monotonic = unit
type ('a, 'p) is_witness_invariant = unit

let (witness_h_exists :
      unit -> unit -> unit -> (unit, Obj.t, Obj.t, Obj.t) action_except) =
 fun opened_invariants ->
  fun a ->
   fun p ->
    lift_tot_action_with_frame () () ()
      (Obj.magic
         (lift_heap_action_with_frame () () () ()
            (Obj.magic (Steel_Heap.witness_h_exists ()))))

let (lift_h_exists :
      unit -> unit -> unit -> (unit, Obj.t, Obj.t, Obj.t) action_except) =
 fun opened_invariants ->
  fun uu___ ->
   fun p ->
    lift_tot_action () () ()
      (Obj.magic
         (lift_heap_action () () () ()
            (Obj.magic (Steel_Heap.lift_h_exists ()))))

let (elim_pure : unit -> unit -> (unit, Obj.t, Obj.t, Obj.t) action_except) =
 fun opened_invariants ->
  fun p ->
   lift_tot_action () () ()
     (Obj.magic
        (lift_heap_action () () () () (Obj.magic (Steel_Heap.elim_pure ()))))

let (id_elim_star : unit -> unit -> mem -> unit * unit) =
 fun p -> fun q -> fun m -> ((), ())
