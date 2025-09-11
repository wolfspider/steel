open Prims

type cell = Ref of unit * Obj.t FStar_PCM.pcm * unit * Obj.t

let (uu___is_Ref : cell -> Prims.bool) = fun projectee -> true

let (__proj__Ref__item__p : cell -> Obj.t FStar_PCM.pcm) =
 fun projectee -> match projectee with Ref (a, p, frac, v) -> p

let (__proj__Ref__item__v : cell -> Obj.t) =
 fun projectee -> match projectee with Ref (a, p, frac, v) -> v

type addr = Prims.nat

type heap =
  ( addr,
    cell FStar_Pervasives_Native.option )
  FStar_FunctionalExtensionality.restricted_t

let (empty_heap : heap) = fun x -> FStar_Pervasives_Native.None

let (contains_addr : heap -> addr -> Prims.bool) =
 fun m -> fun a -> FStar_Pervasives_Native.uu___is_Some (m a)

let select_addr (m : heap) (a : addr) : cell =
  match m a with
  | FStar_Pervasives_Native.Some c -> c
  | FStar_Pervasives_Native.None ->
      failwith (Printf.sprintf "[heap] missing address")

let (update_addr' : heap -> addr -> cell FStar_Pervasives_Native.option -> heap)
    =
 fun m -> fun a -> fun c -> fun x -> if a = x then c else m x

let (update_addr : heap -> addr -> cell -> heap) =
 fun m -> fun a -> fun c -> update_addr' m a (FStar_Pervasives_Native.Some c)

type ('c0, 'c1) disjoint_cells = Obj.t
type ('m0, 'm1, 'a) disjoint_addr = Obj.t
type core_ref = Null | Addr of addr

let (uu___is_Null : core_ref -> Prims.bool) =
 fun projectee -> match projectee with Null -> true | uu___ -> false

let (uu___is_Addr : core_ref -> Prims.bool) =
 fun projectee -> match projectee with Addr _0 -> true | uu___ -> false

let (__proj__Addr__item___0 : core_ref -> addr) =
 fun projectee -> match projectee with Addr _0 -> _0

type ('a, 'pcm) ref = core_ref

let (core_ref_null : core_ref) = Null
let null : 'a. 'a FStar_PCM.pcm -> ('a, Obj.t) ref = fun pcm -> core_ref_null
let (core_ref_is_null : core_ref -> Prims.bool) = fun r -> uu___is_Null r

let is_null : 'a. 'a FStar_PCM.pcm -> ('a, Obj.t) ref -> Prims.bool =
 fun pcm -> fun r -> core_ref_is_null r

type ('m0, 'm1) disjoint = unit

(* ---- debug helpers ---- *)
let string_of_pos (p : Prims.pos) : string =
  try Z.to_string (Obj.magic p : Z.t)
  with _ -> string_of_int (Obj.magic p : int)

let string_of_addr (a : addr) : string = string_of_pos a

let (join_cells : cell -> cell -> cell) =
 fun c0 ->
  fun c1 ->
   let uu___ = c0 in
   match uu___ with
   | Ref (a0, p0, f0, v0) -> (
       let uu___1 = c1 in
       match uu___1 with
       | Ref (a1, p1, f1, v1) -> Ref ((), p0, (), FStar_PCM.op p0 v0 v1))

let (join : heap -> heap -> heap) =
 fun m0 ->
  fun m1 ->
   fun x ->
    match (m0 x, m1 x) with
    | FStar_Pervasives_Native.None, FStar_Pervasives_Native.None ->
        FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some x1 ->
        FStar_Pervasives_Native.Some x1
    | FStar_Pervasives_Native.Some x1, FStar_Pervasives_Native.None ->
        FStar_Pervasives_Native.Some x1
    | FStar_Pervasives_Native.Some c0, FStar_Pervasives_Native.Some c1 ->
        FStar_Pervasives_Native.Some (join_cells c0 c1)

type ('m0, 'm1) mem_equiv = unit
type 'p heap_prop_is_affine = unit
type a_heap_prop = unit
type slprop = unit
type ('p, 'm) interp = 'p
type 'fp hprop = unit
type 'p hheap = heap
type ('p1, 'p2) equiv = unit
type ('a, 'pcm, 'v, 'c) pts_to_cell = Obj.t
type ('a, 'f, 'h, 'x) h_exists_body = ('f, 'h) interp
type ('a, 'f, 'h, 'x) h_forall_body = ('f, 'h) interp
type ('p, 'q) sl_implies = unit
type ('p, 'q) stronger = unit
type 'h full_heap_pred = unit
type full_heap = heap
type 'fp full_hheap = 'fp hheap
type ('h0, 'h1) heap_evolves = unit
type ('h, 'a) free_above_addr = unit

type ('fp, 'a, 'fpu) pre_action =
  'fp full_hheap -> ('a, 'fpu full_hheap) Prims.dtuple2

type ('frame, 'h0, 'h1) action_related_heaps = unit
type ('a, 'fp, 'fpu, 'f) is_frame_preserving = unit
type ('fp, 'a, 'fpu) action = ('fp, 'a, 'fpu) pre_action

type ('fp, 'a, 'fpu) action_with_frame =
  unit -> Obj.t full_hheap -> ('a, Obj.t full_hheap) Prims.dtuple2

type ('h0, 'h1, 'fp0, 'fp1, 'frame, 'allocates) frame_related_heaps = unit

let sel : 'a. 'a FStar_PCM.pcm -> ('a, Obj.t) ref -> full_heap -> 'a =
 fun _pcm r m ->
  match r with
  | Null ->
      Printf.printf "[heap] sel: Null ref\n%!";
      failwith "sel Null"
  | Addr a -> (
      let got = m a in
      match got with
      | FStar_Pervasives_Native.None ->
          Printf.printf "[heap] sel: Addr %s not in heap\n%!" (string_of_addr a);
          failwith "missing address"
      | FStar_Pervasives_Native.Some c -> (
          (* Keep the original shape check *)
          match c with
          | Ref (_a, _p, _frac, v) -> Obj.magic v))

let sel_v :
    'a. 'a FStar_PCM.pcm -> ('a, Obj.t) ref -> unit -> Obj.t full_hheap -> 'a =
 fun pcm -> fun r -> fun v -> fun m -> sel pcm r m

type ('a, 'pcm, 'r, 'fact, 'h) witnessed_ref = unit

let sel_action :
    'a. 'a FStar_PCM.pcm -> ('a, Obj.t) ref -> unit -> (Obj.t, 'a, Obj.t) action
    =
 fun pcm ->
  fun r ->
   fun v0 ->
    let f m0 = Prims.Mkdtuple2 (sel pcm r m0, m0) in
    f

let sel_action' :
    'a. 'a FStar_PCM.pcm -> ('a, Obj.t) ref -> unit -> Obj.t full_hheap -> 'a =
 fun pcm -> fun r -> fun v0 -> fun h -> sel_v pcm r () h

type ('fp0, 'a, 'fp1) refined_pre_action =
  'fp0 full_hheap -> ('a, 'fp1 full_hheap) Prims.dtuple2

let (refined_pre_action_as_action :
      unit ->
      unit ->
      unit ->
      (Obj.t, Obj.t, Obj.t) refined_pre_action ->
      (Obj.t, Obj.t, Obj.t) action) =
 fun fp0 ->
  fun a ->
   fun fp1 ->
    fun f ->
     let g m = f m in
     g

let select_refine_pre :
    'a.
    'a FStar_PCM.pcm ->
    ('a, Obj.t) ref ->
    unit ->
    unit ->
    (Obj.t, 'a, Obj.t) refined_pre_action =
 fun p ->
  fun r ->
   fun x ->
    fun f ->
     fun h0 ->
      let v = sel_v p r () h0 in
      Prims.Mkdtuple2 (v, h0)

let select_refine :
    'a.
    'a FStar_PCM.pcm ->
    ('a, Obj.t) ref ->
    unit ->
    unit ->
    (Obj.t, 'a, Obj.t) action =
 fun uu___3 ->
  fun uu___2 ->
   fun uu___1 ->
    fun uu___ ->
     (fun p ->
       fun r ->
        fun x ->
         fun f ->
          Obj.magic
            (refined_pre_action_as_action () () ()
               (Obj.magic (select_refine_pre p r () ()))))
       uu___3 uu___2 uu___1 uu___

let (update_addr_full_heap : full_heap -> addr -> cell -> full_heap) =
 fun h ->
  fun a ->
   fun c ->
    let h' = update_addr h a c in
    h'

type ('fp, 'a, 'fpu) partial_pre_action =
  'fp full_hheap -> ('a, 'fpu full_hheap) Prims.dtuple2

let upd_gen :
    'a.
    'a FStar_PCM.pcm ->
    ('a, Obj.t) ref ->
    unit ->
    unit ->
    ('a, Obj.t, Obj.t, Obj.t) FStar_PCM.frame_preserving_upd ->
    (Obj.t, unit, Obj.t) partial_pre_action =
 fun p ->
  fun r ->
   fun x ->
    fun v ->
     fun f ->
      fun h ->
       let uu___ = select_addr h (__proj__Addr__item___0 r) in
       match uu___ with
       | Ref (a1, p1, frac, old_v) ->
           let new_v = f (Obj.magic old_v) in
           let cell1 = Ref ((), p1, (), Obj.magic new_v) in
           let h' = update_addr_full_heap h (__proj__Addr__item___0 r) cell1 in
           Prims.Mkdtuple2 ((), h')

let upd_gen_action :
    'a.
    'a FStar_PCM.pcm ->
    ('a, Obj.t) ref ->
    unit ->
    unit ->
    ('a, Obj.t, Obj.t, Obj.t) FStar_PCM.frame_preserving_upd ->
    (Obj.t, unit, Obj.t) action =
 fun uu___4 ->
  fun uu___3 ->
   fun uu___2 ->
    fun uu___1 ->
     fun uu___ ->
      (fun p ->
        fun r ->
         fun x ->
          fun y ->
           fun f ->
            let refined h =
              let uu___ = upd_gen p r () () f h in
              match uu___ with
              | Prims.Mkdtuple2 (u, h1) ->
                  let h11 = h1 in
                  Prims.Mkdtuple2 ((), h11)
            in
            Obj.magic
              (refined_pre_action_as_action () () () (Obj.magic refined)))
        uu___4 uu___3 uu___2 uu___1 uu___

let upd_action :
    'a.
    'a FStar_PCM.pcm ->
    ('a, Obj.t) ref ->
    unit ->
    'a ->
    (Obj.t, unit, Obj.t) action =
 fun pcm ->
  fun r ->
   fun v0 ->
    fun v1 ->
     upd_gen_action pcm r () ()
       (FStar_PCM.frame_preserving_val_to_fp_upd pcm () v1)

let free_action :
    'a.
    'a FStar_PCM.pcm -> ('a, Obj.t) ref -> unit -> (Obj.t, unit, Obj.t) action =
 fun pcm ->
  fun r ->
   fun v0 ->
    let one = pcm.FStar_PCM.p.FStar_PCM.one in
    let f v = one in
    upd_gen_action pcm r () () f

let split_action :
    'a.
    'a FStar_PCM.pcm ->
    ('a, Obj.t) ref ->
    unit ->
    unit ->
    (Obj.t, unit, Obj.t) action =
 fun uu___3 ->
  fun uu___2 ->
   fun uu___1 ->
    fun uu___ ->
     (fun pcm ->
       fun r ->
        fun v0 ->
         fun v1 ->
          let g m = Prims.Mkdtuple2 ((), m) in
          Obj.magic (refined_pre_action_as_action () () () (Obj.magic g)))
       uu___3 uu___2 uu___1 uu___

let gather_action :
    'a.
    'a FStar_PCM.pcm ->
    ('a, Obj.t) ref ->
    unit ->
    unit ->
    (Obj.t, unit, Obj.t) action =
 fun uu___3 ->
  fun uu___2 ->
   fun uu___1 ->
    fun uu___ ->
     (fun pcm ->
       fun r ->
        fun v0 ->
         fun v1 ->
          let g m = Prims.Mkdtuple2 ((), m) in
          Obj.magic (refined_pre_action_as_action () () () (Obj.magic g)))
       uu___3 uu___2 uu___1 uu___

let extend :
    'a.
    'a FStar_PCM.pcm ->
    'a ->
    Prims.nat ->
    full_heap ->
    (('a, Obj.t) ref, full_heap) Prims.dtuple2 =
 fun pcm x addr1 h ->
  (* Printf.printf "[heap] extend: write Addr %s\n%!" (string_of_addr addr1); *)
  let r = Addr addr1 in
  let h' =
    update_addr_full_heap h addr1 (Ref ((), Obj.magic pcm, (), Obj.magic x))
  in
  Prims.Mkdtuple2 (r, h')

let frame :
    'a.
    unit ->
    unit ->
    unit ->
    (Obj.t, 'a, Obj.t) action ->
    (Obj.t, 'a, Obj.t) action =
 fun uu___3 ->
  fun uu___2 ->
   fun uu___1 ->
    fun uu___ ->
     (fun pre ->
       fun post ->
        fun frame1 ->
         fun f ->
          let g h0 =
            let uu___ = f h0 in
            match uu___ with Prims.Mkdtuple2 (x, h1) -> Prims.Mkdtuple2 (x, h1)
          in
          Obj.magic (refined_pre_action_as_action () () () (Obj.magic g)))
       uu___3 uu___2 uu___1 uu___

let (change_slprop : unit -> unit -> unit -> (Obj.t, unit, Obj.t) action) =
 fun uu___2 ->
  fun uu___1 ->
   fun uu___ ->
    (fun p ->
      fun q ->
       fun proof ->
        let g h = Prims.Mkdtuple2 ((), h) in
        Obj.magic (refined_pre_action_as_action () () () (Obj.magic g)))
      uu___2 uu___1 uu___

let (id_elim_star : unit -> unit -> heap -> unit * unit) =
 fun p -> fun q -> fun m -> ((), ())

type ('a, 'p) is_frame_monotonic = unit
type ('a, 'p) is_witness_invariant = unit

let witness_h_exists : 'a. unit -> (Obj.t, unit, Obj.t) action_with_frame =
 fun p -> fun frame1 -> fun h0 -> Prims.Mkdtuple2 ((), h0)

let lift_h_exists : 'a. unit -> (Obj.t, unit, Obj.t) action =
 fun uu___ ->
  (fun p ->
    let g h = Prims.Mkdtuple2 ((), h) in
    Obj.magic (refined_pre_action_as_action () () () (Obj.magic g)))
    uu___

let elim_pure : 'p. unit -> (Obj.t, unit, Obj.t) action =
 fun uu___ ->
  (fun uu___ ->
    let f h = Prims.Mkdtuple2 ((), h) in
    Obj.magic (refined_pre_action_as_action () () () (Obj.magic f)))
    uu___
