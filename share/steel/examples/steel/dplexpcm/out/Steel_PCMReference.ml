open Prims
let read :
  'a . 'a FStar_PCM.pcm -> ('a, Obj.t) Steel_Memory.ref -> unit -> 'a =
  fun pcm ->
    fun r ->
      fun v0 ->
        let v =
          Steel_Effect.as_action () () (Steel_Memory.sel_action pcm () r ()) in
        v
let write :
  'a . 'a FStar_PCM.pcm -> ('a, Obj.t) Steel_Memory.ref -> unit -> 'a -> unit
  =
  fun pcm ->
    fun r ->
      fun v0 ->
        fun v1 ->
          Steel_Effect.as_action () ()
            (Steel_Memory.upd_action pcm () r () v1)
let alloc' : 'a . 'a FStar_PCM.pcm -> 'a -> ('a, Obj.t) Steel_Memory.ref =
  fun pcm ->
    fun x ->
      Steel_Effect.as_action () () (Steel_Memory.alloc_action pcm () x)
(* out/Steel_PCMReference.ml *)
let alloc (pcm : 'a FStar_PCM.pcm) (x : 'a)
  : ('a, Obj.t) Steel_Memory.ref =
  (* alloc_action already does the NMST get/put internally via lift_tot_action *)
  (Steel_Memory.alloc_action pcm () x) ()

let free :
  'a . 'a FStar_PCM.pcm -> ('a, Obj.t) Steel_Memory.ref -> unit -> unit =
  fun p ->
    fun r ->
      fun x ->
        Steel_Effect.as_action () () (Steel_Memory.free_action p () r ())
type ('a, 'pcm, 'fact, 'v) fact_valid_compat = unit
let (witness' :
  unit ->
    unit ->
      Obj.t FStar_PCM.pcm ->
        unit ->
        unit ->
        unit ->
        unit ->
        (Obj.t, Obj.t, Obj.t, Obj.t) Steel_Memory.witnessed)
  =
  fun _inames ->
  fun _u ->
  fun pcm ->
  fun r ->
  fun fact ->
  fun v ->
  fun _u2 ->
    Steel_Effect_Atomic.as_atomic_unobservable_action () () ()
      (fun h ->
         (* run the Steel_Memory.witness action (unit -> token) *)
         let tok = Steel_Memory.witness pcm () () () () () () in
         Prims.Mkdtuple2 (tok, h))

let (witness :
  unit ->
    unit ->
      Obj.t FStar_PCM.pcm ->
        unit ->
          unit ->
            unit ->
              unit -> (Obj.t, Obj.t, Obj.t, Obj.t) Steel_Memory.witnessed)
  =
  fun inames ->
    fun a ->
      fun pcm ->
        fun r ->
          fun fact ->
            fun v -> fun s -> let w = witness' () () pcm () () () () in w
let (recall' :
  unit ->
    unit ->
      Obj.t FStar_PCM.pcm ->
        unit ->
          unit ->
            unit ->
              (Obj.t, Obj.t, Obj.t, Obj.t) Steel_Memory.witnessed -> unit)
  =
  fun inames ->
    fun a ->
      fun pcm ->
        fun fact ->
          fun r ->
            fun v ->
              fun w ->
                Steel_Effect_Atomic.as_atomic_unobservable_action () () ()
                  (fun h ->
                    (* run the Steel_Memory.witness action (unit -> token) *)
                    let tok = Steel_Memory.recall pcm () () () () () () in
                    Prims.Mkdtuple2 (tok, h))
let (recall :
  unit ->
    unit ->
      Obj.t FStar_PCM.pcm ->
        unit ->
          unit ->
            unit ->
              (Obj.t, Obj.t, Obj.t, Obj.t) Steel_Memory.witnessed -> unit)
  =
  fun inames ->
    fun a ->
      fun pcm ->
        fun fact -> fun r -> fun v -> fun w -> recall' () () pcm () () () w
(* Steel_PCMReference.ml *)
let select_refine
  (p  : 'a FStar_PCM.pcm)
  (r  : ('a, Obj.t) Steel_Memory.ref)
  (_x : unit)
  (_f : unit)
  : 'a
=
  (* select_refine returns a thunk: unit -> 'a; run it *)
  let run = Steel_Memory.select_refine p () r () () in
  run ()

(* out/Steel_PCMReference.ml *)
let upd_gen
    (pcm : 'a FStar_PCM.pcm)
    (r   : ('a, Obj.t) Steel_Memory.ref)
    (_x  : unit)
    (_y  : unit)
    (f   : ('a, Obj.t, Obj.t, Obj.t) FStar_PCM.frame_preserving_upd)
  : unit
  =
  Steel_Effect_Atomic.as_atomic_action () () ()
    (fun h ->
       (* read current value *)
       let v  = (Steel_Memory.sel_action pcm () r ()) () in
       (* compute updated value *)
       let v' = f v in
       (* write back *)
       let () = (Steel_Memory.upd_action pcm () r () v') () in
       (* hand the heap back to the shim; it ignores it *)
       Prims.Mkdtuple2 ((), h))

let (atomic_read :
  unit ->
    unit ->
      Obj.t FStar_PCM.pcm ->
      (Obj.t, Obj.t) Steel_Memory.ref -> unit -> Obj.t)
  =
  fun _opened ->
  fun _ ->
  fun pcm ->
  fun r ->
  fun _v0 ->
    let v =
      Steel_Effect_Atomic.as_atomic_action () () ()
        (fun h ->
           (* run the thunk: unit -> value *)
           let x = Steel_Memory.sel_action pcm () r () in
           (* unobservable read: heap unchanged *)
           Prims.Mkdtuple2 (x, h))
    in
    v ()

let (atomic_write :
  unit ->
    unit ->
      Obj.t FStar_PCM.pcm ->
        (Obj.t, Obj.t) Steel_Memory.ref -> unit -> Obj.t -> unit)
  =
  fun _opened ->
  fun _ ->
  fun pcm ->
  fun r ->
  fun _v0 ->
  fun v1 ->
    Steel_Effect_Atomic.as_atomic_action () () ()
      (fun h ->
         (* run the write action (unit -> unit), which updates NMST heap *)
         let () = (Steel_Memory.upd_action pcm () r () v1) () in
         (* read back the post-write heap to hand to the atomic wrapper *)
         let (h', _ctr') = FStar_NMSTTotal.get () in
         Prims.Mkdtuple2 ((), h'))

