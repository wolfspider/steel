open Prims

let pure_upd_next : 'a. 'a Queue_Def.cell -> 'a Queue_Def.t -> 'a Queue_Def.cell
    =
 fun c -> fun next -> { Queue_Def.data = c.Queue_Def.data; Queue_Def.next }

let upd_next : 'a. unit -> unit -> 'a Queue_Def.t -> 'a Queue_Def.t -> unit =
 fun _u _v tl last ->
  let last_cell = Steel_Reference.read_pt () () tl in
  let updated = pure_upd_next last_cell last in
  Steel_Reference.write_pt () tl updated;
  Steel_Effect_Atomic.return () () ()

let rec next_last :
    'a.
    'a Queue_Def.cell Steel_Reference.ref ->
    ('a Queue_Def.cell Steel_Reference.ref * 'a Queue_Def.cell) Prims.list ->
    'a Queue_Def.cell Steel_Reference.ref =
 fun pstart ->
  fun l ->
   match l with [] -> pstart | (uu___, c) :: q -> next_last c.Queue_Def.next q

let get_data :
    'a. 'a Queue_Def.cell Steel_Reference.ref * 'a Queue_Def.cell -> 'a =
 fun x -> (FStar_Pervasives_Native.snd x).Queue_Def.data

type ('a, 'tl, 'l, 'lc) queue_lc_prop = unit

let new_queue : 'a. 'a -> 'a Queue_Def.t =
 fun v ->
  let c = { Queue_Def.data = v; Queue_Def.next = NullCompat.S.null () } in
  let pc = Steel_Reference.alloc_pt c in
  Steel_Effect_Atomic.return () () pc

let unsnoc : 'a. 'a Prims.list -> 'a Prims.list * 'a =
 fun l -> FStar_List_Tot_Base.unsnoc l

let unsnoc_hd : 'a. 'a Prims.list -> 'a Prims.list =
 fun l -> FStar_Pervasives_Native.fst (unsnoc l)

let unsnoc_tl : 'a. 'a Prims.list -> 'a =
 fun l -> FStar_Pervasives_Native.snd (unsnoc l)

let enqueue :
    'a. unit -> unit -> 'a Queue_Def.t -> unit -> 'a Queue_Def.t -> unit =
 fun u ->
  fun hd ->
   fun tl ->
    fun v ->
     fun last ->
      upd_next () () tl last;
      Steel_Effect_Atomic.return () () ()

let read_next : 'a. unit -> unit -> 'a Queue_Def.t -> 'a Queue_Def.t =
 fun _u _v hd ->
  let c = Steel_Reference.read_pt () () hd in
  c.Queue_Def.next

let dequeue :
    'a.
    unit ->
    unit ->
    'a Queue_Def.t ->
    'a Queue_Def.t FStar_Pervasives_Native.option =
 fun _u _tl hd ->
  let p = read_next () () hd in
  if NullCompat.S.is_null p then
    Steel_Effect_Atomic.return () () FStar_Pervasives_Native.None
  else Steel_Effect_Atomic.return () () (FStar_Pervasives_Native.Some p)
