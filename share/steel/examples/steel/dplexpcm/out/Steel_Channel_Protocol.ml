open Prims

type tag = Send | Recv

let (uu___is_Send : tag -> Prims.bool) =
 fun projectee -> match projectee with Send -> true | uu___ -> false

let (uu___is_Recv : tag -> Prims.bool) =
 fun projectee -> match projectee with Recv -> true | uu___ -> false

type 'dummyV0 prot =
  | Return of unit * Obj.t
  | Msg of tag * unit * unit * (Obj.t -> Obj.t prot)
  | DoWhile of Prims.bool prot * unit * Obj.t prot

let uu___is_Return : 'uuuuu. 'uuuuu prot -> Prims.bool =
 fun projectee ->
  match Obj.magic projectee with Return (a, v) -> true | uu___ -> false

let __proj__Return__item__v : 'uuuuu. 'uuuuu prot -> Obj.t =
 fun projectee -> match Obj.magic projectee with Return (a, v) -> v

let uu___is_Msg : 'uuuuu. 'uuuuu prot -> Prims.bool =
 fun projectee ->
  match Obj.magic projectee with Msg (_0, a, b, k) -> true | uu___ -> false

let __proj__Msg__item___0 : 'uuuuu. 'uuuuu prot -> tag =
 fun projectee -> match Obj.magic projectee with Msg (_0, a, b, k) -> _0

let __proj__Msg__item__k : 'uuuuu. 'uuuuu prot -> Obj.t -> Obj.t prot =
 fun projectee -> match Obj.magic projectee with Msg (_0, a, b, k) -> k

let uu___is_DoWhile : 'uuuuu. 'uuuuu prot -> Prims.bool =
 fun projectee ->
  match Obj.magic projectee with DoWhile (_0, a, k) -> true | uu___ -> false

let __proj__DoWhile__item___0 : 'uuuuu. 'uuuuu prot -> Prims.bool prot =
 fun projectee -> match Obj.magic projectee with DoWhile (_0, a, k) -> _0

let __proj__DoWhile__item__k : 'uuuuu. 'uuuuu prot -> Obj.t prot =
 fun projectee -> match Obj.magic projectee with DoWhile (_0, a, k) -> k

type ('a, 'p) ok = Obj.t
type 'a protocol = 'a prot

let (flip_tag : tag -> tag) =
 fun uu___ -> match uu___ with Send -> Recv | Recv -> Send

let rec dual : 'a. 'a protocol -> 'a protocol =
 fun uu___ ->
  (fun p ->
    match Obj.magic p with
    | Return (uu___, uu___1) -> Obj.magic (Obj.repr p)
    | Msg (tag1, b, a1, k) ->
        Obj.magic
          (Obj.repr
             (let k1 x = dual (k x) in
              Msg (flip_tag tag1, (), (), k1)))
    | DoWhile (p1, a1, k) ->
        Obj.magic (Obj.repr (DoWhile (dual p1, (), dual k))))
    uu___

let rec bind : 'a 'b. 'a protocol -> ('a -> 'b protocol) -> 'b protocol =
 fun uu___1 ->
  fun uu___ ->
   (fun p ->
     fun q ->
      match Obj.magic p with
      | Return (uu___, v) -> Obj.magic (Obj.repr (q (Obj.magic v)))
      | Msg (tag1, c, a', k) ->
          Obj.magic
            (Obj.repr
               (let k1 x = bind (k x) (fun uu___ -> (Obj.magic q) uu___) in
                Msg (tag1, (), (), fun uu___ -> (Obj.magic k1) uu___)))
      | DoWhile (w, uu___, k) ->
          Obj.magic
            (Obj.repr
               (DoWhile
                  ( w,
                    (),
                    Obj.magic (bind k (fun uu___1 -> (Obj.magic q) uu___1)) ))))
     uu___1 uu___

let op_let_Hat :
    'uuuuu 'uuuuu1.
    unit -> 'uuuuu protocol -> ('uuuuu -> 'uuuuu1 protocol) -> 'uuuuu1 protocol
    =
 fun uu___ -> bind

let return : 'a. 'a -> 'a protocol =
 fun uu___ -> (fun x -> Obj.magic (Return ((), Obj.magic x))) uu___

let (done1 : unit protocol) = return ()

let send : 't. unit -> 't protocol =
 fun uu___ ->
  (fun uu___ ->
    Obj.magic
      (Msg
         ( Send,
           (),
           (),
           fun uu___1 ->
             (fun x ->
               let x = Obj.magic x in
               Obj.magic (return x))
               uu___1 )))
    uu___

let recv : 't. unit -> 't protocol =
 fun uu___ ->
  (fun uu___ ->
    Obj.magic
      (Msg
         ( Recv,
           (),
           (),
           fun uu___1 ->
             (fun x ->
               let x = Obj.magic x in
               Obj.magic (return x))
               uu___1 )))
    uu___

let (xy : unit prot) =
  bind (send ()) (fun x -> bind (recv ()) (fun y -> return ()))

let rec hnf : 'a. 'a protocol -> 'a protocol =
 fun uu___ ->
  (fun p ->
    match Obj.magic p with
    | DoWhile (p1, uu___, k) ->
        Obj.magic
          (Obj.repr
             (bind (hnf p1) (fun b -> if b then DoWhile (p1, (), k) else k)))
    | uu___ -> Obj.magic (Obj.repr p))
    uu___

type ('a, 'p) next_msg_t = Obj.t

let step : 'a. 'a protocol -> Obj.t -> 'a protocol =
 fun uu___1 ->
  fun uu___ ->
   (fun p -> fun x -> Obj.magic (__proj__Msg__item__k (hnf p) x)) uu___1 uu___

type ('dummyV0, 'dummyV1) trace =
  | Waiting of unit protocol
  | Message of unit protocol * Obj.t * unit protocol * (Obj.t, Obj.t) trace

let (uu___is_Waiting :
      unit protocol -> unit protocol -> (Obj.t, Obj.t) trace -> Prims.bool) =
 fun from ->
  fun to1 ->
   fun projectee -> match projectee with Waiting p -> true | uu___ -> false

let (__proj__Waiting__item__p :
      unit protocol -> unit protocol -> (Obj.t, Obj.t) trace -> unit protocol) =
 fun from -> fun to1 -> fun projectee -> match projectee with Waiting p -> p

let (uu___is_Message :
      unit protocol -> unit protocol -> (Obj.t, Obj.t) trace -> Prims.bool) =
 fun from ->
  fun to1 ->
   fun projectee ->
    match projectee with Message (from1, x, to2, _3) -> true | uu___ -> false

let (__proj__Message__item__from :
      unit protocol -> unit protocol -> (Obj.t, Obj.t) trace -> unit protocol) =
 fun from ->
  fun to1 ->
   fun projectee -> match projectee with Message (from1, x, to2, _3) -> from1

let (__proj__Message__item__x :
      unit protocol -> unit protocol -> (Obj.t, Obj.t) trace -> Obj.t) =
 fun from ->
  fun to1 ->
   fun projectee -> match projectee with Message (from1, x, to2, _3) -> x

let (__proj__Message__item__to :
      unit protocol -> unit protocol -> (Obj.t, Obj.t) trace -> unit protocol) =
 fun from ->
  fun to1 ->
   fun projectee -> match projectee with Message (from1, x, to2, _3) -> to2

let (__proj__Message__item___3 :
      unit protocol ->
      unit protocol ->
      (Obj.t, Obj.t) trace ->
      (Obj.t, Obj.t) trace) =
 fun from ->
  fun to1 ->
   fun projectee -> match projectee with Message (from1, x, to2, _3) -> _3

let rec (extend :
          unit protocol ->
          unit protocol ->
          (Obj.t, Obj.t) trace ->
          Obj.t ->
          (Obj.t, Obj.t) trace) =
 fun from ->
  fun to1 ->
   fun t ->
    fun m ->
     match t with
     | Waiting uu___ -> Message (to1, m, step to1 m, Waiting (step to1 m))
     | Message (_from, x, _to, tail) ->
         Message (_from, x, step _to m, extend (step _from x) _to tail m)

let rec (last_step_of :
          unit protocol ->
          unit protocol ->
          (Obj.t, Obj.t) trace ->
          (unit protocol, Obj.t, unit) FStar_Pervasives.dtuple3) =
 fun from ->
  fun to1 ->
   fun t ->
    match t with
    | Message (uu___, x, uu___1, Waiting uu___2) ->
        FStar_Pervasives.Mkdtuple3 (from, x, ())
    | Message (uu___, uu___1, uu___2, tail) ->
        last_step_of (step uu___ uu___1) uu___2 tail

type 'p partial_trace_of = { to1 : unit protocol; tr : ('p, Obj.t) trace }

let (__proj__Mkpartial_trace_of__item__to :
      unit protocol -> Obj.t partial_trace_of -> unit protocol) =
 fun p -> fun projectee -> match projectee with { to1; tr; _ } -> to1

let (__proj__Mkpartial_trace_of__item__tr :
      unit protocol -> Obj.t partial_trace_of -> (Obj.t, Obj.t) trace) =
 fun p -> fun projectee -> match projectee with { to1; tr; _ } -> tr

type ('p, 't0, 't1) next = unit

type ('p, 'uuuuu, 'uuuuu1) extended_to =
  ( 'p partial_trace_of,
    unit,
    'uuuuu,
    'uuuuu1 )
  FStar_ReflexiveTransitiveClosure.closure

let (extend_partial_trace :
      unit protocol -> Obj.t partial_trace_of -> Obj.t -> Obj.t partial_trace_of)
    =
 fun p ->
  fun x ->
   fun msg ->
    {
      to1 = step (__proj__Mkpartial_trace_of__item__to p x) msg;
      tr = extend p (__proj__Mkpartial_trace_of__item__to p x) x.tr msg;
    }

type 'p msg_t = Obj.t
type ('p, 'tr) extension_of = 'p partial_trace_of

let (until : unit protocol -> Obj.t partial_trace_of -> unit protocol) =
 fun p -> fun tr -> tr.to1
