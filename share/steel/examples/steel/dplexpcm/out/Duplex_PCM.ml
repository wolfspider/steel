open Prims
type dprot' = unit Steel_Channel_Protocol.protocol
type ('a, 'p) no_loop = Obj.t
type dprot = dprot'
type 'a nl_protocol = 'a Steel_Channel_Protocol.protocol
let return : 'a . 'a -> 'a nl_protocol =
  fun uu___ ->
    (fun x -> Obj.magic (Steel_Channel_Protocol.Return ((), (Obj.magic x))))
      uu___
let (done1 : dprot) = return ()
let send : 'a . unit -> 'a nl_protocol =
  fun uu___ ->
    (fun uu___ ->
       Obj.magic
         (Steel_Channel_Protocol.Msg
            (Steel_Channel_Protocol.Send, (), (),
              (fun uu___1 -> (Obj.magic return) uu___1)))) uu___
let recv : 'a . unit -> 'a nl_protocol =
  fun uu___ ->
    (fun uu___ ->
       Obj.magic
         (Steel_Channel_Protocol.Msg
            (Steel_Channel_Protocol.Recv, (), (),
              (fun uu___1 -> (Obj.magic return) uu___1)))) uu___
let rec bind :
  'a 'b . 'a nl_protocol -> ('a -> 'b nl_protocol) -> 'b nl_protocol =
  fun uu___1 ->
    fun uu___ ->
      (fun p ->
         fun q ->
           match Obj.magic p with
           | Steel_Channel_Protocol.Return (uu___, v) ->
               Obj.magic (Obj.repr (q (Obj.magic v)))
           | Steel_Channel_Protocol.Msg (tag, c, a', k) ->
               Obj.magic
                 (Obj.repr
                    (let k1 x = bind (k x) (fun uu___ -> (Obj.magic q) uu___) in
                     Steel_Channel_Protocol.Msg
                       (tag, (), (), (fun uu___ -> (Obj.magic k1) uu___)))))
        uu___1 uu___
type party =
  | A 
  | B 
let (uu___is_A : party -> Prims.bool) =
  fun projectee -> match projectee with | A -> true | uu___ -> false
let (uu___is_B : party -> Prims.bool) =
  fun projectee -> match projectee with | B -> true | uu___ -> false
type 'name send_next_dprot_t = dprot
type 'name recv_next_dprot_t = dprot
let (is_send : dprot -> Prims.bool) =
  fun p ->
    (Steel_Channel_Protocol.uu___is_Msg p) &&
      (Steel_Channel_Protocol.uu___is_Send
         (Steel_Channel_Protocol.__proj__Msg__item___0 p))
let (is_recv : dprot -> Prims.bool) =
  fun p ->
    (Steel_Channel_Protocol.uu___is_Msg p) &&
      (Steel_Channel_Protocol.uu___is_Recv
         (Steel_Channel_Protocol.__proj__Msg__item___0 p))
let (is_fin : dprot -> Prims.bool) =
  fun p -> Steel_Channel_Protocol.uu___is_Return p
let (empty_trace : dprot -> (Obj.t, Obj.t) Steel_Channel_Protocol.trace) =
  fun p -> Steel_Channel_Protocol.Waiting p
type 'p partial_trace_of = 'p Steel_Channel_Protocol.partial_trace_of
type ('tag, 'p, 't0, 't1) next = unit
type ('tag, 'p, 'uuuuu, 'uuuuu1) extended_to =
  ('p partial_trace_of, unit, 'uuuuu, 'uuuuu1)
    FStar_ReflexiveTransitiveClosure.closure
type 'p t =
  | V of 'p partial_trace_of 
  | A_W of dprot * ('p, Obj.t) Steel_Channel_Protocol.trace 
  | A_R of dprot * ('p, Obj.t) Steel_Channel_Protocol.trace 
  | B_R of dprot * ('p, Obj.t) Steel_Channel_Protocol.trace 
  | B_W of dprot * ('p, Obj.t) Steel_Channel_Protocol.trace 
  | A_Fin of dprot * ('p, Obj.t) Steel_Channel_Protocol.trace 
  | B_Fin of dprot * ('p, Obj.t) Steel_Channel_Protocol.trace 
  | Nil 
let (uu___is_V : dprot -> Obj.t t -> Prims.bool) =
  fun p ->
    fun projectee -> match projectee with | V _0 -> true | uu___ -> false
let (__proj__V__item___0 : dprot -> Obj.t t -> Obj.t partial_trace_of) =
  fun p -> fun projectee -> match projectee with | V _0 -> _0
let (uu___is_A_W : dprot -> Obj.t t -> Prims.bool) =
  fun p ->
    fun projectee ->
      match projectee with | A_W (q, _1) -> true | uu___ -> false
let (__proj__A_W__item__q : dprot -> Obj.t t -> dprot) =
  fun p -> fun projectee -> match projectee with | A_W (q, _1) -> q
let (__proj__A_W__item___1 :
  dprot -> Obj.t t -> (Obj.t, Obj.t) Steel_Channel_Protocol.trace) =
  fun p -> fun projectee -> match projectee with | A_W (q, _1) -> _1
let (uu___is_A_R : dprot -> Obj.t t -> Prims.bool) =
  fun p ->
    fun projectee ->
      match projectee with | A_R (q, _1) -> true | uu___ -> false
let (__proj__A_R__item__q : dprot -> Obj.t t -> dprot) =
  fun p -> fun projectee -> match projectee with | A_R (q, _1) -> q
let (__proj__A_R__item___1 :
  dprot -> Obj.t t -> (Obj.t, Obj.t) Steel_Channel_Protocol.trace) =
  fun p -> fun projectee -> match projectee with | A_R (q, _1) -> _1
let (uu___is_B_R : dprot -> Obj.t t -> Prims.bool) =
  fun p ->
    fun projectee ->
      match projectee with | B_R (q, _1) -> true | uu___ -> false
let (__proj__B_R__item__q : dprot -> Obj.t t -> dprot) =
  fun p -> fun projectee -> match projectee with | B_R (q, _1) -> q
let (__proj__B_R__item___1 :
  dprot -> Obj.t t -> (Obj.t, Obj.t) Steel_Channel_Protocol.trace) =
  fun p -> fun projectee -> match projectee with | B_R (q, _1) -> _1
let (uu___is_B_W : dprot -> Obj.t t -> Prims.bool) =
  fun p ->
    fun projectee ->
      match projectee with | B_W (q, _1) -> true | uu___ -> false
let (__proj__B_W__item__q : dprot -> Obj.t t -> dprot) =
  fun p -> fun projectee -> match projectee with | B_W (q, _1) -> q
let (__proj__B_W__item___1 :
  dprot -> Obj.t t -> (Obj.t, Obj.t) Steel_Channel_Protocol.trace) =
  fun p -> fun projectee -> match projectee with | B_W (q, _1) -> _1
let (uu___is_A_Fin : dprot -> Obj.t t -> Prims.bool) =
  fun p ->
    fun projectee ->
      match projectee with | A_Fin (q, _1) -> true | uu___ -> false
let (__proj__A_Fin__item__q : dprot -> Obj.t t -> dprot) =
  fun p -> fun projectee -> match projectee with | A_Fin (q, _1) -> q
let (__proj__A_Fin__item___1 :
  dprot -> Obj.t t -> (Obj.t, Obj.t) Steel_Channel_Protocol.trace) =
  fun p -> fun projectee -> match projectee with | A_Fin (q, _1) -> _1
let (uu___is_B_Fin : dprot -> Obj.t t -> Prims.bool) =
  fun p ->
    fun projectee ->
      match projectee with | B_Fin (q, _1) -> true | uu___ -> false
let (__proj__B_Fin__item__q : dprot -> Obj.t t -> dprot) =
  fun p -> fun projectee -> match projectee with | B_Fin (q, _1) -> q
let (__proj__B_Fin__item___1 :
  dprot -> Obj.t t -> (Obj.t, Obj.t) Steel_Channel_Protocol.trace) =
  fun p -> fun projectee -> match projectee with | B_Fin (q, _1) -> _1
let (uu___is_Nil : dprot -> Obj.t t -> Prims.bool) =
  fun p ->
    fun projectee -> match projectee with | Nil -> true | uu___ -> false
type ('tag, 'p, 'q, 'qu, 's, 'su) ahead = unit
let rec (trace_length :
  unit Steel_Channel_Protocol.protocol ->
    unit Steel_Channel_Protocol.protocol ->
      (Obj.t, Obj.t) Steel_Channel_Protocol.trace -> Prims.nat)
  =
  fun p ->
    fun q ->
      fun s ->
        match s with
        | Steel_Channel_Protocol.Waiting uu___ -> Prims.int_zero
        | Steel_Channel_Protocol.Message (uu___, uu___1, uu___2, t1) ->
            Prims.int_one +
              (trace_length (Steel_Channel_Protocol.step uu___ uu___1) uu___2
                 t1)
type ('p, 't0, 't1) composable = Obj.t
let (compose : dprot -> Obj.t t -> Obj.t t -> Obj.t t) =
  fun p ->
    fun s0 ->
      fun s1 ->
        match (s0, s1) with
        | (a, Nil) -> a
        | (Nil, a) -> a
        | (A_Fin (q, s), uu___) ->
            V
              { Steel_Channel_Protocol.to1 = q; Steel_Channel_Protocol.tr = s
              }
        | (uu___, A_Fin (q, s)) ->
            V
              { Steel_Channel_Protocol.to1 = q; Steel_Channel_Protocol.tr = s
              }
        | (B_Fin (q, s), uu___) ->
            V
              { Steel_Channel_Protocol.to1 = q; Steel_Channel_Protocol.tr = s
              }
        | (uu___, B_Fin (q, s)) ->
            V
              { Steel_Channel_Protocol.to1 = q; Steel_Channel_Protocol.tr = s
              }
        | (A_W (q, s), B_R (q', s')) ->
            V
              { Steel_Channel_Protocol.to1 = q; Steel_Channel_Protocol.tr = s
              }
        | (B_R (q', s'), A_W (q, s)) ->
            V
              { Steel_Channel_Protocol.to1 = q; Steel_Channel_Protocol.tr = s
              }
        | (B_W (q, s), A_R (q', s')) ->
            V
              { Steel_Channel_Protocol.to1 = q; Steel_Channel_Protocol.tr = s
              }
        | (A_R (q', s'), B_W (q, s)) ->
            V
              { Steel_Channel_Protocol.to1 = q; Steel_Channel_Protocol.tr = s
              }
        | (A_R (q, s), B_R (q', s')) ->
            if (trace_length p q s) >= (trace_length p q' s')
            then
              V
                {
                  Steel_Channel_Protocol.to1 = q;
                  Steel_Channel_Protocol.tr = s
                }
            else
              V
                {
                  Steel_Channel_Protocol.to1 = q';
                  Steel_Channel_Protocol.tr = s'
                }
        | (B_R (q', s'), A_R (q, s)) ->
            if (trace_length p q s) >= (trace_length p q' s')
            then
              V
                {
                  Steel_Channel_Protocol.to1 = q;
                  Steel_Channel_Protocol.tr = s
                }
            else
              V
                {
                  Steel_Channel_Protocol.to1 = q';
                  Steel_Channel_Protocol.tr = s'
                }
let (p' : dprot -> Obj.t t FStar_PCM.pcm') =
  fun p ->
    {
      FStar_PCM.composable = ();
      FStar_PCM.op = (compose p);
      FStar_PCM.one = Nil
    }
type ('prot, 'x) refine = unit
let (pcm : dprot -> Obj.t t FStar_PCM.pcm) =
  fun prot ->
    {
      FStar_PCM.p = (p' prot);
      FStar_PCM.comm = ();
      FStar_PCM.assoc = ();
      FStar_PCM.assoc_r = ();
      FStar_PCM.is_unit = ();
      FStar_PCM.refine = ()
    }
type 'p chan = ('p t, Obj.t) Steel_Memory.ref
let (ep_a :
  dprot -> dprot -> (Obj.t, Obj.t) Steel_Channel_Protocol.trace -> Obj.t t) =
  fun p ->
    fun next1 ->
      fun tr ->
        if is_send next1
        then A_W (next1, tr)
        else if is_recv next1 then A_R (next1, tr) else A_Fin (next1, tr)
type ('p, 'x, 'v, 'y) frame_compatible = unit
let (select_refine' : dprot -> Obj.t chan -> unit -> unit -> Obj.t t) =
  fun p ->
    fun r ->
      fun x -> fun f -> Steel_PCMReference.select_refine (pcm p) r () ()
let (select_refine : dprot -> Obj.t chan -> unit -> unit -> Obj.t t) =
  fun p ->
    fun r ->
      fun x ->
        fun f ->
          let v = select_refine' p r () () in
          Steel_Effect_Atomic.return () () v
type ('from, 'to1, 'tou, 'tr, 'tru) is_trace_prefix = Obj.t
let rec (next_message_aux :
  dprot ->
    dprot ->
      dprot ->
        (Obj.t, Obj.t) Steel_Channel_Protocol.trace ->
          (Obj.t, Obj.t) Steel_Channel_Protocol.trace -> Obj.t)
  =
  fun from ->
    fun to1 ->
      fun to' ->
        fun tr ->
          fun tr' ->
            match tr with
            | Steel_Channel_Protocol.Waiting uu___ ->
                Steel_Channel_Protocol.__proj__Message__item__x from to' tr'
            | Steel_Channel_Protocol.Message (uu___, x, to2, tail) ->
                let uu___1 = tr' in
                (match uu___1 with
                 | Steel_Channel_Protocol.Message (uu___2, x', to'1, tail')
                     ->
                     next_message_aux (Steel_Channel_Protocol.step uu___ x)
                       to2 to'1 tail tail')
let (next_message :
  dprot ->
    dprot ->
      dprot ->
        (Obj.t, Obj.t) Steel_Channel_Protocol.trace ->
          (Obj.t, Obj.t) Steel_Channel_Protocol.trace -> Obj.t)
  =
  fun from ->
    fun to1 ->
      fun to' -> fun tr -> fun tr' -> next_message_aux from to1 to' tr tr'
let (extend_node_a_r :
  dprot ->
    dprot ->
      (Obj.t, Obj.t) Steel_Channel_Protocol.trace ->
        Obj.t partial_trace_of -> Obj.t t)
  =
  fun p ->
    fun q ->
      fun tr ->
        fun tr' ->
          let x =
            next_message p q
              (Steel_Channel_Protocol.__proj__Mkpartial_trace_of__item__to p
                 tr') tr tr'.Steel_Channel_Protocol.tr in
          let q' = Steel_Channel_Protocol.step q x in
          let tr'1 = Steel_Channel_Protocol.extend p q tr x in
          if is_send q'
          then A_W (q', tr'1)
          else if is_recv q' then A_R (q', tr'1) else A_Fin (q', tr'1)
let (extend_node_b_r :
  dprot ->
    dprot ->
      (Obj.t, Obj.t) Steel_Channel_Protocol.trace ->
        Obj.t partial_trace_of -> Obj.t t)
  =
  fun p ->
    fun q ->
      fun tr ->
        fun tr' ->
          let x =
            next_message p q
              (Steel_Channel_Protocol.__proj__Mkpartial_trace_of__item__to p
                 tr') tr tr'.Steel_Channel_Protocol.tr in
          let q' = Steel_Channel_Protocol.step q x in
          let tr'1 = Steel_Channel_Protocol.extend p q tr x in
          if is_send q'
          then B_R (q', tr'1)
          else if is_recv q' then B_W (q', tr'1) else B_Fin (q', tr'1)
let (get_a_r :
  dprot ->
    Obj.t chan ->
      dprot ->
        (Obj.t, Obj.t) Steel_Channel_Protocol.trace -> Obj.t partial_trace_of)
  =
  fun p ->
    fun c ->
      fun q ->
        fun tr ->
          let v = select_refine p c () () in
          let tr' = __proj__V__item___0 p v in
          Steel_Effect_Atomic.return () () tr'

(* put these once near the top of Duplex_PCM.ml (or inline in each fn) *)
let pr (s:string) = print_endline s
let int_of_nat (n:Prims.nat) : int = (Obj.magic n : int)     (* F* nat -> OCaml int *)
let show_nat (n:Prims.nat) : string = string_of_int (int_of_nat n)
let show_exn (e:exn) = Printexc.to_string e


let show_core_ref (r : (Obj.t, Obj.t) Steel_Memory.ref) : string =
  match (Obj.magic r : Steel_Heap.core_ref) with
  | Steel_Heap.Null -> "Null"
  | Steel_Heap.Addr a -> "Addr " ^ string_of_int (Obj.magic a : int)


let get_b_r p c next1 tr =
  Printf.printf "[pcm] get_b_r: will read chan\n%!";
  let _ =
    Steel_Effect_Atomic.as_atomic_action () () ()
      (fun h ->
         (* extract address *)
         let a =
           match (c : Obj.t chan) with
           | r -> (match r with Steel_Heap.Addr a -> a | Steel_Heap.Null -> failwith "Null chan")
         in
         let has = Steel_Heap.contains_addr h a in
         Printf.printf "[pcm] get_b_r: heap has addr? %b\n%!" has;
         if not has then failwith "chan missing in heap";
         Prims.Mkdtuple2 ((), h))
  in
  let v = select_refine p c () () in
  (* your existing projection below… *)
  let tr' = __proj__V__item___0 p v in
  Steel_Effect_Atomic.return () () tr'




(* tiny printers so logs are readable *)
let pp_tag (p:Steel_Channel_Protocol.tag) =
  if Steel_Channel_Protocol.uu___is_Send p then "Send"
  else if Steel_Channel_Protocol.uu___is_Recv p then "Recv"
  else "?"

let pp_t (v: Obj.t t) =
  match v with
  | V _                         -> "V"
  | A_W (q,_)                   -> "A_W(" ^ pp_tag (Steel_Channel_Protocol.__proj__Msg__item___0 q) ^ ")"
  | A_R (q,_)                   -> "A_R(" ^ pp_tag (Steel_Channel_Protocol.__proj__Msg__item___0 q) ^ ")"
  | B_R (q,_)                   -> "B_R(" ^ pp_tag (Steel_Channel_Protocol.__proj__Msg__item___0 q) ^ ")"
  | B_W (q,_)                   -> "B_W(" ^ pp_tag (Steel_Channel_Protocol.__proj__Msg__item___0 q) ^ ")"
  | A_Fin (q,_)                 -> "A_Fin(" ^ (if Steel_Channel_Protocol.uu___is_Return q then "Return" else "?") ^ ")"
  | B_Fin (q,_)                 -> "B_Fin(" ^ (if Steel_Channel_Protocol.uu___is_Return q then "Return" else "?") ^ ")"
  | Nil                         -> "Nil"

let upd_gen_action
  (p:dprot)
  (r:Obj.t chan)
  (_x:Obj.t t)
  (_y:Obj.t t)
  (f:(Obj.t t, Obj.t, Obj.t, Obj.t) FStar_PCM.frame_preserving_upd)
  : unit
=
  Printf.printf "[pcm] upd_gen_action: begin\n%!";
  (* Wrap the updater to log old/new values *)
  let f_logged (oldv:Obj.t t) : Obj.t t =
    Printf.printf "[pcm]   old=%s\n%!" (pp_t oldv);
    let newv = f oldv in
    Printf.printf "[pcm]   new=%s\n%!" (pp_t newv);
    newv
  in
  Steel_PCMReference.upd_gen (pcm p) r () () f_logged;
  Printf.printf "[pcm] upd_gen_action: end\n%!"

let write_a_f_aux p next1 tr x : (Obj.t t, _, _, _) FStar_PCM.frame_preserving_upd =
  fun old ->
    match old with
    | V tr0 ->
        let next' = Steel_Channel_Protocol.step next1 x in
        let tr'   = Steel_Channel_Protocol.extend p next1 tr x in
        V { Steel_Channel_Protocol.to1 = next' ; Steel_Channel_Protocol.tr = tr' }
    | _ -> failwith "write_a_f_aux: expected V"

let write_b_f_aux p next1 tr x : (Obj.t t, _, _, _) FStar_PCM.frame_preserving_upd =
  fun old ->
    match old with
    | V tr0 ->
        let next' = Steel_Channel_Protocol.step next1 x in
        let tr'   = Steel_Channel_Protocol.extend p next1 tr x in
        V { Steel_Channel_Protocol.to1 = next' ; Steel_Channel_Protocol.tr = tr' }
    | _ -> failwith "write_b_f_aux: expected V"


let write_a p r next1 tr x =
  (* post is unused by our extraction path, keeping your call shape *)
  upd_gen_action p r (A_W (next1, tr))
    (* “v” here is the post we *want*; not consulted by our updater *)
    (if is_send (Steel_Channel_Protocol.step next1 x)
     then A_W (Steel_Channel_Protocol.step next1 x,
               Steel_Channel_Protocol.extend p next1 tr x)
     else if is_recv (Steel_Channel_Protocol.step next1 x)
     then A_R (Steel_Channel_Protocol.step next1 x,
               Steel_Channel_Protocol.extend p next1 tr x)
     else A_Fin (Steel_Channel_Protocol.step next1 x,
                 Steel_Channel_Protocol.extend p next1 tr x))
    (write_a_f_aux p next1 tr x)
;;

let write_b p r next1 tr x =
  upd_gen_action p r (B_W (next1, tr))
    (if is_send (Steel_Channel_Protocol.step next1 x)
     then B_R (Steel_Channel_Protocol.step next1 x,
               Steel_Channel_Protocol.extend p next1 tr x)
     else if is_recv (Steel_Channel_Protocol.step next1 x)
     then B_W (Steel_Channel_Protocol.step next1 x,
               Steel_Channel_Protocol.extend p next1 tr x)
     else B_Fin (Steel_Channel_Protocol.step next1 x,
                 Steel_Channel_Protocol.extend p next1 tr x))
    (write_b_f_aux p next1 tr x)
;;

let (alloc : dprot -> Obj.t t -> Obj.t chan) =
  fun p ->
    fun x ->
      let r = Steel_PCMReference.alloc (pcm p) x in
      Steel_Effect_Atomic.return () () r
let (split :
  dprot ->
    Obj.t chan -> Obj.t t -> Obj.t t -> Obj.t t -> unit -> unit -> unit)
  = fun p -> fun r -> fun v -> fun v0 -> fun v1 -> fun u1 -> fun u2 -> ()
let (new_chan : dprot -> Obj.t chan) =
  fun p ->
    let v =
      V
        {
          Steel_Channel_Protocol.to1 = p;
          Steel_Channel_Protocol.tr = (empty_trace p)
        } in
    let r = alloc p v in
    split p r v
      (if is_send p
       then A_W (p, (empty_trace p))
       else
         if is_recv p
         then A_R (p, (empty_trace p))
         else A_Fin (p, (empty_trace p)))
      (if is_send p
       then B_R (p, (empty_trace p))
       else
         if is_recv p
         then B_W (p, (empty_trace p))
         else B_Fin (p, (empty_trace p))) () ();
    r
let (send_a :
  dprot ->
    Obj.t chan ->
      dprot -> Obj.t -> (Obj.t, Obj.t) Steel_Channel_Protocol.trace -> unit)
  = fun p -> fun c -> fun next1 -> fun x -> fun tr -> write_a p c next1 tr x
let (send_b :
  dprot ->
    Obj.t chan ->
      dprot -> Obj.t -> (Obj.t, Obj.t) Steel_Channel_Protocol.trace -> unit)
  = fun p -> fun c -> fun next1 -> fun x -> fun tr -> write_b p c next1 tr x

  (* F* nat/pos extract to Zarith bigints; print them safely *)
let show_nat (n:Prims.nat) : string = Z.to_string (Obj.magic n)
let show_pos (p:Prims.pos) : string = Z.to_string (Obj.magic p)

(* --- helpers for logging / sizes --- *)

(* ---------- debug helpers ---------- *)
let show_nat (n: Prims.nat) : string =
  string_of_int (Obj.magic n : int)

let dbg (s:string) : unit =
  FStar_IO.print_string (s ^ "\n")

let dbg_nat (label:string) (n:Prims.nat) : unit =
  dbg (label ^ show_nat n)


  let rec (recv_a :
  dprot ->
    Obj.t chan ->
      dprot -> (Obj.t, Obj.t) Steel_Channel_Protocol.trace -> Obj.t)
  =
  fun p ->
  fun c ->
  fun next1 ->
  fun tr ->
    let tr' = get_a_r p c next1 tr in
    let to' =
      Steel_Channel_Protocol.__proj__Mkpartial_trace_of__item__to p tr'
    in
    let l_local  : Prims.nat = trace_length p next1 tr in
    let l_remote : Prims.nat =
      trace_length p to' tr'.Steel_Channel_Protocol.tr
    in
    dbg ("[pcm] recv_a: l_local=" ^ show_nat l_local ^
         "  l_remote=" ^ show_nat l_remote);
    if l_local >= l_remote then (
      dbg "[pcm] recv_a: spin (no new remote message yet)";
      recv_a p c next1 tr
    ) else (
      let x =
        next_message p next1 to' tr tr'.Steel_Channel_Protocol.tr
      in
      dbg "[pcm] recv_a: got next message";
      Steel_Effect_Atomic.return () () x
    )

(* in out/Duplex_PCM.ml *)

(* ---------- updated recv_b with logging ---------- *)
let rec (recv_b :
  dprot ->
    Obj.t chan ->
      dprot -> (Obj.t, Obj.t) Steel_Channel_Protocol.trace -> Obj.t)
  =
  fun p ->
  fun c ->
  fun next1 ->
  fun tr ->
    pr "[pcm] recv_b: enter";
    let tr' = get_b_r p c next1 tr in
    let to' =
      Steel_Channel_Protocol.__proj__Mkpartial_trace_of__item__to p tr'
    in
    let l_local  : Prims.nat = trace_length p next1 tr in
    let l_remote : Prims.nat =
      trace_length p to' tr'.Steel_Channel_Protocol.tr
    in
    pr ("[pcm] recv_b: l_local=" ^ show_nat l_local ^
        "  l_remote=" ^ show_nat l_remote);
    if l_local >= l_remote then (
      pr "[pcm] recv_b: spin (no new remote message yet)";
      recv_b p c next1 tr
    ) else (
      pr "[pcm] recv_b: computing next_message…";
      let x =
        next_message p next1 to' tr tr'.Steel_Channel_Protocol.tr
      in
      pr "[pcm] recv_b: next_message ok";
      Steel_Effect_Atomic.return () () x
    )



let (send_aux :
  dprot ->
    party ->
      Obj.t chan ->
        Obj.t send_next_dprot_t ->
          Obj.t -> (Obj.t, Obj.t) Steel_Channel_Protocol.trace -> unit)
  =
  fun p ->
    fun name ->
      fun c ->
        fun next1 ->
          fun x ->
            fun t1 ->
              if name = A
              then send_a p c next1 x t1
              else send_b p c next1 x t1
let (recv_aux :
  dprot ->
    party ->
      Obj.t chan ->
        Obj.t recv_next_dprot_t ->
          (Obj.t, Obj.t) Steel_Channel_Protocol.trace -> Obj.t)
  =
  fun p ->
    fun name ->
      fun c ->
        fun next1 ->
          fun t1 ->
            if name = A
            then
              let x = recv_a p c next1 t1 in
              Steel_Effect_Atomic.return () () x
            else
              (let x = recv_b p c next1 t1 in
               Steel_Effect_Atomic.return () () x)
type 'p trace_t =
  (dprot, ('p, Obj.t) Steel_Channel_Protocol.trace) Prims.dtuple2
type 'p channel =
  ('p chan * (dprot, ('p, Obj.t) Steel_Channel_Protocol.trace) Prims.dtuple2
    Steel_HigherReference.ref)
let fst : 'uuuuu 'uuuuu1 . unit -> ('uuuuu * 'uuuuu1) -> 'uuuuu =
  fun uu___ -> FStar_Pervasives_Native.fst
let snd : 'uuuuu 'uuuuu1 . unit -> ('uuuuu * 'uuuuu1) -> 'uuuuu1 =
  fun uu___ -> FStar_Pervasives_Native.snd
type ('a, 'x, 'y) eq2_prop = unit
let (read_trace_ref :
  dprot ->
    unit ->
      (dprot, (Obj.t, Obj.t) Steel_Channel_Protocol.trace) Prims.dtuple2
        Steel_HigherReference.ref ->
        dprot -> (Obj.t, Obj.t) Steel_Channel_Protocol.trace)
  =
  fun p ->
    fun w ->
      fun r ->
        fun next1 ->
          let x = Steel_HigherReference.read () () r in
          let tr = FStar_Pervasives.dsnd x in
          Steel_Effect_Atomic.return () () tr
let (unpack_trace_ref :
  dprot ->
    party ->
      Obj.t channel ->
        Prims.bool -> Obj.t -> (Obj.t, Obj.t) Steel_Channel_Protocol.trace)
  =
  fun p ->
    fun name ->
      fun c ->
        fun is_send1 ->
          fun next1 ->
            let tr = read_trace_ref p () ((snd ()) c) (Obj.magic next1) in
            Steel_Effect_Atomic.return () () tr
let (pack_trace_ref :
  dprot ->
    party ->
      Obj.t channel ->
        (dprot, (Obj.t, Obj.t) Steel_Channel_Protocol.trace) Prims.dtuple2 ->
          Prims.bool ->
            Obj.t ->
              (Obj.t, Obj.t) Steel_Channel_Protocol.trace -> Obj.t -> unit)
  =
  fun p ->
    fun name ->
      fun c ->
        fun w ->
          fun is_send1 ->
            fun next1 ->
              fun tr ->
                fun x ->
                  let w' =
                    Prims.Mkdtuple2
                      ((Steel_Channel_Protocol.step (Obj.magic next1) x),
                        (Steel_Channel_Protocol.extend p (Obj.magic next1) tr
                           x)) in
                  Steel_HigherReference.write () ((snd ()) c) w'
(* --- dbg helpers --- *)
let _dbg msg = Printf.eprintf "[pcm] %s\n%!" msg

type ch = (dprot, Obj.t channel) Prims.dtuple2

let (new_chan : dprot -> Obj.t chan) =
  fun p ->
    _dbg "new_chan: start";
    let v =
      V { Steel_Channel_Protocol.to1 = p;
          Steel_Channel_Protocol.tr  = (empty_trace p) } in
    _dbg "new_chan: V + empty_trace ok";
    let r = alloc p v in
    _dbg "new_chan: alloc ok";
    split p r v
      (if is_send p then A_W (p, (empty_trace p))
       else if is_recv p then A_R (p, (empty_trace p))
       else A_Fin (p, (empty_trace p)))
      (if is_send p then B_R (p, (empty_trace p))
       else if is_recv p then B_W (p, (empty_trace p))
       else B_Fin (p, (empty_trace p))) () ();
    _dbg "new_chan: split ok";
    r

let (new_channel' : dprot -> (Obj.t channel * Obj.t channel)) =
  fun p ->
    _dbg "new_channel': start";
    let v = Prims.Mkdtuple2 (p, (empty_trace p)) in
    _dbg "new_channel': empty_trace ok";
    let rA = Steel_HigherReference.alloc v in
    _dbg "new_channel': alloc rA ok";
    let rB = Steel_HigherReference.alloc v in
    _dbg "new_channel': alloc rB ok";
    let c = new_chan p in
    _dbg "new_channel': new_chan ok";
    let cA = (c, rA) in
    let cB = (c, rB) in
    _dbg "new_channel': done";
    Steel_Effect_Atomic.return () () (cA, cB)

let (channel_as_ch : dprot -> party -> Obj.t channel -> dprot -> unit) =
  fun _p -> fun _party -> fun _c -> fun _prot -> ()

let (new_channel : dprot -> (ch * ch)) =
  fun p ->
    _dbg "new_channel: start";
    let (cA, cB) = new_channel' p in
    _dbg "new_channel: new_channel' ok";
    channel_as_ch p A cA p;
    channel_as_ch p B cB p;
    _dbg "new_channel: channel_as_ch ok";
    ((Prims.Mkdtuple2 (p, cA)), (Prims.Mkdtuple2 (p, cB)))

(* in out/Duplex_PCM.ml (or wherever channel_send' is) *)

let (channel_send' :
  party -> dprot -> Obj.t send_next_dprot_t -> Obj.t channel -> Obj.t -> unit)
  =
  fun name p next1 c x ->
    let tr = unpack_trace_ref p name c true (Obj.magic next1) in
    print_endline "[pcm] channel_send': unpack_trace_ref ok";
    send_aux p name ((fst ()) c) next1 x tr;
    print_endline "[pcm] channel_send': send_aux ok";
    pack_trace_ref p name c (Prims.Mkdtuple2 (next1, tr)) true
      (Obj.magic next1) tr x


let (ch_as_channel : party -> ch -> dprot -> unit) =
  fun _party -> fun _c -> fun _prot -> ()

let (channel_send :
  party -> Obj.t send_next_dprot_t -> ch -> Obj.t -> unit) =
  fun name ->
  fun next1 ->
  fun c ->
  fun x ->
    _dbg "channel_send: start";
    ch_as_channel name c next1;
    let p = (Prims.__proj__Mkdtuple2__item___1 c) in
    let chan = (FStar_Pervasives.dsnd c) in
    channel_send' name p next1 chan x;
    channel_as_ch p name chan (Steel_Channel_Protocol.step next1 x);
    _dbg "channel_send: done"

let (channel_recv' :
  party -> dprot -> Obj.t recv_next_dprot_t -> Obj.t channel -> Obj.t) =
  fun name ->
  fun p ->
  fun next1 ->
  fun c ->
    _dbg "channel_recv': unpack_trace_ref…";
    let tr = unpack_trace_ref p name c false (Obj.magic next1) in
    _dbg "channel_recv': recv_aux…";
    let x = recv_aux p name ((fst ()) c) next1 tr in
    _dbg "channel_recv': pack_trace_ref…";
    pack_trace_ref p name c (Prims.Mkdtuple2 (next1, tr)) false
      (Obj.magic next1) tr x;
    _dbg "channel_recv': done";
    x

let (channel_recv :
  party -> Obj.t recv_next_dprot_t -> ch -> Obj.t) =
  fun name ->
  fun next1 ->
  fun c ->
    _dbg "channel_recv: start";
    ch_as_channel name c next1;
    let p    = (Prims.__proj__Mkdtuple2__item___1 c) in
    let chan = (FStar_Pervasives.dsnd c) in
    let x =
      channel_recv' name p next1 chan in
    channel_as_ch p name chan (Steel_Channel_Protocol.step next1 x);
    _dbg "channel_recv: done";
    Steel_Effect_Atomic.return () () x

