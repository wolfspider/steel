open Prims
let pingpong : Steel_Channel_Duplex.prot=
  Steel_Channel_Protocol.bind (Steel_Channel_Protocol.send ())
    (fun x ->
       Steel_Channel_Protocol.bind (Steel_Channel_Protocol.recv ())
         (fun y -> Steel_Channel_Protocol.done1))
let client (c : Obj.t Steel_Channel_Duplex.chan) : unit=
  Steel_Channel_Duplex.send pingpong c pingpong
    (Obj.magic (Prims.of_int (17)));
  (let y =
     Steel_Channel_Duplex.recv pingpong
       (Steel_Channel_Protocol.step pingpong (Obj.magic (Prims.of_int (17))))
       c in
   ())
let server (c : Obj.t Steel_Channel_Duplex.chan) : unit=
  let y =
    Steel_Channel_Duplex.recv pingpong (Steel_Channel_Protocol.dual pingpong)
      c in
  Steel_Channel_Duplex.send pingpong c
    (Steel_Channel_Protocol.step (Steel_Channel_Protocol.dual pingpong) y)
    (Obj.magic ((Obj.magic y) + (Prims.of_int (42))))
let client_server (uu___ : unit) : unit=
  let c = Steel_Channel_Duplex.new_chan pingpong in
  let uu___1 =
    Steel_Effect.par () () (fun uu___2 -> client c) () ()
      (fun uu___2 -> server c) in
  ()
let rec join_all (threads : unit Steel_Primitive_ForkJoin.thread Prims.list)
  : unit=
  if FStar_List_Tot_Base.isEmpty threads
  then ()
  else
    (let uu___1 = threads in
     match uu___1 with
     | hd::tl ->
         (Steel_Primitive_ForkJoin.join () (Obj.magic hd); join_all tl))
let rec many (n : Prims.nat)
  (threads : unit Steel_Primitive_ForkJoin.thread Prims.list) : unit=
  if n = Prims.int_zero
  then join_all threads
  else
    Steel_Primitive_ForkJoin.fork () () () () client_server
      (fun uu___2 uu___1 ->
         (fun t ->
            let t = Obj.magic t in
            fun uu___1 -> Obj.magic (many (n - Prims.int_one) (t :: threads)))
           uu___2 uu___1)
