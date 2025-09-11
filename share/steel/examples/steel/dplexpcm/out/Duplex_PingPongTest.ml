open Prims

let (pingpong : Duplex_PCM.dprot) =
  Duplex_PCM.bind (Duplex_PCM.send ()) (fun x ->
      Duplex_PCM.bind (Duplex_PCM.recv ()) (fun y -> Duplex_PCM.done1))

let (client : Duplex_PCM.ch -> unit) =
 fun c ->
  Duplex_PCM.channel_send Duplex_PCM.A pingpong c (Obj.magic (Prims.of_int 18));
  let y =
    Duplex_PCM.channel_recv Duplex_PCM.A
      (Steel_Channel_Protocol.step pingpong (Obj.magic (Prims.of_int 18)))
      c
  in
  ()
