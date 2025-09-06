open Prims

(* ping→pong: A sends int; then A receives a bigger int; then done *)
let (pingpong : Duplex_PCM.dprot) =
  Duplex_PCM.bind (Duplex_PCM.send ())
    (fun x ->
       Duplex_PCM.bind (Duplex_PCM.recv ())
         (fun y -> Duplex_PCM.done1))

let () =
  print_endline "[demo] new_channel…";
  let (cA, cB) = Duplex_PCM.new_channel pingpong in

  (* client(A) sends 18 *)
  print_endline "[demo] client(A): send 18";
  let eighteen = (Obj.magic (Prims.of_int 18) : Obj.t) in
  Duplex_PCM.channel_send Duplex_PCM.A pingpong cA eighteen;

  (* server(B) receives, then sends y = x + 42 *)
  print_endline "[demo] server(B): recv x";
  let x =
    Duplex_PCM.channel_recv Duplex_PCM.B
      (Steel_Channel_Protocol.dual pingpong)
      cB
  in
  let xi : Prims.int = (Obj.magic x : Prims.int) in
  let yi : Prims.int = Prims.op_Addition xi (Prims.of_int 42) in
  Printf.printf "[demo] server(B): got %s; sending %s\n"
    (Prims.string_of_int xi) (Prims.string_of_int yi);

  let stepB =
    Steel_Channel_Protocol.step
      (Steel_Channel_Protocol.dual pingpong)
      x
  in
  Duplex_PCM.channel_send Duplex_PCM.B stepB cB (Obj.magic yi);

  (* client(A) receives y *)
  print_endline "[demo] client(A): recv y";
  let stepA =
    Steel_Channel_Protocol.step
      pingpong
      eighteen
  in
  let y =
    Duplex_PCM.channel_recv Duplex_PCM.A stepA cA
  in
  let yi' : Prims.int = (Obj.magic y : Prims.int) in
  Printf.printf "[demo] client(A): got %s\n" (Prims.string_of_int yi');
