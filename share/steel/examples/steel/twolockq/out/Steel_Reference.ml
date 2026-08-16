(* Steel_Reference.ml — js_of_ocaml runtime *)

type 'a ref = 'a Stdlib.ref

let alloc_pt (x : 'a) : 'a ref =
  Stdlib.ref x

let read_pt (_perm : unit) (_v : unit) (r : 'a ref) : 'a =
  !r

let read_refine_pt (_perm : unit) (_q : unit) (r : 'a ref) : 'a =
  !r

let write_pt (_v : unit) (r : 'a ref) (x : 'a) : unit =
  r := x

let free_pt (_v : unit) (_r : 'a ref) : unit =
  ()