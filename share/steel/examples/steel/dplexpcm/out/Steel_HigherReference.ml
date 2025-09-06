(* out/Steel_HigherReference.ml *)

type 'a ref = { mutable v : 'a }

let alloc (x : 'a) : 'a ref =
  { v = x }

let read (_:unit) (_:unit) (r : 'a ref) : 'a =
  r.v

let write (_:unit) (r : 'a ref) (x : 'a) : unit =
  r.v <- x
