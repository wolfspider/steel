(* Steel_SpinLock.ml — sequential js_of_ocaml runtime *)

type lock_t = unit
type 'a lock = lock_t

let new_lock (_ : unit) : unit lock =
  ()

let acquire (_ : unit) (_ : unit lock) =
  ()

let release (_ : unit) (_ : unit lock) =
  ()