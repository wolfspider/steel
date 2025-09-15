(* Stop_Flag.ml *)
module Stop_flag : sig
  type t
  val create : bool -> t
  val get    : t -> bool
  val set    : t -> bool -> unit
  val test_and_set : t -> bool  (* returns previous value *)
end = struct
  type t = bool Atomic.t
  let create init = Atomic.make init
  let get t       = Atomic.get t
  let set t v     = Atomic.set t v
  let test_and_set t =
    (* CAS loop: set true, return previous value *)
    let rec loop () =
      let old = Atomic.get t in
      if Atomic.compare_and_set t old true then old else loop ()
    in
    loop ()
end
