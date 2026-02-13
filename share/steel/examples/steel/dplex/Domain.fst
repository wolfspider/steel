module Domain
open FStar.List.Tot.Base

assume new type model  : eqtype
assume new type action : eqtype
assume new type err    : Type0

type result (t:Type0) (e:Type0) =
  | Ok  : value:t -> result t e
  | Err : error:e -> result t e

assume val reject_err : unit -> err

assume val inv      : model -> prop
assume val init     : unit -> model
assume val try_step : model -> action -> result model err

assume val init_satisfies_inv : unit -> Lemma (inv (init ()))

assume val step_preserves_inv :
  m:model -> a:action -> m2:model ->
  Lemma (requires inv m /\ try_step m a == Ok m2)
        (ensures  inv m2)

assume val rebase : remote:action -> local:action -> action

let rebase_through_suffix (suffix:list action) (a:action) : action =
  fold_left (fun acc remote -> rebase remote acc) a (rev suffix)

assume val candidates : model -> action -> list action
assume val explains   : action -> action -> prop

assume val candidates_complete :
  m:model -> orig:action -> a_good:action -> m2:model ->
  Lemma (requires inv m /\ explains orig a_good /\ try_step m a_good == Ok m2)
        (ensures  mem a_good (candidates m orig))

// A computable equality test for models (needed for noChange)
assume val model_eqb : model -> model -> bool

// Optional: relate it to propositional equality (useful later for proofs)
assume val model_eqb_spec : x:model -> y:model -> Lemma (ensures (model_eqb x y <==> (x == y)))

