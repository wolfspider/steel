module Domain
module L = FStar.List.Tot.Base

type model (t:Type) = t
type action =
  | Step
  | Sync
  | Flush
type err = unit
type result (t:Type0) (e:Type0) =
  | Ok  : value:t -> result t e
  | Err : error:e -> result t e
let reject_err (_:unit) : err = ()
assume val inv (#t:Type) : model t -> prop
let init (#t:Type) (zero:t) : model t = zero
let try_step (#t:Type) (next: t -> t) (m:model t) (a:action) : result (model t) err =
  match a with
  | Step  -> Ok (next m)
  | Sync  -> Ok m
  | Flush -> Ok m
assume val init_satisfies_inv : (#t:Type) -> (zero:t) -> Lemma (inv (init zero))
assume val step_preserves_inv :
  (#t:Type) ->
  m:model t -> a:action -> m2:model t ->
  Lemma (requires inv m /\ (exists (next: t -> t). try_step next m a == Ok m2))
        (ensures  inv m2)
let rebase (_remote:action) (local:action) : action = local
let rebase_through_suffix (suffix:list action) (a:action) : action =
  L.fold_left (fun acc remote -> rebase remote acc) a (L.rev suffix)
let candidates (#t:Type) (_m:model t) (orig:action) : list action = [orig]
assume val explains : action -> action -> prop
assume val candidates_complete :
  (#t:Type) ->
  m:model t -> orig:action -> a_good:action -> m2:model t ->
  Lemma (requires inv m /\ explains orig a_good /\ (exists (next: t -> t). try_step next m a_good == Ok m2))
        (ensures  L.mem a_good (candidates m orig))
let model_eqb (#t:Type) (eqb: t -> t -> bool) (x:model t) (y:model t) : bool =
  eqb x y
assume val model_eqb_spec :
  (#t:Type) ->
  x:model t -> y:model t ->
  Lemma (ensures (forall (eqb: t -> t -> bool). model_eqb eqb x y <==> (x == y)))