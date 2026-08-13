module Domain
module L = FStar.List.Tot.Base
module M = Model

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect

open Selectors.Tree
open Selectors.Tree.Core
module Spec = Trees

type model = M.model
type action = M.action

type err = unit
type result (t:Type0) (e:Type0) =
  | Ok  : value:t -> result t e
  | Err : error:e -> result t e

let reject_err (_:unit) : err = ()

assume val inv : model -> prop

let init (_:unit) : model = M.init ()

let try_step (m:model) (a:action) : result model err =
  match a with
  | M.Sync  -> Ok m
  | M.Flush -> Ok m
  | _       -> Ok (M.next m a)

assume val init_satisfies_inv : unit -> Lemma (inv (init ()))
assume val step_preserves_inv :
  m:model -> a:action -> m2:model ->
  Lemma (requires inv m /\ try_step m a == Ok m2)
        (ensures  inv m2)

let rebase (_remote:action) (local:action) : action = local

let rebase_through_suffix (suffix:list action) (a:action) : action =
  L.fold_left (fun acc remote -> rebase remote acc) a (L.rev suffix)

let candidates (_m:model) (orig:action) : list action = [orig]

assume val explains : action -> action -> prop
assume val candidates_complete :
  m:model -> orig:action -> a_good:action -> m2:model ->
  Lemma (requires inv m /\ explains orig a_good /\ try_step m a_good == Ok m2)
        (ensures  L.mem a_good (candidates m orig))

let model_ref = t (Spec.node_data M.field_key M.field_value)

assume val model_eqb
  (ptr1 ptr2: model_ref)
  : Steel bool
    (linked_tree ptr1 `star` linked_tree ptr2)
    (fun _ -> linked_tree ptr1 `star` linked_tree ptr2)
    (requires fun _ -> True)
    (ensures fun h0 b h1 ->
      v_linked_tree ptr1 h0 == v_linked_tree ptr1 h1 /\
      v_linked_tree ptr2 h0 == v_linked_tree ptr2 h1 /\
      b == M.model_eqb
             (v_linked_tree ptr1 h0)
             (v_linked_tree ptr2 h0))