module Domain.Steel

module M  = Model
module TC = Selectors.Tree.Core
module T  = Trees

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect

// A Steel reference to a model
let model_ref = TC.t (T.node_data M.field_key M.field_value)

// Pure equality lifted to Steel via selector
val model_eqb
  (ptr1 ptr2: model_ref)
  : Steel bool
    (TC.linked_tree ptr1 `star` TC.linked_tree ptr2)
    (fun _ -> TC.linked_tree ptr1 `star` TC.linked_tree ptr2)
    (requires fun _ -> True)
    (ensures fun h0 b h1 ->
      TC.v_linked_tree ptr1 h0 == TC.v_linked_tree ptr1 h1 /\
      TC.v_linked_tree ptr2 h0 == TC.v_linked_tree ptr2 h1 /\
      b == M.model_eqb
             (TC.v_linked_tree ptr1 h0)
             (TC.v_linked_tree ptr2 h0))