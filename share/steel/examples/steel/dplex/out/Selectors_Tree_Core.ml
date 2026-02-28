open Prims
type 'a node =
  {
  data: 'a ;
  left: 'a node Steel_Reference.ref ;
  right: 'a node Steel_Reference.ref }
let __proj__Mknode__item__data (projectee : 'a node) : 'a=
  match projectee with | { data; left; right;_} -> data
let __proj__Mknode__item__left (projectee : 'a node) :
  'a node Steel_Reference.ref=
  match projectee with | { data; left; right;_} -> left
let __proj__Mknode__item__right (projectee : 'a node) :
  'a node Steel_Reference.ref=
  match projectee with | { data; left; right;_} -> right
type 'a t = 'a node Steel_Reference.ref
type 'a tree = 'a Trees.tree
let get_left (n : 'a node) : 'a t= n.left
let get_right (n : 'a node) : 'a t= n.right
let get_data (n : 'a node) : 'a= n.data
let mk_node (data : 'a) (left : 'a t) (right : 'a t) : 'a node=
  { data; left; right }
let null_t (uu___ : unit) : 'a t= Steel_Reference.null ()
let is_null_t (ptr : 'a t) : Prims.bool= Steel_Reference.is_null ptr
let rec tree_view : 'a . 'a node Trees.tree -> 'a Trees.tree =
  fun tree1 ->
    match tree1 with
    | Trees.Leaf -> Trees.Leaf
    | Trees.Node (data, left, right) ->
        Trees.Node ((get_data data), (tree_view left), (tree_view right))



let intro_linked_tree_leaf (uu___ : unit) : unit= ()
let elim_linked_tree_leaf (ptr : 'a t) : unit= ()
let node_is_not_null (ptr : 'a t) : unit= ()
let pack_tree (ptr : 'a t) (left : 'a t) (right : 'a t) : unit= ()
type ('a, 't1) is_node = Obj.t
let reveal_non_empty_tree (ptr : 'a t) : unit= ()
let unpack_tree_node (ptr : 'a t) : 'a node=
  reveal_non_empty_tree ptr;
  (let n = Steel_Reference.read ptr in Steel_Effect_Atomic.return () () n)
let unpack_tree (ptr : 'a t) : 'a node=
  let n = unpack_tree_node ptr in Steel_Effect_Atomic.return () () n
