open Prims
type 'a tree =
  | Leaf 
  | Node of 'a * 'a tree * 'a tree 
let uu___is_Leaf (projectee : 'a tree) : Prims.bool=
  match projectee with | Leaf -> true | uu___ -> false
let uu___is_Node (projectee : 'a tree) : Prims.bool=
  match projectee with | Node (data, left, right) -> true | uu___ -> false
let __proj__Node__item__data (projectee : 'a tree) : 'a=
  match projectee with | Node (data, left, right) -> data
let __proj__Node__item__left (projectee : 'a tree) : 'a tree=
  match projectee with | Node (data, left, right) -> left
let __proj__Node__item__right (projectee : 'a tree) : 'a tree=
  match projectee with | Node (data, left, right) -> right
type ('a, 'b) node_data = {
  key: 'a ;
  payload: 'b }
let __proj__Mknode_data__item__key (projectee : ('a, 'b) node_data) : 
  'a= match projectee with | { key; payload;_} -> key
let __proj__Mknode_data__item__payload (projectee : ('a, 'b) node_data) : 
  'b= match projectee with | { key; payload;_} -> payload
type ('a, 'b) kv_tree = ('a, 'b) node_data tree
type 'a cmp = 'a -> 'a -> Prims.int
let rec forall_keys : 'a . 'a tree -> ('a -> Prims.bool) -> Prims.bool =
  fun t cond ->
    match t with
    | Leaf -> true
    | Node (data, left, right) ->
        ((cond data) && (forall_keys left cond)) && (forall_keys right cond)
let key_left (compare : 'a cmp) (root : 'a) (key : 'a) : Prims.bool=
  (compare root key) >= Prims.int_zero
let key_right (compare : 'a cmp) (root : 'a) (key : 'a) : Prims.bool=
  (compare root key) <= Prims.int_zero
let rec is_bst : 'a . 'a cmp -> 'a tree -> Prims.bool =
  fun compare x ->
    match x with
    | Leaf -> true
    | Node (data, left, right) ->
        (((is_bst compare left) && (is_bst compare right)) &&
           (forall_keys left (key_left compare data)))
          && (forall_keys right (key_right compare data))
type ('a, 'cmp1) bst = 'a tree
type ('a, 'r, 'x) mem = Obj.t
let rec bst_search :
  'a . 'a cmp -> ('a, Obj.t) bst -> 'a -> 'a FStar_Pervasives_Native.option =
  fun cmp1 x key ->
    match x with
    | Leaf -> FStar_Pervasives_Native.None
    | Node (data, left, right) ->
        let delta = cmp1 data key in
        if delta < Prims.int_zero
        then bst_search cmp1 right key
        else
          if delta > Prims.int_zero
          then bst_search cmp1 left key
          else FStar_Pervasives_Native.Some data
let rec height : 'a . 'a tree -> Prims.nat =
  fun x ->
    match x with
    | Leaf -> Prims.int_zero
    | Node (data, left, right) ->
        if (height left) > (height right)
        then (height left) + Prims.int_one
        else (height right) + Prims.int_one
let rec append_left : 'a . 'a tree -> 'a -> 'a tree =
  fun x v ->
    match x with
    | Leaf -> Node (v, Leaf, Leaf)
    | Node (x1, left, right) -> Node (x1, (append_left left v), right)
let rec append_right : 'a . 'a tree -> 'a -> 'a tree =
  fun x v ->
    match x with
    | Leaf -> Node (v, Leaf, Leaf)
    | Node (x1, left, right) -> Node (x1, left, (append_right right v))
let rec insert_bst : 'a . 'a cmp -> ('a, Obj.t) bst -> 'a -> 'a tree =
  fun cmp1 x key ->
    match x with
    | Leaf -> Node (key, Leaf, Leaf)
    | Node (data, left, right) ->
        let delta = cmp1 data key in
        if delta >= Prims.int_zero
        then
          let new_left = insert_bst cmp1 left key in
          Node (data, new_left, right)
        else
          (let new_right = insert_bst cmp1 right key in
           Node (data, left, new_right))
let rec is_balanced : 'a . 'a tree -> Prims.bool =
  fun x ->
    match x with
    | Leaf -> true
    | Node (data, left, right) ->
        (((FStar_Math_Lib.abs ((height right) - (height left))) <=
            Prims.int_one)
           && (is_balanced right))
          && (is_balanced left)
type ('a, 'cmp1, 'x) is_avl = unit
type ('a, 'cmp1) avl = 'a tree
let rotate_left (r : 'a tree) : 'a tree FStar_Pervasives_Native.option=
  match r with
  | Node (x, t1, Node (z, t2, t3)) ->
      FStar_Pervasives_Native.Some (Node (z, (Node (x, t1, t2)), t3))
  | uu___ -> FStar_Pervasives_Native.None
let rotate_right (r : 'a tree) : 'a tree FStar_Pervasives_Native.option=
  match r with
  | Node (x, Node (z, t1, t2), t3) ->
      FStar_Pervasives_Native.Some (Node (z, t1, (Node (x, t2, t3))))
  | uu___ -> FStar_Pervasives_Native.None
let rotate_right_left (r : 'a tree) : 'a tree FStar_Pervasives_Native.option=
  match r with
  | Node (x, t1, Node (z, Node (y, t2, t3), t4)) ->
      FStar_Pervasives_Native.Some
        (Node (y, (Node (x, t1, t2)), (Node (z, t3, t4))))
  | uu___ -> FStar_Pervasives_Native.None
let rotate_left_right (r : 'a tree) : 'a tree FStar_Pervasives_Native.option=
  match r with
  | Node (x, Node (z, t1, Node (y, t2, t3)), t4) ->
      FStar_Pervasives_Native.Some
        (Node (y, (Node (z, t1, t2)), (Node (x, t3, t4))))
  | uu___ -> FStar_Pervasives_Native.None
let rebalance_avl (x : 'a tree) : 'a tree=
  match x with
  | Leaf -> x
  | Node (data, left, right) ->
      if is_balanced x
      then x
      else
        if ((height left) - (height right)) > Prims.int_one
        then
          (let uu___1 = left in
           match uu___1 with
           | Node (ldata, lleft, lright) ->
               if (height lright) > (height lleft)
               then
                 (match rotate_left_right x with
                  | FStar_Pervasives_Native.Some y -> y
                  | uu___2 -> x)
               else
                 (match rotate_right x with
                  | FStar_Pervasives_Native.Some y -> y
                  | uu___3 -> x))
        else
          if ((height left) - (height right)) < (Prims.of_int (-1))
          then
            (let uu___2 = right in
             match uu___2 with
             | Node (rdata, rleft, rright) ->
                 if (height rleft) > (height rright)
                 then
                   (match rotate_right_left x with
                    | FStar_Pervasives_Native.Some y -> y
                    | uu___3 -> x)
                 else
                   (match rotate_left x with
                    | FStar_Pervasives_Native.Some y -> y
                    | uu___4 -> x))
          else x
let rec insert_avl : 'a . 'a cmp -> 'a tree -> 'a -> 'a tree =
  fun cmp1 x key ->
    match x with
    | Leaf -> Node (key, Leaf, Leaf)
    | Node (data, left, right) ->
        let delta = cmp1 data key in
        if delta >= Prims.int_zero
        then
          let new_left = insert_avl cmp1 left key in
          let tmp = Node (data, new_left, right) in rebalance_avl tmp
        else
          (let new_right = insert_avl cmp1 right key in
           let tmp = Node (data, left, new_right) in rebalance_avl tmp)
