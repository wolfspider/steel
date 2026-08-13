open Prims
let rec append_left :
  'a . 'a Selectors_Tree_Core.t -> 'a -> 'a Selectors_Tree_Core.t =
  fun ptr v ->
    if Selectors_Tree_Core.is_null_t ptr
    then
      (Selectors_Tree_Core.elim_linked_tree_leaf ptr;
       (let node =
          Selectors_Tree_Core.mk_node v ptr (Selectors_Tree_Core.null_t ()) in
        let new_tree = Steel_Reference.malloc node in
        Selectors_Tree_Core.intro_linked_tree_leaf ();
        Selectors_Tree_Core.pack_tree new_tree ptr
          (Selectors_Tree_Core.null_t ());
        new_tree))
    else
      (let node = Selectors_Tree_Core.unpack_tree ptr in
       let new_left = append_left (Selectors_Tree_Core.get_left node) v in
       let new_node =
         Selectors_Tree_Core.mk_node (Selectors_Tree_Core.get_data node)
           new_left (Selectors_Tree_Core.get_right node) in
       Steel_Reference.write ptr new_node;
       Selectors_Tree_Core.pack_tree ptr new_left
         (Selectors_Tree_Core.get_right node);
       ptr)
let rec append_right :
  'a . 'a Selectors_Tree_Core.t -> 'a -> 'a Selectors_Tree_Core.t =
  fun ptr v ->
    if Selectors_Tree_Core.is_null_t ptr
    then
      (Selectors_Tree_Core.elim_linked_tree_leaf ptr;
       (let node =
          Selectors_Tree_Core.mk_node v (Selectors_Tree_Core.null_t ()) ptr in
        let new_tree = Steel_Reference.malloc node in
        Selectors_Tree_Core.intro_linked_tree_leaf ();
        Selectors_Tree_Core.pack_tree new_tree
          (Selectors_Tree_Core.null_t ()) ptr;
        new_tree))
    else
      (let node = Selectors_Tree_Core.unpack_tree ptr in
       let new_right = append_right (Selectors_Tree_Core.get_right node) v in
       let new_node =
         Selectors_Tree_Core.mk_node (Selectors_Tree_Core.get_data node)
           (Selectors_Tree_Core.get_left node) new_right in
       Steel_Reference.write ptr new_node;
       Selectors_Tree_Core.pack_tree ptr (Selectors_Tree_Core.get_left node)
         new_right;
       ptr)
let rec height : 'a . 'a Selectors_Tree_Core.t -> Prims.nat =
  fun ptr ->
    if Selectors_Tree_Core.is_null_t ptr
    then (Selectors_Tree_Core.elim_linked_tree_leaf ptr; Prims.int_zero)
    else
      (let node = Selectors_Tree_Core.unpack_tree ptr in
       let hleft = height (Selectors_Tree_Core.get_left node) in
       let hright = height (Selectors_Tree_Core.get_right node) in
       Selectors_Tree_Core.pack_tree ptr (Selectors_Tree_Core.get_left node)
         (Selectors_Tree_Core.get_right node);
       if hleft > hright
       then hleft + Prims.int_one
       else hright + Prims.int_one)
let rec member : 'a . 'a Selectors_Tree_Core.t -> 'a -> Prims.bool =
  fun ptr v ->
    if Selectors_Tree_Core.is_null_t ptr
    then (Selectors_Tree_Core.elim_linked_tree_leaf ptr; false)
    else
      (let node = Selectors_Tree_Core.unpack_tree ptr in
       if v = (Selectors_Tree_Core.get_data node)
       then
         (Selectors_Tree_Core.pack_tree ptr
            (Selectors_Tree_Core.get_left node)
            (Selectors_Tree_Core.get_right node);
          true)
       else
         (let mleft = member (Selectors_Tree_Core.get_left node) v in
          let mright = member (Selectors_Tree_Core.get_right node) v in
          Selectors_Tree_Core.pack_tree ptr
            (Selectors_Tree_Core.get_left node)
            (Selectors_Tree_Core.get_right node);
          mleft || mright))
let rotate_left (ptr : 'a Selectors_Tree_Core.t) : 'a Selectors_Tree_Core.t=
  Selectors_Tree_Core.node_is_not_null ptr;
  (let x_node = Selectors_Tree_Core.unpack_tree ptr in
   let x = Selectors_Tree_Core.get_data x_node in
   Selectors_Tree_Core.node_is_not_null
     (Selectors_Tree_Core.get_right x_node);
   (let z_node =
      Selectors_Tree_Core.unpack_tree (Selectors_Tree_Core.get_right x_node) in
    let z = Selectors_Tree_Core.get_data z_node in
    let new_subnode =
      Selectors_Tree_Core.mk_node x (Selectors_Tree_Core.get_left x_node)
        (Selectors_Tree_Core.get_left z_node) in
    let new_node =
      Selectors_Tree_Core.mk_node z ptr
        (Selectors_Tree_Core.get_right z_node) in
    Steel_Reference.write (Selectors_Tree_Core.get_right x_node) new_node;
    Steel_Reference.write ptr new_subnode;
    Selectors_Tree_Core.pack_tree ptr (Selectors_Tree_Core.get_left x_node)
      (Selectors_Tree_Core.get_left z_node);
    Selectors_Tree_Core.pack_tree (Selectors_Tree_Core.get_right x_node) ptr
      (Selectors_Tree_Core.get_right z_node);
    Selectors_Tree_Core.get_right x_node))
let rotate_right (ptr : 'a Selectors_Tree_Core.t) : 'a Selectors_Tree_Core.t=
  Selectors_Tree_Core.node_is_not_null ptr;
  (let x_node = Selectors_Tree_Core.unpack_tree ptr in
   let x = Selectors_Tree_Core.get_data x_node in
   Selectors_Tree_Core.node_is_not_null (Selectors_Tree_Core.get_left x_node);
   (let z_node =
      Selectors_Tree_Core.unpack_tree (Selectors_Tree_Core.get_left x_node) in
    let z = Selectors_Tree_Core.get_data z_node in
    let new_subnode =
      Selectors_Tree_Core.mk_node x (Selectors_Tree_Core.get_right z_node)
        (Selectors_Tree_Core.get_right x_node) in
    let new_node =
      Selectors_Tree_Core.mk_node z (Selectors_Tree_Core.get_left z_node) ptr in
    Steel_Reference.write (Selectors_Tree_Core.get_left x_node) new_node;
    Steel_Reference.write ptr new_subnode;
    Selectors_Tree_Core.pack_tree ptr (Selectors_Tree_Core.get_right z_node)
      (Selectors_Tree_Core.get_right x_node);
    Selectors_Tree_Core.pack_tree (Selectors_Tree_Core.get_left x_node)
      (Selectors_Tree_Core.get_left z_node) ptr;
    Selectors_Tree_Core.get_left x_node))
let rotate_right_left (ptr : 'a Selectors_Tree_Core.t) :
  'a Selectors_Tree_Core.t=
  Selectors_Tree_Core.node_is_not_null ptr;
  (let x_node = Selectors_Tree_Core.unpack_tree ptr in
   let x = Selectors_Tree_Core.get_data x_node in
   Selectors_Tree_Core.node_is_not_null
     (Selectors_Tree_Core.get_right x_node);
   (let z_node =
      Selectors_Tree_Core.unpack_tree (Selectors_Tree_Core.get_right x_node) in
    let z = Selectors_Tree_Core.get_data z_node in
    Selectors_Tree_Core.node_is_not_null
      (Selectors_Tree_Core.get_left z_node);
    (let y_node =
       Selectors_Tree_Core.unpack_tree (Selectors_Tree_Core.get_left z_node) in
     let y = Selectors_Tree_Core.get_data y_node in
     let new_x =
       Selectors_Tree_Core.mk_node x (Selectors_Tree_Core.get_left x_node)
         (Selectors_Tree_Core.get_left y_node) in
     let new_z =
       Selectors_Tree_Core.mk_node z (Selectors_Tree_Core.get_right y_node)
         (Selectors_Tree_Core.get_right z_node) in
     let new_y =
       Selectors_Tree_Core.mk_node y ptr
         (Selectors_Tree_Core.get_right x_node) in
     Steel_Reference.write ptr new_x;
     Steel_Reference.write (Selectors_Tree_Core.get_right x_node) new_z;
     Steel_Reference.write (Selectors_Tree_Core.get_left z_node) new_y;
     Selectors_Tree_Core.pack_tree ptr (Selectors_Tree_Core.get_left x_node)
       (Selectors_Tree_Core.get_left y_node);
     Selectors_Tree_Core.pack_tree (Selectors_Tree_Core.get_right x_node)
       (Selectors_Tree_Core.get_right y_node)
       (Selectors_Tree_Core.get_right z_node);
     Selectors_Tree_Core.pack_tree (Selectors_Tree_Core.get_left z_node) ptr
       (Selectors_Tree_Core.get_right x_node);
     Selectors_Tree_Core.get_left z_node)))
let rotate_left_right (ptr : 'a Selectors_Tree_Core.t) :
  'a Selectors_Tree_Core.t=
  Selectors_Tree_Core.node_is_not_null ptr;
  (let x_node = Selectors_Tree_Core.unpack_tree ptr in
   let x = Selectors_Tree_Core.get_data x_node in
   Selectors_Tree_Core.node_is_not_null (Selectors_Tree_Core.get_left x_node);
   (let z_node =
      Selectors_Tree_Core.unpack_tree (Selectors_Tree_Core.get_left x_node) in
    let z = Selectors_Tree_Core.get_data z_node in
    Selectors_Tree_Core.node_is_not_null
      (Selectors_Tree_Core.get_right z_node);
    (let y_node =
       Selectors_Tree_Core.unpack_tree (Selectors_Tree_Core.get_right z_node) in
     let y = Selectors_Tree_Core.get_data y_node in
     let new_z =
       Selectors_Tree_Core.mk_node z (Selectors_Tree_Core.get_left z_node)
         (Selectors_Tree_Core.get_left y_node) in
     let new_x =
       Selectors_Tree_Core.mk_node x (Selectors_Tree_Core.get_right y_node)
         (Selectors_Tree_Core.get_right x_node) in
     let new_y =
       Selectors_Tree_Core.mk_node y (Selectors_Tree_Core.get_left x_node)
         ptr in
     Steel_Reference.write (Selectors_Tree_Core.get_left x_node) new_z;
     Steel_Reference.write ptr new_x;
     Steel_Reference.write (Selectors_Tree_Core.get_right z_node) new_y;
     Selectors_Tree_Core.pack_tree (Selectors_Tree_Core.get_left x_node)
       (Selectors_Tree_Core.get_left z_node)
       (Selectors_Tree_Core.get_left y_node);
     Selectors_Tree_Core.pack_tree ptr (Selectors_Tree_Core.get_right y_node)
       (Selectors_Tree_Core.get_right x_node);
     Selectors_Tree_Core.pack_tree (Selectors_Tree_Core.get_right z_node)
       (Selectors_Tree_Core.get_left x_node) ptr;
     Selectors_Tree_Core.get_right z_node)))
let rec is_balanced : 'a . 'a Selectors_Tree_Core.t -> Prims.bool =
  fun ptr ->
    if Selectors_Tree_Core.is_null_t ptr
    then (Selectors_Tree_Core.elim_linked_tree_leaf ptr; true)
    else
      (let node = Selectors_Tree_Core.unpack_tree ptr in
       let lh = height (Selectors_Tree_Core.get_left node) in
       let rh = height (Selectors_Tree_Core.get_right node) in
       let lbal = is_balanced (Selectors_Tree_Core.get_left node) in
       let rbal = is_balanced (Selectors_Tree_Core.get_right node) in
       Selectors_Tree_Core.pack_tree ptr (Selectors_Tree_Core.get_left node)
         (Selectors_Tree_Core.get_right node);
       (lbal && rbal) &&
         (((rh - lh) >= (Prims.of_int (-1))) && ((rh - lh) <= Prims.int_one)))
let rebalance_avl (cmp : 'a Trees.cmp) (ptr : 'a Selectors_Tree_Core.t) :
  'a Selectors_Tree_Core.t=
  let uu___ = is_balanced ptr in
  if uu___
  then Steel_Effect_Atomic.return () () ptr
  else
    (Selectors_Tree_Core.node_is_not_null ptr;
     (let node = Selectors_Tree_Core.unpack_tree ptr in
      let lh = height (Selectors_Tree_Core.get_left node) in
      let rh = height (Selectors_Tree_Core.get_right node) in
      if (lh - rh) > Prims.int_one
      then
        (Selectors_Tree_Core.node_is_not_null
           (Selectors_Tree_Core.get_left node);
         (let l_node =
            Selectors_Tree_Core.unpack_tree
              (Selectors_Tree_Core.get_left node) in
          let llh = height (Selectors_Tree_Core.get_left l_node) in
          let lrh = height (Selectors_Tree_Core.get_right l_node) in
          Selectors_Tree_Core.pack_tree (Selectors_Tree_Core.get_left node)
            (Selectors_Tree_Core.get_left l_node)
            (Selectors_Tree_Core.get_right l_node);
          Selectors_Tree_Core.pack_tree ptr
            (Selectors_Tree_Core.get_left node)
            (Selectors_Tree_Core.get_right node);
          if lrh > llh then rotate_left_right ptr else rotate_right ptr))
      else
        if (lh - rh) < (Prims.of_int (-1))
        then
          (Selectors_Tree_Core.node_is_not_null
             (Selectors_Tree_Core.get_right node);
           (let r_node =
              Selectors_Tree_Core.unpack_tree
                (Selectors_Tree_Core.get_right node) in
            let rlh = height (Selectors_Tree_Core.get_left r_node) in
            let rrh = height (Selectors_Tree_Core.get_right r_node) in
            Selectors_Tree_Core.pack_tree
              (Selectors_Tree_Core.get_right node)
              (Selectors_Tree_Core.get_left r_node)
              (Selectors_Tree_Core.get_right r_node);
            Selectors_Tree_Core.pack_tree ptr
              (Selectors_Tree_Core.get_left node)
              (Selectors_Tree_Core.get_right node);
            if rlh > rrh then rotate_right_left ptr else rotate_left ptr))
        else
          (Selectors_Tree_Core.pack_tree ptr
             (Selectors_Tree_Core.get_left node)
             (Selectors_Tree_Core.get_right node);
           ptr)))
let rec insert_avl :
  'a .
    'a Trees.cmp ->
      'a Selectors_Tree_Core.t -> 'a -> 'a Selectors_Tree_Core.t
  =
  fun cmp ptr v ->
    if Selectors_Tree_Core.is_null_t ptr
    then
      (Selectors_Tree_Core.elim_linked_tree_leaf ptr;
       (let node =
          Selectors_Tree_Core.mk_node v ptr (Selectors_Tree_Core.null_t ()) in
        let new_tree = Steel_Reference.malloc node in
        Selectors_Tree_Core.intro_linked_tree_leaf ();
        Selectors_Tree_Core.pack_tree new_tree ptr
          (Selectors_Tree_Core.null_t ());
        new_tree))
    else
      (let node = Selectors_Tree_Core.unpack_tree ptr in
       if (cmp (Selectors_Tree_Core.get_data node) v) >= Prims.int_zero
       then
         let new_left = insert_avl cmp (Selectors_Tree_Core.get_left node) v in
         let new_node =
           Selectors_Tree_Core.mk_node (Selectors_Tree_Core.get_data node)
             new_left (Selectors_Tree_Core.get_right node) in
         (Steel_Reference.write ptr new_node;
          Selectors_Tree_Core.pack_tree ptr new_left
            (Selectors_Tree_Core.get_right node);
          rebalance_avl cmp ptr)
       else
         (let new_right =
            insert_avl cmp (Selectors_Tree_Core.get_right node) v in
          let new_node =
            Selectors_Tree_Core.mk_node (Selectors_Tree_Core.get_data node)
              (Selectors_Tree_Core.get_left node) new_right in
          Steel_Reference.write ptr new_node;
          Selectors_Tree_Core.pack_tree ptr
            (Selectors_Tree_Core.get_left node) new_right;
          rebalance_avl cmp ptr))
