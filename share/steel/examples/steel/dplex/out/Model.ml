open Prims
type user_id = Prims.string
type list_id = Prims.nat
type task_id = Prims.nat
type tag_id = Prims.nat
type space_type =
  | Personal 
  | Shared 
let uu___is_Personal (projectee : space_type) : Prims.bool=
  match projectee with | Personal -> true | uu___ -> false
let uu___is_Shared (projectee : space_type) : Prims.bool=
  match projectee with | Shared -> true | uu___ -> false
type field_key =
  | FKSpace 
  | FKOwner 
  | FKMembers 
  | FKLists 
  | FKListName of list_id 
  | FKTask of task_id 
  | FKTaskData of task_id 
  | FKTag of tag_id 
  | FKNextListId 
  | FKNextTaskId 
  | FKNextTagId 
let uu___is_FKSpace (projectee : field_key) : Prims.bool=
  match projectee with | FKSpace -> true | uu___ -> false
let uu___is_FKOwner (projectee : field_key) : Prims.bool=
  match projectee with | FKOwner -> true | uu___ -> false
let uu___is_FKMembers (projectee : field_key) : Prims.bool=
  match projectee with | FKMembers -> true | uu___ -> false
let uu___is_FKLists (projectee : field_key) : Prims.bool=
  match projectee with | FKLists -> true | uu___ -> false
let uu___is_FKListName (projectee : field_key) : Prims.bool=
  match projectee with | FKListName _0 -> true | uu___ -> false
let __proj__FKListName__item___0 (projectee : field_key) : list_id=
  match projectee with | FKListName _0 -> _0
let uu___is_FKTask (projectee : field_key) : Prims.bool=
  match projectee with | FKTask _0 -> true | uu___ -> false
let __proj__FKTask__item___0 (projectee : field_key) : task_id=
  match projectee with | FKTask _0 -> _0
let uu___is_FKTaskData (projectee : field_key) : Prims.bool=
  match projectee with | FKTaskData _0 -> true | uu___ -> false
let __proj__FKTaskData__item___0 (projectee : field_key) : task_id=
  match projectee with | FKTaskData _0 -> _0
let uu___is_FKTag (projectee : field_key) : Prims.bool=
  match projectee with | FKTag _0 -> true | uu___ -> false
let __proj__FKTag__item___0 (projectee : field_key) : tag_id=
  match projectee with | FKTag _0 -> _0
let uu___is_FKNextListId (projectee : field_key) : Prims.bool=
  match projectee with | FKNextListId -> true | uu___ -> false
let uu___is_FKNextTaskId (projectee : field_key) : Prims.bool=
  match projectee with | FKNextTaskId -> true | uu___ -> false
let uu___is_FKNextTagId (projectee : field_key) : Prims.bool=
  match projectee with | FKNextTagId -> true | uu___ -> false
type field_value =
  | FVSpace of space_type 
  | FVUser of user_id 
  | FVMembers of user_id Prims.list 
  | FVIdList of Prims.nat Prims.list 
  | FVString of Prims.string 
  | FVNat of Prims.nat 
let uu___is_FVSpace (projectee : field_value) : Prims.bool=
  match projectee with | FVSpace _0 -> true | uu___ -> false
let __proj__FVSpace__item___0 (projectee : field_value) : space_type=
  match projectee with | FVSpace _0 -> _0
let uu___is_FVUser (projectee : field_value) : Prims.bool=
  match projectee with | FVUser _0 -> true | uu___ -> false
let __proj__FVUser__item___0 (projectee : field_value) : user_id=
  match projectee with | FVUser _0 -> _0
let uu___is_FVMembers (projectee : field_value) : Prims.bool=
  match projectee with | FVMembers _0 -> true | uu___ -> false
let __proj__FVMembers__item___0 (projectee : field_value) :
  user_id Prims.list= match projectee with | FVMembers _0 -> _0
let uu___is_FVIdList (projectee : field_value) : Prims.bool=
  match projectee with | FVIdList _0 -> true | uu___ -> false
let __proj__FVIdList__item___0 (projectee : field_value) :
  Prims.nat Prims.list= match projectee with | FVIdList _0 -> _0
let uu___is_FVString (projectee : field_value) : Prims.bool=
  match projectee with | FVString _0 -> true | uu___ -> false
let __proj__FVString__item___0 (projectee : field_value) : Prims.string=
  match projectee with | FVString _0 -> _0
let uu___is_FVNat (projectee : field_value) : Prims.bool=
  match projectee with | FVNat _0 -> true | uu___ -> false
let __proj__FVNat__item___0 (projectee : field_value) : Prims.nat=
  match projectee with | FVNat _0 -> _0
type model = (field_key, field_value) Trees.kv_tree
let bucket : Prims.nat= (Prims.parse_int "1000000")
let field_key_to_int (k : field_key) : Prims.int=
  match k with
  | FKSpace -> Prims.int_zero
  | FKOwner -> Prims.int_one
  | FKMembers -> (Prims.of_int (2))
  | FKLists -> (Prims.of_int (3))
  | FKListName lid -> (Prims.parse_int "4000000") + lid
  | FKTask tid -> (Prims.parse_int "5000000") + tid
  | FKTaskData tid -> (Prims.parse_int "6000000") + tid
  | FKTag gid -> (Prims.parse_int "7000000") + gid
  | FKNextListId -> (Prims.parse_int "7999999")
  | FKNextTaskId -> (Prims.parse_int "8999999")
  | FKNextTagId -> (Prims.parse_int "9999999")
let cmp_field_key : field_key Trees.cmp=
  fun a b -> (field_key_to_int a) - (field_key_to_int b)
let rec model_get (m : model) (k : field_key) :
  (field_key, field_value) Trees.node_data FStar_Pervasives_Native.option=
  match m with
  | Trees.Leaf -> FStar_Pervasives_Native.None
  | Trees.Node (data, left, right) ->
      let delta = cmp_field_key data.Trees.key k in
      if delta < Prims.int_zero
      then model_get right k
      else
        if delta > Prims.int_zero
        then model_get left k
        else FStar_Pervasives_Native.Some data
let rec model_set (m : model) (k : field_key) (v : field_value) : model=
  match m with
  | Trees.Leaf ->
      Trees.Node
        ({ Trees.key = k; Trees.payload = v }, Trees.Leaf, Trees.Leaf)
  | Trees.Node (data, left, right) ->
      let delta = cmp_field_key data.Trees.key k in
      if delta < Prims.int_zero
      then Trees.Node (data, left, (model_set right k v))
      else
        if delta > Prims.int_zero
        then Trees.Node (data, (model_set left k v), right)
        else Trees.Node ({ Trees.key = k; Trees.payload = v }, left, right)
let get_nat (m : model) (k : field_key) : Prims.nat=
  match model_get m k with
  | FStar_Pervasives_Native.Some
      { Trees.key = uu___; Trees.payload = FVNat n;_} -> n
  | uu___ -> Prims.int_zero
let get_id_list (m : model) (k : field_key) : Prims.nat Prims.list=
  match model_get m k with
  | FStar_Pervasives_Native.Some
      { Trees.key = uu___; Trees.payload = FVIdList xs;_} -> xs
  | uu___ -> []
let get_members (m : model) : user_id Prims.list=
  match model_get m FKMembers with
  | FStar_Pervasives_Native.Some
      { Trees.key = uu___; Trees.payload = FVMembers xs;_} -> xs
  | uu___ -> []
let get_string (m : model) (k : field_key) : Prims.string=
  match model_get m k with
  | FStar_Pervasives_Native.Some
      { Trees.key = uu___; Trees.payload = FVString s;_} -> s
  | uu___ -> ""
let get_space (m : model) : space_type=
  match model_get m FKSpace with
  | FStar_Pervasives_Native.Some
      { Trees.key = uu___; Trees.payload = FVSpace s;_} -> s
  | uu___ -> Personal
let get_owner (m : model) : user_id=
  match model_get m FKOwner with
  | FStar_Pervasives_Native.Some
      { Trees.key = uu___; Trees.payload = FVUser u;_} -> u
  | uu___ -> ""
type 'm inv = unit
let initial_owner : user_id= ""
let init (uu___ : unit) : model=
  let m = Trees.Leaf in
  let m1 = model_set m FKSpace (FVSpace Personal) in
  let m2 = model_set m1 FKOwner (FVUser initial_owner) in
  let m3 = model_set m2 FKMembers (FVMembers [initial_owner]) in
  let m4 = model_set m3 FKLists (FVIdList []) in
  let m5 = model_set m4 FKNextListId (FVNat Prims.int_zero) in
  let m6 = model_set m5 FKNextTaskId (FVNat Prims.int_zero) in
  let m7 = model_set m6 FKNextTagId (FVNat Prims.int_zero) in m7
type action =
  | AddList of Prims.string 
  | AddTask of list_id * Prims.string 
  | AddTag of Prims.string 
  | AddMember of user_id 
  | Sync 
  | Flush 
let uu___is_AddList (projectee : action) : Prims.bool=
  match projectee with | AddList name -> true | uu___ -> false
let __proj__AddList__item__name (projectee : action) : Prims.string=
  match projectee with | AddList name -> name
let uu___is_AddTask (projectee : action) : Prims.bool=
  match projectee with | AddTask (lid, data) -> true | uu___ -> false
let __proj__AddTask__item__lid (projectee : action) : list_id=
  match projectee with | AddTask (lid, data) -> lid
let __proj__AddTask__item__data (projectee : action) : Prims.string=
  match projectee with | AddTask (lid, data) -> data
let uu___is_AddTag (projectee : action) : Prims.bool=
  match projectee with | AddTag name -> true | uu___ -> false
let __proj__AddTag__item__name (projectee : action) : Prims.string=
  match projectee with | AddTag name -> name
let uu___is_AddMember (projectee : action) : Prims.bool=
  match projectee with | AddMember uid -> true | uu___ -> false
let __proj__AddMember__item__uid (projectee : action) : user_id=
  match projectee with | AddMember uid -> uid
let uu___is_Sync (projectee : action) : Prims.bool=
  match projectee with | Sync -> true | uu___ -> false
let uu___is_Flush (projectee : action) : Prims.bool=
  match projectee with | Flush -> true | uu___ -> false
let next (m : model) (a : action) : model=
  match a with
  | Sync -> m
  | Flush -> m
  | AddList name ->
      let lid = get_nat m FKNextListId in
      let lids = get_id_list m FKLists in
      let m1 = model_set m (FKListName lid) (FVString name) in
      let m2 =
        model_set m1 FKLists
          (FVIdList (FStar_List_Tot_Base.op_At lids [lid])) in
      let m3 = model_set m2 FKNextListId (FVNat (lid + Prims.int_one)) in m3
  | AddTask (lid, data) ->
      let tid = get_nat m FKNextTaskId in
      let m1 = model_set m (FKTask tid) (FVNat lid) in
      let m2 = model_set m1 (FKTaskData tid) (FVString data) in
      let m3 = model_set m2 FKNextTaskId (FVNat (tid + Prims.int_one)) in m3
  | AddTag name ->
      let gid = get_nat m FKNextTagId in
      let m1 = model_set m (FKTag gid) (FVString name) in
      let m2 = model_set m1 FKNextTagId (FVNat (gid + Prims.int_one)) in m2
  | AddMember uid ->
      let ms = get_members m in
      model_set m FKMembers (FVMembers (FStar_List_Tot_Base.op_At ms [uid]))
let field_key_eqb (x : field_key) (y : field_key) : Prims.bool=
  (cmp_field_key x y) = Prims.int_zero
let field_value_eqb (x : field_value) (y : field_value) : Prims.bool=
  match (x, y) with
  | (FVSpace sx, FVSpace sy) -> sx = sy
  | (FVUser ux, FVUser uy) -> ux = uy
  | (FVMembers mx, FVMembers my) ->
      ((FStar_List_Tot_Base.length mx) = (FStar_List_Tot_Base.length my)) &&
        (FStar_List_Tot_Base.fold_left2 (fun acc a b -> acc && (a = b)) true
           mx my)
  | (FVIdList lx, FVIdList ly) ->
      ((FStar_List_Tot_Base.length lx) = (FStar_List_Tot_Base.length ly)) &&
        (FStar_List_Tot_Base.fold_left2 (fun acc a b -> acc && (a = b)) true
           lx ly)
  | (FVString sx, FVString sy) -> sx = sy
  | (FVNat nx, FVNat ny) -> nx = ny
  | uu___ -> false
type field_key_eqb_false_prop = unit
type field_key_eqb_spec_prop = unit
let rec list_str_eqb (xs : Prims.string Prims.list)
  (ys : Prims.string Prims.list) : Prims.bool=
  match (xs, ys) with
  | ([], []) -> true
  | (x::tl, y::tl2) -> (x = y) && (list_str_eqb tl tl2)
  | uu___ -> false
let rec list_nat_eqb (xs : Prims.nat Prims.list) (ys : Prims.nat Prims.list)
  : Prims.bool=
  match (xs, ys) with
  | ([], []) -> true
  | (x::tl, y::tl2) -> (x = y) && (list_nat_eqb tl tl2)
  | uu___ -> false
type field_value_eqb_sym_prop = unit
type field_value_eqb_spec_prop = unit
let rec model_eqb (x : model) (y : model) : Prims.bool=
  match (x, y) with
  | (Trees.Leaf, Trees.Leaf) -> true
  | (Trees.Node (dx, lx, rx), Trees.Node (dy, ly, ry)) ->
      (((field_key_eqb dx.Trees.key dy.Trees.key) &&
          (field_value_eqb dx.Trees.payload dy.Trees.payload))
         && (model_eqb lx ly))
        && (model_eqb rx ry)
  | uu___ -> false
type ('a, 'equals) symmetry = unit
type ('a, 'equals) reflexivity = unit
type ('a, 'equals) transitivity = unit
type ('a, 'equals) reflexivity2 = unit
