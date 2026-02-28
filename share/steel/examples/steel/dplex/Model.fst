module Model
open FStar.List.Tot
open Trees

// ============================================================================
// Base types
// ============================================================================

type user_id  = string
type list_id  = nat
type task_id  = nat
type tag_id   = nat

type space_type =
  | Personal
  | Shared

// ============================================================================
// Field keys and values
// ============================================================================

type field_key =
  | FKSpace
  | FKOwner
  | FKMembers
  | FKLists
  | FKListName  : list_id -> field_key
  | FKTask      : task_id -> field_key
  | FKTaskData  : task_id -> field_key
  | FKTag       : tag_id  -> field_key
  | FKNextListId
  | FKNextTaskId
  | FKNextTagId

type field_value =
  | FVSpace    : space_type   -> field_value
  | FVUser     : user_id      -> field_value
  | FVMembers  : list user_id -> field_value
  | FVIdList   : list nat     -> field_value
  | FVString   : string       -> field_value
  | FVNat      : nat          -> field_value

type model = kv_tree field_key field_value

// ============================================================================
// Comparison for field_key
// ============================================================================

let bucket : nat = 1000000

let field_key_to_int (k:field_key) : int =
  match k with
  | FKSpace         -> 0
  | FKOwner         -> 1
  | FKMembers       -> 2
  | FKLists         -> 3
  | FKListName  lid -> 4000000 + lid
  | FKTask      tid -> 5000000 + tid
  | FKTaskData  tid -> 6000000 + tid
  | FKTag       gid -> 7000000 + gid
  | FKNextListId    -> 7999999
  | FKNextTaskId    -> 8999999
  | FKNextTagId     -> 9999999

let cmp_field_key : cmp field_key =
  fun a b -> field_key_to_int a - field_key_to_int b

// ============================================================================
// Model lookup and update helpers
// ============================================================================

let rec model_get (m:model) (k:field_key) : option (node_data field_key field_value) =
  match m with
  | Leaf -> None
  | Node data left right ->
      let delta = cmp_field_key data.key k in
      if delta < 0 then model_get right k
      else if delta > 0 then model_get left k
      else Some data

let rec model_set (m:model) (k:field_key) (v:field_value) : model =
  match m with
  | Leaf -> Node { key = k; payload = v } Leaf Leaf
  | Node data left right ->
      let delta = cmp_field_key data.key k in
      if delta < 0 then Node data left (model_set right k v)
      else if delta > 0 then Node data (model_set left k v) right
      else Node { key = k; payload = v } left right

// ============================================================================
// Typed accessors
// ============================================================================

let get_nat (m:model) (k:field_key) : nat =
  match model_get m k with
  | Some { payload = FVNat n } -> n
  | _ -> 0

let get_id_list (m:model) (k:field_key) : list nat =
  match model_get m k with
  | Some { payload = FVIdList xs } -> xs
  | _ -> []

let get_members (m:model) : list user_id =
  match model_get m FKMembers with
  | Some { payload = FVMembers xs } -> xs
  | _ -> []

let get_string (m:model) (k:field_key) : string =
  match model_get m k with
  | Some { payload = FVString s } -> s
  | _ -> ""

let get_space (m:model) : space_type =
  match model_get m FKSpace with
  | Some { payload = FVSpace s } -> s
  | _ -> Personal

let get_owner (m:model) : user_id =
  match model_get m FKOwner with
  | Some { payload = FVUser u } -> u
  | _ -> ""

// ============================================================================
// Invariant
// ============================================================================

let inv (m:model) : prop =
  // Owner is always in members
  FStar.List.Tot.mem (get_owner m) (get_members m) /\
  // Next ids are monotonically valid
  get_nat m FKNextListId <= bucket /\
  get_nat m FKNextTaskId <= bucket /\
  get_nat m FKNextTagId  <= bucket

// ============================================================================
// Init
// ============================================================================

let initial_owner : user_id = ""

let init () : model =
  let m = Leaf in
  let m = model_set m FKSpace      (FVSpace Personal) in
  let m = model_set m FKOwner      (FVUser initial_owner) in
  let m = model_set m FKMembers    (FVMembers [initial_owner]) in
  let m = model_set m FKLists      (FVIdList []) in
  let m = model_set m FKNextListId (FVNat 0) in
  let m = model_set m FKNextTaskId (FVNat 0) in
  let m = model_set m FKNextTagId  (FVNat 0) in
  m

// ============================================================================
// Actions
// ============================================================================

type action =
  | AddList   : name:string -> action
  | AddTask   : lid:list_id -> data:string -> action
  | AddTag    : name:string -> action
  | AddMember : uid:user_id -> action
  | Sync
  | Flush

// ============================================================================
// next: core state transition
// ============================================================================

let next (m:model) (a:action) : model =
  match a with
  | Sync  -> m
  | Flush -> m

  | AddList name ->
      let lid  = get_nat m FKNextListId in
      let lids = get_id_list m FKLists in
      let m = model_set m (FKListName lid) (FVString name) in
      let m = model_set m FKLists          (FVIdList (lids @ [lid])) in
      let m = model_set m FKNextListId     (FVNat (lid + 1)) in
      m

  | AddTask lid data ->
      let tid = get_nat m FKNextTaskId in
      let m = model_set m (FKTask tid)     (FVNat lid) in
      let m = model_set m (FKTaskData tid) (FVString data) in
      let m = model_set m FKNextTaskId     (FVNat (tid + 1)) in
      m

  | AddTag name ->
      let gid = get_nat m FKNextTagId in
      let m = model_set m (FKTag gid)  (FVString name) in
      let m = model_set m FKNextTagId  (FVNat (gid + 1)) in
      m

  | AddMember uid ->
      let ms = get_members m in
      model_set m FKMembers (FVMembers (ms @ [uid]))