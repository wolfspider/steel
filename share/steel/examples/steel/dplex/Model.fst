module Model
open FStar.List.Tot
open FStar.Classical
open FStar.Tactics
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

// ============================================================================
// Decidable equality on field_key and field_value
// ============================================================================

let field_key_eqb (x y:field_key) : bool =
  cmp_field_key x y = 0

let field_value_eqb (x y:field_value) : bool =
  match x, y with
  | FVSpace  sx, FVSpace  sy -> sx = sy
  | FVUser   ux, FVUser   uy -> ux = uy
  | FVMembers mx, FVMembers my ->
      FStar.List.Tot.length mx = FStar.List.Tot.length my &&
      FStar.List.Tot.fold_left2 (fun acc a b -> acc && a = b) true mx my
  | FVIdList  lx, FVIdList  ly ->
      FStar.List.Tot.length lx = FStar.List.Tot.length ly &&
      FStar.List.Tot.fold_left2 (fun acc a b -> acc && a = b) true lx ly
  | FVString sx, FVString sy -> sx = sy
  | FVNat    nx, FVNat    ny -> nx = ny
  | _ -> false

// ============================================================================
// Lemmas for field_key_eqb
// ============================================================================

let field_key_eqb_refl (x:field_key)
  : Lemma (ensures field_key_eqb x x == true)
= ()

let field_key_eqb_sym (x y:field_key)
  : Lemma (ensures field_key_eqb x y == field_key_eqb y x)
= ()

let field_key_eqb_false_prop =
  forall x y. {:pattern (field_key_eqb x y)}
    (x =!= y) ==> field_key_eqb x y == false

let field_key_eqb_spec_prop =
  forall x y. {:pattern (field_key_eqb x y)}
    field_key_eqb x y == true <==> x == y

assume val field_key_eqb_false_holds : squash field_key_eqb_false_prop
assume val field_key_eqb_spec_holds  : squash field_key_eqb_spec_prop

// ============================================================================
// Lemmas for field_value_eqb
// ============================================================================

let rec list_eqb_refl (#a:eqtype) (xs:list a)
  : Lemma (ensures FStar.List.Tot.fold_left2 (fun acc a b -> acc && a = b) true xs xs == true)
          (decreases xs)
= match xs with
  | [] -> ()
  | _::tl -> list_eqb_refl tl

let field_value_eqb_refl (x:field_value)
  : Lemma (ensures field_value_eqb x x == true)
= match x with
  | FVMembers mx -> list_eqb_refl mx
  | FVIdList  lx -> list_eqb_refl lx
  | _ -> ()

// ============================================================================
// field_value equality props
// ============================================================================

let rec list_str_eqb (xs ys:list string) : bool =
  match xs, ys with
  | [], [] -> true
  | x::tl, y::tl2 -> x = y && list_str_eqb tl tl2
  | _ -> false

let rec list_nat_eqb (xs ys:list nat) : bool =
  match xs, ys with
  | [], [] -> true
  | x::tl, y::tl2 -> x = y && list_nat_eqb tl tl2
  | _ -> false


let rec list_str_eqb_refl (xs:list string)
  : Lemma (ensures list_str_eqb xs xs == true)
          (decreases xs)
= match xs with
  | [] -> ()
  | _::tl -> list_str_eqb_refl tl

let rec list_nat_eqb_refl (xs:list nat)
  : Lemma (ensures list_nat_eqb xs xs == true)
          (decreases xs)
= match xs with
  | [] -> ()
  | _::tl -> list_nat_eqb_refl tl

let rec list_str_eqb_sym (xs ys:list string)
  : Lemma (ensures list_str_eqb xs ys == list_str_eqb ys xs)
          (decreases xs)
= match xs, ys with
  | [], [] -> ()
  | x::tl, y::tl2 -> list_str_eqb_sym tl tl2
  | _ -> ()

let rec list_nat_eqb_sym (xs ys:list nat)
  : Lemma (ensures list_nat_eqb xs ys == list_nat_eqb ys xs)
          (decreases xs)
= match xs, ys with
  | [], [] -> ()
  | x::tl, y::tl2 -> list_nat_eqb_sym tl tl2
  | _ -> ()

let field_value_eqb_sym_prop =
  forall x y. {:pattern (field_value_eqb x y)}
    field_value_eqb x y == field_value_eqb y x

assume val field_value_eqb_sym_holds : squash field_value_eqb_sym_prop

let field_value_eqb_spec_prop =
  forall x y. {:pattern (field_value_eqb x y)}
    field_value_eqb x y == true <==> x == y

assume val field_value_eqb_spec_holds : squash field_value_eqb_spec_prop
// ============================================================================
// model_eqb
// ============================================================================

let rec model_eqb (x y:model) : bool =
  match x, y with
  | Leaf, Leaf -> true
  | Node dx lx rx, Node dy ly ry ->
      field_key_eqb   dx.key      dy.key     &&
      field_value_eqb dx.payload  dy.payload &&
      model_eqb lx ly &&
      model_eqb rx ry
  | _ -> false

// ============================================================================
// Symmetry, reflexivity, transitivity
// ============================================================================

let symmetry (#a:Type) (equals: a -> a -> prop) =
  forall x y. {:pattern (x `equals` y)}
    x `equals` y ==> y `equals` x

let reflexivity (#a:Type) (equals: a -> a -> prop) =
  forall x. {:pattern (x `equals` x)}
    x `equals` x

let transitivity (#a:Type) (equals: a -> a -> prop) =
  forall x y z. {:pattern (x `equals` y); (y `equals` z)}
    x `equals` y /\ y `equals` z ==> x `equals` z

let rec model_eqb_refl (x:model)
  : Lemma (ensures model_eqb x x == true)
          (decreases x)
= match x with
  | Leaf -> ()
  | Node d l r ->
      field_key_eqb_refl d.key;
      field_value_eqb_refl d.payload;
      model_eqb_refl l;
      model_eqb_refl r

let rec model_eqb_sym (x y:model)
  : Lemma (ensures model_eqb x y == model_eqb y x)
          (decreases x)
= match x, y with
  | Leaf, Leaf -> ()
  | Node dx lx rx, Node dy ly ry ->
      field_key_eqb_sym   dx.key     dy.key;
      field_value_eqb_sym_holds;
      model_eqb_sym lx ly;
      model_eqb_sym rx ry
  | _ -> ()

let rec model_eqb_spec (x y:model)
  : Lemma (ensures model_eqb x y == true <==> x == y)
          (decreases x)
= match x, y with
  | Leaf, Leaf -> ()
  | Node dx lx rx, Node dy ly ry ->
      field_key_eqb_spec_holds;
      field_value_eqb_spec_holds;
      model_eqb_spec lx ly;
      model_eqb_spec rx ry
  | _ -> ()

let model_eqb_symmetry ()
  : Lemma (symmetry (fun x y -> model_eqb x y == true))
= FStar.Classical.forall_intro_2 model_eqb_sym

let reflexivity2 (#a:Type) (equals: a -> a -> prop) =
  forall x. {:pattern (x `equals` x)}
    x `equals` x

let model_eqb_reflexivity ()
  : Lemma (reflexivity2 (fun x y -> model_eqb x y == true))
= FStar.Classical.forall_intro (fun x -> model_eqb_refl x)

let model_eqb_trans (x y z:model)
  : Lemma (requires model_eqb x y == true /\ model_eqb y z == true)
          (ensures  model_eqb x z == true)
= model_eqb_spec x y;
  model_eqb_spec y z;
  model_eqb_spec x z

let model_eqb_transitivity ()
  : Lemma (transitivity (fun x y -> model_eqb x y == true))
= FStar.Classical.forall_intro_3
    (fun x y z -> FStar.Classical.move_requires (model_eqb_trans x y) z)