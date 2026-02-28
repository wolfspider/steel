open Prims
type model = Model.model
type action = Model.action
type err = unit
type ('t, 'e) result =
  | Ok of 't 
  | Err of 'e 
let uu___is_Ok (projectee : ('t, 'e) result) : Prims.bool=
  match projectee with | Ok value -> true | uu___ -> false
let __proj__Ok__item__value (projectee : ('t, 'e) result) : 't=
  match projectee with | Ok value -> value
let uu___is_Err (projectee : ('t, 'e) result) : Prims.bool=
  match projectee with | Err error -> true | uu___ -> false
let __proj__Err__item__error (projectee : ('t, 'e) result) : 'e=
  match projectee with | Err error -> error

type 'uuuuu inv = unit
let init (uu___ : unit) : model= Model.init ()
let try_step (m : model) (a : action) : (model, unit) result=
  match a with
  | Model.Sync -> Ok m
  | Model.Flush -> Ok m
  | uu___ -> Ok (Model.next m a)
let rebase (_remote : action) (local : action) : action= local
let rebase_through_suffix (suffix : action Prims.list) (a : action) : 
  action=
  FStar_List_Tot_Base.fold_left (fun acc remote -> rebase remote acc) a
    (FStar_List_Tot_Base.rev suffix)
let candidates (_m : model) (orig : action) : action Prims.list= [orig]
type ('uuuuu, 'uuuuu1) explains = unit
type model_ref =
  (Model.field_key, Model.field_value) Trees.node_data Selectors_Tree_Core.t
let model_eqb (ptr1 : model_ref) (ptr2 : model_ref) : Prims.bool=
  failwith "Not yet implemented: Domain.model_eqb"
