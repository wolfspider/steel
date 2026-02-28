open Prims
type 't model = 't
type action =
  | Step 
  | Sync 
  | Flush 
let uu___is_Step (projectee : action) : Prims.bool=
  match projectee with | Step -> true | uu___ -> false
let uu___is_Sync (projectee : action) : Prims.bool=
  match projectee with | Sync -> true | uu___ -> false
let uu___is_Flush (projectee : action) : Prims.bool=
  match projectee with | Flush -> true | uu___ -> false
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

type ('t, 'uuuuu) inv = unit
let init (zero : 't) : 't model= zero
let try_step (next : 't -> 't) (m : 't model) (a : action) :
  ('t model, unit) result=
  match a with | Step -> Ok (next m) | Sync -> Ok m | Flush -> Ok m
let rebase (_remote : action) (local : action) : action= local
let rebase_through_suffix (suffix : action Prims.list) (a : action) : 
  action=
  FStar_List_Tot_Base.fold_left (fun acc remote -> rebase remote acc) a
    (FStar_List_Tot_Base.rev suffix)
let candidates (_m : 't model) (orig : action) : action Prims.list= [orig]
type ('uuuuu, 'uuuuu1) explains = unit
let model_eqb (eqb : 't -> 't -> Prims.bool) (x : 't model) (y : 't model) :
  Prims.bool= eqb x y
