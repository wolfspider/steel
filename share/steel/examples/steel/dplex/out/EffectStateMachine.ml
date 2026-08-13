open Prims
type model = Model.model
type network_status =
  | Online 
  | Offline 
let uu___is_Online (projectee : network_status) : Prims.bool=
  match projectee with | Online -> true | uu___ -> false
let uu___is_Offline (projectee : network_status) : Prims.bool=
  match projectee with | Offline -> true | uu___ -> false
type effect_mode =
  | Idle 
  | Dispatching of Prims.nat 
let uu___is_Idle (projectee : effect_mode) : Prims.bool=
  match projectee with | Idle -> true | uu___ -> false
let uu___is_Dispatching (projectee : effect_mode) : Prims.bool=
  match projectee with | Dispatching retries -> true | uu___ -> false
let __proj__Dispatching__item__retries (projectee : effect_mode) : Prims.nat=
  match projectee with | Dispatching retries -> retries
type effect_state =
  {
  network: network_status ;
  mode: effect_mode ;
  client: MultiCollaboration.client_state ;
  serverVersion: Prims.nat }
let __proj__Mkeffect_state__item__network (projectee : effect_state) :
  network_status=
  match projectee with | { network; mode; client; serverVersion;_} -> network
let __proj__Mkeffect_state__item__mode (projectee : effect_state) :
  effect_mode=
  match projectee with | { network; mode; client; serverVersion;_} -> mode
let __proj__Mkeffect_state__item__client (projectee : effect_state) :
  MultiCollaboration.client_state=
  match projectee with | { network; mode; client; serverVersion;_} -> client
let __proj__Mkeffect_state__item__serverVersion (projectee : effect_state) :
  Prims.nat=
  match projectee with
  | { network; mode; client; serverVersion;_} -> serverVersion
let max_retries : Prims.nat= (Prims.of_int (5))
type event =
  | UserAction of Domain.action 
  | DispatchAccepted of Prims.nat * model 
  | DispatchConflict of Prims.nat * model 
  | DispatchRejected of Prims.nat * model 
  | NetworkError 
  | NetworkRestored 
  | ManualGoOffline 
  | ManualGoOnline 
  | Tick 
let uu___is_UserAction (projectee : event) : Prims.bool=
  match projectee with | UserAction action -> true | uu___ -> false
let __proj__UserAction__item__action (projectee : event) : Domain.action=
  match projectee with | UserAction action -> action
let uu___is_DispatchAccepted (projectee : event) : Prims.bool=
  match projectee with
  | DispatchAccepted (newVersion, newModel) -> true
  | uu___ -> false
let __proj__DispatchAccepted__item__newVersion (projectee : event) :
  Prims.nat=
  match projectee with
  | DispatchAccepted (newVersion, newModel) -> newVersion
let __proj__DispatchAccepted__item__newModel (projectee : event) : model=
  match projectee with | DispatchAccepted (newVersion, newModel) -> newModel
let uu___is_DispatchConflict (projectee : event) : Prims.bool=
  match projectee with
  | DispatchConflict (freshVersion, freshModel) -> true
  | uu___ -> false
let __proj__DispatchConflict__item__freshVersion (projectee : event) :
  Prims.nat=
  match projectee with
  | DispatchConflict (freshVersion, freshModel) -> freshVersion
let __proj__DispatchConflict__item__freshModel (projectee : event) : 
  model=
  match projectee with
  | DispatchConflict (freshVersion, freshModel) -> freshModel
let uu___is_DispatchRejected (projectee : event) : Prims.bool=
  match projectee with
  | DispatchRejected (freshVersion, freshModel) -> true
  | uu___ -> false
let __proj__DispatchRejected__item__freshVersion (projectee : event) :
  Prims.nat=
  match projectee with
  | DispatchRejected (freshVersion, freshModel) -> freshVersion
let __proj__DispatchRejected__item__freshModel (projectee : event) : 
  model=
  match projectee with
  | DispatchRejected (freshVersion, freshModel) -> freshModel
let uu___is_NetworkError (projectee : event) : Prims.bool=
  match projectee with | NetworkError -> true | uu___ -> false
let uu___is_NetworkRestored (projectee : event) : Prims.bool=
  match projectee with | NetworkRestored -> true | uu___ -> false
let uu___is_ManualGoOffline (projectee : event) : Prims.bool=
  match projectee with | ManualGoOffline -> true | uu___ -> false
let uu___is_ManualGoOnline (projectee : event) : Prims.bool=
  match projectee with | ManualGoOnline -> true | uu___ -> false
let uu___is_Tick (projectee : event) : Prims.bool=
  match projectee with | Tick -> true | uu___ -> false
type command =
  | NoOp 
  | SendDispatch of Prims.nat * Domain.action 
  | FetchFreshState 
let uu___is_NoOp (projectee : command) : Prims.bool=
  match projectee with | NoOp -> true | uu___ -> false
let uu___is_SendDispatch (projectee : command) : Prims.bool=
  match projectee with
  | SendDispatch (baseVersion, action) -> true
  | uu___ -> false
let __proj__SendDispatch__item__baseVersion (projectee : command) :
  Prims.nat=
  match projectee with | SendDispatch (baseVersion, action) -> baseVersion
let __proj__SendDispatch__item__action (projectee : command) : Domain.action=
  match projectee with | SendDispatch (baseVersion, action) -> action
let uu___is_FetchFreshState (projectee : command) : Prims.bool=
  match projectee with | FetchFreshState -> true | uu___ -> false
let pending_count (es : effect_state) : Prims.nat=
  MultiCollaboration.pending_count es.client
let has_pending (es : effect_state) : Prims.bool=
  (pending_count es) > Prims.int_zero
let is_online (es : effect_state) : Prims.bool=
  match es.network with | Online -> true | Offline -> false | uu___ -> false
let is_idle (es : effect_state) : Prims.bool=
  match es.mode with
  | Idle -> true
  | Dispatching uu___ -> false
  | uu___ -> false
let can_start_dispatch (es : effect_state) : Prims.bool=
  ((is_online es) && (is_idle es)) && (has_pending es)
let first_pending_action (es : effect_state) :
  Domain.action FStar_Pervasives_Native.option=
  let pending = (es.client).MultiCollaboration.pending in
  match pending with
  | hd::uu___ -> FStar_Pervasives_Native.Some hd
  | [] -> FStar_Pervasives_Native.None
  | uu___ -> FStar_Pervasives_Native.None
let step (es : effect_state) (ev : event) : (effect_state * command)=
  match ev with
  | UserAction action ->
      let newClient =
        MultiCollaboration.client_local_dispatch es.client action in
      let es1 =
        {
          network = (es.network);
          mode = (es.mode);
          client = newClient;
          serverVersion = (es.serverVersion)
        } in
      if can_start_dispatch es1
      then
        (match first_pending_action es1 with
         | FStar_Pervasives_Native.Some a0 ->
             ({
                network = (es1.network);
                mode = (Dispatching Prims.int_zero);
                client = (es1.client);
                serverVersion = (es1.serverVersion)
              },
               (SendDispatch
                  ((MultiCollaboration.client_version es1.client), a0)))
         | FStar_Pervasives_Native.None -> (es1, NoOp)
         | uu___ -> (es1, NoOp))
      else (es1, NoOp)
  | DispatchAccepted (newVersion, newModel) ->
      (match es.mode with
       | Dispatching uu___ ->
           let newClient =
             MultiCollaboration.client_accept_reply es.client newVersion
               newModel in
           let es1 =
             {
               network = (es.network);
               mode = Idle;
               client = newClient;
               serverVersion = newVersion
             } in
           if can_start_dispatch es1
           then
             (match first_pending_action es1 with
              | FStar_Pervasives_Native.Some a0 ->
                  ({
                     network = (es1.network);
                     mode = (Dispatching Prims.int_zero);
                     client = (es1.client);
                     serverVersion = (es1.serverVersion)
                   },
                    (SendDispatch
                       ((MultiCollaboration.client_version es1.client), a0)))
              | FStar_Pervasives_Native.None -> (es1, NoOp)
              | uu___1 -> (es1, NoOp))
           else (es1, NoOp)
       | Idle -> (es, NoOp)
       | uu___ -> (es, NoOp))
  | DispatchConflict (freshVersion, freshModel) ->
      (match es.mode with
       | Dispatching retries ->
           if retries >= max_retries
           then
             ({
                network = (es.network);
                mode = Idle;
                client = (es.client);
                serverVersion = (es.serverVersion)
              }, NoOp)
           else
             (let newClient =
                MultiCollaboration.handle_realtime_update es.client
                  freshVersion freshModel in
              let es1 =
                {
                  network = (es.network);
                  mode = (Dispatching (retries + Prims.int_one));
                  client = newClient;
                  serverVersion = freshVersion
                } in
              if has_pending es1
              then
                match first_pending_action es1 with
                | FStar_Pervasives_Native.Some a0 ->
                    (es1, (SendDispatch (freshVersion, a0)))
                | FStar_Pervasives_Native.None ->
                    ({
                       network = (es1.network);
                       mode = Idle;
                       client = (es1.client);
                       serverVersion = (es1.serverVersion)
                     }, NoOp)
                | uu___1 ->
                    ({
                       network = (es1.network);
                       mode = Idle;
                       client = (es1.client);
                       serverVersion = (es1.serverVersion)
                     }, NoOp)
              else
                ({
                   network = (es1.network);
                   mode = Idle;
                   client = (es1.client);
                   serverVersion = (es1.serverVersion)
                 }, NoOp))
       | Idle -> (es, NoOp)
       | uu___ -> (es, NoOp))
  | DispatchRejected (freshVersion, freshModel) ->
      (match es.mode with
       | Dispatching uu___ ->
           let newClient =
             MultiCollaboration.client_reject_reply es.client freshVersion
               freshModel in
           let es1 =
             {
               network = (es.network);
               mode = Idle;
               client = newClient;
               serverVersion = freshVersion
             } in
           if can_start_dispatch es1
           then
             (match first_pending_action es1 with
              | FStar_Pervasives_Native.Some a0 ->
                  ({
                     network = (es1.network);
                     mode = (Dispatching Prims.int_zero);
                     client = (es1.client);
                     serverVersion = (es1.serverVersion)
                   },
                    (SendDispatch
                       ((MultiCollaboration.client_version es1.client), a0)))
              | FStar_Pervasives_Native.None -> (es1, NoOp)
              | uu___1 -> (es1, NoOp))
           else (es1, NoOp)
       | Idle -> (es, NoOp)
       | uu___ -> (es, NoOp))
  | NetworkError ->
      ({
         network = Offline;
         mode = Idle;
         client = (es.client);
         serverVersion = (es.serverVersion)
       }, NoOp)
  | NetworkRestored ->
      let es1 =
        {
          network = Online;
          mode = (es.mode);
          client = (es.client);
          serverVersion = (es.serverVersion)
        } in
      if can_start_dispatch es1
      then
        (match first_pending_action es1 with
         | FStar_Pervasives_Native.Some a0 ->
             ({
                network = (es1.network);
                mode = (Dispatching Prims.int_zero);
                client = (es1.client);
                serverVersion = (es1.serverVersion)
              },
               (SendDispatch
                  ((MultiCollaboration.client_version es1.client), a0)))
         | FStar_Pervasives_Native.None -> (es1, NoOp)
         | uu___ -> (es1, NoOp))
      else (es1, NoOp)
  | ManualGoOffline ->
      ({
         network = Offline;
         mode = Idle;
         client = (es.client);
         serverVersion = (es.serverVersion)
       }, NoOp)
  | ManualGoOnline ->
      let es1 =
        {
          network = Online;
          mode = (es.mode);
          client = (es.client);
          serverVersion = (es.serverVersion)
        } in
      if can_start_dispatch es1
      then
        (match first_pending_action es1 with
         | FStar_Pervasives_Native.Some a0 ->
             ({
                network = (es1.network);
                mode = (Dispatching Prims.int_zero);
                client = (es1.client);
                serverVersion = (es1.serverVersion)
              },
               (SendDispatch
                  ((MultiCollaboration.client_version es1.client), a0)))
         | FStar_Pervasives_Native.None -> (es1, NoOp)
         | uu___ -> (es1, NoOp))
      else (es1, NoOp)
  | Tick ->
      if can_start_dispatch es
      then
        (match first_pending_action es with
         | FStar_Pervasives_Native.Some a0 ->
             ({
                network = (es.network);
                mode = (Dispatching Prims.int_zero);
                client = (es.client);
                serverVersion = (es.serverVersion)
              },
               (SendDispatch
                  ((MultiCollaboration.client_version es.client), a0)))
         | FStar_Pervasives_Native.None -> (es, NoOp)
         | uu___ -> (es, NoOp))
      else (es, NoOp)
  | uu___ -> Prims.admit ()
type 'es mode_consistent = Obj.t
type 'es retries_bounded = Obj.t
type 'es inv = unit
let init (version : Prims.nat) (m : model) : effect_state=
  {
    network = Online;
    mode = Idle;
    client = (MultiCollaboration.init_client version m);
    serverVersion = version
  }
