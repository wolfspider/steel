open Prims
type model = Model.model
type 'a option =
  | None 
  | Some of 'a 
let uu___is_None (projectee : 'a option) : Prims.bool=
  match projectee with | None -> true | uu___ -> false
let uu___is_Some (projectee : 'a option) : Prims.bool=
  match projectee with | Some v -> true | uu___ -> false
let __proj__Some__item__v (projectee : 'a option) : 'a=
  match projectee with | Some v -> v
type client_mode =
  | Normal 
  | Flushing 
  | Offline 
let uu___is_Normal (projectee : client_mode) : Prims.bool=
  match projectee with | Normal -> true | uu___ -> false
let uu___is_Flushing (projectee : client_mode) : Prims.bool=
  match projectee with | Flushing -> true | uu___ -> false
let uu___is_Offline (projectee : client_mode) : Prims.bool=
  match projectee with | Offline -> true | uu___ -> false
type client_state =
  {
  base: MultiCollaboration.client_state ;
  mode: client_mode }
let __proj__Mkclient_state__item__base (projectee : client_state) :
  MultiCollaboration.client_state=
  match projectee with | { base; mode;_} -> base
let __proj__Mkclient_state__item__mode (projectee : client_state) :
  client_mode= match projectee with | { base; mode;_} -> mode
let base_version (c : client_state) : Prims.nat=
  MultiCollaboration.client_version c.base
let present (c : client_state) : model=
  MultiCollaboration.client_model c.base
let pending (c : client_state) : Domain.action Prims.list=
  (c.base).MultiCollaboration.pending
let init_client (v : Prims.nat) (m : model) : client_state=
  { base = (MultiCollaboration.init_client v m); mode = Normal }
let sync (server : MultiCollaboration.server_state) : client_state=
  { base = (MultiCollaboration.sync server); mode = Normal }
let local_dispatch (c : client_state) (a : Domain.action) : client_state=
  let b' = MultiCollaboration.client_local_dispatch c.base a in
  { base = b'; mode = (c.mode) }
let handle_realtime_update (c : client_state) (serverVersion : Prims.nat)
  (serverModel : model) : client_state=
  match c.mode with
  | Flushing -> c
  | Offline -> c
  | Normal ->
      let b' =
        MultiCollaboration.handle_realtime_update c.base serverVersion
          serverModel in
      { base = b'; mode = Normal }
  | uu___ -> c
let enter_flush_mode (c : client_state) : client_state=
  { base = (c.base); mode = Flushing }
let exit_flush_mode (c : client_state)
  (server : MultiCollaboration.server_state) : client_state= sync server
type flush_one_result =
  {
  server: MultiCollaboration.server_state ;
  client: client_state ;
  reply: MultiCollaboration.reply }
let __proj__Mkflush_one_result__item__server (projectee : flush_one_result) :
  MultiCollaboration.server_state=
  match projectee with | { server; client; reply;_} -> server
let __proj__Mkflush_one_result__item__client (projectee : flush_one_result) :
  client_state= match projectee with | { server; client; reply;_} -> client
let __proj__Mkflush_one_result__item__reply (projectee : flush_one_result) :
  MultiCollaboration.reply=
  match projectee with | { server; client; reply;_} -> reply
let flush_one (server : MultiCollaboration.server_state)
  (client : client_state) : flush_one_result option=
  match pending client with
  | [] -> None
  | action::rest ->
      let uu___ =
        MultiCollaboration.dispatch server (base_version client) action in
      (match uu___ with
       | (newServer, rep) ->
           (match rep with
            | MultiCollaboration.Accepted
                (newVersion, newPresent, applied, noChange) ->
                let newBase =
                  {
                    MultiCollaboration.baseVersion1 = newVersion;
                    MultiCollaboration.present1 = newPresent;
                    MultiCollaboration.pending = rest
                  } in
                let newClient = { base = newBase; mode = (client.mode) } in
                Some { server = newServer; client = newClient; reply = rep }
            | MultiCollaboration.Rejected (reason, rebased) ->
                let newBase =
                  {
                    MultiCollaboration.baseVersion1 =
                      (MultiCollaboration.version server);
                    MultiCollaboration.present1 =
                      (server.MultiCollaboration.present);
                    MultiCollaboration.pending = rest
                  } in
                let newClient = { base = newBase; mode = (client.mode) } in
                Some { server = newServer; client = newClient; reply = rep }
            | uu___1 -> None))
type flush_all_result =
  {
  server1: MultiCollaboration.server_state ;
  client1: client_state ;
  replies: MultiCollaboration.reply Prims.list }
let __proj__Mkflush_all_result__item__server (projectee : flush_all_result) :
  MultiCollaboration.server_state=
  match projectee with
  | { server1 = server; client1 = client; replies;_} -> server
let __proj__Mkflush_all_result__item__client (projectee : flush_all_result) :
  client_state=
  match projectee with
  | { server1 = server; client1 = client; replies;_} -> client
let __proj__Mkflush_all_result__item__replies (projectee : flush_all_result)
  : MultiCollaboration.reply Prims.list=
  match projectee with
  | { server1 = server; client1 = client; replies;_} -> replies
let rec flush_all (server : MultiCollaboration.server_state)
  (client : client_state) : flush_all_result=
  match pending client with
  | [] -> { server1 = server; client1 = client; replies = [] }
  | uu___::uu___1 ->
      (match flush_one server client with
       | None -> { server1 = server; client1 = client; replies = [] }
       | Some r ->
           if
             (base_version r.client) <= (MultiCollaboration.version r.server)
           then
             let rest = flush_all r.server r.client in
             {
               server1 = (rest.server1);
               client1 = (rest.client1);
               replies = ((r.reply) :: (rest.replies))
             }
           else
             {
               server1 = (r.server);
               client1 = (r.client);
               replies = [r.reply]
             }
       | uu___2 -> { server1 = server; client1 = client; replies = [] })
type flush_cycle_result =
  {
  server2: MultiCollaboration.server_state ;
  client2: client_state ;
  replies1: MultiCollaboration.reply Prims.list }
let __proj__Mkflush_cycle_result__item__server
  (projectee : flush_cycle_result) : MultiCollaboration.server_state=
  match projectee with
  | { server2 = server; client2 = client; replies1 = replies;_} -> server
let __proj__Mkflush_cycle_result__item__client
  (projectee : flush_cycle_result) : client_state=
  match projectee with
  | { server2 = server; client2 = client; replies1 = replies;_} -> client
let __proj__Mkflush_cycle_result__item__replies
  (projectee : flush_cycle_result) : MultiCollaboration.reply Prims.list=
  match projectee with
  | { server2 = server; client2 = client; replies1 = replies;_} -> replies
let flush_cycle (server : MultiCollaboration.server_state)
  (client : client_state) : flush_cycle_result=
  let flushingClient = enter_flush_mode client in
  let all = flush_all server flushingClient in
  let finalClient = exit_flush_mode all.client1 all.server1 in
  { server2 = (all.server1); client2 = finalClient; replies1 = (all.replies)
  }
type realtime_event = {
  version: Prims.nat ;
  model: model }
let __proj__Mkrealtime_event__item__version (projectee : realtime_event) :
  Prims.nat= match projectee with | { version; model = model1;_} -> version
let __proj__Mkrealtime_event__item__model (projectee : realtime_event) :
  model= match projectee with | { version; model = model1;_} -> model1
let rec process_realtime_events (client : client_state)
  (events : realtime_event Prims.list) : client_state=
  match events with
  | [] -> client
  | e::tl ->
      let client' = handle_realtime_update client e.version e.model in
      process_realtime_events client' tl
let flush_with_realtime_events (server : MultiCollaboration.server_state)
  (client : client_state) (events : realtime_event Prims.list) :
  flush_cycle_result=
  let flushingClient = enter_flush_mode client in
  let afterEvents = process_realtime_events flushingClient events in
  let all = flush_all server flushingClient in
  let finalClient = exit_flush_mode all.client1 all.server1 in
  { server2 = (all.server1); client2 = finalClient; replies1 = (all.replies)
  }
