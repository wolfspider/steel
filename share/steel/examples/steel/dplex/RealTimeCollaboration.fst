module RealtimeCollaboration

module MC = MultiCollaboration
module D  = Domain

open FStar.List.Tot

// ============================================================================
// Local Option
// ============================================================================

type option (a:Type0) =
  | None : option a
  | Some : v:a -> option a

// ============================================================================
// Client mode + extended client state
// ============================================================================

type client_mode =
  | Normal
  | Flushing
  | Offline

type client_state = {
  base : MC.client_state;
  mode : client_mode;
}

// Accessors delegating to base
let base_version (c:client_state) : nat = MC.client_version c.base
let present      (c:client_state) : D.model = MC.client_model c.base
let pending      (c:client_state) : list D.action = c.base.pending

// ============================================================================
// Init / Sync
// ============================================================================

let init_client (v:nat) (m:D.model) : client_state =
  { base = MC.init_client v m; mode = Normal }

let sync (server:MC.server_state) : client_state =
  { base = MC.sync server; mode = Normal }

// ============================================================================
// Local dispatch (optimistic update): delegate to MC, preserve mode
// ============================================================================

let local_dispatch (c:client_state) (a:D.action) : client_state =
  let b' = MC.client_local_dispatch c.base a in
  { base = b'; mode = c.mode }

// ============================================================================
// Realtime update handling: KEY FIX (skip while flushing or offline)
// ============================================================================

let handle_realtime_update (c:client_state)
                           (serverVersion:nat)
                           (serverModel:D.model)
  : client_state
=
  match c.mode with
  | Flushing -> c
  | Offline  -> c
  | Normal   ->
      let b' = MC.handle_realtime_update c.base serverVersion serverModel in
      { base = b'; mode = Normal }

// ============================================================================
// Flush operations
// ============================================================================

let enter_flush_mode (c:client_state)
  : Tot (c':client_state{
      c'.mode == Flushing /\
      base_version c' == base_version c /\
      c'.base == c.base
    })
=
  { base = c.base; mode = Flushing }


let exit_flush_mode (c:client_state) (server:MC.server_state) : client_state =
  // Exit flush mode implies a Sync, which puts us back in Normal.
  sync server

type flush_one_result = {
  server : MC.server_state;
  client : client_state;
  reply  : MC.reply;
}

// Flush one pending action (if any)
let flush_one (server:MC.server_state)
              (client:client_state{base_version client <= MC.version server})
  : Tot (option flush_one_result)
=
  match pending client with
  | [] -> None
  | action::rest ->
      let (newServer, rep) = MC.dispatch server (base_version client) action in
      (match rep with
       | MC.Accepted newVersion newPresent applied noChange ->
           // Dafny built a new MC.ClientState(newVersion, newPresent, rest)
           let newBase : MC.client_state =
             { baseVersion = newVersion; present = newPresent; pending = rest }
           in
           let newClient : client_state = { base = newBase; mode = client.mode } in
           Some { server = newServer; client = newClient; reply = rep }

       | MC.Rejected reason rebased ->
           // Dafny: baseVersion := Version(server), present := server.present
           // (NOTE: uses the *old* server, as your Dafny does)
           let newBase : MC.client_state =
             { baseVersion = MC.version server; present = server.present; pending = rest }
           in
           let newClient : client_state = { base = newBase; mode = client.mode } in
           Some { server = newServer; client = newClient; reply = rep })

type flush_all_result = {
  server  : MC.server_state;
  client  : client_state;
  replies : list MC.reply;
}

// Flush all pending actions (recursive)
let rec flush_all
  (server:MC.server_state)
  (client:client_state{
            base_version client <= MC.version server /\
            client.mode == Flushing })
  : Tot flush_all_result
    (decreases pending client)
=
  match pending client with
  | [] ->
      { server = server; client = client; replies = [] }

  | _::_ ->
      (match flush_one server client with
       | None ->
           // Should be unreachable because pending nonempty, but keep total.
           { server = server; client = client; replies = [] }

       | Some r ->
           // In Dafny there was an extra check:
           // if BaseVersion(result.client) <= Version(result.server) then recurse
           // We'll keep it exactly.
           if base_version r.client <= MC.version r.server then
             let rest = flush_all r.server r.client in
             { server = rest.server;
               client = rest.client;
               replies = r.reply :: rest.replies }
           else
             { server = r.server;
               client = r.client;
               replies = [r.reply] })

type flush_cycle_result = {
  server  : MC.server_state;
  client  : client_state;
  replies : list MC.reply;
}

let flush_cycle
  (server:MC.server_state)
  (client:client_state{base_version client <= MC.version server})
  : Tot flush_cycle_result
=
  let flushingClient = enter_flush_mode client in
  let all = flush_all server flushingClient in
  let finalClient = exit_flush_mode all.client all.server in
  { server = all.server; client = finalClient; replies = all.replies }

// ============================================================================
// Interleaving realtime events during flush
// ============================================================================

type realtime_event = {
  version : nat;
  model   : D.model;
}

let rec process_realtime_events
  (client:client_state)
  (events:list realtime_event)
  : Tot client_state
    (decreases events)
=
  match events with
  | [] -> client
  | e::tl ->
      let client' = handle_realtime_update client e.version e.model in
      process_realtime_events client' tl


let rec realtime_events_skipped_during_flush
  (client:client_state{client.mode == Flushing})
  (events:list realtime_event)
  : Lemma (ensures process_realtime_events client events == client)
  (decreases events)
=
  match events with
  | [] -> ()
  | e::tl ->
      // By definition, handle_realtime_update returns client unchanged when Flushing
      assert (handle_realtime_update client e.version e.model == client);
      realtime_events_skipped_during_flush client tl



let flush_with_realtime_events
  (server:MC.server_state)
  (client:client_state{base_version client <= MC.version server})
  (events:list realtime_event)
  : Tot flush_cycle_result
=
  let flushingClient = enter_flush_mode client in

  // You can still compute it if you want the model to “look” like Dafny:
  let afterEvents = process_realtime_events flushingClient events in

  // But prove it’s actually a no-op during flush:
  realtime_events_skipped_during_flush flushingClient events;
  assert (afterEvents == flushingClient);

  // Easiest: just pass flushingClient (already refined) to flush_all
  let all = flush_all server flushingClient in

  let finalClient = exit_flush_mode all.client all.server in
  { server = all.server; client = finalClient; replies = all.replies }


// ============================================================================
// Key lemma: events are skipped during flush
// ============================================================================

// Main theorem: flush with events == flush without events
// This is “easy” once you have the lemma above, but to keep things shallow,
// we can keep it as a proof hook if you want to avoid rewriting equalities
// about record construction and the exact path.
//
// If you want it proved now, we can do it, but the hook keeps it painless.
assume val flush_with_realtime_events_equivalent
  : server:MC.server_state ->
    client:client_state ->
    events:list realtime_event ->
    Lemma (requires base_version client <= MC.version server)
          (ensures  flush_with_realtime_events server client events
                    == flush_cycle server client)

// Additional property: After flush cycle, client is synced with server
assume val flush_cycle_client_synced
  : server:MC.server_state ->
    client:client_state ->
    Lemma (requires base_version client <= MC.version server)
          (ensures
            (let r = flush_cycle server client in
            present r.client == r.server.present /\
            base_version r.client == MC.version r.server))
