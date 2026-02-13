module EffectStateMachine

module MC = MultiCollaboration
module D  = Domain

open FStar.List.Tot

// ============================================================================
// Effect state
// ============================================================================

type network_status =
  | Online
  | Offline

type effect_mode =
  | Idle
  | Dispatching : retries:nat -> effect_mode

type effect_state = {
  network       : network_status;
  mode          : effect_mode;
  client        : MC.client_state;
  serverVersion : nat;
}

let max_retries : nat = 5

// ============================================================================
// Events (inputs)
// ============================================================================

type event =
  | UserAction       : action:D.action -> event
  | DispatchAccepted : newVersion:nat -> newModel:D.model -> event
  | DispatchConflict : freshVersion:nat -> freshModel:D.model -> event
  | DispatchRejected : freshVersion:nat -> freshModel:D.model -> event
  | NetworkError
  | NetworkRestored
  | ManualGoOffline
  | ManualGoOnline
  | Tick

// ============================================================================
// Commands (outputs / side effects)
// ============================================================================

type command =
  | NoOp
  | SendDispatch   : baseVersion:nat -> action:D.action -> command
  | FetchFreshState

// ============================================================================
// Helpers
// ============================================================================

let pending_count (es:effect_state) : nat =
  MC.pending_count es.client

let has_pending (es:effect_state) : bool =
  pending_count es > 0

let is_online (es:effect_state) : bool =
  match es.network with
  | Online -> true
  | Offline -> false

let is_idle (es:effect_state) : bool =
  match es.mode with
  | Idle -> true
  | Dispatching _ -> false

let can_start_dispatch (es:effect_state) : bool =
  is_online es && is_idle es && has_pending es

let first_pending_action (es:effect_state{has_pending es}) : D.action =
  match es.client.pending with
  | hd::_ -> hd

// ============================================================================
// Main transition
// ============================================================================

let step (es:effect_state) (ev:event) : effect_state * command =
  match ev with

  | UserAction action ->
      let newClient = MC.client_local_dispatch es.client action in
      let es1 = { es with client = newClient } in
      if can_start_dispatch es1 then
        let a0 = first_pending_action es1 in
        ({ es1 with mode = Dispatching 0 },
         SendDispatch (MC.client_version es1.client) a0)
      else
        (es1, NoOp)

  | DispatchAccepted newVersion newModel ->
      (match es.mode with
       | Dispatching _ ->
           let newClient = MC.client_accept_reply es.client newVersion newModel in
           let es1 =
             { network = es.network; mode = Idle; client = newClient; serverVersion = newVersion }
           in
           if can_start_dispatch es1 then
             let a0 = first_pending_action es1 in
             ({ es1 with mode = Dispatching 0 },
              SendDispatch (MC.client_version es1.client) a0)
           else
             (es1, NoOp)
       | Idle ->
           (es, NoOp))

  | DispatchConflict freshVersion freshModel ->
      (match es.mode with
       | Dispatching retries ->
           if retries >= max_retries then
             ({ es with mode = Idle }, NoOp)
           else
             let newClient =
               MC.handle_realtime_update es.client freshVersion freshModel
             in
             let es1 =
               { network = es.network;
                 mode = Dispatching (retries + 1);
                 client = newClient;
                 serverVersion = freshVersion }
             in
             if has_pending es1 then
               let a0 = first_pending_action es1 in
               (es1, SendDispatch freshVersion a0)
             else
               // Dafny calls this "dead code"; keep total by going idle.
               ({ es1 with mode = Idle }, NoOp)
       | Idle ->
           (es, NoOp))

  | DispatchRejected freshVersion freshModel ->
      (match es.mode with
       | Dispatching _ ->
           let newClient =
             MC.client_reject_reply es.client freshVersion freshModel
           in
           let es1 =
             { network = es.network; mode = Idle; client = newClient; serverVersion = freshVersion }
           in
           if can_start_dispatch es1 then
             let a0 = first_pending_action es1 in
             ({ es1 with mode = Dispatching 0 },
              SendDispatch (MC.client_version es1.client) a0)
           else
             (es1, NoOp)
       | Idle ->
           (es, NoOp))

  | NetworkError ->
      ({ network = Offline; mode = Idle; client = es.client; serverVersion = es.serverVersion }, NoOp)

  | NetworkRestored ->
      let es1 = { es with network = Online } in
      if can_start_dispatch es1 then
        let a0 = first_pending_action es1 in
        ({ es1 with mode = Dispatching 0 },
         SendDispatch (MC.client_version es1.client) a0)
      else
        (es1, NoOp)

  | ManualGoOffline ->
      ({ network = Offline; mode = Idle; client = es.client; serverVersion = es.serverVersion }, NoOp)

  | ManualGoOnline ->
      let es1 = { es with network = Online } in
      if can_start_dispatch es1 then
        let a0 = first_pending_action es1 in
        ({ es1 with mode = Dispatching 0 },
         SendDispatch (MC.client_version es1.client) a0)
      else
        (es1, NoOp)

  | Tick ->
      if can_start_dispatch es then
        let a0 = first_pending_action es in
        ({ es with mode = Dispatching 0 },
         SendDispatch (MC.client_version es.client) a0)
      else
        (es, NoOp)

// ============================================================================
// Invariants
// ============================================================================

let mode_consistent (es:effect_state) : prop =
  match es.mode with
  | Idle -> True
  | Dispatching _ -> has_pending es == true

let retries_bounded (es:effect_state) : prop =
  match es.mode with
  | Idle -> True
  | Dispatching r -> r <= max_retries

let inv (es:effect_state) : prop =
  mode_consistent es /\ retries_bounded es

// ============================================================================
// Init
// ============================================================================

let init (version:nat) (model:D.model) : effect_state =
  { network = Online;
    mode = Idle;
    client = MC.init_client version model;
    serverVersion = version }

// ============================================================================
// Proof hooks (keep as assumptions for now, like MultiCollaboration)
// ============================================================================

assume val init_satisfies_inv : v:nat -> m:D.model ->
  Lemma (ensures inv (init v m))

assume val step_preserves_inv : es:effect_state -> ev:event ->
  Lemma (requires inv es)
        (ensures  inv (fst (step es ev)))
