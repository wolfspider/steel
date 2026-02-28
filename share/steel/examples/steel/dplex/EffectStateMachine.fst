module EffectStateMachine

module MC = MultiCollaboration
module D  = Domain
module M  = Model

open FStar.List.Tot

type model = M.model

// ============================================================================
// Effect state
// ============================================================================

type network_status =
  | Online
  | Offline

type effect_mode =
  | Idle
  | Dispatching : retries:nat -> effect_mode

noeq type effect_state = {
  network       : network_status;
  mode          : effect_mode;
  client        : MC.client_state;
  serverVersion : nat;
}

let max_retries : nat = 5

// ============================================================================
// Events (inputs)
// ============================================================================

noeq type event =
  | UserAction       : action:D.action -> event
  | DispatchAccepted : newVersion:nat -> newModel:model -> event
  | DispatchConflict : freshVersion:nat -> freshModel:model -> event
  | DispatchRejected : freshVersion:nat -> freshModel:model -> event
  | NetworkError
  | NetworkRestored
  | ManualGoOffline
  | ManualGoOnline
  | Tick

// ============================================================================
// Commands (outputs / side effects)
// ============================================================================

noeq type command =
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
  | _ -> false

let is_idle (es:effect_state) : bool =
  match es.mode with
  | Idle -> true
  | Dispatching _ -> false
  | _ -> false

let can_start_dispatch (es:effect_state) : bool =
  is_online es && is_idle es && has_pending es

let first_pending_action (es:effect_state) : option D.action =
  let pending = es.client.pending in
  match pending with
  | hd::_ -> Some hd
  | [] -> None
  | _ -> None

// ============================================================================
// Main transition
// ============================================================================



let step (es:effect_state) (ev:event) : effect_state * command =
  match ev with
  | UserAction action ->
      let newClient = MC.client_local_dispatch es.client action in
      let es1 = { es with client = newClient } in
      if can_start_dispatch es1 then
        match first_pending_action es1 with
        | Some a0 ->
            ({ es1 with mode = Dispatching 0 },
             SendDispatch (MC.client_version es1.client) a0)
        | None -> (es1, NoOp)
        | _ -> (es1, NoOp)
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
             match first_pending_action es1 with
             | Some a0 ->
                 ({ es1 with mode = Dispatching 0 },
                  SendDispatch (MC.client_version es1.client) a0)
             | None -> (es1, NoOp)
             | _ -> (es1, NoOp)
           else
             (es1, NoOp)
       | Idle -> (es, NoOp)
       | _ -> (es, NoOp))

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
               match first_pending_action es1 with
               | Some a0 -> (es1, SendDispatch freshVersion a0)
               | None -> ({ es1 with mode = Idle }, NoOp)
               | _ -> ({ es1 with mode = Idle }, NoOp)
             else
               ({ es1 with mode = Idle }, NoOp)
       | Idle -> (es, NoOp)
       | _ -> (es, NoOp))

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
             match first_pending_action es1 with
             | Some a0 ->
                 ({ es1 with mode = Dispatching 0 },
                  SendDispatch (MC.client_version es1.client) a0)
             | None -> (es1, NoOp)
             | _ -> (es1, NoOp)
           else
             (es1, NoOp)
       | Idle -> (es, NoOp)
       | _ -> (es, NoOp))

  | NetworkError ->
      ({ network = Offline; mode = Idle; client = es.client; serverVersion = es.serverVersion }, NoOp)

  | NetworkRestored ->
      let es1 = { es with network = Online } in
      if can_start_dispatch es1 then
        match first_pending_action es1 with
        | Some a0 ->
            ({ es1 with mode = Dispatching 0 },
             SendDispatch (MC.client_version es1.client) a0)
        | None -> (es1, NoOp)
        | _ -> (es1, NoOp)
      else
        (es1, NoOp)

  | ManualGoOffline ->
      ({ network = Offline; mode = Idle; client = es.client; serverVersion = es.serverVersion }, NoOp)

  | ManualGoOnline ->
      let es1 = { es with network = Online } in
      if can_start_dispatch es1 then
        match first_pending_action es1 with
        | Some a0 ->
            ({ es1 with mode = Dispatching 0 },
             SendDispatch (MC.client_version es1.client) a0)
        | None -> (es1, NoOp)
        | _ -> (es1, NoOp)
      else
        (es1, NoOp)

  | Tick ->
      if can_start_dispatch es then
        match first_pending_action es with
        | Some a0 ->
            ({ es with mode = Dispatching 0 },
             SendDispatch (MC.client_version es.client) a0)
        | None -> (es, NoOp)
        | _ -> (es, NoOp)
      else
        (es, NoOp)

  | _ -> admit ()

// ============================================================================
// Invariants
// ============================================================================

let mode_consistent (es:effect_state) : prop =
  match es.mode with
  | Idle -> True
  | Dispatching _ -> has_pending es == true
  | _ -> false

let retries_bounded (es:effect_state) : prop =
  match es.mode with
  | Idle -> True
  | Dispatching r -> r <= max_retries
  | _ -> false

let inv (es:effect_state) : prop =
  mode_consistent es /\ retries_bounded es

// ============================================================================
// Init
// ============================================================================

let init (version:nat) (m:model) : effect_state =
  { network = Online;
    mode = Idle;
    client = MC.init_client version m;
    serverVersion = version }

// ============================================================================
// Proof hooks
// ============================================================================

assume val init_satisfies_inv : v:nat -> m:model ->
  Lemma (ensures inv (init v m))

assume val step_preserves_inv : es:effect_state -> ev:event ->
  Lemma (requires inv es)
        (ensures inv (fst (step es ev)))