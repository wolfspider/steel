module EffectSystemProperties

module E  = EffectStateMachine
module MC = MultiCollaboration
module D  = Domain

open FStar.List.Tot
open FStar.List.Tot.Base

// ---------------------------------------------------------------------------
// Pending helpers (list-based; matches your ES.client.pending : list action)
// ---------------------------------------------------------------------------

let pending (es:E.effect_state) : list D.action =
  es.client.pending

let pending_tail (es:E.effect_state) : list D.action =
  match pending es with
  | [] -> []
  | _::tl -> tl

// ---------------------------------------------------------------------------
// Helper: Apply a sequence (list) of events
// Mirrors Dafny ApplyEvents, but list-based.
// ---------------------------------------------------------------------------

let rec apply_events
  (es:E.effect_state{E.inv es})
  (events:list E.event)
  : Tot (es':E.effect_state{E.inv es'})
    (decreases events)
=
  match events with
  | [] -> es
  | ev::tl ->
      let (es1, _cmd) = E.step es ev in
      let _ = E.step_preserves_inv es ev in
      apply_events es1 tl


// ---------------------------------------------------------------------------
// Action fate: “processed” = was head AND accept/reject while Dispatching
// ---------------------------------------------------------------------------

let processed_now (es:E.effect_state) (ev:E.event) (a:D.action) : prop =
  match es.mode, ev, pending es with
  | E.Dispatching _, E.DispatchAccepted _ _, hd::_ -> hd == a
  | E.Dispatching _, E.DispatchRejected _ _, hd::_ -> hd == a
  | _ -> False

let rec action_was_processed (es:E.effect_state) (events:list E.event) (a:D.action)
  : Tot (prop)
(decreases events)
=
  match events with
  | [] -> False
  | ev::tl ->
    processed_now es ev a \/
    (let (es1, _cmd) = E.step es ev in
     action_was_processed es1 tl a)

// ---------------------------------------------------------------------------
// SYSTEM PROPERTY 1: No Silent Data Loss
// ---------------------------------------------------------------------------

let no_silent_data_loss (es:E.effect_state) (a:D.action) (events:list E.event)
  : Lemma
      (requires E.inv es /\ mem a (pending es))
      (ensures
        (let es' = apply_events es events in
        mem a (pending es') \/ action_was_processed es events a))
      (decreases events)
=
  admit ()

// ---------------------------------------------------------------------------
// SYSTEM PROPERTY 2: UserAction is captured (enters pending)
// ---------------------------------------------------------------------------

let user_action_enters_pending (es:E.effect_state) (a:D.action)
  : Lemma
      (requires E.inv es)
      (ensures
        (let (es', _cmd) = E.step es (E.UserAction a) in
        mem a (pending es')))
=
  admit ()

// ---------------------------------------------------------------------------
// SYSTEM PROPERTY 3: FIFO Processing
//
// List form: if an action is in the tail (not at head), one step can’t remove it.
// This is the clean “only the head can leave” FIFO claim.
// ---------------------------------------------------------------------------

let fifo_processing (es:E.effect_state) (ev:E.event) (a:D.action)
  : Lemma
      (requires E.inv es /\ mem a (pending_tail es))
      (ensures
        (let (es', _cmd) = E.step es ev in
        mem a (pending es')))
=
  admit ()

// ---------------------------------------------------------------------------
// SYSTEM PROPERTY 4: Progress trigger (Tick when Online+Idle+Pending)
// ---------------------------------------------------------------------------

let online_idle_pending_makes_progress (es:E.effect_state)
  : Lemma
      (requires E.inv es /\ E.is_online es == true /\ E.is_idle es == true /\ E.has_pending es == true)
      (ensures
        (let (_es', cmd) = E.step es E.Tick in
        match cmd with
        | E.SendDispatch _ _ -> True
        | _ -> False))
=
  admit ()

// ---------------------------------------------------------------------------
// SYSTEM PROPERTY 6: Quiescence
//
// In your MC, client_model c = c.present by definition, so this is immediate.
// ---------------------------------------------------------------------------

let quiescence (es:E.effect_state)
  : Lemma
      (requires E.inv es /\ pending es == [])
      (ensures MC.client_model es.client == es.client.present /\ es.client.pending == [])
=
  ()
