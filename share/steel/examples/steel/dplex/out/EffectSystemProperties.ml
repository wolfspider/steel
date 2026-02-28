open Prims
let pending (es : EffectStateMachine.effect_state) :
  Domain.action Prims.list=
  (es.EffectStateMachine.client).MultiCollaboration.pending
let pending_tail (es : EffectStateMachine.effect_state) :
  Domain.action Prims.list=
  match pending es with | [] -> [] | uu___::tl -> tl
let rec apply_events (next : Prims.nat -> Prims.nat)
  (es : EffectStateMachine.effect_state)
  (events : EffectStateMachine.event Prims.list) :
  EffectStateMachine.effect_state=
  match events with
  | [] -> es
  | ev::tl ->
      let uu___ = EffectStateMachine.step next es ev in
      (match uu___ with | (es1, _cmd) -> apply_events next es1 tl)
type ('es, 'ev, 'a) processed_now = Obj.t
type ('next, 'es, 'events, 'a) action_was_processed = Obj.t
