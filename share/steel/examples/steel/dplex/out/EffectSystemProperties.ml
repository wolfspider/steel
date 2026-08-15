open Prims
let pending (es : EffectStateMachine.effect_state) :
  Domain.action Prims.list=
  (es.EffectStateMachine.client).MultiCollaboration.pending
let pending_tail (es : EffectStateMachine.effect_state) :
  Domain.action Prims.list=
  match pending es with | [] -> [] | uu___::tl -> tl | uu___ -> []
let rec apply_events (es : EffectStateMachine.effect_state)
  (events : EffectStateMachine.event Prims.list) :
  EffectStateMachine.effect_state=
  match events with
  | [] -> es
  | ev::tl ->
      let uu___ = EffectStateMachine.step es ev in
      (match uu___ with | (es1, _cmd) -> apply_events es1 tl)
