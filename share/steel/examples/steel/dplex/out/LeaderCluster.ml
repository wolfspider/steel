open Prims
type model = Prims.nat Domain.model
type leader = MultiCollaboration.server_state
type follower = MultiCollaboration.server_state
let leader_version (l : leader) : Prims.nat= MultiCollaboration.version l
let follower_version (f : follower) : Prims.nat= MultiCollaboration.version f
type ('a, 'xs, 'ys) is_prefix = unit
type ('l, 'f) follower_is_prefix = unit
type commit = {
  idx: Prims.nat ;
  act: Domain.action }
let __proj__Mkcommit__item__idx (projectee : commit) : Prims.nat=
  match projectee with | { idx; act;_} -> idx
let __proj__Mkcommit__item__act (projectee : commit) : Domain.action=
  match projectee with | { idx; act;_} -> act
type leader_commit_result =
  {
  leader': leader ;
  reply: MultiCollaboration.reply ;
  committed: commit RealtimeCollaboration.option }
let __proj__Mkleader_commit_result__item__leader'
  (projectee : leader_commit_result) : leader=
  match projectee with | { leader'; reply; committed;_} -> leader'
let __proj__Mkleader_commit_result__item__reply
  (projectee : leader_commit_result) : MultiCollaboration.reply=
  match projectee with | { leader'; reply; committed;_} -> reply
let __proj__Mkleader_commit_result__item__committed
  (projectee : leader_commit_result) : commit RealtimeCollaboration.option=
  match projectee with | { leader'; reply; committed;_} -> committed
let leader_commit (next : Prims.nat -> Prims.nat) (l : leader)
  (baseVersion : Prims.nat) (orig : Domain.action) : leader_commit_result=
  let uu___ = MultiCollaboration.dispatch next l baseVersion orig in
  match uu___ with
  | (l', rep) ->
      (match rep with
       | MultiCollaboration.Accepted (newV, _newPresent, applied, _noChange)
           ->
           {
             leader' = l';
             reply = rep;
             committed =
               (RealtimeCollaboration.Some { idx = newV; act = applied })
           }
       | MultiCollaboration.Rejected (_reason, _rebased) ->
           {
             leader' = l';
             reply = rep;
             committed = RealtimeCollaboration.None
           })
type delivered = {
  idx1: Prims.nat ;
  model: model ;
  act1: Domain.action }
let __proj__Mkdelivered__item__idx (projectee : delivered) : Prims.nat=
  match projectee with | { idx1 = idx; model = model1; act1 = act;_} -> idx
let __proj__Mkdelivered__item__model (projectee : delivered) : model=
  match projectee with
  | { idx1 = idx; model = model1; act1 = act;_} -> model1
let __proj__Mkdelivered__item__act (projectee : delivered) : Domain.action=
  match projectee with | { idx1 = idx; model = model1; act1 = act;_} -> act
let follower_apply (f : follower) (d : delivered) : follower=
  {
    MultiCollaboration.present = (d.model);
    MultiCollaboration.appliedLog =
      (FStar_List_Tot_Base.op_At f.MultiCollaboration.appliedLog [d.act1]);
    MultiCollaboration.auditLog = (f.MultiCollaboration.auditLog)
  }
type delivered_ok = {
  rest: Domain.action Prims.list }
let __proj__Mkdelivered_ok__item__rest (projectee : delivered_ok) :
  Domain.action Prims.list= match projectee with | { rest;_} -> rest
let delivered_is_next (l : leader) (f : follower) (d : delivered) :
  delivered_ok=
  failwith "Not yet implemented: LeaderCluster.delivered_is_next"
let leader_snapshot (l : leader) : RealtimeCollaboration.realtime_event=
  {
    RealtimeCollaboration.version = (leader_version l);
    RealtimeCollaboration.model = (l.MultiCollaboration.present)
  }
let client_on_snapshot (next : Prims.nat -> Prims.nat)
  (c : RealtimeCollaboration.client_state)
  (e : RealtimeCollaboration.realtime_event) :
  RealtimeCollaboration.client_state=
  RealtimeCollaboration.handle_realtime_update next c
    e.RealtimeCollaboration.version e.RealtimeCollaboration.model
let rec push_snapshots (next : Prims.nat -> Prims.nat)
  (c : RealtimeCollaboration.client_state)
  (es : RealtimeCollaboration.realtime_event Prims.list) :
  RealtimeCollaboration.client_state=
  match es with
  | [] -> c
  | e::tl -> push_snapshots next (client_on_snapshot next c e) tl
