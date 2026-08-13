module LeaderCluster

module MC = MultiCollaboration
module D  = Domain
module RT = RealtimeCollaboration
module M  = Model

open FStar.List.Tot
open FStar.Classical

type model = M.model

// ============================================================================
// Cluster view
// ============================================================================

type leader   = MC.server_state
type follower = MC.server_state

let leader_version   (l:leader)   : nat = MC.version l
let follower_version (f:follower) : nat = MC.version f

let is_prefix (#a:Type0) (xs:list a) (ys:list a) : prop =
  exists (zs:list a). ys == xs @ zs

let follower_is_prefix (l:leader) (f:follower) : prop =
  is_prefix f.appliedLog l.appliedLog

// ============================================================================
// Leader commit
// ============================================================================

noeq type commit = {
  idx : nat;
  act : D.action;
}

noeq type leader_commit_result = {
  leader'   : leader;
  reply     : MC.reply;
  committed : RT.option commit;
}

let leader_commit
  (l:leader)
  (baseVersion:nat{baseVersion <= leader_version l})
  (orig:D.action)
  : Tot leader_commit_result
=
  let (l', rep) = MC.dispatch l baseVersion orig in
  match rep with
  | MC.Accepted newV _newPresent applied _noChange ->
      { leader' = l';
        reply = rep;
        committed = RT.Some { idx = newV; act = applied } }
  | MC.Rejected _reason _rebased ->
      { leader' = l';
        reply = rep;
        committed = RT.None }
  | _ ->
      { leader' = l';
        reply = rep;
        committed = RT.None }

// ============================================================================
// Delivery / follower apply
// ============================================================================

noeq type delivered = {
  idx   : nat;
  model : model;
  act   : D.action;
}

let follower_apply
  (f:follower)
  (d:delivered{d.idx == follower_version f + 1})
  : Tot follower
=
  { present    = d.model;
    appliedLog = f.appliedLog @ [d.act];
    auditLog   = f.auditLog }

noeq type delivered_ok = {
  rest : list D.action
}

assume val delivered_is_next :
  l:leader ->
  f:follower ->
  d:delivered{ d.idx == follower_version f + 1 /\ d.idx <= leader_version l } ->
  Pure delivered_ok
    (requires follower_is_prefix l f)
    (ensures  fun ok ->
      l.appliedLog == f.appliedLog @ (d.act :: ok.rest) /\
      d.model == l.present)

// ============================================================================
// Prefix lemma
// ============================================================================

let eq_sym (#a:Type0) (x:a) (y:a)
  : Lemma (requires x == y) (ensures y == x)
= ()

let eq_trans (#a:Type0) (x:a) (y:a) (z:a)
  : Lemma (requires x == y /\ y == z) (ensures x == z)
= ()

let eq_trans_r (#a:Type0) (x:a) (y:a) (z:a)
  : Lemma (requires x == y /\ z == y) (ensures x == z)
=
  eq_sym z y;
  eq_trans x y z

let follower_apply_preserves_prefix
  (l:leader)
  (f:follower)
  (d:delivered{d.idx == follower_version f + 1 /\ d.idx <= leader_version l})
  : Lemma (requires follower_is_prefix l f)
          (ensures  follower_is_prefix l (follower_apply f d))
=
  let ok = delivered_is_next l f d in
  let rest = ok.rest in
  let f' = follower_apply f d in
  assert ([d.act] @ rest == d.act :: rest);
  append_assoc f.appliedLog [d.act] rest;
  assert (l.appliedLog == f.appliedLog @ (d.act :: rest));
  assert (f.appliedLog @ (d.act :: rest) == f.appliedLog @ ([d.act] @ rest));
  assert (f.appliedLog @ ([d.act] @ rest) == (f.appliedLog @ [d.act]) @ rest);
  assert (l.appliedLog == (f.appliedLog @ [d.act]) @ rest);
  eq_trans_r l.appliedLog ((f.appliedLog @ [d.act]) @ rest) (f'.appliedLog @ rest);
  ()

// ============================================================================
// RT client snapshots
// ============================================================================

let leader_snapshot (l:leader) : RT.realtime_event =
  { version = leader_version l; model = l.present }

let client_on_snapshot
  (c:RT.client_state)
  (e:RT.realtime_event)
  : Tot RT.client_state
=
  RT.handle_realtime_update c e.version e.model

let rec push_snapshots
  (c:RT.client_state)
  (es:list RT.realtime_event)
  : Tot RT.client_state
    (decreases es)
=
  match es with
  | [] -> c
  | e::tl -> push_snapshots (client_on_snapshot c e) tl

let rec snapshots_skipped_during_flush
  (c:RT.client_state{c.mode == RT.Flushing})
  (es:list RT.realtime_event)
  : Lemma (ensures push_snapshots c es == c)
  (decreases es)
=
  match es with
  | [] -> ()
  | e::tl ->
      assert (client_on_snapshot c e == c);
      snapshots_skipped_during_flush c tl