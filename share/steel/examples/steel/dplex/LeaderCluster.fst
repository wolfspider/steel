module LeaderCluster

module MC = MultiCollaboration
module D  = Domain
module RT = RealtimeCollaboration

open FStar.List.Tot
open FStar.Classical

// ============================================================================
// Cluster view
//   - One leader provides the linear commit log
//   - Followers apply commits in strict next-index order
//   - Safety we want first: follower log is always a prefix of leader log
// ============================================================================

type leader   = MC.server_state
type follower = MC.server_state

let leader_version   (l:leader)   : nat = MC.version l
let follower_version (f:follower) : nat = MC.version f

// Prefix predicate on logs: ys = xs @ zs
let is_prefix (#a:Type0) (xs:list a) (ys:list a) : prop =
  exists (zs:list a). ys == xs @ zs

let follower_is_prefix (l:leader) (f:follower) : prop =
  is_prefix f.appliedLog l.appliedLog

// ============================================================================
// Leader commit: run MC.dispatch at the leader
// ============================================================================

type commit = {
  idx : nat;       // new version after accept
  act : D.action;  // chosen/applied action
}

type leader_commit_result = {
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

// ============================================================================
// Delivery / follower apply
//   We model replication as: follower receives the *next* log entry plus a model
//   snapshot from the leader (so follower adopts leader model).
// ============================================================================

type delivered = {
  idx   : nat;      // must equal follower_version + 1
  model : D.model;  // leader snapshot model at that idx
  act   : D.action; // leader's committed action at that idx
}

let follower_apply
  (f:follower)
  (d:delivered{d.idx == follower_version f + 1})
  : Tot follower
=
  { present    = d.model;
    appliedLog = f.appliedLog @ [d.act];
    auditLog   = f.auditLog }

// --------------------------------------------------------------------------
// The “wiring” assumption (for now):
// If f is a prefix of l and d is the next entry,
// then leader’s log decomposes as f.log @ (d.act :: rest),
// and d.model matches leader’s present snapshot (whatever you choose that to mean).
//
// This is the *right* place to later connect SQLite / transport correctness.
// --------------------------------------------------------------------------

type delivered_ok = {
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
// Optional: Leader → RT client snapshots (ties directly to your RT kernel)
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
  // Get the "next element in leader log" witness and its equation
  let ok = delivered_is_next l f d in
  let rest = ok.rest in

  // Let f' be the updated follower
  let f' = follower_apply f d in

  // 1) Normalize the singleton-append shape the solver will need
  //    ([x] @ ys == x :: ys) is definitional for lists, so this is usually trivial:
  assert ([d.act] @ rest == d.act :: rest);

  // 2) Bring associativity into context
  append_assoc f.appliedLog [d.act] rest;

  // 3) Rewrite ok's equation into the exact "prefix after apply" shape
  //    ok.eq is presumably: l.appliedLog == f.appliedLog @ (d.act :: rest)
  assert (l.appliedLog == f.appliedLog @ (d.act :: rest));
  assert (f.appliedLog @ (d.act :: rest) == f.appliedLog @ ([d.act] @ rest));
  assert (f.appliedLog @ ([d.act] @ rest) == (f.appliedLog @ [d.act]) @ rest);
  assert (l.appliedLog == (f.appliedLog @ [d.act]) @ rest);
  
  eq_trans_r l.appliedLog ((f.appliedLog @ [d.act]) @ rest) (f'.appliedLog @ rest);

()

// Use RT.realtime_event as the snapshot payload shape
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

// If the client is flushing, snapshots are skipped (same pattern you already proved)
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
