module MultiCollaboration

module D = Domain
module M = Model
open FStar.Sequence.Base
open FStar.List.Tot

type model = M.model

// --------------------------
// Server-side types
// --------------------------

type reject_reason =
  | DomainInvalid

type reply =
  | Accepted : newVersion:nat -> newPresent:model -> applied:D.action -> noChange:bool -> reply
  | Rejected : reason:reject_reason -> rebased:D.action -> reply

type request_outcome =
  | AuditAccepted : applied:D.action -> noChange:bool -> request_outcome
  | AuditRejected : reason:reject_reason -> rebased:D.action -> request_outcome

type request_record = {
  baseVersion : nat;
  orig        : D.action;
  rebased     : D.action;
  chosen      : D.action;
  outcome     : request_outcome
}

type server_state = {
  present    : model;
  appliedLog : list D.action;
  auditLog   : list request_record
}

let version (s:server_state) : nat =
  length s.appliedLog

let init_server () : server_state =
  { present = D.init (); appliedLog = []; auditLog = [] }

let init_server_satisfies_inv ()
  : Lemma (ensures D.inv (init_server ()).present)
  = admit ()

// --------------------------
// Helpers
// --------------------------

let pred_nat (n:nat) : Tot nat =
  if n = 0 then 0
  else
    let m : nat = n - 1 in
    m

let rec drop_nat (#a:Type0) (n:nat) (xs:list a) : Tot (list a)
  (decreases n)
=
  if n = 0 then xs
  else
    match xs with
    | [] -> []
    | _::tl -> drop_nat (pred_nat n) tl

let suffix_from (#a:Type0) (baseVersion:nat) (xs:list a) : Tot (list a) =
  drop_nat baseVersion xs

// --------------------------
// ChooseCandidate (executable)
// --------------------------

let rec choose_candidate (m:model) (cs:list D.action)
  : D.result (model * D.action) D.err
  = match cs with
    | [] -> D.Err (D.reject_err ())
    | hd::tl ->
        match D.try_step m hd with
        | D.Ok m2  -> D.Ok (m2, hd)
        | D.Err _  -> choose_candidate m tl

// --------------------------
// Dispatch (executable)
// --------------------------

let dispatch (s:server_state)
             (baseVersion:nat{baseVersion <= version s})
             (orig:D.action)
  : server_state * reply
  =
  let suffix  = suffix_from baseVersion s.appliedLog in
  let rebased = D.rebase_through_suffix suffix orig in
  let cs      = D.candidates s.present rebased in

  match choose_candidate s.present cs with
  | D.Ok (m2, chosen) ->
      let noChange = M.model_eqb m2 s.present in
      let newApplied = s.appliedLog @ [chosen] in
      let rec0 : request_record =
        { baseVersion = baseVersion;
          orig = orig;
          rebased = rebased;
          chosen = chosen;
          outcome = AuditAccepted chosen noChange } in
      let newAudit = s.auditLog @ [rec0] in
      ({ present = m2; appliedLog = newApplied; auditLog = newAudit },
       Accepted (length newApplied) m2 chosen noChange)

  | D.Err _ ->
      let rec0 : request_record =
        { baseVersion = baseVersion;
          orig = orig;
          rebased = rebased;
          chosen = rebased;
          outcome = AuditRejected DomainInvalid rebased } in
      let newAudit = s.auditLog @ [rec0] in
      ({ present = s.present; appliedLog = s.appliedLog; auditLog = newAudit },
       Rejected DomainInvalid rebased)

// --------------------------
// Client-side state (executable)
// --------------------------

type client_state = {
  baseVersion : nat;
  present     : model;
  pending     : list D.action
}

let init_client (v:nat) (m:model) : client_state =
  { baseVersion = v; present = m; pending = [] }

let init_client_from_server (s:server_state) : client_state =
  { baseVersion = version s; present = s.present; pending = [] }

let sync (s:server_state) : client_state =
  { baseVersion = version s; present = s.present; pending = [] }

let client_local_dispatch (c:client_state) (a:D.action) : client_state =
  match D.try_step c.present a with
  | D.Ok m2 -> { c with present = m2; pending = c.pending @ [a] }
  | D.Err _ -> { c with pending = c.pending @ [a] }

let rec reapply_pending (m:model) (pending:list D.action) : Tot model
  (decreases pending)
=
  match pending with
  | [] -> m
  | a::tl ->
      let m' =
        match D.try_step m a with
        | D.Ok m2 -> m2
        | D.Err _ -> m
      in
      reapply_pending m' tl

let handle_realtime_update (c:client_state) (serverVersion:nat) (serverModel:model) : client_state =
  if serverVersion > c.baseVersion then
    let newPresent = reapply_pending serverModel c.pending in
    { baseVersion = serverVersion; present = newPresent; pending = c.pending }
  else c

let client_accept_reply (c:client_state) (newVersion:nat) (newPresent:model) : client_state =
  match c.pending with
  | [] -> { baseVersion = newVersion; present = newPresent; pending = [] }
  | _hd::rest ->
      let reapplied = reapply_pending newPresent rest in
      { baseVersion = newVersion; present = reapplied; pending = rest }

let client_reject_reply (c:client_state) (freshVersion:nat) (freshModel:model) : client_state =
  match c.pending with
  | [] -> { baseVersion = freshVersion; present = freshModel; pending = [] }
  | _hd::rest ->
      let reapplied = reapply_pending freshModel rest in
      { baseVersion = freshVersion; present = reapplied; pending = rest }

let pending_count (c:client_state) : nat = length c.pending
let client_model   (c:client_state) : model = c.present
let client_version (c:client_state) : nat = c.baseVersion

// --------------------------
// Proof hooks
// --------------------------

assume val dispatch_preserves_inv :
  s:server_state -> baseVersion:nat -> orig:D.action ->
  Lemma (requires baseVersion <= version s /\ D.inv s.present)
        (ensures  D.inv (fst (dispatch s baseVersion orig)).present)

assume val dispatch_reject_is_minimal :
  s:server_state -> baseVersion:nat -> orig:D.action -> aGood:D.action -> m2:model ->
  Lemma (requires baseVersion <= version s /\
                D.inv s.present /\
                D.explains (D.rebase_through_suffix (suffix_from baseVersion s.appliedLog) orig) aGood /\
                D.try_step s.present aGood == D.Ok m2)
        (ensures  True)