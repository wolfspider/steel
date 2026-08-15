open Prims
type model = Model.model
type reject_reason =
  | DomainInvalid 
let uu___is_DomainInvalid (projectee : reject_reason) : Prims.bool= true
type reply =
  | Accepted of Prims.nat * model * Domain.action * Prims.bool 
  | Rejected of reject_reason * Domain.action 
let uu___is_Accepted (projectee : reply) : Prims.bool=
  match projectee with
  | Accepted (newVersion, newPresent, applied, noChange) -> true
  | uu___ -> false
let __proj__Accepted__item__newVersion (projectee : reply) : Prims.nat=
  match projectee with
  | Accepted (newVersion, newPresent, applied, noChange) -> newVersion
let __proj__Accepted__item__newPresent (projectee : reply) : model=
  match projectee with
  | Accepted (newVersion, newPresent, applied, noChange) -> newPresent
let __proj__Accepted__item__applied (projectee : reply) : Domain.action=
  match projectee with
  | Accepted (newVersion, newPresent, applied, noChange) -> applied
let __proj__Accepted__item__noChange (projectee : reply) : Prims.bool=
  match projectee with
  | Accepted (newVersion, newPresent, applied, noChange) -> noChange
let uu___is_Rejected (projectee : reply) : Prims.bool=
  match projectee with | Rejected (reason, rebased) -> true | uu___ -> false
let __proj__Rejected__item__reason (projectee : reply) : reject_reason=
  match projectee with | Rejected (reason, rebased) -> reason
let __proj__Rejected__item__rebased (projectee : reply) : Domain.action=
  match projectee with | Rejected (reason, rebased) -> rebased
type request_outcome =
  | AuditAccepted of Domain.action * Prims.bool 
  | AuditRejected of reject_reason * Domain.action 
let uu___is_AuditAccepted (projectee : request_outcome) : Prims.bool=
  match projectee with
  | AuditAccepted (applied, noChange) -> true
  | uu___ -> false
let __proj__AuditAccepted__item__applied (projectee : request_outcome) :
  Domain.action=
  match projectee with | AuditAccepted (applied, noChange) -> applied
let __proj__AuditAccepted__item__noChange (projectee : request_outcome) :
  Prims.bool=
  match projectee with | AuditAccepted (applied, noChange) -> noChange
let uu___is_AuditRejected (projectee : request_outcome) : Prims.bool=
  match projectee with
  | AuditRejected (reason, rebased) -> true
  | uu___ -> false
let __proj__AuditRejected__item__reason (projectee : request_outcome) :
  reject_reason=
  match projectee with | AuditRejected (reason, rebased) -> reason
let __proj__AuditRejected__item__rebased (projectee : request_outcome) :
  Domain.action=
  match projectee with | AuditRejected (reason, rebased) -> rebased
type request_record =
  {
  baseVersion: Prims.nat ;
  orig: Domain.action ;
  rebased: Domain.action ;
  chosen: Domain.action ;
  outcome: request_outcome }
let __proj__Mkrequest_record__item__baseVersion (projectee : request_record)
  : Prims.nat=
  match projectee with
  | { baseVersion; orig; rebased; chosen; outcome;_} -> baseVersion
let __proj__Mkrequest_record__item__orig (projectee : request_record) :
  Domain.action=
  match projectee with
  | { baseVersion; orig; rebased; chosen; outcome;_} -> orig
let __proj__Mkrequest_record__item__rebased (projectee : request_record) :
  Domain.action=
  match projectee with
  | { baseVersion; orig; rebased; chosen; outcome;_} -> rebased
let __proj__Mkrequest_record__item__chosen (projectee : request_record) :
  Domain.action=
  match projectee with
  | { baseVersion; orig; rebased; chosen; outcome;_} -> chosen
let __proj__Mkrequest_record__item__outcome (projectee : request_record) :
  request_outcome=
  match projectee with
  | { baseVersion; orig; rebased; chosen; outcome;_} -> outcome
type server_state =
  {
  present: model ;
  appliedLog: Domain.action Prims.list ;
  auditLog: request_record Prims.list }
let __proj__Mkserver_state__item__present (projectee : server_state) : 
  model= match projectee with | { present; appliedLog; auditLog;_} -> present
let __proj__Mkserver_state__item__appliedLog (projectee : server_state) :
  Domain.action Prims.list=
  match projectee with | { present; appliedLog; auditLog;_} -> appliedLog
let __proj__Mkserver_state__item__auditLog (projectee : server_state) :
  request_record Prims.list=
  match projectee with | { present; appliedLog; auditLog;_} -> auditLog
let version (s : server_state) : Prims.nat=
  FStar_List_Tot_Base.length s.appliedLog
let init_server (uu___ : unit) : server_state=
  { present = (Domain.init ()); appliedLog = []; auditLog = [] }
let pred_nat (n : Prims.nat) : Prims.nat=
  if n = Prims.int_zero
  then Prims.int_zero
  else (let m = n - Prims.int_one in m)
let rec drop_nat : 'a . Prims.nat -> 'a Prims.list -> 'a Prims.list =
  fun n xs ->
    if n = Prims.int_zero
    then xs
    else (match xs with | [] -> [] | uu___::tl -> drop_nat (pred_nat n) tl)
let suffix_from (baseVersion : Prims.nat) (xs : 'a Prims.list) :
  'a Prims.list= drop_nat baseVersion xs
let rec choose_candidate (m : model) (cs : Domain.action Prims.list) :
  ((model * Domain.action), unit) Domain.result=
  match cs with
  | [] -> Domain.Err ()
  | hd::tl ->
      (match Domain.try_step m hd with
       | Domain.Ok m2 -> Domain.Ok (m2, hd)
       | Domain.Err uu___ -> choose_candidate m tl)
let dispatch (s : server_state) (baseVersion : Prims.nat)
  (orig : Domain.action) : (server_state * reply)=
  let suffix = suffix_from baseVersion s.appliedLog in
  let rebased = Domain.rebase_through_suffix suffix orig in
  let cs = Domain.candidates s.present rebased in
  match choose_candidate s.present cs with
  | Domain.Ok (m2, chosen) ->
      let noChange = Model.model_eqb m2 s.present in
      let newApplied = FStar_List_Tot_Base.op_At s.appliedLog [chosen] in
      let rec0 =
        {
          baseVersion;
          orig;
          rebased;
          chosen;
          outcome = (AuditAccepted (chosen, noChange))
        } in
      let newAudit = FStar_List_Tot_Base.op_At s.auditLog [rec0] in
      ({ present = m2; appliedLog = newApplied; auditLog = newAudit },
        (Accepted
           ((FStar_List_Tot_Base.length newApplied), m2, chosen, noChange)))
  | Domain.Err uu___ ->
      let rec0 =
        {
          baseVersion;
          orig;
          rebased;
          chosen = rebased;
          outcome = (AuditRejected (DomainInvalid, rebased))
        } in
      let newAudit = FStar_List_Tot_Base.op_At s.auditLog [rec0] in
      ({
         present = (s.present);
         appliedLog = (s.appliedLog);
         auditLog = newAudit
       }, (Rejected (DomainInvalid, rebased)))
type client_state =
  {
  baseVersion1: Prims.nat ;
  present1: model ;
  pending: Domain.action Prims.list }
let __proj__Mkclient_state__item__baseVersion (projectee : client_state) :
  Prims.nat=
  match projectee with
  | { baseVersion1 = baseVersion; present1 = present; pending;_} ->
      baseVersion
let __proj__Mkclient_state__item__present (projectee : client_state) : 
  model=
  match projectee with
  | { baseVersion1 = baseVersion; present1 = present; pending;_} -> present
let __proj__Mkclient_state__item__pending (projectee : client_state) :
  Domain.action Prims.list=
  match projectee with
  | { baseVersion1 = baseVersion; present1 = present; pending;_} -> pending
let init_client (v : Prims.nat) (m : model) : client_state=
  { baseVersion1 = v; present1 = m; pending = [] }
let init_client_from_server (s : server_state) : client_state=
  { baseVersion1 = (version s); present1 = (s.present); pending = [] }
let sync (s : server_state) : client_state=
  { baseVersion1 = (version s); present1 = (s.present); pending = [] }
let client_local_dispatch (c : client_state) (a : Domain.action) :
  client_state=
  match Domain.try_step c.present1 a with
  | Domain.Ok m2 ->
      {
        baseVersion1 = (c.baseVersion1);
        present1 = m2;
        pending = (FStar_List_Tot_Base.op_At c.pending [a])
      }
  | Domain.Err uu___ ->
      {
        baseVersion1 = (c.baseVersion1);
        present1 = (c.present1);
        pending = (FStar_List_Tot_Base.op_At c.pending [a])
      }
let rec reapply_pending (m : model) (pending : Domain.action Prims.list) :
  model=
  match pending with
  | [] -> m
  | a::tl ->
      let m' =
        match Domain.try_step m a with
        | Domain.Ok m2 -> m2
        | Domain.Err uu___ -> m in
      reapply_pending m' tl
let handle_realtime_update (c : client_state) (serverVersion : Prims.nat)
  (serverModel : model) : client_state=
  if serverVersion > c.baseVersion1
  then
    let newPresent = reapply_pending serverModel c.pending in
    {
      baseVersion1 = serverVersion;
      present1 = newPresent;
      pending = (c.pending)
    }
  else c
let client_accept_reply (c : client_state) (newVersion : Prims.nat)
  (newPresent : model) : client_state=
  match c.pending with
  | [] -> { baseVersion1 = newVersion; present1 = newPresent; pending = [] }
  | _hd::rest ->
      let reapplied = reapply_pending newPresent rest in
      { baseVersion1 = newVersion; present1 = reapplied; pending = rest }
let client_reject_reply (c : client_state) (freshVersion : Prims.nat)
  (freshModel : model) : client_state=
  match c.pending with
  | [] ->
      { baseVersion1 = freshVersion; present1 = freshModel; pending = [] }
  | _hd::rest ->
      let reapplied = reapply_pending freshModel rest in
      { baseVersion1 = freshVersion; present1 = reapplied; pending = rest }
let pending_count (c : client_state) : Prims.nat=
  FStar_List_Tot_Base.length c.pending
let client_model (c : client_state) : model= c.present1
let client_version (c : client_state) : Prims.nat= c.baseVersion1
