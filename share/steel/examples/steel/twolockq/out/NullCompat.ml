(* Demo-only null ref shim for extracted Steel code. *)
module S = struct
  type 'a sref = 'a Steel_Reference.ref
  (* Represent null as an immediate (non-block) so GC never scans it. *)
  let null () : 'a sref = (Obj.magic 0 : 'a sref)
  (* Robust test: immediate values are NOT heap blocks. *)
  let is_null (r : 'a sref) : bool = Obj.is_int (Obj.repr r)
end
