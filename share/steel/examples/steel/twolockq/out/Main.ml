let to_str_u32 (v: FStar_UInt32.t) : string =
  Z.to_string (FStar_UInt32.v v)

let pp_opt_u32 = function
  | FStar_Pervasives_Native.None -> "None"
  | FStar_Pervasives_Native.Some v -> "Some(" ^ to_str_u32 v ^ ")"

let () =
  let (r0, r1, r2) = TwoLockQueueTest.smoke_u32 () in
  FStar_IO.print_string ("r0 = " ^ pp_opt_u32 r0 ^ "\n");
  FStar_IO.print_string ("r1 = " ^ pp_opt_u32 r1 ^ "\n");
  FStar_IO.print_string ("r2 = " ^ pp_opt_u32 r2 ^ "\n");
  FStar_IO.print_string "TwoLockQueueTest.smoke_u32 ran (OCaml)\n"
