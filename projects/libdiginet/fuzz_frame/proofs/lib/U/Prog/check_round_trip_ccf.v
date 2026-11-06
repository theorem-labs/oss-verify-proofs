(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_egress/lib/U/Prog/check_inject_ccf.v, with its module paths and module names changed; 18 of its 46 lines of code are new or changed and 17 lines of the source are left out. *)
(* The crash-free contract of check_round_trip in fuzz_frame.ubsan (0x131e4), in the form of
   libreac/fuzz_decode's lib/U/Prog/check_round_trip_ccf.v. ubsan_agrees uses it.
   It is check_round_trip_contract (U/Prog/check_round_trip_c.v) with SRcf (U/SlotAgree.v:
   every run from the start that the post-state continues is also free of a cut) in place of
   SR, and the room premise of the crash-free allocator (U/Prog/LLVMFuzzerTestOneInput_cfb.v
   room_ag): sb_live sb + 3 <= sb_cap sb <= CAP_AG, 128 <= sb_cap sb, 0 <= sb_bytes sb and
   sb_bytes sb + 3 * n_want <= 2^29, where n_want is crt_len b, the size of each of the three
   blocks (n_want, n_want and n_want - 1 bytes). All other premises and the post-state are
   those of check_round_trip_contract: call_pre_k with U_CRT_STACK, a0 = w, fr_code b = 0,
   length b < 2^26, 0 < buf < 2^64 in a block of the caller holding b, w 8-aligned at sp or
   above with w + 80 <= 2^63 holding spec_bytes buf b, ro_agree, frm_zero, res_ok_slots A sb;
   the function returns to ra with call_post_k, the same blocks, each byte of each block kept,
   the guard kept, ro_agree, res_ok_slots A' sb and st_init_done.
   The UBSan trap at 0x134f4 and the abort at 0x134f8 are unreachable for the reasons that
   U/Prog/check_round_trip_c.v gives.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YM05 YL0i YL00.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require Import check_parse_fields_c CheckStackU.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require Import check_round_trip_c.
Import ListNotations.
Local Open Scope Z_scope.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition check_round_trip_contract_cf : Prop :=
  forall L A regs mem md (w buf : Z) (b : list byte) (sb : sbound),
    ms_segs B = rsegs ->
    call_pre_k B MR U_CRT_STACK L A regs mem md ->
    getr regs 10 = Z_to_bv 64 w ->
    fr_code b = 0 -> Z.of_nat (length b) < 2 ^ 26 ->
    0 < buf < 2 ^ 64 -> in_block L A buf (Z.of_nat (length b)) -> blk_data B mem buf b ->
    spZ regs <= w -> w mod 8 = 0 -> w + 80 <= 2 ^ 63 ->
    blk_data B mem w (spec_bytes buf b) ->
    ro_agree (ms_segs B) mem ->
    frm_zero fp_csr ->
    res_ok_slots A sb ->
    (sb_live sb + 3 <= sb_cap sb <= CAP_AG /\ 128 <= sb_cap sb) /\ 0 <= sb_bytes sb /\
      sb_bytes sb + 3 * crt_len b <= 2 ^ 29 ->
    SRcf B (mkCfg (mkst regs (Z_to_bv 64 CHECK_ROUND_TRIP) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : FPState) L' A' regs' mem' md',
         c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         frm_zero (@fp_csr fx') /\
         call_post_k B MR U_CRT_STACK L A regs mem md (fun _ => False) L' A' regs' mem' md' /\
         blocks L' A' = blocks L A /\
         blocks_kept B L A mem mem' (fun _ => False) /\
         guard_kept B mem mem' /\
         ro_agree (ms_segs B) mem' /\
         res_ok_slots A' sb /\
         st_init_done A' = true).

End K.
