(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for reac-repacer/fuzz_egress: the cut-free (SRcf) contract of check_restamp on the UBSan image, for the agree
   chain, as reac-repacer/fuzz_uci's lib/U/Prog/check_value_ccf.v (at bc49657c087a) is to its check_value_c.v: the
   premises and the post of lib/U/Prog/check_restamp_c.v, with SR replaced by SRcf and the room taken at the agree
   bounds (at most CAP_AG slots, at least 128, bytes within 2^29). check_restamp_c.v states its room as
   room_slots b n (the one n-byte copy fuzz_dup holds); cr_room_cf states that room in the agree-bound form of the
   other rooms (one free slot, n bytes), from which, as n <= 1600, the kit's room_slots_small gives room_slots b n
   and room_ag_gen gives the agree room of malloc. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U Require Import Contract Img0 SlotAgree.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Prog Require Import check_restamp_c.
Import ListNotations.
Local Open Scope Z_scope.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

(* room for the one n-byte copy fuzz_dup holds, at the agree bounds *)
Definition cr_room_cf (b : sbound) (n : Z) : Prop :=
  (sb_live b + 1 <= sb_cap b <= CAP_AG /\ 128 <= sb_cap b) /\ 0 <= sb_bytes b /\ sb_bytes b + n <= 2 ^ 29.

Definition check_restamp_contract_cf : Prop :=
  forall L A regs mem md (f n ctr : Z) (b : sbound),
    ms_segs B = rsegs ->
    call_pre_k B MR CHECK_RESTAMP_STACK L A regs mem md ->
    getr regs 10 = Z_to_bv 64 f -> getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 ctr ->
    0 <= n <= 1600 ->
    in_block L A f n ->
    ro_agree (ms_segs B) mem ->
    frm_zero fp_csr ->
    res_ok_slots A b ->
    cr_room_cf b n ->
    SRcf B (mkCfg (mkst regs (Z_to_bv 64 CHECK_RESTAMP) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : FPState) L' A' regs' mem' md',
         c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         frm_zero (@fp_csr fx') /\
         call_post_k B MR CHECK_RESTAMP_STACK L A regs mem md (fun _ => False) L' A' regs' mem' md' /\
         blocks L' A' = blocks L A /\
         blocks_kept B L A mem mem' (fun _ => False) /\
         guard_kept B mem mem' /\
         ro_agree (ms_segs B) mem' /\
         res_ok_slots A' b /\
         (st_init_done A = true -> st_init_done A' = true)).

End K.
