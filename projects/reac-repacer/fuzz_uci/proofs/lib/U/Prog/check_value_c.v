(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for reac-repacer/fuzz_uci: the contract of check_value (fuzz_uci.c) on the UBSan
   image, at 0x12e48 (frame 48, as the plain image). The UBSan twin of lib/Prog/check_value_c.v, the same text at
   this image's values. Its UBSan checks on r (expected_value's r[i]: 0x12ec0 / 0x12ecc / 0x12ed0 / 0x12f1c /
   0x12f38 / 0x12f40 / 0x12f7c / 0x12fd0, all to the unimp at 0x13058) need no premise: they run only for n > 0,
   where in_block puts [r, r + n) in a live block (at or above 4096, below alloc_ceiling); its multiply and
   negate checks (0x12fa0, 0x13010) cannot fire on a value below 10^10. The post says the call returns: neither
   abort (jal abort at 0x13054) nor a trap runs. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YM05 YL0i YL00.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Prog Require Import rp_uci_int_c check_no_overread_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition CHECK_VALUE : Z := 0x12e48.
Definition CV_FRAME : Z := 48.
Definition CV_STACK : Z := CV_FRAME + ALLOC_STACK.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

(* room for the one max(n, 1) byte copy fuzz_dup holds *)
Definition cv_room (b : sbound) (n : Z) : Prop :=
  sb_live b + 1 <= sb_cap b <= CAPMAX /\ 0 <= sb_bytes b /\ sb_bytes b + n + 1 <= 2 ^ 40.

Definition check_value_contract : Prop :=
  forall L A regs mem md (r n cur : Z) (bs : list byte) (b : sbound),
    ms_segs B = rsegs ->
    call_pre_k B MR CV_STACK L A regs mem md ->
    getr regs 10 = Z_to_bv 64 r -> getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 cur ->
    INT_MIN <= cur <= INT_MAX ->
    0 <= n <= REPLY_MAX ->
    Z.of_nat (length bs) = n ->
    blk_data B mem r bs ->
    (0 < n -> in_block L A r n) ->
    ro_agree (ms_segs B) mem ->
    frm_zero fp_csr ->
    res_ok_slots A b ->
    cv_room b n ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 CHECK_VALUE) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : FPState) L' A' regs' mem' md',
         c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         frm_zero (@fp_csr fx') /\
         call_post_k B MR CV_STACK L A regs mem md (fun _ => False) L' A' regs' mem' md' /\
         getr regs' 10 = Z_to_bv 64 (rp_uci_int_m (zbytes bs) cur) /\
         blocks L' A' = blocks L A /\
         blocks_kept B L A mem mem' (fun _ => False) /\
         guard_kept B mem mem' /\
         ro_agree (ms_segs B) mem' /\
         res_ok_slots A' b /\
         st_init_done A' = true).

End K.
