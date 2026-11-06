(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for reac-repacer/fuzz_uci: the contract of check_value (fuzz_uci.c), the plain
   image's 0x12dc4. It inlines fuzz.h's fuzz_dup (malloc + abort on NULL + memcpy) and fuzz_uci.c's expected_value,
   calls rp_uci_int and free, and aborts, so it is stated in the SR / call_pre_k / call_post_k style of
   libreac/fuzz_decode's released lib/Prog/check_round_trip_c.v. The returned value is lib/Spec/UciModel.v's
   rp_uci_int_m of the n reply bytes; the post says the call returns, which is the statement that neither abort runs
   (the NULL one by the allocator contract, the property one by UciModel.uci_value_ok). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YM05 YL0i YL00.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib Require Import Contract Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog Require Import rp_uci_int_c check_no_overread_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition CHECK_VALUE : Z := 0x12dc4.
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
