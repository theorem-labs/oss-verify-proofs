(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/U/Prog/LLVMFuzzerTestOneInput_cfb.v, with its module paths and module names changed; 14 of its 47 lines of code are new or changed and 97 lines of the source are left out. *)
(* The crash-free (SRcf) contracts the agreement of fuzz_lock.ubsan with fuzz_lock.plain needs: the contract of
   LLVMFuzzerTestOneInput and the contracts of the two harness functions it calls, in the form of
   libreac/fuzz_decode's released lib/U/Prog/check_round_trip_ccf.v and LLVMFuzzerTestOneInput_cfb.v
   (25e3d17bdb50). check_no_overread_contract_cf is the statement of lib/U/Prog/check_no_overread_ccf.v
   (check_no_overread_contract_cf) and check_lookup_contract_cf that of lib/U/Prog/check_lookup_ccf.v
   (check_lookup_contract_cf), with the names prefixed by lt_, taken as given until those files land: each is its
   lane's SR contract with SRcf B in place of SR segs and the allocator's agreement budget (CAP_AG, 2 ^ 29) in
   place of the halting one (CAPMAX, 2 ^ 40). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YI06 YI16 YI14 YL01.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YM05 YL0i YL00 YL0g.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import Contract Img0 SlotAgree AgreeLift.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require Import FrameRet AgreeRet check_no_overread_c check_lookup_c
  LLVMFuzzerTestOneInput_c.
Import ListNotations.
Local Open Scope Z_scope.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Let MR := aa_MR API.

(* the allocator's agreement budget, as fuzz_decode's LLVMFuzzerTestOneInput_cfb.v states it *)
Definition llvm_room_cf (b : sbound) : Prop :=
  sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ 128 <= sb_cap b <= CAP_AG.

Definition llvm_ls_laws_cf : Prop :=
  (forall pl fs (K : lleaf -> TSet), t_eq (LIBK pl fs K) (K (LL (lock_ret pl) fs []))) /\
  (forall b n, lib_room b n -> llvm_room_cf b) /\
  (forall n b, lib_delta n b = b).

Definition LLVMFuzzerTestOneInput_contract_cg : Prop :=
  llvm_binds B API -> llvm_ls_laws_cf ->
  forall j, (j < 4)%nat ->
  forall ra empty stk, LLVM_K <= stk -> YK0s.ret_ok (Z_to_bv 64 ra) ->
    lib_contract_cgr B API lock_ret llvm_G llvm_RELRO llvm_GI j LLVM_ENTRY ra empty stk.

Definition LLVMFuzzerTestOneInput_sr_contract_cf : Prop :=
  llvm_binds B API ->
  forall j, (j < 4)%nat ->
  forall ra empty stk, LLVM_K <= stk -> YK0s.ret_ok (Z_to_bv 64 ra) ->
  forall L A regs mem md p n pl b,
    lib_pre B API stk empty L A regs mem md ra p n ->
    n = Z.of_nat (length pl) -> blk_data B mem p pl ->
    sink_none B mem md -> spZ regs <= 2 ^ 47 ->
    res_ok_slots A b ->
    llvm_room_cf b ->
    ro_agree rsegs mem -> G_img_c B llvm_RELRO mem ->
    llvm_GI j mem ->
    frm_zero fp_csr ->
    SRcf B (mkCfg (mkst regs (Z_to_bv 64 LLVM_ENTRY) mem (seg_rom segs)) md)
      (llvm_post B API (lock_ret pl) stk L A regs mem md ra p n b j).

End K.
