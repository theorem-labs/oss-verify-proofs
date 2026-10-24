(* SPDX-License-Identifier: MIT *)
(** The remaining exact full-target obligation, isolated to valid-size payloads.
    This module proves a reduction, not the remaining contract itself. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.zlib.checksum_fuzzer Require Statements.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
  YK11 YK0o YK15 YM05 YO0d YO09 YH02 YI5b YI5c YL0g YL0i YL0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib Require Import
  ZImage ZTraceSpec ZComplete ZAllocator ZBoundaryContract.
Open Scope Z_scope.
Section Valid.
Context {rc : RunCeil} {fx : FPState}.
Definition valid_checksum_contract : Prop := forall L A regs mem md p n pl b (K : lleaf -> TSet),
  lib_pre_x src0_msyms zlib_API LIB_STACK EMPTY L A regs mem md RA_LIB p n pl b ->
  (1 <= n <= 1048576) -> frm_zero fp_csr ->
  (forall l c',
    (exists (fx' : FPState) L' A' regs' mem' md',
      c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 RA_LIB) mem' (seg_rom zsegs)) md' /\
      frm_zero (@fp_csr fx') /\
      lib_post_x src0_msyms zlib_API LIB_STACK L A regs mem md p n b l L' A' regs' mem' md') ->
    realizes zsegs c' (K l)) ->
  realizes zsegs (mkCfg (mkst regs (Z_to_bv 64 LIBPC) mem (seg_rom zsegs)) md)
    (LIBK pl (m_fs md) K).
End Valid.
Definition all_valid_checksum_contracts : Prop := forall rc fx,
  @valid_checksum_contract rc fx.
Theorem zlib_checksum_from_valid :
  all_valid_checksum_contracts -> zlib_checksum_contract.
Proof.
  intros HV rc fx L A regs mem md p n pl b K HP Hfrm HK.
  assert (Hnonneg : 0 <= n).
  { destruct HP as [_ [Hlen _]]. rewrite Hlen. lia. }
  destruct (Z_le_gt_dec n 1048576) as [Hsmall|Hlarge].
  - destruct (Z.eq_dec n 0) as [Hz|Hpos].
    + eapply checksum_boundary_contract; [exact HP|left;exact Hz|exact Hfrm|exact HK].
    + exact (HV rc fx L A regs mem md p n pl b K HP ltac:(lia) Hfrm HK).
  - eapply checksum_boundary_contract; [exact HP|right;lia|exact Hfrm|exact HK].
Qed.
Theorem plain_halts_from_valid_checksum :
  all_valid_checksum_contracts -> Statements.plain_halts.
Proof.
  intros H. apply plain_halts_from_runtime_contracts, runtime_contracts_from_checksum,
    zlib_checksum_from_valid. exact H.
Qed.
