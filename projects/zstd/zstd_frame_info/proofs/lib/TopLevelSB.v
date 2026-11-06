(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib Require Import TopLevel.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import TopLevelGen.

Theorem side_ok_equiv_L :
  forall (L : Z) (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
         (segsT : list Segment) (pcT : N) (phT : PhdrInfo) (TS TT : tfam),
    side_ok segsS pcS phS L TS ->
    side_ok segsT pcT phT target_alloc_limit TT ->
    (forall enS enT inp,
        valid_entry (mkImage segsS pcS phS) enS inp ->
        valid_entry (mkImage segsT pcT phT) enT inp ->
        valid_input_either inp ->
        trace_equiv (TS inp enS) (TT inp enT)) ->
    forall enS enT inp,
      valid_entry (mkImage segsS pcS phS) enS inp ->
      valid_entry (mkImage segsT pcT phT) enT inp ->
      valid_input inp ->
      strong_equiv_error_free_budgets_scfg ACFG L target_alloc_limit (mkImage segsS pcS phS) (mkImage segsT pcT phT) enS enT inp.
Proof.
  intros L segsS pcS phS segsT pcT phT TS TT HS HT HEQ enS enT inp HvS HvT Hvi0.
  pose proof (valid_input_either_of_valid_input _ Hvi0) as Hvi.
  destruct (HS enS inp HvS Hvi) as [HtrS HerrS].
  destruct (HT enT inp HvT Hvi) as [HtrT HerrT].
  split; [exact HerrS|]. split; [exact HerrT|].
  eapply trace_equiv_trans; [exact HtrS|].
  eapply trace_equiv_trans; [exact (HEQ enS enT inp HvS HvT Hvi)|].
  apply trace_equiv_sym. exact HtrT.
Qed.

Theorem side_ok_equiv_budgets_L :
  forall (L : Z) (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
         (segsT : list Segment) (pcT : N) (phT : PhdrInfo) (TS TT : tfam),
    side_ok segsS pcS phS L TS ->
    side_ok segsT pcT phT target_alloc_limit TT ->
    (forall enS enT inp,
        valid_entry (mkImage segsS pcS phS) enS inp ->
        valid_entry (mkImage segsT pcT phT) enT inp ->
        valid_input_either inp ->
        trace_equiv (TS inp enS) (TT inp enT)) ->
    strong_universal_error_free_T_scfg_budgets ACFG L target_alloc_limit (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof.
  intros L segsS pcS phS segsT pcT phT TS TT HS HT HEQ enS enT inp HvS HvT Hvi _.
  exact (side_ok_equiv_L L segsS pcS phS segsT pcT phT TS TT HS HT HEQ enS enT inp HvS HvT Hvi).
Qed.

(* [comment removed for export] *)
Theorem side_ok_equiv_sb :
  forall (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
         (segsT : list Segment) (pcT : N) (phT : PhdrInfo) (TS TT : tfam),
    side_ok segsS pcS phS sanitizer_source_limit TS ->
    side_ok segsT pcT phT target_alloc_limit TT ->
    (forall enS enT inp,
        valid_entry (mkImage segsS pcS phS) enS inp ->
        valid_entry (mkImage segsT pcT phT) enT inp ->
        valid_input_either inp ->
        trace_equiv (TS inp enS) (TT inp enT)) ->
    strong_universal_error_free_T_scfg_budgets (alloc_only_cfg false) SanitizerBudgets.lim_source SanitizerBudgets.lim_target
      (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof.
  intros segsS pcS phS segsT pcT phT TS TT HS HT HEQ.
  cbv delta [SanitizerBudgets.lim_source SanitizerBudgets.lim_target].
  exact (side_ok_equiv_budgets_L sanitizer_source_limit segsS pcS phS segsT pcT phT TS TT HS HT HEQ).
Qed.
