(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import LiaTuning.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import GlueCfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Section Glue.
Variable cfg : SpuriousCfg.

Theorem strong_universal_error_free_budgets_of_realizes_cfg :
  forall (ls lt : Z)
         (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
         (segsT : list Segment) (pcT : N) (phT : PhdrInfo)
         (T : ProcInput -> TSet),
    realizes_spec_cfg cfg segsS pcS phS ls T ->
    realizes_spec_cfg cfg segsT pcT phT lt T ->
    strong_universal_error_free_T_scfg_budgets cfg ls lt
      (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof.
  intros ls lt segsS pcS phS segsT pcT phT T HS HT enS enT inp HvS HvT Hvi _.
  destruct (run_scfg_of_realizes_spec cfg segsS pcS phS ls T enS inp HS HvS Hvi) as [HeS HtS].
  destruct (run_scfg_of_realizes_spec cfg segsT pcT phT lt T enT inp HT HvT Hvi) as [HeT HtT].
  split; [exact HeS |]. split; [exact HeT |].
  intros tr. rewrite (HtS tr), (HtT tr). reflexivity.
Qed.

Corollary strong_universal_error_free_budgets_of_realizes_cfg_shipped :
  forall segsS pcS phS segsT pcT phT (T : ProcInput -> TSet),
    realizes_spec_cfg cfg segsS pcS phS source_alloc_limit T ->
    realizes_spec_cfg cfg segsT pcT phT target_alloc_limit T ->
    strong_universal_error_free_T_scfg_budgets cfg ShippedBudgets.lim_source ShippedBudgets.lim_target
      (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof. intros. apply strong_universal_error_free_budgets_of_realizes_cfg with (T := T); assumption. Qed.

Corollary strong_universal_error_free_budgets_of_realizes_cfg_sanitizer :
  forall segsS pcS phS segsT pcT phT (T : ProcInput -> TSet),
    realizes_spec_cfg cfg segsS pcS phS sanitizer_source_limit T ->
    realizes_spec_cfg cfg segsT pcT phT target_alloc_limit T ->
    strong_universal_error_free_T_scfg_budgets cfg SanitizerBudgets.lim_source SanitizerBudgets.lim_target
      (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof. intros. apply strong_universal_error_free_budgets_of_realizes_cfg with (T := T); assumption. Qed.

End Glue.

Lemma sanitizer_source_limit_val : sanitizer_source_limit = 2147483648%Z.
Proof. reflexivity. Qed.

Lemma source_alloc_limit_val : source_alloc_limit = 17179869184%Z.
Proof. reflexivity. Qed.

Lemma target_alloc_limit_val : target_alloc_limit = 549755813888%Z.
Proof. reflexivity. Qed.
