(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only Require Import TopLevel.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import TopLevelGen.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import Prog ModelInv ImgFacts ModelOK EquivPA.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Plain Require Import PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.FO Require Import FOCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Theorem side_ok_equiv_budgets :
  forall (limS limT : Z) (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
         (segsT : list Segment) (pcT : N) (phT : PhdrInfo) (TS TT : tfam),
    side_ok segsS pcS phS limS TS ->
    side_ok segsT pcT phT limT TT ->
    (forall enS enT inp,
        valid_entry (mkImage segsS pcS phS) enS inp ->
        valid_entry (mkImage segsT pcT phT) enT inp ->
        valid_input_either inp ->
        trace_equiv (TS inp enS) (TT inp enT)) ->
    strong_universal_error_free_T_scfg_budgets alloc_forced_cfg limS limT
      (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof.
  intros limS limT segsS pcS phS segsT pcT phT TS TT HS HT HEQ enS enT inp HvS HvT Hvi0 _.
  pose proof (valid_input_either_of_valid_input _ Hvi0) as Hvi.
  destruct (HS enS inp HvS Hvi) as [HtrS HerrS].
  destruct (HT enT inp HvT Hvi) as [HtrT HerrT].
  split; [exact HerrS|]. split; [exact HerrT|].
  eapply trace_equiv_trans; [exact HtrS|].
  eapply trace_equiv_trans; [exact (HEQ enS enT inp HvS HvT Hvi)|].
  apply trace_equiv_sym. exact HtrT.
Qed.


Definition plain_impl_stmt : Prop :=
  forall (en : ExecEntry) (inp : ProcInput),
    valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
    impl psegs (at_node psegs) (Prog.prog psegs PREAD_STAGE inp en) (epost (fun (_ : unit) (_ : machine_state) => True))
         (ms0 psegs p_init_pc p_phdrs en inp).

Definition TP (lim : Z) : tfam := fun inp en => tree_traces (prog psegs PREAD_STAGE inp en) (mo0 psegs lim en inp).
Definition TA (lim : Z) : tfam := fun inp en => tree_traces (prog psegs PREAD_STAGE inp (toP en)) (mo0 psegs lim (toP en) inp).

Definition asan_side_stmt (segsX : list Segment) (pcX : N) (phX : PhdrInfo) : Prop :=
  forall lim, 2^31 <= lim -> side_ok segsX pcX phX target_alloc_limit (TA lim).

Section Plain.
  Hypothesis plain_impl : plain_impl_stmt.

  Lemma plain_tree_ok : forall lim, 2^31 <= lim ->
    tree_ok psegs p_init_pc p_phdrs lim
            (Prog.prog psegs PREAD_STAGE) (epost (fun (_ : unit) (_ : machine_state) => True)).
  Proof.
    intros lim Hlim en inp Hen Hinp. split.
    - exact (plain_impl en inp Hen Hinp).
    - exact (prog_model_ok_plain_L lim PREAD_STAGE en inp Hlim Hen Hinp).
  Qed.

  Lemma plain_side_ok : forall lim, 2^31 <= lim -> side_ok psegs p_init_pc p_phdrs lim (TP lim).
  Proof. intros lim Hlim. exact (side_ok_of_tree_ok _ _ _ _ _ _ (plain_tree_ok lim Hlim)). Qed.

  Section AsanSide.
    Variables (segsX : list Segment) (pcX : N) (phX : PhdrInfo).
    Hypothesis asan_side : asan_side_stmt segsX pcX phX.

    Lemma middle : forall lim, 2^31 <= lim -> forall enS enT inp,
      valid_entry (mkImage psegs p_init_pc p_phdrs) enS inp -> valid_entry (mkImage segsX pcX phX) enT inp -> valid_input_either inp ->
      trace_equiv (TP lim inp enS) (TA lim inp enT).
    Proof.
      intros lim Hlim enS enT inp HvS HvT Hi. unfold TP, TA.
      apply (equiv_PP lim Hlim); [exact HvS | exact (toP_valid _ _ _ enT inp HvT) | exact Hi].
    Qed.

    Theorem z_base_asan_plain :
      strong_universal_error_free_T_scfg alloc_forced_cfg (mkImage psegs p_init_pc p_phdrs) (mkImage segsX pcX phX).
    Proof. exact (side_ok_equiv _ _ _ _ _ _ (TP source_alloc_limit) (TA source_alloc_limit) (plain_side_ok _ lim_p) (asan_side _ lim_p) (middle _ lim_p)). Qed.

    Theorem z_base_asan :
      strong_universal_error_free_T_scfg_budgets alloc_forced_cfg SanitizerBudgets.lim_source SanitizerBudgets.lim_target
        (mkImage psegs p_init_pc p_phdrs) (mkImage segsX pcX phX).
    Proof.
      exact (side_ok_equiv_budgets sanitizer_source_limit target_alloc_limit _ _ _ _ _ _ (TP sanitizer_source_limit) (TA sanitizer_source_limit)
               (plain_side_ok _ lim_s) (asan_side _ lim_s) (middle _ lim_s)).
    Qed.
  End AsanSide.
End Plain.
