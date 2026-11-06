(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Frame Exec ITree Nodes RegsEquiv FP.
From OSSVerify.Proofs.zstd.simple_decompress.lib Require Import TopLevel.
From OSSVerify.Proofs.zstd.simple_decompress.lib.AS Require SpinAlg ShapeAlg.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition tfam : Type := ProcInput -> ExecEntry -> list event -> Prop.

Definition side_ok (segs : list Segment) (pc : N) (ph : PhdrInfo) (lim : Z) (T : tfam) : Prop :=
  forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
    trace_equiv (bh_traces (run_scfg ACFG (mkImage segs pc ph) lim en inp)) (T inp en)
    /\ ~ bh_errors (run_scfg ACFG (mkImage segs pc ph) lim en inp).

(* [comment removed for export] *)
Lemma run_init_config : forall segs pc ph lim en inp,
  run_scfg ACFG (mkImage segs pc ph) lim en inp =
  {| bh_traces := obs_trace_cfg segs ACFG (init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp);
     bh_errors := reaches_error_cfg segs ACFG (init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp);
     bh_all_errors := all_traces_error_cfg segs ACFG (init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp);
     bh_unmodeled := reaches_unmodeled_cfg segs ACFG (init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp) |}.
Proof. intros segs pc ph lim [sp brk mb rnd] inp. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem side_ok_equiv :
  forall (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
         (segsT : list Segment) (pcT : N) (phT : PhdrInfo) (TS TT : tfam),
    side_ok segsS pcS phS source_alloc_limit TS ->
    side_ok segsT pcT phT target_alloc_limit TT ->
    (forall enS enT inp,
        valid_entry (mkImage segsS pcS phS) enS inp ->
        valid_entry (mkImage segsT pcT phT) enT inp ->
        valid_input_either inp ->
        trace_equiv (TS inp enS) (TT inp enT)) ->
    strong_universal_error_free_T_scfg ACFG (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof.
  intros segsS pcS phS segsT pcT phT TS TT HS HT HEQ enS enT inp HvS HvT Hvi0.
  pose proof (valid_input_either_of_valid_input _ Hvi0) as Hvi.
  destruct (HS enS inp HvS Hvi) as [HtrS HerrS].
  destruct (HT enT inp HvT Hvi) as [HtrT HerrT].
  split; [exact HerrS|]. split; [exact HerrT|].
  eapply trace_equiv_trans; [exact HtrS|].
  eapply trace_equiv_trans; [exact (HEQ enS enT inp HvS HvT Hvi)|].
  apply trace_equiv_sym. exact HtrT.
Qed.

(* [comment removed for export] *)
Theorem side_ok_equiv_budgets :
  forall (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
         (segsT : list Segment) (pcT : N) (phT : PhdrInfo) (TS TT : tfam),
    side_ok segsS pcS phS source_alloc_limit TS ->
    side_ok segsT pcT phT target_alloc_limit TT ->
    (forall enS enT inp,
        valid_entry (mkImage segsS pcS phS) enS inp ->
        valid_entry (mkImage segsT pcT phT) enT inp ->
        valid_input_either inp ->
        trace_equiv (TS inp enS) (TT inp enT)) ->
    strong_universal_error_free_T_scfg_budgets ACFG ShippedBudgets.lim_source ShippedBudgets.lim_target
      (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof.
  intros segsS pcS phS segsT pcT phT TS TT HS HT HEQ.
  cbv delta [ShippedBudgets.lim_source ShippedBudgets.lim_target].
  apply strong_universal_error_free_T_scfg_budgets_of_scfg.
  exact (side_ok_equiv segsS pcS phS segsT pcT phT TS TT HS HT HEQ).
Qed.

(* [comment removed for export] *)
Definition tfam_no_kill (T : tfam) : Prop :=
  forall inp en tr, T inp en tr -> forall sig fs, ~ In (KillEv sig fs) tr.

Lemma tfam_no_kill_tree : forall {R : Type} segs lim (t : prog_tree R),
  tfam_no_kill (fun inp en => tree_traces (t inp en) (mo0 segs lim en inp)).
Proof. intros R segs lim t inp en tr H. exact (tree_traces_no_kill _ _ _ H). Qed.

(* [comment removed for export] *)
Theorem side_ok_equiv_budgets_abort :
  forall (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
         (segsT : list Segment) (pcT : N) (phT : PhdrInfo) (TS TT : tfam),
    side_ok segsS pcS phS source_alloc_limit TS ->
    side_ok segsT pcT phT target_alloc_limit TT ->
    tfam_no_kill TS ->
    (forall enS enT inp,
        valid_entry (mkImage segsS pcS phS) enS inp ->
        valid_entry (mkImage segsT pcT phT) enT inp ->
        valid_input_either inp ->
        trace_equiv (TS inp enS) (TT inp enT)) ->
    strong_universal_error_free_T_scfg_budgets_abort ACFG ShippedBudgets.lim_source ShippedBudgets.lim_target
      (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof.
  intros segsS pcS phS segsT pcT phT TS TT HS HT HNK HEQ.
  cbv delta [ShippedBudgets.lim_source ShippedBudgets.lim_target].
  apply strong_universal_error_free_T_scfg_budgets_abort_of_scfg.
  intros enS enT inp HvS HvT Hvi0.
  pose proof (valid_input_either_of_valid_input_abort _ Hvi0) as Hvi.
  destruct (HS enS inp HvS Hvi) as [HtrS HerrS].
  destruct (HT enT inp HvT Hvi) as [HtrT HerrT].
  pose proof (HEQ enS enT inp HvS HvT Hvi) as Hst.
  split; [| split].
  - split; [exact HerrS|]. intros (tr & sig & fs & Hb & Hin).
    apply (proj1 (HtrS tr)) in Hb. exact (HNK _ _ _ Hb sig fs Hin).
  - split; [exact HerrT|]. intros (tr & sig & fs & Hb & Hin).
    apply (proj1 (HtrT tr)) in Hb. apply (proj2 (Hst tr)) in Hb. exact (HNK _ _ _ Hb sig fs Hin).
  - eapply trace_equiv_trans; [exact HtrS|].
    eapply trace_equiv_trans; [exact Hst|].
    apply trace_equiv_sym. exact HtrT.
Qed.

(* [comment removed for export] *)
Corollary side_ok_equiv_base :
  forall (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
         (segsT : list Segment) (pcT : N) (phT : PhdrInfo) (TS TT : tfam),
    side_ok segsS pcS phS source_alloc_limit TS ->
    side_ok segsT pcT phT target_alloc_limit TT ->
    (forall enS enT inp,
        valid_entry (mkImage segsS pcS phS) enS inp ->
        valid_entry (mkImage segsT pcT phT) enT inp ->
        valid_input_either inp ->
        trace_equiv (TS inp enS) (TT inp enT)) ->
    strong_universal_T_scfg ACFG (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof.
  intros segsS pcS phS segsT pcT phT TS TT HS HT HEQ enS enT inp HvS HvT Hvi.
  apply strong_equiv_error_free_scfg_implies. eapply side_ok_equiv; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma side_ok_of_tree_ok : forall {R : Type} segs pc ph lim (t : prog_tree R) (Q : R -> machine_state -> Prop),
  tree_ok segs pc ph lim t Q ->
  side_ok segs pc ph lim (fun inp en => tree_traces (t inp en) (mo0 segs lim en inp)).
Proof.
  intros R segs pc ph lim t Q HT en inp Hv Hi.
  destruct (HT en inp Hv Hi) as (Himpl & Hleaves & Hsafe).
  destruct (run_of_tree segs pc ph lim (t inp en) Q en inp Hv (valid_input_either_va_size _ Hi) Himpl Hleaves Hsafe) as (Htr & Herr & _).
  split; [exact Htr| exact Herr].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma side_ok_of_srealizes : forall segs pc ph lim (T : tfam),
  (forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
      SpinAlg.srealizes segs (init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp) (T inp en)) ->
  side_ok segs pc ph lim T.
Proof.
  intros segs pc ph lim T H en inp Hv Hi. specialize (H en inp Hv Hi).
  rewrite run_init_config. cbn [bh_traces bh_errors]. split.
  - intros tr. apply SpinAlg.srealizes_obs_iff. exact H.
  - eapply SpinAlg.srealizes_no_error. exact H.
Qed.

(* [comment removed for export] *)
Lemma side_ok_of_srealizes_eq : forall segs pc ph lim (T T' : tfam),
  (forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
      SpinAlg.srealizes segs (init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp) (T' inp en)
      /\ ShapeAlg.t_eq (T' inp en) (T inp en)) ->
  side_ok segs pc ph lim T.
Proof.
  intros segs pc ph lim T T' H. apply side_ok_of_srealizes.
  intros en inp Hv Hi. destruct (H en inp Hv Hi) as [Hs Heq].
  eapply SpinAlg.srz_conseq; [exact Hs| exact Heq].
Qed.
