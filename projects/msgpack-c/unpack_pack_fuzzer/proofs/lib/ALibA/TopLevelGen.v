(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Frame Exec ITree Nodes RegsEquiv FP.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require Import TopLevel.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require SpinAlg ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Scfg Require Import Fcfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition tfam : Type := ProcInput -> ExecEntry -> list event -> Prop.

Definition side_ok (segs : list Segment) (pc : N) (ph : PhdrInfo) (lim : Z) (T : tfam) : Prop :=
  forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
    trace_equiv (bh_traces (run_scfg fcfg (mkImage segs pc ph) lim en inp)) (T inp en)
    /\ ~ bh_errors (run_scfg fcfg (mkImage segs pc ph) lim en inp).

Lemma run_init_config : forall segs pc ph lim en inp,
  run_scfg fcfg (mkImage segs pc ph) lim en inp =
  {| bh_traces := obs_trace_cfg segs fcfg (init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp);
     bh_errors := reaches_error_cfg segs fcfg (init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp);
     bh_all_errors := all_traces_error_cfg segs fcfg (init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp);
     bh_unmodeled := reaches_unmodeled_cfg segs fcfg (init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp) |}.
Proof. intros segs pc ph lim [sp brk mb rnd] inp. reflexivity. Qed.

Definition tfam_no_kill (T : tfam) : Prop :=
  forall inp en tr, T inp en tr -> forall sig fs, ~ In (KillEv sig fs) tr.

Lemma tfam_no_kill_tree : forall {R : Type} segs lim (t : prog_tree R),
  tfam_no_kill (fun inp en => tree_traces (t inp en) (mo0 segs lim en inp)).
Proof. intros R segs lim t inp en tr H. exact (tree_traces_no_kill _ _ _ H). Qed.

Definition side_ok_p (segs : list Segment) (pc : N) (ph : PhdrInfo) (lim : Z) (T : tfam) : Prop :=
  forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
    ~ run_scfg_budget_refused fcfg (mkImage segs pc ph) lim en inp ->
    trace_equiv (bh_traces (run_scfg fcfg (mkImage segs pc ph) lim en inp)) (T inp en)
    /\ ~ bh_errors (run_scfg fcfg (mkImage segs pc ph) lim en inp).

Lemma side_ok_p_of_side_ok : forall segs pc ph lim T, side_ok segs pc ph lim T -> side_ok_p segs pc ph lim T.
Proof. intros segs pc ph lim T H en inp Hv Hi _. exact (H en inp Hv Hi). Qed.

Theorem side_ok_equiv_budgets_abort_gen :
  forall (limS limT : Z)
         (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
         (segsT : list Segment) (pcT : N) (phT : PhdrInfo) (TS TT : tfam),
    side_ok_p segsS pcS phS limS TS ->
    side_ok segsT pcT phT limT TT ->
    tfam_no_kill TS ->
    (forall enS enT inp,
        valid_entry (mkImage segsS pcS phS) enS inp ->
        valid_entry (mkImage segsT pcT phT) enT inp ->
        valid_input_either inp ->
        trace_equiv (TS inp enS) (TT inp enT)) ->
    strong_universal_error_free_T_scfg_budgets_abort fcfg limS limT (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof.
  intros limS limT segsS pcS phS segsT pcT phT TS TT HS HT HNK HEQ enS enT inp HvS HvT Hvi0 HB.
  pose proof (valid_input_either_of_valid_input_abort _ Hvi0) as Hvi.
  destruct (HS enS inp HvS Hvi HB) as [HtrS HerrS].
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

Lemma side_ok_p_of_srealizes : forall segs pc ph lim (T : tfam),
  (forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
      ~ run_scfg_budget_refused fcfg (mkImage segs pc ph) lim en inp ->
      SpinAlg.srealizes segs (init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp) (T inp en)) ->
  side_ok_p segs pc ph lim T.
Proof.
  intros segs pc ph lim T H en inp Hv Hi HB. specialize (H en inp Hv Hi HB).
  rewrite run_init_config. cbn [bh_traces bh_errors]. split.
  - intros tr. apply SpinAlg.srealizes_obs_iff. exact H.
  - eapply SpinAlg.srealizes_no_error. exact H.
Qed.

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
