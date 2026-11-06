(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Frame Exec Cfg ITree Nodes RegsEquiv FP.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib Require Import TopLevel.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AS Require SpinAlg ShapeAlg.
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
Definition tfam_no_kill (T : tfam) : Prop :=
  forall inp en tr, T inp en tr -> forall sig fs, ~ In (KillEv sig fs) tr.

Lemma tfam_no_kill_tree : forall {R : Type} segs lim (t : prog_tree R),
  tfam_no_kill (fun inp en => tree_traces (t inp en) (mo0 segs lim en inp)).
Proof. intros R segs lim t inp en tr H. exact (tree_traces_no_kill _ _ _ H). Qed.

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
