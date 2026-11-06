(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.skcms.iccprofile_info.images Require Import Plain.
From OSSVerify.skcms.iccprofile_info.images Require Import Ubsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec ShapeAlg ShapeEF Spec ProofInfoPlan.
Unset Nia Cache.  (* [comment removed for export] *)
Unset Lia Cache.
#[local] Existing Instance PropExec.fp0.

(* [comment removed for export] *)
Lemma traces_entry_indep : forall (segs : list Segment) (pc : N) (ph : PhdrInfo) (lim : Z),
  realizes_spec_stmt segs pc ph lim ->
  forall inp, valid_input inp ->
  forall en1 en2,
    valid_entry (mkImage segs pc ph) en1 inp -> valid_entry (mkImage segs pc ph) en2 inp ->
    trace_equiv (bh_traces (run_scfg CFG (mkImage segs pc ph) lim en1 inp))
                (bh_traces (run_scfg CFG (mkImage segs pc ph) lim en2 inp)).
Proof.
  intros segs pc ph lim RZ inp Hvalid [sp1 brk1 mb1 rnd1] [sp2 brk2 mb2 rnd2] He1 He2 tr.
  (* [comment removed for export] *)
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in He1. rewrite (valid_entry_sv48 _ _ _ Hsv48) in He2.
  destruct He1 as (Hsp1 & Hbrk1 & _ & Hfit1). destruct He2 as (Hsp2 & Hbrk2 & _ & Hfit2).
  destruct Hvalid as (Hargv & Henvp & Hfs & _).
  pose proof (RZ sp1 brk1 mb1 rnd1 inp Hsp1 Hbrk1 Hfit1 Hargv Henvp Hfs) as R1.
  pose proof (RZ sp2 brk2 mb2 rnd2 inp Hsp2 Hbrk2 Hfit2 Hargv Henvp Hfs) as R2.
  cbn.
  rewrite (realizes_obs_iff segs _ _ R1 tr).
  rewrite (realizes_obs_iff segs _ _ R2 tr).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma agree_s_self : forall (segs : list Segment) (pc : N) (ph : PhdrInfo) (lim : Z),
  realizes_spec_stmt segs pc ph lim ->
  forall inp, valid_input inp ->
  agree_s CFG (mkImage segs pc ph) (mkImage segs pc ph) lim inp.
Proof.
  intros segs pc ph lim RZ inp Hinp.
  split; [| split; [| split]].
  - intros enX enY HX HY. exact (traces_entry_indep segs pc ph lim RZ inp Hinp enX enY HX HY).
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Section Rows.
  Hypothesis REF : realizes_spec_stmt SSEGS SPC SPH source_alloc_limit.
  Hypothesis UB : realizes_spec_stmt TSEGS TPC TPH target_alloc_limit.

  (* [comment removed for export] *)
  Theorem ca_iff_info_ubsan : forall (C : Image),
    (forall inp en, valid_input inp -> valid_entry C en inp ->
       must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en inp) ->
    classifies_good_inputs_T_s CFG (mkImage SSEGS SPC SPH) (mkImage TSEGS TPC TPH) C.
  Proof.
    intros C MX f Hf en Hen.
    pose proof (MX (to_proc_input f) en Hf Hen) as Hacc.
    split; [split | left; exact Hacc].
    - intros _ en1 en2 H1 H2.
      exact (info_ubsan_scfg REF UB en1 en2 (to_proc_input f) H1 H2 Hf).
    - intros _. exact Hacc.
  Qed.

  (* [comment removed for export] *)
  Theorem cb_iff_info_ubsan : forall (C : Image),
    (forall inp en, valid_input inp -> valid_entry C en inp ->
       must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en inp) ->
    classifies_patch_diff_T_s CFG (mkImage SSEGS SPC SPH) (mkImage SSEGS SPC SPH)
                                  (mkImage TSEGS TPC TPH) (mkImage TSEGS TPC TPH) C.
  Proof.
    intros C MX f Hf en Hen.
    pose proof (MX (to_proc_input f) en Hf Hen) as Hacc.
    split; [split | left; exact Hacc].
    - intros _. split.
      + exact (agree_s_self SSEGS SPC SPH source_alloc_limit REF (to_proc_input f) Hf).
      + exact (agree_s_self TSEGS TPC TPH target_alloc_limit UB (to_proc_input f) Hf).
    - intros _. exact Hacc.
  Qed.
End Rows.
