(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout Fs State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import ShapeSet RealizesCfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Rows.
Variable cfg : SpuriousCfg.

(* [comment removed for export] *)
#[using="Type"] Lemma good_input_s_of_realizes :
  forall s_segs spc sph t_segs tpc tph (Spec : ProcInput -> TSet) inp,
    image_realizes_cfg cfg s_segs spc sph source_alloc_limit Spec ->
    image_realizes_cfg cfg t_segs tpc tph target_alloc_limit Spec ->
    valid_input inp ->
    good_input_s cfg (mkImage s_segs spc sph) (mkImage t_segs tpc tph) inp.
Proof.
  intros s_segs spc sph t_segs tpc tph Spec inp HS HT Hinp
    [rsp rbrk rmb rrnd] [asp abrk amb arnd] Hvs Hvt.
  apply shape_strong_equiv_error_free_scfg with (T := Spec inp).
  - exact (HS rsp rbrk rmb rrnd inp Hvs Hinp).
  - exact (HT asp abrk amb arnd inp Hvt Hinp).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma agree_s_self_of_realizes :
  forall segs pc ph lim (Spec : ProcInput -> TSet) inp,
    image_realizes_cfg cfg segs pc ph lim Spec ->
    valid_input inp ->
    agree_s cfg (mkImage segs pc ph) (mkImage segs pc ph) lim inp.
Proof.
  intros segs pc ph lim Spec inp H Hinp.
  split; [| split; [tauto | split; tauto]].
  intros [sp1 b1 m1 r1] [sp2 b2 m2 r2] H1 H2 tr.
  cbn [run_scfg bh_traces].
  rewrite (realizes_cfg_obs_iff _ _ _ _ (H _ _ _ _ _ H1 Hinp) tr).
  rewrite (realizes_cfg_obs_iff _ _ _ _ (H _ _ _ _ _ H2 Hinp) tr).
  tauto.
Qed.

End Rows.

(* [comment removed for export] *)
Definition accepts_all (C : Image) : Prop :=
  forall f : FinProcInput,
    valid_fin_input f ->
    forall en,
      valid_entry C en (to_proc_input f) ->
      must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en (to_proc_input f).

Lemma total_of_accepts_all : forall C, accepts_all C -> classifier_total_T_fo C.
Proof. intros C HA f Hf en Hen. left. exact (HA f Hf en Hen). Qed.

(* [comment removed for export] *)
Lemma decides_fo_of_accepts_all : forall (C : Image) (spec : ProcInput -> Prop),
    accepts_all C ->
    (forall inp, valid_input inp -> spec inp) ->
    decides_fo C spec.
Proof.
  intros C spec HA HS f Hf en Hen. split.
  - split; intros _; [apply HS; exact Hf | exact (HA f Hf en Hen)].
  - left. exact (HA f Hf en Hen).
Qed.

(* [comment removed for export] *)
Theorem classifies_good_inputs_of_realizes :
  forall cfg s_segs spc sph t_segs tpc tph (Spec : ProcInput -> TSet) (C : Image),
    accepts_all C ->
    image_realizes_cfg cfg s_segs spc sph source_alloc_limit Spec ->
    image_realizes_cfg cfg t_segs tpc tph target_alloc_limit Spec ->
    classifies_good_inputs_T_s cfg (mkImage s_segs spc sph) (mkImage t_segs tpc tph) C.
Proof.
  intros cfg s_segs spc sph t_segs tpc tph Spec C HA HS HT.
  apply decides_fo_of_accepts_all; [exact HA |].
  intros inp Hinp. exact (good_input_s_of_realizes cfg _ _ _ _ _ _ Spec inp HS HT Hinp).
Qed.

(* [comment removed for export] *)
Theorem classifies_patch_diff_of_realizes :
  forall cfg x_segs xpc xph y_segs ypc yph (SpecX SpecY : ProcInput -> TSet) (C : Image),
    accepts_all C ->
    image_realizes_cfg cfg x_segs xpc xph source_alloc_limit SpecX ->
    image_realizes_cfg cfg y_segs ypc yph target_alloc_limit SpecY ->
    classifies_patch_diff_T_s cfg (mkImage x_segs xpc xph) (mkImage x_segs xpc xph)
                                  (mkImage y_segs ypc yph) (mkImage y_segs ypc yph) C.
Proof.
  intros cfg x_segs xpc xph y_segs ypc yph SpecX SpecY C HA HX HY.
  apply decides_fo_of_accepts_all; [exact HA |].
  intros inp Hinp. split.
  - exact (agree_s_self_of_realizes cfg _ _ _ _ SpecX inp HX Hinp).
  - exact (agree_s_self_of_realizes cfg _ _ _ _ SpecY inp HY Hinp).
Qed.
