(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import
  Equivalence MustExit FinInput Classifier.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

Section Generic.
  Variable cfg : SpuriousCfg.
  Variables O1 O2 C : Image.

  (* [comment removed for export] *)
  Hypothesis Hbase : strong_universal_error_free_T_scfg cfg O1 O2.
  (* [comment removed for export] *)
  Hypothesis Hsat1 : image_brk_satisfiable (img_segments O1) = true.
  Hypothesis Hsat2 : image_brk_satisfiable (img_segments O2) = true.
  (* [comment removed for export] *)
  Hypothesis HC : forall inp en,
      valid_input inp -> valid_entry C en inp ->
      must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en inp.

  Lemma good_input_all : forall inp, valid_input inp -> good_input_s cfg O1 O2 inp.
  Proof.
    intros inp Hv en1 en2 H1 H2. exact (Hbase en1 en2 inp H1 H2 Hv).
  Qed.

  Lemma agree_self_source : forall inp,
      valid_input inp -> agree_s cfg O1 O1 source_alloc_limit inp.
  Proof.
    intros inp Hv.
    destruct (image_brk_satisfiable_entry O2 inp Hv Hsat2) as [en2 Hen2].
    split; [| split; [| split]]; try (split; intro H; exact H).
    intros enX enY HX HY tr.
    destruct (Hbase enX en2 inp HX Hen2 Hv) as (_ & _ & HXe).
    destruct (Hbase enY en2 inp HY Hen2 Hv) as (_ & _ & HYe).
    split; intro Htr.
    - apply (proj2 (HYe tr)). apply (proj1 (HXe tr)). exact Htr.
    - apply (proj2 (HXe tr)). apply (proj1 (HYe tr)). exact Htr.
  Qed.

  Lemma agree_self_target : forall inp,
      valid_input inp -> agree_s cfg O2 O2 target_alloc_limit inp.
  Proof.
    intros inp Hv.
    destruct (image_brk_satisfiable_entry O1 inp Hv Hsat1) as [en1 Hen1].
    split; [| split; [| split]]; try (split; intro H; exact H).
    intros enX enY HX HY tr.
    destruct (Hbase en1 enX inp Hen1 HX Hv) as (_ & _ & HXe).
    destruct (Hbase en1 enY inp Hen1 HY Hv) as (_ & _ & HYe).
    split; intro Htr.
    - apply (proj1 (HYe tr)). apply (proj2 (HXe tr)). exact Htr.
    - apply (proj1 (HXe tr)). apply (proj2 (HYe tr)). exact Htr.
  Qed.

  Theorem clf_total : classifier_total_T_fo C.
  Proof.
    intros f Hf en Hen. left. exact (HC _ _ Hf Hen).
  Qed.

  Theorem clf_good_inputs : classifies_good_inputs_T_s cfg O1 O2 C.
  Proof.
    intros f Hf en Hen. split.
    - split.
      + intros _. exact (good_input_all _ Hf).
      + intros _. exact (HC _ _ Hf Hen).
    - left. exact (HC _ _ Hf Hen).
  Qed.

  Theorem clf_patch_diff : classifies_patch_diff_T_s cfg O1 O1 O2 O2 C.
  Proof.
    intros f Hf en Hen. split.
    - split.
      + intros _. split; [exact (agree_self_source _ Hf) | exact (agree_self_target _ Hf)].
      + intros _. exact (HC _ _ Hf Hen).
    - left. exact (HC _ _ Hf Hen).
  Qed.
End Generic.

(* [comment removed for export] *)
Lemma clf_total_only : forall C,
    (forall inp en, valid_input inp -> valid_entry C en inp ->
        must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en inp) ->
    classifier_total_T_fo C.
Proof.
  intros C HC f Hf en Hen. left. exact (HC _ _ Hf Hen).
Qed.
