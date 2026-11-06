(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section Rows.
  Variable cfg : SpuriousCfg.
  Variables O1 O2 C : Image.

  Definition accepts_all : Prop :=
    forall f : FinProcInput, valid_fin_input f ->
    forall en, valid_entry C en (to_proc_input f) ->
      must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en (to_proc_input f).

  Hypothesis BASE : strong_universal_error_free_T_scfg cfg O1 O2.
  Hypothesis ACC : accepts_all.

  Lemma good_of_base : forall inp, valid_input inp -> good_input_s cfg O1 O2 inp.
  Proof.
    intros inp Hinp en1 en2 H1 H2. exact (BASE en1 en2 inp H1 H2 Hinp).
  Qed.

  Theorem ca_iff_of_base : classifies_good_inputs_T_s cfg O1 O2 C.
  Proof.
    intros f Hf en Hen. split.
    - split; intros _; [exact (good_of_base _ Hf) | exact (ACC f Hf en Hen)].
    - left. exact (ACC f Hf en Hen).
  Qed.

  Hypothesis O1_brk : image_brk_satisfiable (img_segments O1) = true.
  Hypothesis O2_brk : image_brk_satisfiable (img_segments O2) = true.

  Lemma agree_self_O1 : forall inp, valid_input inp -> agree_s cfg O1 O1 source_alloc_limit inp.
  Proof.
    intros inp Hinp.
    destruct (image_brk_satisfiable_entry O2 inp Hinp O2_brk) as [en2 Hen2].
    split; [| split; [| split]]; try tauto.
    intros enX enY HX HY tr.
    destruct (BASE enX en2 inp HX Hen2 Hinp) as (_ & _ & TX).
    destruct (BASE enY en2 inp HY Hen2 Hinp) as (_ & _ & TY).
    rewrite (TX tr), (TY tr). tauto.
  Qed.

  Lemma agree_self_O2 : forall inp, valid_input inp -> agree_s cfg O2 O2 target_alloc_limit inp.
  Proof.
    intros inp Hinp.
    destruct (image_brk_satisfiable_entry O1 inp Hinp O1_brk) as [en1 Hen1].
    split; [| split; [| split]]; try tauto.
    intros enX enY HX HY tr.
    destruct (BASE en1 enX inp Hen1 HX Hinp) as (_ & _ & TX).
    destruct (BASE en1 enY inp Hen1 HY Hinp) as (_ & _ & TY).
    rewrite <- (TX tr), <- (TY tr). tauto.
  Qed.

  Theorem cb_iff_of_base : classifies_patch_diff_T_s cfg O1 O1 O2 O2 C.
  Proof.
    intros f Hf en Hen. split.
    - split; intros _.
      + split; [exact (agree_self_O1 _ Hf) | exact (agree_self_O2 _ Hf)].
      + exact (ACC f Hf en Hen).
    - left. exact (ACC f Hf en Hen).
  Qed.
End Rows.

Section RejectRows.
  Variable cfg : SpuriousCfg.
  Variables O1 O2 C : Image.

  Definition rejects_all : Prop :=
    forall f : FinProcInput, valid_fin_input f ->
    forall en, valid_entry C en (to_proc_input f) ->
      must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit en (to_proc_input f).

  Hypothesis REJ : rejects_all.
  Hypothesis BAD : forall inp, valid_input inp -> ~ good_input_s cfg O1 O2 inp.

End RejectRows.
