(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Section Glue.
Variable cfg : SpuriousCfg.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition realizes_spec_cfg (segs : list Segment) (pc : N) (ph : PhdrInfo) (lim : Z)
           (T : ProcInput -> TSet) : Prop :=
  forall en inp,
    valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
    behaves_cfg cfg segs
      (init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp)
      (T inp).

(* [comment removed for export] *)
Lemma realizes_spec_cfg_intro : forall segs pc ph lim T,
  (forall en inp,
     valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
     realizes_cfg cfg segs
       (init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp)
       (T inp)) ->
  realizes_spec_cfg segs pc ph lim T.
Proof. intros segs pc ph lim T H en inp HE HI. apply realizes_cfg_behaves. apply H; assumption. Qed.

(* [comment removed for export] *)
Lemma run_scfg_of_realizes_spec : forall segs pc ph lim T en inp,
  realizes_spec_cfg segs pc ph lim T ->
  valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
  error_free (run_scfg cfg (mkImage segs pc ph) lim en inp)
  /\ (forall tr, bh_traces (run_scfg cfg (mkImage segs pc ph) lim en inp) tr <-> T inp tr).
Proof.
  intros segs pc ph lim T [sp brk0 mb dr] inp HR HE HI.
  exact (run_scfg_of_behaves cfg segs pc ph lim sp brk0 mb dr inp (T inp) (HR _ inp HE HI)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem strong_universal_error_free_of_realizes_cfg :
  forall (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
         (segsT : list Segment) (pcT : N) (phT : PhdrInfo)
         (T : ProcInput -> TSet),
    realizes_spec_cfg segsS pcS phS source_alloc_limit T ->
    realizes_spec_cfg segsT pcT phT target_alloc_limit T ->
    strong_universal_error_free_T_scfg cfg (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof.
  intros segsS pcS phS segsT pcT phT T HS HT enS enT inp HvS HvT Hvi.
  destruct (run_scfg_of_realizes_spec segsS pcS phS source_alloc_limit T enS inp HS HvS Hvi) as [HeS HtS].
  destruct (run_scfg_of_realizes_spec segsT pcT phT target_alloc_limit T enT inp HT HvT Hvi) as [HeT HtT].
  split; [exact HeS|]. split; [exact HeT|].
  intros tr. rewrite (HtS tr), (HtT tr). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma good_input_s_of_base : forall O1 O2,
  strong_universal_error_free_T_scfg cfg O1 O2 ->
  forall inp, valid_input inp -> good_input_s cfg O1 O2 inp.
Proof. intros O1 O2 Hbase inp Hv en1 en2 H1 H2. exact (Hbase en1 en2 inp H1 H2 Hv). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sat (X : Image) : Prop := image_brk_satisfiable (img_segments X) = true.

Lemma agree_s_self_source : forall O1 O2,
  strong_universal_error_free_T_scfg cfg O1 O2 -> sat O2 ->
  forall inp, valid_input inp -> agree_s cfg O1 O1 source_alloc_limit inp.
Proof.
  intros O1 O2 Hbase Hsat2 inp Hv.
  destruct (image_brk_satisfiable_entry O2 inp Hv Hsat2) as [en2 Hen2].
  split; [| split; [| split]]; try (split; intro H; exact H).
  intros enX enY HX HY tr.
  destruct (Hbase enX en2 inp HX Hen2 Hv) as (_ & _ & HXe).
  destruct (Hbase enY en2 inp HY Hen2 Hv) as (_ & _ & HYe).
  split; intro Htr.
  - apply (proj2 (HYe tr)). apply (proj1 (HXe tr)). exact Htr.
  - apply (proj2 (HXe tr)). apply (proj1 (HYe tr)). exact Htr.
Qed.

Lemma agree_s_self_target : forall O1 O2,
  strong_universal_error_free_T_scfg cfg O1 O2 -> sat O1 ->
  forall inp, valid_input inp -> agree_s cfg O2 O2 target_alloc_limit inp.
Proof.
  intros O1 O2 Hbase Hsat1 inp Hv.
  destruct (image_brk_satisfiable_entry O1 inp Hv Hsat1) as [en1 Hen1].
  split; [| split; [| split]]; try (split; intro H; exact H).
  intros enX enY HX HY tr.
  destruct (Hbase en1 enX inp Hen1 HX Hv) as (_ & _ & HXe).
  destruct (Hbase en1 enY inp Hen1 HY Hv) as (_ & _ & HYe).
  split; intro Htr.
  - apply (proj1 (HYe tr)). apply (proj2 (HXe tr)). exact Htr.
  - apply (proj1 (HXe tr)). apply (proj2 (HYe tr)). exact Htr.
Qed.

(* [comment removed for export] *)
Lemma agree_s_self_of_realizes_cfg : forall segs pc ph lim T,
  realizes_spec_cfg segs pc ph lim T ->
  forall inp, valid_input inp -> agree_s cfg (mkImage segs pc ph) (mkImage segs pc ph) lim inp.
Proof.
  intros segs pc ph lim T HR inp Hv.
  split; [| split; [| split]]; try (split; intro H; exact H).
  intros enX enY HX HY tr.
  destruct (run_scfg_of_realizes_spec segs pc ph lim T enX inp HR HX Hv) as [_ HtX].
  destruct (run_scfg_of_realizes_spec segs pc ph lim T enY inp HR HY Hv) as [_ HtY].
  rewrite (HtX tr), (HtY tr). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition exits0s (C : Image) : Prop :=
  forall inp en, valid_input inp -> valid_entry C en inp ->
    must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en inp.

Section Rows.
  Variables O1 O2 C : Image.

  Theorem clf_total_fo : exits0s C -> classifier_total_T_fo C.
  Proof. intros HC f Hf en Hen. left. exact (HC _ _ Hf Hen). Qed.

  Theorem clf_good_inputs_s :
    strong_universal_error_free_T_scfg cfg O1 O2 -> exits0s C ->
    classifies_good_inputs_T_s cfg O1 O2 C.
  Proof.
    intros Hbase HC f Hf en Hen. split.
    - split.
      + intros _. exact (good_input_s_of_base O1 O2 Hbase _ Hf).
      + intros _. exact (HC _ _ Hf Hen).
    - left. exact (HC _ _ Hf Hen).
  Qed.

  Theorem clf_patch_diff_s :
    strong_universal_error_free_T_scfg cfg O1 O2 -> sat O1 -> sat O2 -> exits0s C ->
    classifies_patch_diff_T_s cfg O1 O1 O2 O2 C.
  Proof.
    intros Hbase Hsat1 Hsat2 HC f Hf en Hen. split.
    - split.
      + intros _. split; [exact (agree_s_self_source O1 O2 Hbase Hsat2 _ Hf)
                        | exact (agree_s_self_target O1 O2 Hbase Hsat1 _ Hf)].
      + intros _. exact (HC _ _ Hf Hen).
    - left. exact (HC _ _ Hf Hen).
  Qed.

  (* [comment removed for export] *)
  Theorem clf_patch_diff_s_of_realizes :
    forall segs1 pc1 ph1 segs2 pc2 ph2 T1 T2,
    O1 = mkImage segs1 pc1 ph1 -> O2 = mkImage segs2 pc2 ph2 ->
    realizes_spec_cfg segs1 pc1 ph1 source_alloc_limit T1 ->
    realizes_spec_cfg segs2 pc2 ph2 target_alloc_limit T2 ->
    exits0s C ->
    classifies_patch_diff_T_s cfg O1 O1 O2 O2 C.
  Proof.
    intros segs1 pc1 ph1 segs2 pc2 ph2 T1 T2 -> -> H1 H2 HC f Hf en Hen. split.
    - split.
      + intros _. split; [exact (agree_s_self_of_realizes_cfg _ _ _ _ _ H1 _ Hf)
                        | exact (agree_s_self_of_realizes_cfg _ _ _ _ _ H2 _ Hf)].
      + intros _. exact (HC _ _ Hf Hen).
    - left. exact (HC _ _ Hf Hen).
  Qed.
End Rows.

End Glue.
