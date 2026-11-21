(** (the pair-29 pilot): classifier B with UNPATCHED originals.

    Two builds that each agree, error-free, with ONE common partner build agree with each other in the sense of
    [Classifier.agree_s]: their trace sets are equal at every pair of valid entries (both equal the partner's), and
    neither can reach an error, an all-error or an unmodelled step (each is error-free).  So, for an accept-all
    classifier, the iff row of classifier B follows from three pair agreements:
      O1 with P2 (the original source with the published target),
      P1 with P2 (the published pair: its base row), and
      P1 with O2 (the published source with the original target).
    Every lemma is generic in the images.  No axiom, no parameter, no unfinished proof. *)
From Stdlib Require Import ZArith QArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType StackLayout State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import
  Equivalence MustExit FinInput Classifier Measure.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.ClsW.OSSV Require Import Images Shapes ClassifierShapes.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.ClsW.Cls Require Import AcceptAllGeneric.
Import ListNotations.

Lemma ef_no_all_errors : forall env X lim en inp,
  error_free (run_scfg env X lim en inp) -> ~ bh_all_errors (run_scfg env X lim en inp).
Proof. intros env X lim en inp H Ha. exact (H (run_scfg_all_errors_errors env X lim en inp Ha)). Qed.

Lemma ef_no_unmodeled : forall env X lim en inp,
  error_free (run_scfg env X lim en inp) -> ~ bh_unmodeled (run_scfg env X lim en inp).
Proof. intros env X lim en inp H Hu. exact (H (run_scfg_unmodeled_errors env X lim en inp Hu)). Qed.

(** Two SOURCE-side builds [O] and [P], each paired with the same target-side build [X]. *)
Lemma agree_s_sources : forall env O P X,
  strong_universal_error_free_T_scfg env O X ->
  strong_universal_error_free_T_scfg env P X ->
  image_brk_satisfiable (img_segments X) = true ->
  forall f, valid_fin_input f -> agree_s env O P source_alloc_limit (to_proc_input f).
Proof.
  intros env O P X TO TP Hb f Hf.
  destruct (image_brk_satisfiable_entry X (to_proc_input f) Hf Hb) as [ex Hex].
  split; [| split; [| split]].
  - intros eo ep Heo Hep.
    destruct (TO eo ex (to_proc_input f) Heo Hex Hf) as (_ & _ & A).
    destruct (TP ep ex (to_proc_input f) Hep Hex Hf) as (_ & _ & B).
    exact (trace_equiv_trans_sym _ _ _ A B).
  - split; intros (en & Hen & He); exfalso.
    + destruct (TO en ex (to_proc_input f) Hen Hex Hf) as (H0 & _ & _). exact (H0 He).
    + destruct (TP en ex (to_proc_input f) Hen Hex Hf) as (H0 & _ & _). exact (H0 He).
  - split; intros (en & Hen & He); exfalso.
    + destruct (TO en ex (to_proc_input f) Hen Hex Hf) as (H0 & _ & _). exact (ef_no_all_errors _ _ _ _ _ H0 He).
    + destruct (TP en ex (to_proc_input f) Hen Hex Hf) as (H0 & _ & _). exact (ef_no_all_errors _ _ _ _ _ H0 He).
  - split; intros (en & Hen & He); exfalso.
    + destruct (TO en ex (to_proc_input f) Hen Hex Hf) as (H0 & _ & _). exact (ef_no_unmodeled _ _ _ _ _ H0 He).
    + destruct (TP en ex (to_proc_input f) Hen Hex Hf) as (H0 & _ & _). exact (ef_no_unmodeled _ _ _ _ _ H0 He).
Qed.

(** Two TARGET-side builds [O] and [P], each paired with the same source-side build [X]. *)
Lemma agree_s_targets : forall env X O P,
  strong_universal_error_free_T_scfg env X O ->
  strong_universal_error_free_T_scfg env X P ->
  image_brk_satisfiable (img_segments X) = true ->
  forall f, valid_fin_input f -> agree_s env O P target_alloc_limit (to_proc_input f).
Proof.
  intros env X O P TO TP Hb f Hf.
  destruct (image_brk_satisfiable_entry X (to_proc_input f) Hf Hb) as [ex Hex].
  split; [| split; [| split]].
  - intros eo ep Heo Hep.
    destruct (TO ex eo (to_proc_input f) Hex Heo Hf) as (_ & _ & A).
    destruct (TP ex ep (to_proc_input f) Hex Hep Hf) as (_ & _ & B).
    exact (trace_equiv_sym_trans _ _ _ A B).
  - split; intros (en & Hen & He); exfalso.
    + destruct (TO ex en (to_proc_input f) Hex Hen Hf) as (_ & H0 & _). exact (H0 He).
    + destruct (TP ex en (to_proc_input f) Hex Hen Hf) as (_ & H0 & _). exact (H0 He).
  - split; intros (en & Hen & He); exfalso.
    + destruct (TO ex en (to_proc_input f) Hex Hen Hf) as (_ & H0 & _). exact (ef_no_all_errors _ _ _ _ _ H0 He).
    + destruct (TP ex en (to_proc_input f) Hex Hen Hf) as (_ & H0 & _). exact (ef_no_all_errors _ _ _ _ _ H0 He).
  - split; intros (en & Hen & He); exfalso.
    + destruct (TO ex en (to_proc_input f) Hex Hen Hf) as (_ & H0 & _). exact (ef_no_unmodeled _ _ _ _ _ H0 He).
    + destruct (TP ex en (to_proc_input f) Hex Hen Hf) as (_ & H0 & _). exact (ef_no_unmodeled _ _ _ _ _ H0 He).
Qed.

(** Classifier B's iff row for an accept-all classifier, with unpatched originals [O1] / [O2] of the published
    builds [P1] / [P2]. *)
Lemma cb_iff_of_cross : forall env O1 P1 O2 P2 C,
  strong_universal_error_free_T_scfg env O1 P2 ->
  strong_universal_error_free_T_scfg env P1 P2 ->
  strong_universal_error_free_T_scfg env P1 O2 ->
  image_brk_satisfiable (img_segments P1) = true ->
  image_brk_satisfiable (img_segments P2) = true ->
  accepts_all C ->
  classifies_patch_diff env O1 P1 O2 P2 C.
Proof.
  intros env O1 P1 O2 P2 C X1 B X2 Hb1 Hb2 H.
  apply (classifies_patch_diff_of_accepts_all env O1 P1 O2 P2 C); [| exact H].
  intros f Hf. split.
  - exact (agree_s_sources env O1 P1 P2 X1 B Hb2 f Hf).
  - exact (agree_s_targets env P1 O2 P2 X2 B Hb1 f Hf).
Qed.
