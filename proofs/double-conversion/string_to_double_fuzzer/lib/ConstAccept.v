From Stdlib Require Import ZArith NArith List QArith String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Examples Omni SpuriousCfg.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier Measure.
From OssFuzzTheorems.Core Require Import Images Shapes.
Require OssFuzzTheorems.double_conversion.string_to_double_fuzzer.Images.
Require OssFuzzTheorems.double_conversion.string_to_double_fuzzer.Statements.
Require OssFuzzTheorems.Proofs.double_conversion.string_to_double_fuzzer.lib.BaseUbsan.
Require OssFuzzTheorems.Proofs.double_conversion.string_to_double_fuzzer.lib.LxLib.
Import ListNotations.

Definition accept_segment : Segment := {|
  seg_base := 65536%N;
  seg_size := 132%N;
  seg_perms := "r-x"%string;
  seg_bytes := ["7f454c460201010000000000000000000200f30001000000780001000000000040000000000000000000000000000000040000004000380001004000000000000100000005000000000000000000000000000100000000000000010000000000840000000000000084000000000000000010000000000000130500009308e00573000000"%pstring]
|}.
Definition accept_segments : list Segment := [accept_segment].
Definition accept_phdrs : PhdrInfo := mkPhdrInfo 65600%N 56%N 1%N.
Definition accept_image : Image := mkImage accept_segments 65656%N accept_phdrs.

Lemma accept_image_wf : image_wf accept_image.
Proof. check_image_wf. Qed.

Lemma accept_exits_c : forall sp rnd argv envp uid hw,
  exits_c accept_segments verdict_accept 8
    (init_machine_state accept_segments 65656%N accept_phdrs sp rnd argv envp uid hw)
  = true.
Proof.
  intros. rewrite (with_mem_eta (init_machine_state _ _ _ _ _ _ _ _ _)).
  generalize (ms_mem (init_machine_state accept_segments 65656%N accept_phdrs sp rnd argv envp uid hw)).
  intros mem. vm_compute. reflexivity.
Qed.

Lemma accept_must_exit : forall inp en,
  must_exit_with_scfg forced_only_cfg verdict_accept accept_image classifier_alloc_limit en inp.
Proof.
  intros inp [sp brk0 mbase rnd]. unfold accept_image. cbn [must_exit_with_scfg].
  unfold init_config.
  apply (exits_c_must_exit_at_cfg _ _ _ 8); [reflexivity | reflexivity | apply accept_exits_c].
Qed.

Lemma good_input_all : forall env plain san,
  strong_universal_error_free_T_scfg env plain san ->
  forall inp, valid_input inp -> good_input_s env plain san inp.
Proof.
  intros env plain san Hbase inp Hv en1 en2 H1 H2. exact (Hbase en1 en2 inp H1 H2 Hv).
Qed.

Lemma accept_classifies : forall env plain san,
  strong_universal_error_free_T_scfg env plain san ->
  classifies_good_inputs_T_s env plain san accept_image.
Proof.
  intros env plain san Hbase f Hf en _. split.
  - split.
    + intros _. exact (good_input_all env plain san Hbase _ Hf).
    + intros _. apply accept_must_exit.
  - left. apply accept_must_exit.
Qed.

Lemma disagrees_at_most_0 : forall env w M plain san,
  strong_universal_error_free_T_scfg env plain san ->
  Shapes.disagrees_at_most env w M plain san 0.
Proof.
  intros env w M plain san Hbase [|f l] _ Hin.
  - rewrite sum_weights_nil. rewrite Qmult_0_l. apply Qle_refl.
  - exfalso. destruct (Hin f (or_introl eq_refl)) as [Hv Hbad].
    apply Hbad. exact (good_input_all env plain san Hbase (to_proc_input f) Hv).
Qed.

Lemma agreement_decidable_of_base : forall env plain san,
  strong_universal_error_free_T_scfg env plain san ->
  Shapes.agreement_decidable env plain san.
Proof.
  intros env plain san Hbase.
  apply (Shapes.agreement_decidable_of_classifier env plain san accept_image accept_image_wf).
  exact (accept_classifies env plain san Hbase).
Qed.

Lemma ubsan_base :
  strong_universal_error_free_T_scfg Env.may_fail
    OssFuzzTheorems.double_conversion.string_to_double_fuzzer.Images.plain
    OssFuzzTheorems.double_conversion.string_to_double_fuzzer.Images.ubsan.
Proof.
  exact (proj2 (strong_universal_error_free_T_scfg_may_fail _ _)
           (OssFuzzTheorems.Proofs.double_conversion.string_to_double_fuzzer.lib.BaseUbsan.ubsan_base
              OssFuzzTheorems.Proofs.double_conversion.string_to_double_fuzzer.lib.LxLib.lib_P
              OssFuzzTheorems.Proofs.double_conversion.string_to_double_fuzzer.lib.LxLib.lib_U)).
Qed.

Theorem ubsan_bound_0 :
  OssFuzzTheorems.double_conversion.string_to_double_fuzzer.Statements.ubsan_disagrees_at_most 0.
Proof. exact (disagrees_at_most_0 _ _ _ _ _ ubsan_base). Qed.

Theorem ubsan_decidable :
  OssFuzzTheorems.double_conversion.string_to_double_fuzzer.Statements.ubsan_agreement_decidable.
Proof. exact (agreement_decidable_of_base _ _ _ ubsan_base). Qed.
