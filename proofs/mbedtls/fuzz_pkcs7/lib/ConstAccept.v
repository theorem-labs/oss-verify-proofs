From Stdlib Require Import ZArith NArith List QArith String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Examples Omni SpuriousCfg.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier Measure.
From OssFuzzTheorems.Core Require Import Images Shapes.
Require OssFuzzTheorems.mbedtls.fuzz_pkcs7.Images.
Require OssFuzzTheorems.mbedtls.fuzz_pkcs7.Statements.
Require OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.FinalAsan.
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

Lemma good_input_all : forall plain san,
  strong_universal_error_free_T plain san ->
  forall inp, valid_input inp -> good_input_s Env.may_fail plain san inp.
Proof.
  intros plain san Hbase inp Hv.
  exact (proj2 (good_input_s_may_fail plain san inp)
           (fun en1 en2 H1 H2 => Hbase en1 en2 inp H1 H2 Hv)).
Qed.

Lemma disagrees_at_most_0 : forall w M plain san,
  strong_universal_error_free_T plain san ->
  Shapes.disagrees_at_most Env.may_fail w M plain san 0.
Proof.
  intros w M plain san Hbase [|f l] _ Hin.
  - rewrite sum_weights_nil. rewrite Qmult_0_l. apply Qle_refl.
  - exfalso. destruct (Hin f (or_introl eq_refl)) as [Hv Hbad].
    apply Hbad.
    exact (good_input_all plain san Hbase (to_proc_input f) Hv).
Qed.

Lemma agreement_decidable_of_base : forall plain san,
  strong_universal_error_free_T plain san ->
  Shapes.agreement_decidable Env.may_fail plain san.
Proof.
  intros plain san Hbase.
  apply (Shapes.agreement_decidable_of_classifier Env.may_fail plain san accept_image accept_image_wf).
  unfold Shapes.classifies. intros f Hf en _. split.
  - split.
    + intros _. exact (good_input_all plain san Hbase (to_proc_input f) Hf).
    + intros _. exact (accept_must_exit (to_proc_input f) en).
  - left. exact (accept_must_exit (to_proc_input f) en).
Qed.

Lemma asan_base :
  strong_universal_error_free_T
    OssFuzzTheorems.mbedtls.fuzz_pkcs7.Images.plain
    OssFuzzTheorems.mbedtls.fuzz_pkcs7.Images.asan.
Proof. exact OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.FinalAsan.asan_assembled. Qed.

Theorem asan_bound_0 : OssFuzzTheorems.mbedtls.fuzz_pkcs7.Statements.asan_disagrees_at_most 0.
Proof. exact (disagrees_at_most_0 _ _ _ _ asan_base). Qed.

Theorem asan_decidable : OssFuzzTheorems.mbedtls.fuzz_pkcs7.Statements.asan_agreement_decidable.
Proof. exact (agreement_decidable_of_base _ _ asan_base). Qed.
