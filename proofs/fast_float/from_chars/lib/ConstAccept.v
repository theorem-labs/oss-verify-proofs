From Stdlib Require Import ZArith NArith List QArith String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Examples Omni SpuriousCfg.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier Measure.
From OssFuzzTheorems.Core Require Import Images Shapes.
Require OssFuzzTheorems.fast_float.from_chars.Images.
Require OssFuzzTheorems.fast_float.from_chars.Statements.
Require OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.RealizesCfg.
Require OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.RealizesAbort.
Require OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.ClfRowsGen.
Require OssFuzzTheorems.Proofs.fast_float.from_chars.lib.PTop.
Require OssFuzzTheorems.Proofs.fast_float.from_chars.lib.PAssemble.
Require OssFuzzTheorems.Proofs.fast_float.from_chars.lib.UAssemble.
Require OssFuzzTheorems.Proofs.fast_float.from_chars.lib.FXD.TopAsanF.
Require OssFuzzTheorems.Proofs.fast_float.from_chars.lib.FXDB.TopBothF.
Require OssFuzzTheorems.Proofs.fast_float.from_chars.lib.TopAsanH.
Require OssFuzzTheorems.Proofs.fast_float.from_chars.lib.TopBothH.
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

Lemma accept_accepts_all :
  OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.ClfRowsGen.accepts_all accept_image.
Proof. intros f _ en _. exact (accept_must_exit (to_proc_input f) en). Qed.

Lemma good_input_all : forall env plain san,
  strong_universal_error_free_T_scfg env plain san ->
  forall inp, valid_input inp -> good_input_s env plain san inp.
Proof.
  intros env plain san Hbase inp Hv en1 en2 H1 H2. exact (Hbase en1 en2 inp H1 H2 Hv).
Qed.

Lemma disagrees_at_most_0 : forall env w M plain san,
  strong_universal_error_free_T_scfg env plain san ->
  Shapes.disagrees_at_most env w M plain san 0.
Proof.
  intros env w M plain san Hbase [|f l] _ Hin.
  - rewrite sum_weights_nil. rewrite Qmult_0_l. apply Qle_refl.
  - exfalso. destruct (Hin f (or_introl eq_refl)) as [Hv Hbad].
    apply Hbad.
    exact (good_input_all env plain san Hbase (to_proc_input f) Hv).
Qed.

Lemma agreement_decidable_of_base : forall env plain san,
  strong_universal_error_free_T_scfg env plain san ->
  Shapes.agreement_decidable env plain san.
Proof.
  intros env plain san Hbase.
  apply (Shapes.agreement_decidable_of_classifier env plain san accept_image accept_image_wf).
  exact (OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.ClfRowsGen.decides_fo_of_accepts_all
           accept_image (good_input_s env plain san) accept_accepts_all
           (good_input_all env plain san Hbase)).
Qed.

Lemma asan_base :
  strong_universal_error_free_T_scfg Env.alloc_forced_only
    OssFuzzTheorems.fast_float.from_chars.Images.plain
    OssFuzzTheorems.fast_float.from_chars.Images.asan.
Proof.
  exact (OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.RealizesCfg.strong_universal_error_free_T_scfg_of_realizes
           _ _ _ _ _ _ _ OssFuzzTheorems.Proofs.fast_float.from_chars.lib.PTop.SPEC
           (OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.RealizesAbort.image_realizes_cfg_of_e _ _ _ _ _ _
              OssFuzzTheorems.Proofs.fast_float.from_chars.lib.PAssemble.plain_realizes_A)
           (OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.RealizesAbort.image_realizes_cfg_of_e _ _ _ _ _ _
              (OssFuzzTheorems.Proofs.fast_float.from_chars.lib.FXD.TopAsanF.asan_realizes_D
                 OssFuzzTheorems.Proofs.fast_float.from_chars.lib.TopAsanH.Hleaves))).
Qed.

Lemma ubsan_base :
  strong_universal_error_free_T_scfg Env.alloc_forced_only
    OssFuzzTheorems.fast_float.from_chars.Images.plain
    OssFuzzTheorems.fast_float.from_chars.Images.ubsan.
Proof.
  exact (OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.RealizesCfg.strong_universal_error_free_T_scfg_of_realizes
           _ _ _ _ _ _ _ OssFuzzTheorems.Proofs.fast_float.from_chars.lib.PTop.SPEC
           (OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.RealizesAbort.image_realizes_cfg_of_e _ _ _ _ _ _
              OssFuzzTheorems.Proofs.fast_float.from_chars.lib.PAssemble.plain_realizes_A)
           (OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.RealizesAbort.image_realizes_cfg_of_e _ _ _ _ _ _
              OssFuzzTheorems.Proofs.fast_float.from_chars.lib.UAssemble.ubsan_realizes_A)).
Qed.

Lemma asan_ubsan_base :
  strong_universal_error_free_T_scfg Env.alloc_forced_only
    OssFuzzTheorems.fast_float.from_chars.Images.plain
    OssFuzzTheorems.fast_float.from_chars.Images.asan_ubsan.
Proof.
  exact (OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.RealizesCfg.strong_universal_error_free_T_scfg_of_realizes
           _ _ _ _ _ _ _ OssFuzzTheorems.Proofs.fast_float.from_chars.lib.PTop.SPEC
           (OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.RealizesAbort.image_realizes_cfg_of_e _ _ _ _ _ _
              OssFuzzTheorems.Proofs.fast_float.from_chars.lib.PAssemble.plain_realizes_A)
           (OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.RealizesAbort.image_realizes_cfg_of_e _ _ _ _ _ _
              (OssFuzzTheorems.Proofs.fast_float.from_chars.lib.FXDB.TopBothF.both_realizes_D
                 OssFuzzTheorems.Proofs.fast_float.from_chars.lib.TopBothH.Hleaves))).
Qed.

Theorem asan_bound_0 : OssFuzzTheorems.fast_float.from_chars.Statements.asan_disagrees_at_most 0.
Proof. exact (disagrees_at_most_0 _ _ _ _ _ asan_base). Qed.

Theorem ubsan_bound_0 : OssFuzzTheorems.fast_float.from_chars.Statements.ubsan_disagrees_at_most 0.
Proof. exact (disagrees_at_most_0 _ _ _ _ _ ubsan_base). Qed.

Theorem asan_ubsan_bound_0 :
  OssFuzzTheorems.fast_float.from_chars.Statements.asan_ubsan_disagrees_at_most 0.
Proof. exact (disagrees_at_most_0 _ _ _ _ _ asan_ubsan_base). Qed.

Theorem asan_decidable : OssFuzzTheorems.fast_float.from_chars.Statements.asan_agreement_decidable.
Proof. exact (agreement_decidable_of_base _ _ _ asan_base). Qed.

Theorem ubsan_decidable : OssFuzzTheorems.fast_float.from_chars.Statements.ubsan_agreement_decidable.
Proof. exact (agreement_decidable_of_base _ _ _ ubsan_base). Qed.

Theorem asan_ubsan_decidable :
  OssFuzzTheorems.fast_float.from_chars.Statements.asan_ubsan_agreement_decidable.
Proof. exact (agreement_decidable_of_base _ _ _ asan_ubsan_base). Qed.
