From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images Require Import Plain.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK15 YN05 YN0b YN01 YH04.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP07 YP08.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YZ02.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import HaltsFO DriverClosedHalts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.

Lemma shape_ok_of_tsafe : forall S T, tsafe S T -> shape_ok S T.
Proof.
  intros S T H tr Htr. unfold trace_ok. pose proof (H tr Htr) as Hf. clear Htr.
  induction Hf as [| e l He _ IH]; [constructor | constructor; [destruct e; exact He | exact IH]].
Qed.

Lemma tsafe_of_shape_ok : forall S T, shape_ok S T -> tsafe S T.
Proof.
  intros S T H tr Htr. pose proof (H tr Htr) as Hf. clear Htr. unfold trace_ok in Hf.
  induction Hf as [| e l He _ IH]; [constructor | constructor; [destruct e; exact He | exact IH]].
Qed.

Lemma shape_ok_tset_plain {St A : Type} : forall S (t : YP0j.itree St A) (K : A -> TSet),
  (forall a, shape_ok S (K a)) -> shape_ok S (YN02.tset t K).
Proof.
  intros S t K HK. apply shape_ok_of_tsafe. apply tsafe_tset.
  intros a. apply tsafe_of_shape_ok. apply HK.
Qed.

Lemma SPEC_shape_ok02 : forall inp, shape_ok codes02 (SPEC inp).
Proof.
  intros inp. unfold SPEC, SPEC_args.
  destruct (in_argv inp) as [| a0 [| p [| x l]]]; try apply shape_ok_diag02.
  destruct (classify_open p (in_fs inp)).
  - apply shape_ok_diag02.
  - apply shape_ok_alt2; [apply shape_ok_diag02 |].
    unfold SPEC_dir. apply shape_ok_tset_plain. intros [b a]. cbn [fst].
    destruct b; apply shape_ok_diag02.
  - apply shape_ok_alt2; [apply shape_ok_diag02 |].
    unfold SPEC_loaded. apply shape_ok_tset_plain. intros a. apply shape_ok_leaf_shape.
Qed.

Theorem halts_plain_forced_only :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source codes02
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs).
Proof.
  apply halts_allowed_T_scfg_budgets_of_scfg.
  intros [sp brk mb rnd] inp Hen Hinp.
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen.
  destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
  unfold must_exit_in_scfg.
  apply (fo_exits_must_exit src2segs codes02 _ (SPEC inp)).
  - apply fo_of_realizes. apply src2_realizes; try assumption. apply SRC_LIM_MIN_le_source.
  - apply SPEC_shape_ok02.
  - reflexivity.
Qed.
