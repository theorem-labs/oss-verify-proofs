(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3. *)
(* [comment removed for export] *)
From Stdlib Require Import NArith List ZArith Lia Bool QArith.
Require OSSVerify.boost_beast.http_request.images.Plain.
Require OSSVerify.boost_beast.http_request.images.Ubsan.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed FinInput Classifier Measure.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import Scfg ShapeAlg ShapeEF ShapeEFA Spec SpecProps HaltsBridge
  ClfGeneric ClfStartup HaltsPlain.
From OSSVerify.Proofs.boost_beast.http_request.lib Require RefTop.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require UbTop.
(* LPS 08b1429: each walk is over the binary's own segments; [RomStable.run_init] /
   [RomStableS.srun_init] lift it to the run's segment list, the vDSO premise closed by
   [reflexivity] on the concrete image. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common.Cfg Require RomStable RomStableS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition CFG : SpuriousCfg := Run.mkSpuriousCfg false true true true true true.

Definition UBSAN : Image :=
  mkImage OSSVerify.boost_beast.http_request.images.Ubsan.M.loaded_segments
          OSSVerify.boost_beast.http_request.images.Ubsan.M.init_pc
          OSSVerify.boost_beast.http_request.images.Ubsan.M.phdrs.

Section WithHarness.
  Hypothesis XF_plain : RefTop.XFUZZ.
  Hypothesis XF_ubsan : UbTop.XFUZZ.

  (* [comment removed for export] *)
  Theorem ubsan_base_scfg : strong_universal_error_free_T_scfg CFG SRC UBSAN.
  Proof.
    intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid.
    pose proof (valid_input_va_size _ Hvalid) as Hsv48.
    pose proof (valid_input_channel_reader _ Hvalid) as Hrd.
    pose proof (valid_input_launch _ Hvalid) as Hvl.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
    destruct Hens as [Hrsp [Hrbrk [Hrmb [Hrfit Hrlau]]]]. destruct Hent as [Hasp [Habrk [Hamb [Hafit Halau]]]].
    destruct Hvalid as (Hargv & Henvp & Hfs & _).
    change CFG with (@the_scfg hunspell_scfg).
    apply (shape_strong_equiv_ef_scfg _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spec (in_argv inp) (in_fs inp))).
    - apply RomStable.run_init; [reflexivity |].
      exact (RefTop.ref_realizes_spec XF_plain rsp rbrk rmb rrnd inp Hrsp Hrbrk Hrfit Hargv Henvp Hfs Hrmb Hrd Hvl Hrlau).
    - apply RomStable.run_init; [reflexivity |].
      exact (UbTop.ub_realizes_spec_lim XF_ubsan asp abrk amb arnd target_alloc_limit inp Hasp Habrk ltac:(unfold target_alloc_limit; lia) Hafit Hargv Henvp Hfs Hamb Hrd Hvl Halau).
  Qed.

  (* [comment removed for export] *)
  Theorem ubsan_base :
    strong_universal_error_free_T_scfg_budgets_abort CFG ShippedBudgets.lim_source ShippedBudgets.lim_target SRC UBSAN.
  Proof.
    intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid _.
    pose proof (valid_input_abort_va_size _ Hvalid) as Hsv48.
    (* [valid_input_abort]'s reader clause; Run proves the accessor for [valid_input] only *)
    assert (Hrd : in_channel_reader inp = true)
      by (red in Hvalid; repeat match goal with H : _ /\ _ |- _ => destruct H end; assumption).
    (* [valid_input_abort]'s launch clause, read the same way *)
    assert (Hvl : valid_launch inp)
      by (red in Hvalid; repeat match goal with H : _ /\ _ |- _ => destruct H end; assumption).
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
    destruct Hens as [Hrsp [Hrbrk [Hrmb [Hrfit Hrlau]]]]. destruct Hent as [Hasp [Habrk [Hamb [Hafit Halau]]]].
    destruct Hvalid as (Hargv & Henvp & Hfs & _).
    change CFG with (@the_scfg hunspell_scfg).
    unfold ShippedBudgets.lim_source, ShippedBudgets.lim_target.
    apply (shape_strong_equiv_ef_abort _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spec (in_argv inp) (in_fs inp))).
    - apply RomStable.run_init; [reflexivity |].
      exact (RefTop.ref_realizes_spec XF_plain rsp rbrk rmb rrnd inp Hrsp Hrbrk Hrfit Hargv Henvp Hfs Hrmb Hrd Hvl Hrlau).
    - apply RomStable.run_init; [reflexivity |].
      exact (UbTop.ub_realizes_spec_lim XF_ubsan asp abrk amb arnd target_alloc_limit inp Hasp Habrk ltac:(unfold target_alloc_limit; lia) Hafit Hargv Henvp Hfs Hamb Hrd Hvl Halau).
    - apply spec_kill_free.
  Qed.

  (* [comment removed for export] *)
  Theorem ubsan_must_exit_scfg :
    forall en inp, valid_entry UBSAN en inp -> valid_input inp ->
      must_exit_in_scfg the_scfg codes02 UBSAN source_alloc_limit en inp.
  Proof.
    intros [sp brk mbase rnd] inp Hen Hvalid.
    pose proof (valid_input_va_size _ Hvalid) as Hsv48.
    pose proof (valid_input_channel_reader _ Hvalid) as Hrd.
    pose proof (valid_input_launch _ Hvalid) as Hvl.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen.
    destruct Hen as [Hsp [Hbrk [Hmb [Hfit Hlau]]]].
    destruct Hvalid as (Hargv & Henvp & Hfs & _).
    unfold UBSAN. rewrite <- spec_exits_codes02.
    eapply (realizes_must_exit_in _ spec_exits).
    - apply RomStable.run_init; [reflexivity |].
      exact (UbTop.ub_realizes_spec XF_ubsan sp brk mbase rnd inp Hsp Hbrk Hfit Hargv Henvp Hfs Hmb Hrd Hvl Hlau).
    - apply spec_shape_good.
  Qed.

  Theorem halts_ubsan :
    halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source codes02 UBSAN.
  Proof.
    intros en inp Hen Hvalid _.
    unfold ShippedBudgets.lim_source.
    apply (must_exit_in_scfg_down forced_only_cfg the_scfg); [apply forced_only_cfg_least|].
    exact (ubsan_must_exit_scfg en inp Hen Hvalid).
  Qed.

  (* [comment removed for export] *)
  Lemma src_sat : image_brk_satisfiable (img_segments SRC) = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma ubsan_sat : image_brk_satisfiable (img_segments UBSAN) = true.
  Proof. vm_compute. reflexivity. Qed.
End WithHarness.

(* [comment removed for export] *)
Lemma weight_bound_fo_accept_all : forall (C : Image) (w : FinProcInput -> Q) (M : Q),
  (forall inp en, valid_input inp -> valid_entry C en inp ->
      must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en inp) ->
  weight_bound_T_fo C w M 0.
Proof.
  intros C w M HC l Hnd Hrej.
  destruct l as [|f l'].
  - rewrite sum_weights_nil. rewrite Qmult_0_l. apply Qle_refl.
  - exfalso. destruct (Hrej f (or_introl eq_refl)) as [Hvf Hnacc].
    apply Hnacc. intros en Hen. apply HC; [exact Hvf | exact Hen].
Qed.
