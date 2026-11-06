(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import NArith List ZArith Lia Bool QArith.
Require OSSVerify.boost_beast.http_request.images.Plain.
Require OSSVerify.boost_beast.http_request.images.AsanUbsan.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed FinInput Classifier Measure.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import Scfg ShapeAlg ShapeEF ShapeEFA Spec SpecProps HaltsBridge
  ClfGeneric ClfStartup HaltsPlain PairUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import SpinAlg ShapeEFAS.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs.
From OSSVerify.Proofs.boost_beast.http_request.lib.Common.LimSim Require Import LimSimSys LimSimRun.
From OSSVerify.Proofs.boost_beast.http_request.lib Require RefTop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition BOTH : Image :=
  mkImage OSSVerify.boost_beast.http_request.images.AsanUbsan.M.loaded_segments
          OSSVerify.boost_beast.http_request.images.AsanUbsan.M.init_pc
          OSSVerify.boost_beast.http_request.images.AsanUbsan.M.phdrs.

Lemma both_sat : image_brk_satisfiable (img_segments BOTH) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma bsegs_eq : bsegs = OSSVerify.boost_beast.http_request.images.AsanUbsan.M.loaded_segments.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition BO_SREALIZES : Prop :=
  forall sp brk mbase rnd inp,
    valid_sp sp -> valid_brk bsegs brk -> valid_mmap_base mbase ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    valid_creds inp -> valid_hwcap (in_hwcap inp) ->
    @srealizes bsegs hunspell_scfg
      (init_config bsegs OSSVerify.boost_beast.http_request.images.AsanUbsan.M.init_pc
                   OSSVerify.boost_beast.http_request.images.AsanUbsan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
      (spec (in_argv inp) (in_fs inp)).

Definition BO_REALIZES : Prop :=
  forall sp brk mbase rnd inp,
    valid_sp sp -> valid_brk bsegs brk -> valid_mmap_base mbase ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    valid_creds inp -> valid_hwcap (in_hwcap inp) ->
    @realizes bsegs hunspell_scfg
      (init_config bsegs OSSVerify.boost_beast.http_request.images.AsanUbsan.M.init_pc
                   OSSVerify.boost_beast.http_request.images.AsanUbsan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
      (spec (in_argv inp) (in_fs inp)).

Lemma BO_SREALIZES_of_REALIZES : BO_REALIZES -> BO_SREALIZES.
Proof. intros H sp brk mbase rnd inp; intros. apply srealizes_of_realizes. apply H; assumption. Qed.

Section WithBoth.
  Hypothesis XF_plain : RefTop.XFUZZ.
  Hypothesis BO_SREAL : BO_SREALIZES.

  (* [comment removed for export] *)
  Lemma both_pair_at_pinned : forall rsp rbrk rmb rrnd asp abrk amb arnd inp,
    valid_entry SRC (mkEntry rsp rbrk rmb rrnd) inp -> valid_entry BOTH (mkEntry asp abrk amb arnd) inp ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) -> valid_creds inp ->
    valid_hwcap (in_hwcap inp) -> in_va_size inp = Sv48 ->
    strong_equiv_error_free_budgets_scfg_abort CFG source_alloc_limit target_alloc_limit SRC BOTH
      (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
  Proof.
    intros rsp rbrk rmb rrnd asp abrk amb arnd inp Hens Hent Hargv Henvp Hfs Hcreds Hhw Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
    destruct Hens as [Hrsp [Hrbrk [Hrmb Hrfit]]]. destruct Hent as [Hasp [Habrk [Hamb Hafit]]].
    change CFG with (@the_scfg hunspell_scfg).
    apply (shape_strong_equiv_ef_abort_s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spec (in_argv inp) (in_fs inp))).
    - exact (RefTop.ref_realizes_spec XF_plain rsp rbrk rmb rrnd inp Hrsp Hrbrk Hrfit Hargv Henvp Hfs).
    - exact (BO_SREAL asp abrk amb arnd inp Hasp Habrk Hamb Hafit Hargv Henvp Hfs Hcreds Hhw).
    - apply spec_kill_free.
  Qed.

  (* [comment removed for export] *)
  Theorem both_base :
    strong_universal_error_free_T_scfg_budgets_abort CFG SanitizerBudgets.lim_source SanitizerBudgets.lim_target SRC BOTH.
  Proof.
    intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid NB.
    pose proof (valid_input_abort_va_size _ Hvalid) as Hsv48.
    destruct Hvalid as (Hargv & Henvp & Hfs & _ & Hcreds & _ & _ & Hhw & _).
    unfold SanitizerBudgets.lim_target.
    apply (strong_equiv_ef_budgets_scfg_relim_source CFG source_alloc_limit SanitizerBudgets.lim_source target_alloc_limit
             SRC BOTH _ _ inp ltac:(unfold source_alloc_limit, SanitizerBudgets.lim_source, sanitizer_source_limit; cbv; discriminate) NB).
    all: destruct (both_pair_at_pinned rsp rbrk rmb rrnd asp abrk amb arnd inp Hens Hent Hargv Henvp Hfs Hcreds Hhw Hsv48) as (Hs & Ht & Htr).
    - exact Hs. - exact Ht. - exact Htr.
  Qed.

  (* [comment removed for export] *)
  Theorem both_base_scfg : strong_universal_error_free_T_scfg CFG SRC BOTH.
  Proof.
    intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid.
    pose proof (valid_input_va_size _ Hvalid) as Hsv48.
    destruct Hvalid as (Hargv & Henvp & Hfs & _ & Hcreds & _ & _ & Hhw & _).
    destruct (both_pair_at_pinned rsp rbrk rmb rrnd asp abrk amb arnd inp Hens Hent Hargv Henvp Hfs Hcreds Hhw Hsv48) as (Hs & Ht & Htr).
    split; [exact (proj1 Hs)|]. split; [exact (proj1 Ht)| exact Htr].
  Qed.
End WithBoth.

Section Halts.
  Hypothesis BO_REAL : BO_REALIZES.

  (* [comment removed for export] *)
  Theorem both_must_exit_scfg :
    forall en inp, valid_entry BOTH en inp -> valid_input inp ->
      must_exit_in_scfg the_scfg codes02 BOTH target_alloc_limit en inp.
  Proof.
    intros [sp brk mbase rnd] inp Hen Hvalid.
    pose proof (valid_input_va_size _ Hvalid) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen.
    destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
    destruct Hvalid as (Hargv & Henvp & Hfs & _ & Hcreds & _ & _ & Hhw & _).
    unfold BOTH. rewrite <- spec_exits_codes02.
    eapply (realizes_must_exit_in _ spec_exits).
    - exact (BO_REAL sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hargv Henvp Hfs Hcreds Hhw).
    - apply spec_shape_good.
  Qed.

  (* [comment removed for export] *)
  Theorem halts_both :
    halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source codes02 BOTH.
  Proof.
    intros en inp Hen Hvalid NB.
    apply (must_exit_in_scfg_relim_closed forced_only_cfg codes02 BOTH target_alloc_limit ShippedBudgets.lim_source en inp
             ltac:(unfold target_alloc_limit, ShippedBudgets.lim_source, source_alloc_limit; cbv; discriminate) NB).
    apply (must_exit_in_scfg_down forced_only_cfg the_scfg); [apply forced_only_cfg_least|].
    exact (both_must_exit_scfg en inp Hen Hvalid).
  Qed.
End Halts.
