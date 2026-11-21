(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the channel-reader and launch premises of Run.valid_input and Run.valid_entry; FZ_p, the plain binary's library, has type Ref.ECH_LibTop.fuzz_vc_type; the ASan library ECHL takes the heap-ceiling record, so the instance and as_realizes_spec take it as fun HC => @ECHL HC; Run.valid_input's creds and hwcap conjuncts are taken at their places after its fs_image_real conjunct); the ASan walk is the run's own, over run_segments from Run.init_config over that list (EAsChainRun.as_chain_run in place of as_chain_srealizes and of RomStableS.srun_init's lift, SpinAlg.srealizes_of_realizes where the agreement theorem asks for an srealizes walk), because the target calls time() and enters the launch's vDSO pair: TR and MAIN take the run's driver laws over the run's tail, and MAIN the three tail statements, which the instance now carries; the instance and the walk are stated at EAsChainRun.P_mainK. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import NArith List ZArith Lia Bool.
Require OSSVerify.openssl.echconfiglist_parser.images.Plain.
Require OSSVerify.openssl.echconfiglist_parser.images.Asan.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import Scfg ShapeAlg ShapeEF SpinAlg ShapeEFS Spec HeapCeil HeapSecret BaseUbsan AsMainState AsMainCells.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require RefTop.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require ECH_LibTop.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.AsCert Require Import EAsStartupTop.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.AsHole Require EAsChainRun.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import RunTail.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As Require Import ASegs AsIface AsIfaceX AsDriverLaws ECH_Iface AsDrvDefs AsMainPre AsInstance AsInstanceMain AsTop AsTargetRun AsMainTop AsMainTails
  ECH_ATraces ECH_ALib ECH_ALibOK AS_InstanceKit.
Import ListNotations.
Import OSSVerify.Proofs.openssl.echconfiglist_parser.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section WithParts.
  (* [comment removed for export] *)
  Hypothesis FZ_p : OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref.ECH_LibTop.fuzz_vc_type.
  (* [comment removed for export] *)
  Hypothesis FZ_a : forall (HCEIL : HeapCeil) (H : asr), asan_rt_hyps_x H -> As.AInstFacts.ainst_facts H -> As.ECH_Iface.fuzz_stmt H ECHL.

  (* [comment removed for export] *)
  Lemma L_OK : forall (HCEIL : HeapCeil), alib_ok ECHL.
  Proof. intros HCEIL. exact ECHL_ok. Qed.
  Lemma TR : forall (HCEIL : HeapCeil) (RT : RunTail.RunTail) (H : asr) (vlo vb vhi : Z),
      asan_rt_hyps H -> asan_driver_laws_run (@RunTail.rt_tail RT) vlo vb vhi H ->
      alib_ok ECHL -> As.ECH_Iface.fuzz_stmt H ECHL ->
      as_target_run_stmt H ECHL.
  Proof. intros HCEIL RT H vlo vb vhi HH DLR LOK FZ. exact (AsTargetRun.as_target_run H HH DLR ECHL LOK FZ). Qed.
  (* the three tail statements are the instance's: at the run instance [AsSRRun.KHr] they are
     [As/AsTailsRun.v]'s lifts of [AsMainTails]', which hold for the binary's driver laws *)
  Lemma MAIN : forall (HCEIL : HeapCeil) (RT : RunTail.RunTail) (H : asr) (vlo vb vhi : Z),
      asan_rt_hyps H -> asan_driver_laws_run (@RunTail.rt_tail RT) vlo vb vhi H -> as_target_run_stmt H ECHL ->
      (ADRV_LIVE <= as_LIVE_MAX H /\ ADRV_CNT <= as_LIVE_CNT_MAX H) ->
      atail_usage_stmt H ECHL -> atail_open_stmt H ECHL -> atail_rderr_stmt H ECHL ->
      as_main_realizes_stmt H ECHL.
  Proof.
    intros HCEIL RT H vlo vb vhi HH DLR TRH LIVE TUS TOP TRD.
    exact (AsMainTop.as_main_realizes H ECHL (L_OK HCEIL) HH DLR TRH LIVE TUS TOP TRD).
  Qed.
  (* [comment removed for export] *)
  Lemma INSTANCE : as_instance_stmt EAsChainRun.P_mainK (fun HC => @ECHL HC).
  (* the library's cost and trace check read only the fields the run instance shares with the
     binary instance, so they are the same at both ([ECHL]'s [al_cost] is [acost], which reads
     [as_Cm] and [as_Cf], and its [al_tr_ok] is [atr_ok], which reads [as_TR]) *)
  Proof. exact (AS_InstanceKit.as_instance_kit (fun HC => @ECHL HC) LIB_TRACES TRLEN DOK LT LCOST L_OK
                  (fun _ _ _ _ _ _ _ => eq_refl) (fun _ _ _ _ _ _ T => T) K_libx0). Qed.

  Lemma as_realizes_spec_closed : forall sp brk mbase rnd inp,
    valid_sp sp -> valid_brk asegs brk -> valid_mmap_base mbase ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    valid_creds inp -> valid_hwcap (in_hwcap inp) ->
    (* 08b1429: [Run.valid_input]'s reader clause *)
    in_channel_reader inp = true ->
    (* #38: [Run.valid_input]'s launch clause and [Run.valid_entry]'s fifth conjunct *)
    valid_launch inp ->
    entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
    realizes (run_segments asegs inp sp mbase)
      (init_config (run_segments asegs inp sp mbase) OSSVerify.openssl.echconfiglist_parser.images.Asan.M.init_pc
                   OSSVerify.openssl.echconfiglist_parser.images.Asan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
      (spec (in_argv inp) (in_fs inp)).
  Proof.
    apply (as_realizes_spec EAsChainRun.P_mainK) with (L := fun HC => @ECHL HC); [| exact INSTANCE | exact L_OK | exact FZ_a | exact TR | exact MAIN].
    intros sp0 brk0 mbase rdraw inp T Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Hrdr Hlaunch Hlau Tnil HMAIN.
    rewrite <- LIMIT_eq. exact (EAsChainRun.as_chain_run sp0 brk0 mbase rdraw inp Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Hrdr Hlaunch Hlau T Tnil
      (fun c HP HK HPn => HMAIN c (conj HP (conj HK HPn)))).
  Qed.

  (* [comment removed for export] *)
  Theorem asan_base :
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
      CFG
      LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
      LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
      (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.openssl.echconfiglist_parser.images.Plain.M.loaded_segments OSSVerify.openssl.echconfiglist_parser.images.Plain.M.init_pc OSSVerify.openssl.echconfiglist_parser.images.Plain.M.phdrs)
      (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.openssl.echconfiglist_parser.images.Asan.M.loaded_segments OSSVerify.openssl.echconfiglist_parser.images.Asan.M.init_pc OSSVerify.openssl.echconfiglist_parser.images.Asan.M.phdrs).
  Proof.
    intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid _.
    pose proof (valid_input_va_size _ Hvalid) as Hsv48.
    (* 08b1429: the launch's channel reader, from [Run.valid_input] *)
    pose proof (valid_input_channel_reader _ Hvalid) as Hrdr.
    (* #38: the launch clause, from [Run.valid_input] *)
    pose proof (valid_input_launch _ Hvalid) as Hlaunch.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
    (* #38: [Run.valid_entry]'s fifth conjunct, the launch the start-up invariant is read under *)
    destruct Hens as [Hrsp [Hrbrk [Hrmb [Hrfit Hrlau]]]]. destruct Hent as [Hasp [Habrk [Hamb [Hafit Halau]]]].
    destruct Hvalid as (Hargv & Henvp & Hfs & _ & _ & Hcreds & _ & _ & Hhw & _).
    change CFG with (@the_scfg hunspell_scfg).
    unfold SanitizerBudgets.lim_source, SanitizerBudgets.lim_target.
    apply (shape_strong_equiv_ef_s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spec (in_argv inp) (in_fs inp))).
    (* The plain binary's theorem states its walk against [run_segments ..] from the run's own
       start, and so does the ASan one ([EAsChainRun.as_chain_run]); the agreement theorem asks for
       the target's walk in the [srealizes] form, which [SpinAlg.srealizes_of_realizes] gives. *)
    - exact (RefTop.ref_realizes_spec_san FZ_p rsp rbrk rmb rrnd inp Hrsp Hrbrk Hrfit Hargv Henvp Hfs Hrmb Hrdr Hlaunch Hrlau).
    - apply srealizes_of_realizes.
      exact (as_realizes_spec_closed asp abrk amb arnd inp Hasp Habrk Hamb Hafit Hargv Henvp Hfs Hcreds Hhw Hrdr Hlaunch Halau).
  Qed.
End WithParts.
