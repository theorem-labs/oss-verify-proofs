(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import NArith List ZArith Lia Bool.
Require OssFuzzTheorems.openssl.echconfiglist_parser.images.Plain.
Require OssFuzzTheorems.openssl.echconfiglist_parser.images.AsanUbsan.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import Scfg ShapeAlg ShapeEF SpinAlg ShapeEFS Spec HeapCeil HeapSecret BaseUbsan. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both Require Import AsMainState AsMainCells.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require RefTop.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsCert Require Import EAsStartupTop.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsHole Require EAsChain.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsIface AsIfaceX AsDriverLaws ECH_Iface AsDrvDefs AsMainPre AsInstance AsInstanceMain AsTop AsTargetRun AsMainTop AsMainTails
  ECH_ATraces ECH_ALib ECH_ALibOK AS_InstanceKit.
Import ListNotations.
Import OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section WithParts.
  (* [comment removed for export] *)
  Hypothesis FZ_p : forall (HCEIL : HeapCeil) (HSEC : HeapSecret),
      @OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Ref.ECH_Iface.fuzz_stmt HCEIL (@OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Ref.MallocSR.HS HCEIL HSEC).
  (* [comment removed for export] *)
  Hypothesis FZ_a : forall (HCEIL : HeapCeil) (H : asr), asan_rt_hyps_x H -> As.AInstFacts.ainst_facts H -> As.ECH_Iface.fuzz_stmt H ECHL.

  (* [comment removed for export] *)
  Lemma L_OK : forall (HCEIL : HeapCeil), alib_ok ECHL.
  Proof. intros HCEIL. exact ECHL_ok. Qed.
  Lemma TR : forall (HCEIL : HeapCeil) (H : asr), asan_rt_hyps H -> asan_driver_laws H -> alib_ok ECHL -> As.ECH_Iface.fuzz_stmt H ECHL ->
      as_target_run_stmt H ECHL.
  Proof. intros HCEIL H HH DL LOK FZ. exact (AsTargetRun.as_target_run H HH DL ECHL LOK FZ). Qed.
  Lemma MAIN : forall (HCEIL : HeapCeil) (H : asr), asan_rt_hyps H -> asan_driver_laws H -> as_target_run_stmt H ECHL ->
      (ADRV_LIVE <= as_LIVE_MAX H /\ ADRV_CNT <= as_LIVE_CNT_MAX H) -> as_main_realizes_stmt H ECHL.
  Proof.
    intros HCEIL H HH DL TRH LIVE.
    exact (AsMainTop.as_main_realizes H ECHL (L_OK HCEIL) HH DL TRH LIVE
             (AsMainTails.atail_usage H ECHL DL) (AsMainTails.atail_open H ECHL DL) (AsMainTails.atail_rderr H ECHL DL)).
  Qed.
  (* [comment removed for export] *)
  Lemma INSTANCE : as_instance_stmt P_main ECHL.
  Proof. exact (AS_InstanceKit.as_instance_kit ECHL LIB_TRACES TRLEN DOK LT LCOST K_libx0). Qed.

  Lemma as_realizes_spec_closed : forall sp brk mbase rnd inp,
    valid_sp sp -> valid_brk asegs brk -> valid_mmap_base mbase ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    valid_creds inp -> valid_hwcap (in_hwcap inp) ->
    @srealizes asegs hunspell_scfg
      (init_config asegs OssFuzzTheorems.openssl.echconfiglist_parser.images.AsanUbsan.M.init_pc
                   OssFuzzTheorems.openssl.echconfiglist_parser.images.AsanUbsan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
      (spec (in_argv inp) (in_fs inp)).
  Proof.
    apply (as_realizes_spec P_main) with (L := ECHL); [| exact INSTANCE | exact L_OK | exact FZ_a | exact TR | exact MAIN].
    intros sp0 brk0 mbase rdraw inp T Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Tnil HMAIN.
    rewrite <- LIMIT_eq. exact (EAsChain.as_chain_srealizes sp0 brk0 mbase rdraw inp Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw T Tnil HMAIN).
  Qed.

  (* [comment removed for export] *)
  Theorem asan_base :
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
      CFG
      LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
      LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
      (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.openssl.echconfiglist_parser.images.Plain.M.loaded_segments OssFuzzTheorems.openssl.echconfiglist_parser.images.Plain.M.init_pc OssFuzzTheorems.openssl.echconfiglist_parser.images.Plain.M.phdrs)
      (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.openssl.echconfiglist_parser.images.AsanUbsan.M.loaded_segments OssFuzzTheorems.openssl.echconfiglist_parser.images.AsanUbsan.M.init_pc OssFuzzTheorems.openssl.echconfiglist_parser.images.AsanUbsan.M.phdrs).
  Proof.
    intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid _.
    pose proof (valid_input_va_size _ Hvalid) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
    destruct Hens as [Hrsp [Hrbrk [Hrmb Hrfit]]]. destruct Hent as [Hasp [Habrk [Hamb Hafit]]].
    destruct Hvalid as (Hargv & Henvp & Hfs & _ & Hcreds & _ & _ & Hhw & _).
    change CFG with (@the_scfg hunspell_scfg).
    unfold SanitizerBudgets.lim_source, SanitizerBudgets.lim_target.
    apply (shape_strong_equiv_ef_s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spec (in_argv inp) (in_fs inp))).
    - exact (RefTop.ref_realizes_spec_san FZ_p rsp rbrk rmb rrnd inp Hrsp Hrbrk Hrfit Hargv Henvp Hfs).
    - exact (as_realizes_spec_closed asp abrk amb arnd inp Hasp Habrk Hamb Hafit Hargv Henvp Hfs Hcreds Hhw).
  Qed.
End WithParts.
