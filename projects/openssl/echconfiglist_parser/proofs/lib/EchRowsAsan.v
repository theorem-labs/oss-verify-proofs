(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit Classifier HaltsAllowed.
Require OSSVerify.openssl.echconfiglist_parser.images.Plain.
Require OSSVerify.openssl.echconfiglist_parser.images.Asan.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import Scfg ShapeAlg SpinAlg ShapeEFS Spec HeapCeil HeapSecret
  EchHalts.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require BaseUbsan BaseAsan RefTop AsanInit.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.LimSim Require Import LimSimSys.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require ECH_Iface MallocSR.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As Require AsIface AsIfaceX ECH_Iface ECH_ALib F_time AInstFacts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition ASAN : Image := mkImage OSSVerify.openssl.echconfiglist_parser.images.Asan.M.loaded_segments OSSVerify.openssl.echconfiglist_parser.images.Asan.M.init_pc OSSVerify.openssl.echconfiglist_parser.images.Asan.M.phdrs.

Lemma LIMIT_ge_lim_source : ShippedBudgets.lim_source <= AsanInit.LIMIT.
Proof. unfold AsanInit.LIMIT, ShippedBudgets.lim_source, target_alloc_limit, source_alloc_limit. apply Z.leb_le. vm_compute. reflexivity. Qed.

Section WithLib.
  Hypothesis FZ_p : forall (HCEIL : HeapCeil) (HSEC : HeapSecret),
      @OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref.ECH_Iface.fuzz_stmt HCEIL (@OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref.MallocSR.HS HCEIL HSEC).
  Hypothesis FZ_a : forall (HCEIL : HeapCeil) (H : OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As.AsIface.asr),
      OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As.AsIfaceX.asan_rt_hyps_x H -> OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As.AInstFacts.ainst_facts H -> OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As.ECH_Iface.fuzz_stmt H OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As.ECH_ALib.ECHL.

  (* [comment removed for export] *)
  Lemma as_realizes_spec_rz : forall sp brk mbase rnd inp,
    valid_sp sp -> valid_brk (img_segments ASAN) brk -> valid_mmap_base mbase ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    valid_creds inp -> valid_hwcap (in_hwcap inp) ->
    realizes (img_segments ASAN)
      (init_config (img_segments ASAN) OSSVerify.openssl.echconfiglist_parser.images.Asan.M.init_pc
                   OSSVerify.openssl.echconfiglist_parser.images.Asan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
      (spec (in_argv inp) (in_fs inp)).
  Proof.
    intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hva Hve Hfs Hcr Hhw.
    apply realizes_of_srealizes.
    exact (BaseAsan.as_realizes_spec_closed FZ_a sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hva Hve Hfs Hcr Hhw).
  Qed.

  (* [comment removed for export] *)
  Theorem halts_asan :
    halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source codes02 ASAN.
  Proof.
    intros [asp abrk amb arnd] inp Hent Hvalid Hbudget.
    apply (must_exit_in_scfg_relim_closed forced_only_cfg codes02 ASAN AsanInit.LIMIT ShippedBudgets.lim_source
             (mkEntry asp abrk amb arnd) inp LIMIT_ge_lim_source Hbudget).
    cbn [must_exit_in_scfg ASAN img_segments].
    pose proof (valid_input_va_size _ Hvalid) as Hsv48.
    pose proof Hent as Hent'. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent'.
    destruct Hent' as [Hsp [Hbrk [Hmb Hfit]]].
    destruct Hvalid as (Hargv & Henvp & Hfs & _ & Hcreds & _ & _ & Hhw & _).
    apply (@must_exit_forced_only _ hunspell_scfg).
    apply (realizes_must_exit _ codes02 _ (spec (in_argv inp) (in_fs inp))).
    - exact (as_realizes_spec_rz asp abrk amb arnd inp Hsp Hbrk Hmb Hfit Hargv Henvp Hfs Hcreds Hhw).
    - apply exits_in_spec02.
    - reflexivity.
  Qed.
End WithLib.
