(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF ITreeA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top Require EntryCeil.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport MainFactsAsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require KnTrans__AS.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainEntry__AS.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepInit_kit__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Fuzz_ifaceA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require Drv_ifaceA F_main_AA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GioaReal.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require GStatKit HarnCompA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require StaticsA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require TlsObjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module MainEntryA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top Require Import EntryCeil.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport MainFactsAsan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require KnTrans__AS. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainEntry__AS. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainFactsAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.MainLedgerAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepInit_kit__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_E.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Fuzz_ifaceA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require Import Drv_ifaceA F_main_AA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section MainEntry.
  Variables (en : ExecEntry) (inp : ProcInput) (lim : Z) (w : bool) (V : nat -> Z) (m : amem) (ms : machine_state) (mo : Model).
  Hypothesis AM : amain_open en inp lim w V m ms mo.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP.
  Hypothesis HTLS : tls_at V.
  Variables (U : list (list Z)) (lz : list (word * word)) (AL : word -> Prop).
  Hypothesis HU : (length U <= Z.to_nat AUMAX)%nat.
  Hypothesis A0I : forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p.
  Hypothesis VI : valid_input inp.
  Hypothesis VE : forall img, valid_entry img en inp -> True.
  Hypothesis VSP : valid_sp (en_sp en).
  Hypothesis FITS : entry_stack_fits (en_sp en) (in_argv inp) (in_envp inp).

  Notation USP := (bv_unsigned (en_sp en)).
  Notation L := (mkALayout (LV V) w U).
  Notation LO := (ATOP + 4096).
  Notation RNG := (fp_ok lz AL).

  #[using="inp lim w m ms mo AM"] Lemma me_usp : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = USP.
  Proof. destruct AM as (_ & _ & (_ & _ & _ & E & _) & _). exact E. Qed.

  #[using="en inp lim w ms mo AM"] Lemma me_facts : Forall (mfact_ok asegs V m) asan_mem_facts /\ Forall (pfact_ok V) asan_pure_facts.
  Proof. destruct AM as (_ & _ & _ & HMall & HPall & _). apply Forall_app in HMall as [HM _]. apply Forall_app in HPall as [HP _]. split; assumption. Qed.

  (* [comment removed for export] *)
  #[using="inp lim w V m ms mo AM HAT U HU"] Lemma me_atop : ATOP + 8388608 <= USP <= ATOP + 8388608 + 4080.
  Proof.
    destruct me_facts as [_ HP]. pf V HP (PVar 6 0 255) P6. pose proof me_usp as E. lia.
  Qed.

  #[using="lim m ms mo AM HAT HU VSP FITS"] Lemma me_geometry :
    (ATOP + 4096 <= LO) /\ (LO + MAIN_STACK <= USP - 128) /\ (USP mod 16 = 0) /\ (USP - 160 <= al_top L) /\ (al_top L <= 2^47)
    /\ (USP + Z.of_nat (length (build_stack_bytes a_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en))) <= 2^47).
  Proof.
    destruct me_facts as [_ HP]. pose proof me_atop as A. pose proof me_usp as E.
    (pose proof (alayout_stack_init V w U HP HAT) as ndP__; nd_pre ndP__ 4%nat; intros _ _ _ T47; nd_post).
    split; [lia|]. split; [unfold MAIN_STACK, TARGET_RUN_STACK, FUZZ_STACK, PCAP_L4_STACK, STDIO_STACK; lia|].
    split; [exact (proj2 (proj2 VSP))|].
    split. { unfold al_top. rewrite LV_sp0, E. pose proof (page_round_up_Z_bounds (USP - 0xa0)) as [T1 _]. lia. }
    split; [exact T47|].
    pose proof (build_stack_bytes_within_span a_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)) as B.
    unfold entry_stack_fits, sp_window_hi in FITS. change (2^47) with 140737488355328. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="inp lim w V ms mo AM HAT U HU"] Lemma me_stk : stk asegs m LO (USP + -48).
  Proof.
    destruct AM as (_ & _ & _ & _ & _ & _ & ST & _). pose proof me_atop as A.
    assert (B1 : USP - 8388608 <= LO <= USP) by lia. assert (B2 : LO <= USP + -48 <= USP) by lia.
    destruct (stk_split asegs m (USP - 8388608) LO USP ST B1) as [_ ST1].
    destruct (stk_split asegs m LO (USP + -48) USP ST1 B2) as [ST2 _]. exact ST2.
  Qed.

  (* [comment removed for export] *)
  #[using="rc lim w V ms mo AM HAT U HU VSP FITS"] Lemma me_args : bytes_at asegs m USP (build_stack_bytes a_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)).
  Proof.
    destruct AM as (_ & _ & _ & _ & _ & _ & _ & PRIS & _). (nd_pre me_geometry 6%nat; intros _ _ _ _ _ B47; nd_post). pose proof me_atop as A. pose proof atop_range as AR.
    pose proof (entry_stack_image_top a_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)) as TOPE.
    assert (IMGHI : USP + Z.of_nat (length (entry_stack_image a_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en))) <= 2^64).
    { rewrite TOPE. unfold entry_page_top, entry_block_top, page_round_up_Z, page_size. change (2^47) with 140737488355328 in B47. change (2^64) with 18446744073709551616.
      clear - B47. Z.div_mod_to_equations. lia. }
    assert (SPLO : stack_max_size <= USP) by (change stack_max_size with 8388608; clear - A AR; lia).
    pose proof (init_stack_bytes asegs a_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) SPLO IMGHI) as B0.
    rewrite (entry_image_eq a_phdrs) in B0. apply bytes_at_app in B0. destruct B0 as [B0 _].
    (nd_pre B0 3%nat; intros H0 H1 HB; nd_post). split; [exact H0|]. split; [exact H1|]. intros i Hi. rewrite <- (HB i Hi). unfold mrd.
    rewrite (PRIS (USP + Z.of_nat i)); [reflexivity|]. change (2^64) with 18446744073709551616 in *. lia.
  Qed.

  #[using="en inp lim w V ms mo AM"] Lemma me_mem_inv : mem_inv asegs m.
  Proof. destruct AM as (_ & _ & _ & _ & _ & MI & _). exact MI. Qed.

  (* [comment removed for export] *)
  #[using="inp lim m ms mo AM HAT HTLS HU A0I VSP"] Lemma me_rngs : rngs (en_sp en) L LO RNG.
  Proof.
    destruct me_facts as [_ HP]. pose proof me_atop as A. pose proof me_usp as E. pose proof (tls_at_tp V HTLS) as HTP.
    (pose proof (alayout_stack_init V w U HP HAT) as ndP__; nd_pre ndP__ 4%nat; intros _ _ (TLO & THI) T47; nd_post). pose proof atop_range as AR.
    assert (STK : forall hi, LO <= hi -> hi <= 2^47 -> rng RNG LO (hi - LO)).
    { intros hi H1 H2. change (2^47) with 140737488355328 in H2. pose proof HAT as HAT'.
      eapply (vis_rng lz AL V U A0I HU 13); [reflexivity| | | |]; cbn [fst snd zv nth_error asan_vis asan_vis_app app]; clear -HAT' H1 H2 AR; lia. }
    (pose proof VSP as ndP__; nd_pre ndP__ 3%nat; intros _ SPHI _; nd_post). unfold sp_window_hi in SPHI.
    unfold rngs. split; [apply STK; [clear -TLO; lia| exact T47]|].
    split; [apply STK; [clear -A; lia| change (2^47) with 140737488355328; clear -SPHI; lia]|].
    split. { eapply (vis_rng lz AL V U A0I HU 12); [reflexivity| cbn; clear; lia| cbn; clear; lia| clear; lia| clear; lia]. }
    split. { eapply (vis_rng_sh lz AL V U A0I HU 12); [reflexivity| | | |]; cbn -[Z.div Z.mul]; clear; Z.div_mod_to_equations; lia. }
    rewrite HTP. eapply (vis_rng lz AL V U A0I HU 12); [reflexivity| | | |]; cbn [fst snd zv nth_error asan_vis asan_vis_app app]; clear; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="lim mo AM HAT HTLS HU A0I VI VSP FITS"] Theorem main_entry_handoff : forall {H hptr : Type}
      (GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> amem -> Prop)
      (s : PState H hptr) (FB : list (@cblock hptr)),
    GIOA L RNG s [] FB [] m ->
    main_entry GIOA (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) L LO s RNG ms.
  Proof.
    intros H hptr GIOA s FB G. pose proof AM as (EMS & _). cbv zeta in EMS.
    rewrite <- (tls_at_tp V HTLS) in EMS. unfold main_entry.
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, m, FB.
    split; [rewrite EMS; lazy [mkRl main_regs nth]; reflexivity|].   (* [comment removed for export] *)
    split; [exact G|]. split; [exact me_mem_inv|]. split; [exact me_stk|]. split; [exact (proj1 VI)|]. split; [exact me_rngs| exact me_args].
  Qed.
End MainEntry.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top.EntryCeil.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS.MainFactsAsan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.MainLedgerAsan.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_E.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_main_AA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section MainEntry.
  Variables (en : ExecEntry) (inp : ProcInput) (lim : Z) (w : bool) (V : nat -> Z) (m : amem) (ms : machine_state) (mo : Model).
  Hypothesis AM : amain_open en inp lim w V m ms mo.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP.
  Hypothesis HTLS : tls_at V.
  Variables (U : list (list Z)) (lz : list (word * word)) (AL : word -> Prop).
  Hypothesis HU : (length U <= Z.to_nat AUMAX)%nat.
  Hypothesis A0I : forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p.
  Hypothesis VI : valid_input inp.
  Hypothesis VE : forall img, valid_entry img en inp -> True.
  Hypothesis VSP : valid_sp (en_sp en).
  Hypothesis FITS : entry_stack_fits (en_sp en) (in_argv inp) (in_envp inp).

  Notation USP := (bv_unsigned (en_sp en)).
  Notation L := (mkALayout (LV V) w U).
  Notation LO := (ATOP + 4096).
  Notation RNG := (fp_ok lz AL).

  #[using="inp lim w m ms mo AM"] Lemma me_usp : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = USP.
  Proof. destruct AM as (_ & _ & (_ & _ & _ & E & _) & _). exact E. Qed.

  #[using="en inp lim w ms mo AM"] Lemma me_facts : Forall (mfact_ok asegs V m) asan_mem_facts /\ Forall (pfact_ok V) asan_pure_facts.
  Proof. destruct AM as (_ & _ & _ & HMall & HPall & _). apply Forall_app in HMall as [HM _]. apply Forall_app in HPall as [HP _]. split; assumption. Qed.

  (* [comment removed for export] *)
  #[using="inp lim w V m ms mo AM HAT U HU"] Lemma me_atop : ATOP + 8388608 <= USP <= ATOP + 8388608 + 4080.
  Proof.
    destruct me_facts as [_ HP]. pf V HP (PVar 6 0 255) P6. pose proof me_usp as E. lia.
  Qed.

  #[using="lim m ms mo AM HAT HU VSP FITS"] Lemma me_geometry :
    (ATOP + 4096 <= LO) /\ (LO + MAIN_STACK <= USP - 128) /\ (USP mod 16 = 0) /\ (USP - 160 <= al_top L) /\ (al_top L <= 2^47)
    /\ (USP + Z.of_nat (length (build_stack_bytes a_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en))) <= 2^47).
  Proof.
    destruct me_facts as [_ HP]. pose proof me_atop as A. pose proof me_usp as E.
    (pose proof (alayout_stack_init V w U HP HAT) as ndP__; nd_pre ndP__ 4%nat; intros _ _ _ T47; nd_post).
    split; [lia|]. split; [unfold MAIN_STACK, TARGET_RUN_STACK, FUZZ_STACK, PCAP_L4_STACK, STDIO_STACK; lia|].
    split; [exact (proj2 (proj2 VSP))|].
    split. { unfold al_top. rewrite LV_sp0, E. pose proof (page_round_up_Z_bounds (USP - 0xa0)) as [T1 _]. lia. }
    split; [exact T47|].
    pose proof (build_stack_bytes_within_span a_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)) as B.
    unfold entry_stack_fits, sp_window_hi in FITS. change (2^47) with 140737488355328. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="inp lim w V ms mo AM HAT U HU"] Lemma me_stk : stk asegs m LO (USP + -48).
  Proof.
    destruct AM as (_ & _ & _ & _ & _ & _ & ST & _). pose proof me_atop as A.
    assert (B1 : USP - 8388608 <= LO <= USP) by lia. assert (B2 : LO <= USP + -48 <= USP) by lia.
    destruct (stk_split asegs m (USP - 8388608) LO USP ST B1) as [_ ST1].
    destruct (stk_split asegs m LO (USP + -48) USP ST1 B2) as [ST2 _]. exact ST2.
  Qed.

  (* [comment removed for export] *)
  #[using="rc lim w V ms mo AM HAT U HU VSP FITS"] Lemma me_args : bytes_at asegs m USP (build_stack_bytes a_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)).
  Proof.
    destruct AM as (_ & _ & _ & _ & _ & _ & _ & PRIS & _). (nd_pre me_geometry 6%nat; intros _ _ _ _ _ B47; nd_post). pose proof me_atop as A. pose proof atop_range as AR.
    pose proof (entry_stack_image_top a_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)) as TOPE.
    assert (IMGHI : USP + Z.of_nat (length (entry_stack_image a_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en))) <= 2^64).
    { rewrite TOPE. unfold entry_page_top, entry_block_top, page_round_up_Z, page_size. change (2^47) with 140737488355328 in B47. change (2^64) with 18446744073709551616.
      clear - B47. Z.div_mod_to_equations. lia. }
    assert (SPLO : stack_max_size <= USP) by (change stack_max_size with 8388608; clear - A AR; lia).
    pose proof (init_stack_bytes asegs a_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) SPLO IMGHI) as B0.
    rewrite (entry_image_eq a_phdrs) in B0. apply bytes_at_app in B0. destruct B0 as [B0 _].
    (nd_pre B0 3%nat; intros H0 H1 HB; nd_post). split; [exact H0|]. split; [exact H1|]. intros i Hi. rewrite <- (HB i Hi). unfold mrd.
    rewrite (PRIS (USP + Z.of_nat i)); [reflexivity|]. change (2^64) with 18446744073709551616 in *. lia.
  Qed.

  #[using="en inp lim w V ms mo AM"] Lemma me_mem_inv : mem_inv asegs m.
  Proof. destruct AM as (_ & _ & _ & _ & _ & MI & _). exact MI. Qed.

  (* [comment removed for export] *)
  #[using="inp lim m ms mo AM HAT HTLS HU A0I VSP"] Lemma me_rngs : rngs (en_sp en) L LO RNG.
  Proof.
    destruct me_facts as [_ HP]. pose proof me_atop as A. pose proof me_usp as E. pose proof (tls_at_tp V HTLS) as HTP.
    (pose proof (alayout_stack_init V w U HP HAT) as ndP__; nd_pre ndP__ 4%nat; intros _ _ (TLO & THI) T47; nd_post). pose proof atop_range as AR.
    assert (STK : forall hi, LO <= hi -> hi <= 2^47 -> rng RNG LO (hi - LO)).
    { intros hi H1 H2. change (2^47) with 140737488355328 in H2. pose proof HAT as HAT'.
      eapply (vis_rng lz AL V U A0I HU 13); [reflexivity| | | |]; cbn [fst snd zv nth_error asan_vis asan_vis_app app]; clear -HAT' H1 H2 AR; lia. }
    (pose proof VSP as ndP__; nd_pre ndP__ 3%nat; intros _ SPHI _; nd_post). unfold sp_window_hi in SPHI.
    unfold rngs. split; [apply STK; [clear -TLO; lia| exact T47]|].
    split; [apply STK; [clear -A; lia| change (2^47) with 140737488355328; clear -SPHI; lia]|].
    split. { eapply (vis_rng lz AL V U A0I HU 12); [reflexivity| cbn; clear; lia| cbn; clear; lia| clear; lia| clear; lia]. }
    split. { eapply (vis_rng_sh lz AL V U A0I HU 12); [reflexivity| | | |]; cbn -[Z.div Z.mul]; clear; Z.div_mod_to_equations; lia. }
    rewrite HTP. eapply (vis_rng lz AL V U A0I HU 12); [reflexivity| | | |]; cbn [fst snd zv nth_error asan_vis asan_vis_app app]; clear; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="lim mo AM HAT HTLS HU A0I VI VSP FITS"] Theorem main_entry_handoff : forall {H hptr : Type}
      (GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> amem -> Prop)
      (s : PState H hptr) (FB : list (@cblock hptr)),
    GIOA L RNG s [] FB [] m ->
    main_entry GIOA (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) L LO s RNG ms.
  Proof.
    intros H hptr GIOA s FB G. pose proof AM as (EMS & _). cbv zeta in EMS.
    rewrite <- (tls_at_tp V HTLS) in EMS. unfold main_entry.
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, m, FB.
    split; [rewrite EMS; lazy [mkRl main_regs nth]; reflexivity|].   (* [comment removed for export] *)
    split; [exact G|]. split; [exact me_mem_inv|]. split; [exact me_stk|]. split; [exact (proj1 VI)|]. split; [exact me_rngs| exact me_args].
  Qed.
End MainEntry.
End CANSEC1.
End TwB.
End MainEntryA.

(* [comment removed for export] *)
Module HarnInitA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport MainFactsAsan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require KnTrans__AS. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainEntry__AS. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainFactsAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.MainLedgerAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepInit_kit__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA GioaReal. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require GStatKit HarnCompA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.MainEntryA__A3D.MainEntryA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.GStatKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.HarnCompA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section Init.
  Variables (en : ExecEntry) (inp : ProcInput) (lim : Z) (w : bool) (V : nat -> Z) (m : amem) (ms : machine_state) (mo : Model).
  Hypothesis AM : amain_open en inp lim w V m ms mo.
  #[local] Notation cblk := (@cblock aptr).
  #[local] Notation PS := (PState aheap aptr).
  Let HMP := me_facts en inp lim w V m ms mo AM.

  #[using="en inp lim w V ms mo AM HMP"] Lemma harn_init : forall (L0 : alayout) (R0 : footprint) (s : PS) (FB : list cblk), ps_outfile s = None -> harn_P L0 R0 s FB m.
  Proof.
    intros L0 R0 s FB EO. unfold harn_P. rewrite EO. destruct HMP as [HM HP].
    aimg V m HM 0x5e0c80 [C8 (Z_to_bv 64 0)] OC. exact OC.
  Qed.
End Init.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS.MainFactsAsan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.MainLedgerAsan.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.MainEntryA__A3D.MainEntryA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.GStatKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.HarnCompA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section Init.
  Variables (en : ExecEntry) (inp : ProcInput) (lim : Z) (w : bool) (V : nat -> Z) (m : amem) (ms : machine_state) (mo : Model).
  Hypothesis AM : amain_open en inp lim w V m ms mo.
  #[local] Notation cblk := (@cblock aptr).
  #[local] Notation PS := (PState aheap aptr).
  Let HMP := me_facts en inp lim w V m ms mo AM.

  #[using="en inp lim w V ms mo AM HMP"] Lemma harn_init : forall (L0 : alayout) (R0 : footprint) (s : PS) (FB : list cblk), ps_outfile s = None -> harn_P L0 R0 s FB m.
  Proof.
    intros L0 R0 s FB EO. unfold harn_P. rewrite EO. destruct HMP as [HM HP].
    aimg V m HM 0x5e1080 [C8 (Z_to_bv 64 0)] OC. exact OC.
  Qed.
End Init.
End CANSEC1.
End TwB.
End HarnInitA.

(* [comment removed for export] *)
Module StaticsInitA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport MainFactsAsan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require KnTrans__AS. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainEntry__AS. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainFactsAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.MainLedgerAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepInit_kit__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_E OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Fuzz_ifaceA GioaReal. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require Drv_ifaceA F_main_AA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require GStatKit StaticsA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_main_AA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.MainEntryA__A3D.MainEntryA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.GStatKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.StaticsA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.

(* [comment removed for export] *)
#[using="Type"] Lemma c1_pointwise : forall (m : amem) A (b : byte), rw_cells asegs m A [C1 b] -> 0x603000 <= A -> m (wa A) = Some b.
Proof.
  intros m A b [[_ B] _] HA. cbn [cells_bytes cbytes app] in B. (nd_pre B 3%nat; intros B0 B1 B; nd_post). cbn [length] in B1.
  specialize (B 0%nat ltac:(cbn; lia)). cbn [nth_error] in B. rewrite Z.add_0_r in B.
  rewrite ref_mrd_overlay in B; [exact B|]. right. rewrite wa_unsigned; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma unp_global_cells : forall (m : amem) A n s, s = 2147450880 + A / 8 -> A mod 8 = 0 -> 0 <= A -> 0 < n -> A + n <= 2^47 ->
  (forall i, 0 <= i < n / 8 -> m (wa (s + i)) = Some (Z_to_bv 8 0)) ->
  (n mod 8 <> 0 -> m (wa (s + n / 8)) = Some (Z_to_bv 8 (n mod 8))) ->
  unpoisoned m A (A + n).
Proof.
  intros m A n s -> A8 A0 N0 AN ZR PR. change (2^47) with 140737488355328 in AN. split; [lia|]. split; [lia|].
  intros G H0 H1 H2. change AsanEmbed.ASHOFF with 2147450880.
  destruct (Z_lt_ge_dec (G - A / 8) (n / 8)) as [FULL|PART].
  - exists (Z_to_bv 8 0). split; [| left; apply sval_zero].
    replace (2147450880 + G) with (2147450880 + A / 8 + (G - A / 8)) by lia. apply ZR. Z.div_mod_to_equations. lia.
  - assert (EG : G - A / 8 = n / 8) by (Z.div_mod_to_equations; lia).
    assert (NM : n mod 8 <> 0) by (Z.div_mod_to_equations; lia).
    exists (Z_to_bv 8 (n mod 8)). split.
    + replace (2147450880 + G) with (2147450880 + A / 8 + n / 8) by lia. exact (PR NM).
    + right. rewrite sval_lit by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations. lia.
Qed.

Section Init.
  Variables (en : ExecEntry) (inp : ProcInput) (lim : Z) (w : bool) (V : nat -> Z) (m : amem) (ms : machine_state) (mo : Model).
  Hypothesis AM : amain_open en inp lim w V m ms mo.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP.
  Hypothesis HTLS : tls_at V.
  Variables (U : list (list Z)) (lz : list (word * word)) (AL : word -> Prop).
  Hypothesis HU : (length U <= Z.to_nat AUMAX)%nat.
  Hypothesis A0I : forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p.
  Hypothesis VSP : valid_sp (en_sp en).
  Hypothesis FITS : entry_stack_fits (en_sp en) (in_argv inp) (in_envp inp).

  Notation USP := (bv_unsigned (en_sp en)).
  Notation L := (mkALayout (LV V) w U).
  Notation RNG := (fp_ok lz AL).
  #[local] Notation cblk := (@cblock aptr).
  #[local] Notation PS := (PState aheap aptr).
  Let HMP := me_facts en inp lim w V m ms mo AM.

  #[using="rc en inp lim w V ms mo AM U HU HMP"] Lemma globals_unp_init : Forall (fun g => unpoisoned m (fst g) (fst g + snd g)) client_globals.
  Proof.
    destruct HMP as [HM HP]. unfold client_globals.
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MCell (ZLit 2147467780) 1 (ZLit 2)) PC.
      apply (unp_global_cells m 135200 2 2147467780); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; exfalso; change (2 / 8) with 0 in Hi; lia| intros _; change (2147467780 + 2 / 8) with 2147467780; change (2 mod 8) with 2; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467784) 1) ZC. mf V m HM (MCell (ZLit 2147467785) 1 (ZLit 2)) PC.
      apply (unp_global_cells m 135232 10 2147467784); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (10 / 8) with 1 in Hi; apply (zchunk_pointwise_k m 2147467784 1 ZC); lia| intros _; change (2147467784 + 10 / 8) with 2147467785; change (10 mod 8) with 2; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467788) 3) ZC. mf V m HM (MCell (ZLit 2147467791) 1 (ZLit 6)) PC.
      apply (unp_global_cells m 135264 30 2147467788); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (30 / 8) with 3 in Hi; apply (zchunk_pointwise_k m 2147467788 3 ZC); lia| intros _; change (2147467788 + 30 / 8) with 2147467791; change (30 mod 8) with 6; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467796) 3) ZC. mf V m HM (MCell (ZLit 2147467799) 1 (ZLit 4)) PC.
      apply (unp_global_cells m 135328 28 2147467796); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (28 / 8) with 3 in Hi; apply (zchunk_pointwise_k m 2147467796 3 ZC); lia| intros _; change (2147467796 + 28 / 8) with 2147467799; change (28 mod 8) with 4; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467804) 2) ZC. mf V m HM (MCell (ZLit 2147467806) 1 (ZLit 5)) PC.
      apply (unp_global_cells m 135392 21 2147467804); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (21 / 8) with 2 in Hi; apply (zchunk_pointwise_k m 2147467804 2 ZC); lia| intros _; change (2147467804 + 21 / 8) with 2147467806; change (21 mod 8) with 5; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467812) 2) ZC. mf V m HM (MCell (ZLit 2147467814) 1 (ZLit 6)) PC.
      apply (unp_global_cells m 135456 22 2147467812); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (22 / 8) with 2 in Hi; apply (zchunk_pointwise_k m 2147467812 2 ZC); lia| intros _; change (2147467812 + 22 / 8) with 2147467814; change (22 mod 8) with 6; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467820) 3) ZC. mf V m HM (MCell (ZLit 2147467823) 1 (ZLit 1)) PC.
      apply (unp_global_cells m 135520 25 2147467820); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (25 / 8) with 3 in Hi; apply (zchunk_pointwise_k m 2147467820 3 ZC); lia| intros _; change (2147467820 + 25 / 8) with 2147467823; change (25 mod 8) with 1; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MCell (ZLit 2147467828) 1 (ZLit 3)) PC.
      apply (unp_global_cells m 135584 3 2147467828); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; exfalso; change (3 / 8) with 0 in Hi; lia| intros _; change (2147467828 + 3 / 8) with 2147467828; change (3 mod 8) with 3; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467832) 2) ZC. mf V m HM (MCell (ZLit 2147467834) 1 (ZLit 7)) PC.
      apply (unp_global_cells m 135616 23 2147467832); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (23 / 8) with 2 in Hi; apply (zchunk_pointwise_k m 2147467832 2 ZC); lia| intros _; change (2147467832 + 23 / 8) with 2147467834; change (23 mod 8) with 7; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467840) 13) ZC. mf V m HM (MCell (ZLit 2147467853) 1 (ZLit 5)) PC.
      apply (unp_global_cells m 135744 45 2147467848); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (45 / 8) with 5 in Hi; replace (2147467848 + i) with (2147467840 + (8 + i)) by lia; apply (zchunk_pointwise_k m 2147467840 13 ZC); lia| intros _; change (2147467848 + 45 / 8) with 2147467853; change (45 mod 8) with 5; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467860) 3) ZC. mf V m HM (MCell (ZLit 2147467863) 1 (ZLit 7)) PC.
      apply (unp_global_cells m 135840 31 2147467860); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (31 / 8) with 3 in Hi; apply (zchunk_pointwise_k m 2147467860 3 ZC); lia| intros _; change (2147467860 + 31 / 8) with 2147467863; change (31 mod 8) with 7; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MCell (ZLit 2147467868) 1 (ZLit 3)) PC.
      apply (unp_global_cells m 135904 3 2147467868); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; exfalso; change (3 / 8) with 0 in Hi; lia| intros _; change (2147467868 + 3 / 8) with 2147467868; change (3 mod 8) with 3; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MCell (ZLit 2147467872) 1 (ZLit 3)) PC.
      apply (unp_global_cells m 135936 3 2147467872); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; exfalso; change (3 / 8) with 0 in Hi; lia| intros _; change (2147467872 + 3 / 8) with 2147467872; change (3 mod 8) with 3; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467876) 6) ZC. mf V m HM (MCell (ZLit 2147467882) 1 (ZLit 6)) PC.
      apply (unp_global_cells m 135968 54 2147467876); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (54 / 8) with 6 in Hi; apply (zchunk_pointwise_k m 2147467876 6 ZC); lia| intros _; change (2147467876 + 54 / 8) with 2147467882; change (54 mod 8) with 6; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467888) 3) ZC.
      apply (unp_global_cells m 136064 24 2147467888); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (24 / 8) with 3 in Hi; apply (zchunk_pointwise_k m 2147467888 3 ZC); lia| intros X; exfalso; apply X; reflexivity]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467896) 8) ZC. mf V m HM (MCell (ZLit 2147467904) 1 (ZLit 7)) PC.
      apply (unp_global_cells m 136128 71 2147467896); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (71 / 8) with 8 in Hi; apply (zchunk_pointwise_k m 2147467896 8 ZC); lia| intros _; change (2147467896 + 71 / 8) with 2147467904; change (71 mod 8) with 7; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467912) 2) ZC. mf V m HM (MCell (ZLit 2147467914) 1 (ZLit 4)) PC.
      apply (unp_global_cells m 136256 20 2147467912); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (20 / 8) with 2 in Hi; apply (zchunk_pointwise_k m 2147467912 2 ZC); lia| intros _; change (2147467912 + 20 / 8) with 2147467914; change (20 mod 8) with 4; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467920) 5) ZC. mf V m HM (MCell (ZLit 2147467925) 1 (ZLit 5)) PC.
      apply (unp_global_cells m 136320 45 2147467920); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (45 / 8) with 5 in Hi; apply (zchunk_pointwise_k m 2147467920 5 ZC); lia| intros _; change (2147467920 + 45 / 8) with 2147467925; change (45 mod 8) with 5; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467932) 6) ZC.
      apply (unp_global_cells m 136416 48 2147467932); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (48 / 8) with 6 in Hi; apply (zchunk_pointwise_k m 2147467932 6 ZC); lia| intros X; exfalso; apply X; reflexivity]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467944) 5) ZC. mf V m HM (MCell (ZLit 2147467949) 1 (ZLit 7)) PC.
      apply (unp_global_cells m 136512 47 2147467944); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (47 / 8) with 5 in Hi; apply (zchunk_pointwise_k m 2147467944 5 ZC); lia| intros _; change (2147467944 + 47 / 8) with 2147467949; change (47 mod 8) with 7; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467956) 5) ZC. mf V m HM (MCell (ZLit 2147467961) 1 (ZLit 3)) PC.
      apply (unp_global_cells m 136608 43 2147467956); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (43 / 8) with 5 in Hi; apply (zchunk_pointwise_k m 2147467956 5 ZC); lia| intros _; change (2147467956 + 43 / 8) with 2147467961; change (43 mod 8) with 3; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MCell (ZLit 2147467976) 1 (ZLit 7)) PC.
      apply (unp_global_cells m 136768 7 2147467976); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; exfalso; change (7 / 8) with 0 in Hi; lia| intros _; change (2147467976 + 7 / 8) with 2147467976; change (7 mod 8) with 7; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467980) 2) ZC. mf V m HM (MCell (ZLit 2147467982) 1 (ZLit 2)) PC.
      apply (unp_global_cells m 136800 18 2147467980); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (18 / 8) with 2 in Hi; apply (zchunk_pointwise_k m 2147467980 2 ZC); lia| intros _; change (2147467980 + 18 / 8) with 2147467982; change (18 mod 8) with 2; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467988) 4) ZC. mf V m HM (MCell (ZLit 2147467992) 1 (ZLit 1)) PC.
      apply (unp_global_cells m 136864 33 2147467988); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (33 / 8) with 4 in Hi; apply (zchunk_pointwise_k m 2147467988 4 ZC); lia| intros _; change (2147467988 + 33 / 8) with 2147467992; change (33 mod 8) with 1; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468000) 5) ZC. mf V m HM (MCell (ZLit 2147468005) 1 (ZLit 5)) PC.
      apply (unp_global_cells m 136960 45 2147468000); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (45 / 8) with 5 in Hi; apply (zchunk_pointwise_k m 2147468000 5 ZC); lia| intros _; change (2147468000 + 45 / 8) with 2147468005; change (45 mod 8) with 5; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MCell (ZLit 2147468020) 1 (ZLit 3)) PC.
      apply (unp_global_cells m 137120 3 2147468020); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; exfalso; change (3 / 8) with 0 in Hi; lia| intros _; change (2147468020 + 3 / 8) with 2147468020; change (3 mod 8) with 3; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MCell (ZLit 2147468032) 1 (ZLit 7)) PC.
      apply (unp_global_cells m 137216 7 2147468032); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; exfalso; change (7 / 8) with 0 in Hi; lia| intros _; change (2147468032 + 7 / 8) with 2147468032; change (7 mod 8) with 7; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468036) 3) ZC. mf V m HM (MCell (ZLit 2147468039) 1 (ZLit 1)) PC.
      apply (unp_global_cells m 137248 25 2147468036); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (25 / 8) with 3 in Hi; apply (zchunk_pointwise_k m 2147468036 3 ZC); lia| intros _; change (2147468036 + 25 / 8) with 2147468039; change (25 mod 8) with 1; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468044) 103) ZC.
      apply (unp_global_cells m 138112 24 2147468144); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (24 / 8) with 3 in Hi; replace (2147468144 + i) with (2147468044 + (100 + i)) by lia; apply (zchunk_pointwise_k m 2147468044 103 ZC); lia| intros X; exfalso; apply X; reflexivity]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468152) 8) ZC. mf V m HM (MCell (ZLit 2147468160) 1 (ZLit 7)) PC.
      apply (unp_global_cells m 138176 71 2147468152); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (71 / 8) with 8 in Hi; apply (zchunk_pointwise_k m 2147468152 8 ZC); lia| intros _; change (2147468152 + 71 / 8) with 2147468160; change (71 mod 8) with 7; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468168) 5) ZC.
      apply (unp_global_cells m 138304 40 2147468168); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (40 / 8) with 5 in Hi; apply (zchunk_pointwise_k m 2147468168 5 ZC); lia| intros X; exfalso; apply X; reflexivity]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468180) 6) ZC. mf V m HM (MCell (ZLit 2147468186) 1 (ZLit 3)) PC.
      apply (unp_global_cells m 138400 51 2147468180); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (51 / 8) with 6 in Hi; apply (zchunk_pointwise_k m 2147468180 6 ZC); lia| intros _; change (2147468180 + 51 / 8) with 2147468186; change (51 mod 8) with 3; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468192) 4) ZC. mf V m HM (MCell (ZLit 2147468196) 1 (ZLit 1)) PC.
      apply (unp_global_cells m 138496 33 2147468192); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (33 / 8) with 4 in Hi; apply (zchunk_pointwise_k m 2147468192 4 ZC); lia| intros _; change (2147468192 + 33 / 8) with 2147468196; change (33 mod 8) with 1; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468204) 1) ZC. mf V m HM (MCell (ZLit 2147468205) 1 (ZLit 6)) PC.
      apply (unp_global_cells m 138592 14 2147468204); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (14 / 8) with 1 in Hi; apply (zchunk_pointwise_k m 2147468204 1 ZC); lia| intros _; change (2147468204 + 14 / 8) with 2147468205; change (14 mod 8) with 6; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468208) 8) ZC. mf V m HM (MCell (ZLit 2147468216) 1 (ZLit 2)) PC.
      apply (unp_global_cells m 138624 66 2147468208); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (66 / 8) with 8 in Hi; apply (zchunk_pointwise_k m 2147468208 8 ZC); lia| intros _; change (2147468208 + 66 / 8) with 2147468216; change (66 mod 8) with 2; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468224) 7) ZC. mf V m HM (MCell (ZLit 2147468231) 1 (ZLit 4)) PC.
      apply (unp_global_cells m 138752 60 2147468224); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (60 / 8) with 7 in Hi; apply (zchunk_pointwise_k m 2147468224 7 ZC); lia| intros _; change (2147468224 + 60 / 8) with 2147468231; change (60 mod 8) with 4; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468236) 7) ZC. mf V m HM (MCell (ZLit 2147468243) 1 (ZLit 4)) PC.
      apply (unp_global_cells m 138848 60 2147468236); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (60 / 8) with 7 in Hi; apply (zchunk_pointwise_k m 2147468236 7 ZC); lia| intros _; change (2147468236 + 60 / 8) with 2147468243; change (60 mod 8) with 4; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468248) 8) ZC. mf V m HM (MCell (ZLit 2147468256) 1 (ZLit 3)) PC.
      apply (unp_global_cells m 138944 67 2147468248); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (67 / 8) with 8 in Hi; apply (zchunk_pointwise_k m 2147468248 8 ZC); lia| intros _; change (2147468248 + 67 / 8) with 2147468256; change (67 mod 8) with 3; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468264) 8) ZC. mf V m HM (MCell (ZLit 2147468272) 1 (ZLit 3)) PC.
      apply (unp_global_cells m 139072 67 2147468264); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (67 / 8) with 8 in Hi; apply (zchunk_pointwise_k m 2147468264 8 ZC); lia| intros _; change (2147468264 + 67 / 8) with 2147468272; change (67 mod 8) with 3; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468280) 11) ZC. mf V m HM (MCell (ZLit 2147468291) 1 (ZLit 4)) PC.
      apply (unp_global_cells m 139264 28 2147468288); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (28 / 8) with 3 in Hi; replace (2147468288 + i) with (2147468280 + (8 + i)) by lia; apply (zchunk_pointwise_k m 2147468280 11 ZC); lia| intros _; change (2147468288 + 28 / 8) with 2147468291; change (28 mod 8) with 4; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468296) 11) ZC.
      apply (unp_global_cells m 139392 24 2147468304); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (24 / 8) with 3 in Hi; replace (2147468304 + i) with (2147468296 + (8 + i)) by lia; apply (zchunk_pointwise_k m 2147468296 11 ZC); lia| intros X; exfalso; apply X; reflexivity]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468312) 12) ZC.
      apply (unp_global_cells m 139456 96 2147468312); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (96 / 8) with 12 in Hi; apply (zchunk_pointwise_k m 2147468312 12 ZC); lia| intros X; exfalso; apply X; reflexivity]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468328) 4) ZC. mf V m HM (MCell (ZLit 2147468332) 1 (ZLit 1)) PC.
      apply (unp_global_cells m 139584 33 2147468328); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (33 / 8) with 4 in Hi; apply (zchunk_pointwise_k m 2147468328 4 ZC); lia| intros _; change (2147468328 + 33 / 8) with 2147468332; change (33 mod 8) with 1; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468340) 1) ZC. mf V m HM (MCell (ZLit 2147468341) 1 (ZLit 6)) PC.
      apply (unp_global_cells m 139680 14 2147468340); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (14 / 8) with 1 in Hi; apply (zchunk_pointwise_k m 2147468340 1 ZC); lia| intros _; change (2147468340 + 14 / 8) with 2147468341; change (14 mod 8) with 6; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468344) 5) ZC. mf V m HM (MCell (ZLit 2147468349) 1 (ZLit 2)) PC.
      apply (unp_global_cells m 139712 42 2147468344); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (42 / 8) with 5 in Hi; apply (zchunk_pointwise_k m 2147468344 5 ZC); lia| intros _; change (2147468344 + 42 / 8) with 2147468349; change (42 mod 8) with 2; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468356) 6) ZC. mf V m HM (MCell (ZLit 2147468362) 1 (ZLit 5)) PC.
      apply (unp_global_cells m 139808 53 2147468356); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (53 / 8) with 6 in Hi; apply (zchunk_pointwise_k m 2147468356 6 ZC); lia| intros _; change (2147468356 + 53 / 8) with 2147468362; change (53 mod 8) with 5; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468368) 9) ZC. mf V m HM (MCell (ZLit 2147468377) 1 (ZLit 4)) PC.
      apply (unp_global_cells m 139904 76 2147468368); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (76 / 8) with 9 in Hi; apply (zchunk_pointwise_k m 2147468368 9 ZC); lia| intros _; change (2147468368 + 76 / 8) with 2147468377; change (76 mod 8) with 4; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468384) 8) ZC. mf V m HM (MCell (ZLit 2147468392) 1 (ZLit 2)) PC.
      apply (unp_global_cells m 140032 66 2147468384); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (66 / 8) with 8 in Hi; apply (zchunk_pointwise_k m 2147468384 8 ZC); lia| intros _; change (2147468384 + 66 / 8) with 2147468392; change (66 mod 8) with 2; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468400) 6) ZC. mf V m HM (MCell (ZLit 2147468406) 1 (ZLit 3)) PC.
      apply (unp_global_cells m 140160 51 2147468400); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (51 / 8) with 6 in Hi; apply (zchunk_pointwise_k m 2147468400 6 ZC); lia| intros _; change (2147468400 + 51 / 8) with 2147468406; change (51 mod 8) with 3; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468412) 9) ZC. mf V m HM (MCell (ZLit 2147468421) 1 (ZLit 1)) PC.
      apply (unp_global_cells m 140256 73 2147468412); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (73 / 8) with 9 in Hi; apply (zchunk_pointwise_k m 2147468412 9 ZC); lia| intros _; change (2147468412 + 73 / 8) with 2147468421; change (73 mod 8) with 1; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468428) 4) ZC. mf V m HM (MCell (ZLit 2147468432) 1 (ZLit 2)) PC.
      apply (unp_global_cells m 140384 34 2147468428); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (34 / 8) with 4 in Hi; apply (zchunk_pointwise_k m 2147468428 4 ZC); lia| intros _; change (2147468428 + 34 / 8) with 2147468432; change (34 mod 8) with 2; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468440) 7) ZC. mf V m HM (MCell (ZLit 2147468447) 1 (ZLit 3)) PC.
      apply (unp_global_cells m 140480 59 2147468440); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (59 / 8) with 7 in Hi; apply (zchunk_pointwise_k m 2147468440 7 ZC); lia| intros _; change (2147468440 + 59 / 8) with 2147468447; change (59 mod 8) with 3; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468452) 6) ZC. mf V m HM (MCell (ZLit 2147468458) 1 (ZLit 2)) PC.
      apply (unp_global_cells m 140576 50 2147468452); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (50 / 8) with 6 in Hi; apply (zchunk_pointwise_k m 2147468452 6 ZC); lia| intros _; change (2147468452 + 50 / 8) with 2147468458; change (50 mod 8) with 2; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468464) 4) ZC. mf V m HM (MCell (ZLit 2147468468) 1 (ZLit 4)) PC.
      apply (unp_global_cells m 140672 36 2147468464); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (36 / 8) with 4 in Hi; apply (zchunk_pointwise_k m 2147468464 4 ZC); lia| intros _; change (2147468464 + 36 / 8) with 2147468468; change (36 mod 8) with 4; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468476) 7) ZC. mf V m HM (MCell (ZLit 2147468483) 1 (ZLit 4)) PC.
      apply (unp_global_cells m 140768 60 2147468476); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (60 / 8) with 7 in Hi; apply (zchunk_pointwise_k m 2147468476 7 ZC); lia| intros _; change (2147468476 + 60 / 8) with 2147468483; change (60 mod 8) with 4; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468488) 9) ZC.
      apply (unp_global_cells m 140864 72 2147468488); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (72 / 8) with 9 in Hi; apply (zchunk_pointwise_k m 2147468488 9 ZC); lia| intros X; exfalso; apply X; reflexivity]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468504) 8) ZC. mf V m HM (MCell (ZLit 2147468512) 1 (ZLit 6)) PC.
      apply (unp_global_cells m 140992 70 2147468504); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (70 / 8) with 8 in Hi; apply (zchunk_pointwise_k m 2147468504 8 ZC); lia| intros _; change (2147468504 + 70 / 8) with 2147468512; change (70 mod 8) with 6; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468520) 8) ZC.
      apply (unp_global_cells m 141120 64 2147468520); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (64 / 8) with 8 in Hi; apply (zchunk_pointwise_k m 2147468520 8 ZC); lia| intros X; exfalso; apply X; reflexivity]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468532) 9) ZC. mf V m HM (MCell (ZLit 2147468541) 1 (ZLit 3)) PC.
      apply (unp_global_cells m 141216 75 2147468532); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (75 / 8) with 9 in Hi; apply (zchunk_pointwise_k m 2147468532 9 ZC); lia| intros _; change (2147468532 + 75 / 8) with 2147468541; change (75 mod 8) with 3; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468548) 9) ZC. mf V m HM (MCell (ZLit 2147468557) 1 (ZLit 4)) PC.
      apply (unp_global_cells m 141344 76 2147468548); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (76 / 8) with 9 in Hi; apply (zchunk_pointwise_k m 2147468548 9 ZC); lia| intros _; change (2147468548 + 76 / 8) with 2147468557; change (76 mod 8) with 4; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468564) 8) ZC. mf V m HM (MCell (ZLit 2147468572) 1 (ZLit 7)) PC.
      apply (unp_global_cells m 141472 71 2147468564); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (71 / 8) with 8 in Hi; apply (zchunk_pointwise_k m 2147468564 8 ZC); lia| intros _; change (2147468564 + 71 / 8) with 2147468572; change (71 mod 8) with 7; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468580) 8) ZC. mf V m HM (MCell (ZLit 2147468588) 1 (ZLit 1)) PC.
      apply (unp_global_cells m 141600 65 2147468580); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (65 / 8) with 8 in Hi; apply (zchunk_pointwise_k m 2147468580 8 ZC); lia| intros _; change (2147468580 + 65 / 8) with 2147468588; change (65 mod 8) with 1; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468596) 9) ZC. mf V m HM (MCell (ZLit 2147468605) 1 (ZLit 2)) PC.
      apply (unp_global_cells m 141728 74 2147468596); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (74 / 8) with 9 in Hi; apply (zchunk_pointwise_k m 2147468596 9 ZC); lia| intros _; change (2147468596 + 74 / 8) with 2147468605; change (74 mod 8) with 2; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468612) 12) ZC.
      apply (unp_global_cells m 141856 96 2147468612); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (96 / 8) with 12 in Hi; apply (zchunk_pointwise_k m 2147468612 12 ZC); lia| intros X; exfalso; apply X; reflexivity]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468628) 6) ZC. mf V m HM (MCell (ZLit 2147468634) 1 (ZLit 1)) PC.
      apply (unp_global_cells m 141984 49 2147468628); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (49 / 8) with 6 in Hi; apply (zchunk_pointwise_k m 2147468628 6 ZC); lia| intros _; change (2147468628 + 49 / 8) with 2147468634; change (49 mod 8) with 1; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468640) 7) ZC. mf V m HM (MCell (ZLit 2147468647) 1 (ZLit 1)) PC.
      apply (unp_global_cells m 142080 57 2147468640); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (57 / 8) with 7 in Hi; apply (zchunk_pointwise_k m 2147468640 7 ZC); lia| intros _; change (2147468640 + 57 / 8) with 2147468647; change (57 mod 8) with 1; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468652) 6) ZC.
      apply (unp_global_cells m 142176 48 2147468652); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (48 / 8) with 6 in Hi; apply (zchunk_pointwise_k m 2147468652 6 ZC); lia| intros X; exfalso; apply X; reflexivity]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468664) 12) ZC.
      apply (unp_global_cells m 142272 96 2147468664); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (96 / 8) with 12 in Hi; apply (zchunk_pointwise_k m 2147468664 12 ZC); lia| intros X; exfalso; apply X; reflexivity]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468680) 7) ZC. mf V m HM (MCell (ZLit 2147468687) 1 (ZLit 4)) PC.
      apply (unp_global_cells m 142400 60 2147468680); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (60 / 8) with 7 in Hi; apply (zchunk_pointwise_k m 2147468680 7 ZC); lia| intros _; change (2147468680 + 60 / 8) with 2147468687; change (60 mod 8) with 4; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZero (ZLit 2147538406) 682923) ZZ.
      apply (unp_global_cells m 6163584 8 2148221328); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (8 / 8) with 1 in Hi; replace (2148221328 + i) with (2147538406 + (682922 + i)) by lia; apply ZZ; lia| intros X; exfalso; apply X; reflexivity]. }
    apply Forall_nil.
  Qed.

  #[using="rc en inp lim w V ms mo AM U HU HMP"] Lemma globals_init : forall (L0 : alayout) (R0 : footprint) (s : PS) (FB : list cblk), globals_P L0 R0 s FB m.
  Proof.
    intros L0 R0 s FB. split; [| exact globals_unp_init]. destruct HMP as [HM HP]. mwr V m HM (ZLit 2147459072) 779776 WR. exact WR.
  Qed.

  #[using="rc en inp lim w V ms mo AM U HU HMP"] Lemma stdinp_init : forall (L0 : alayout) (R0 : footprint) (s : PS) (FB : list cblk), stdinp_P L0 R0 s FB m.
  Proof.
    intros L0 R0 s FB. destruct HMP as [HM HP]. mf V m HM (MZero (ZLit 2147468692) 69154) Z1. unfold stdinp_P.
    eapply (unpoisoned_of_zero m 2147468692 (2147468692 + 69154) (fun _ => 0)).
    - apply shadow_bytes_of_pointwise; [exact Z1| lia| lia].
    - intros; reflexivity.
    - unfold STDIN_P. rewrite shad_div. change AsanEmbed.ASHOFF with 2147450880. vm_compute. discriminate.
    - unfold STDIN_P. rewrite shad_div. change AsanEmbed.ASHOFF with 2147450880. vm_compute. discriminate.
    - unfold STDIN_P. lia.
    - unfold STDIN_P. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="tlsI en inp lim ms mo AM HAT HTLS HU A0I HMP"] Lemma stacksh_init : forall (s : PS) (FB : list cblk), stacksh_P L RNG s FB m.
  Proof.
    intros s FB. destruct HMP as [HM HP]. (pose proof AM as ndP__; nd_pre ndP__ 11%nat; intros _ _ _ _ _ _ _ _ _ _ SH1; nd_post).
    (pose proof (alayout_stack_init V w U HP HAT) as ndP__; nd_pre ndP__ 4%nat; intros _ TPG (TLO & THI) T47; nd_post). pose proof atop_range as AR. pose proof ATOP_pg as PG.
    pose proof (alayout_ok_init V w U HP HU HAT HTLS) as ALO.
    (pose proof (ao_res L ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ RESHI _; nd_post). (pose proof (ao_ctx L ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ CTXHI _; nd_post).
    change (al_res L) with (4096 * V 208%nat) in RESHI. rewrite LV_ctx in CTXHI.
    pose proof (tls_at_tp V HTLS) as HTP. pose proof ATPv_hi as THI0. rewrite HTP in THI0.
    pf V HP (PVar 209 0 15) P209.
    set (T := al_top L) in *. change (2^47) with 140737488355328 in T47.
    assert (E1 : shad (ATOP + 4096) = 2147450880 + (ATOP + 4096) / 8) by (rewrite shad_div; reflexivity).
    assert (E2 : shad T = 2147450880 + T / 8) by (rewrite shad_div; reflexivity).
    unfold stacksh_P. fold T. rewrite E1, E2.
    assert (LEN : 0 < 2147450880 + T / 8 - (2147450880 + (ATOP + 4096) / 8)) by (clear - TLO; Z.div_mod_to_equations; lia).
    destruct (shadow_zero_run V m (2147450880 + (ATOP + 4096) / 8) (2147450880 + T / 8 - (2147450880 + (ATOP + 4096) / 8)) SH1 HM HP LEN) as (Z0 & WR & _).
    { intros a Ha. right. clear - Ha AR T47. Z.div_mod_to_equations. lia. }
    { intros a Ha. change OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReadyA.ASHOFF with 2147450880.
      split; [clear - Ha AR; Z.div_mod_to_equations; lia|].
      split; [clear - Ha AR RESHI P209; Z.div_mod_to_equations; lia|].
      clear - Ha AR CTXHI; Z.div_mod_to_equations; lia. }
    split; [exact TPG|]. split; [change (2^47) with 140737488355328; clear - TLO T47; lia|].
    split.
    { eapply (unpoisoned_of_zero m (2147450880 + (ATOP + 4096) / 8) (2147450880 + T / 8) (fun _ => 0)).
      - replace (2147450880 + T / 8) with (2147450880 + (ATOP + 4096) / 8 + (2147450880 + T / 8 - (2147450880 + (ATOP + 4096) / 8))) by lia.
        apply shadow_bytes_of_pointwise; [exact Z0| clear - AR; Z.div_mod_to_equations; lia| clear - AR T47; Z.div_mod_to_equations; lia].
      - intros; reflexivity.
      - rewrite shad_div. change AsanEmbed.ASHOFF with 2147450880. lia.
      - rewrite shad_div. change AsanEmbed.ASHOFF with 2147450880. clear - TPG TLO AR. Z.div_mod_to_equations. lia.
      - clear - AR. lia.
      - clear - T47. lia. }
    split; [exact WR|].
    eapply (vis_rng_sh lz AL V U A0I HU 13); [reflexivity| | | |]; cbn [fst snd zv nth_error asan_vis asan_vis_app app]; clear - HAT AR T47 TLO PG; Z.div_mod_to_equations; lia.
  Qed.
End Init.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS.MainFactsAsan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.MainLedgerAsan.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_E.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_main_AA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.MainEntryA__A3D.MainEntryA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.GStatKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.StaticsA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.

(* [comment removed for export] *)
#[using="Type"] Lemma c1_pointwise : forall (m : amem) A (b : byte), rw_cells asegs m A [C1 b] -> 0x604000 <= A -> m (wa A) = Some b.
Proof.
  intros m A b [[_ B] _] HA. cbn [cells_bytes cbytes app] in B. (nd_pre B 3%nat; intros B0 B1 B; nd_post). cbn [length] in B1.
  specialize (B 0%nat ltac:(cbn; lia)). cbn [nth_error] in B. rewrite Z.add_0_r in B.
  rewrite ref_mrd_overlay in B; [exact B|]. right. rewrite wa_unsigned; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma unp_global_cells : forall (m : amem) A n s, s = 2147450880 + A / 8 -> A mod 8 = 0 -> 0 <= A -> 0 < n -> A + n <= 2^47 ->
  (forall i, 0 <= i < n / 8 -> m (wa (s + i)) = Some (Z_to_bv 8 0)) ->
  (n mod 8 <> 0 -> m (wa (s + n / 8)) = Some (Z_to_bv 8 (n mod 8))) ->
  unpoisoned m A (A + n).
Proof.
  intros m A n s -> A8 A0 N0 AN ZR PR. change (2^47) with 140737488355328 in AN. split; [lia|]. split; [lia|].
  intros G H0 H1 H2. change AsanEmbed.ASHOFF with 2147450880.
  destruct (Z_lt_ge_dec (G - A / 8) (n / 8)) as [FULL|PART].
  - exists (Z_to_bv 8 0). split; [| left; apply sval_zero].
    replace (2147450880 + G) with (2147450880 + A / 8 + (G - A / 8)) by lia. apply ZR. Z.div_mod_to_equations. lia.
  - assert (EG : G - A / 8 = n / 8) by (Z.div_mod_to_equations; lia).
    assert (NM : n mod 8 <> 0) by (Z.div_mod_to_equations; lia).
    exists (Z_to_bv 8 (n mod 8)). split.
    + replace (2147450880 + G) with (2147450880 + A / 8 + n / 8) by lia. exact (PR NM).
    + right. rewrite sval_lit by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations. lia.
Qed.

Section Init.
  Variables (en : ExecEntry) (inp : ProcInput) (lim : Z) (w : bool) (V : nat -> Z) (m : amem) (ms : machine_state) (mo : Model).
  Hypothesis AM : amain_open en inp lim w V m ms mo.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP.
  Hypothesis HTLS : tls_at V.
  Variables (U : list (list Z)) (lz : list (word * word)) (AL : word -> Prop).
  Hypothesis HU : (length U <= Z.to_nat AUMAX)%nat.
  Hypothesis A0I : forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p.
  Hypothesis VSP : valid_sp (en_sp en).
  Hypothesis FITS : entry_stack_fits (en_sp en) (in_argv inp) (in_envp inp).

  Notation USP := (bv_unsigned (en_sp en)).
  Notation L := (mkALayout (LV V) w U).
  Notation RNG := (fp_ok lz AL).
  #[local] Notation cblk := (@cblock aptr).
  #[local] Notation PS := (PState aheap aptr).
  Let HMP := me_facts en inp lim w V m ms mo AM.

  #[using="rc en inp lim w V ms mo AM U HU HMP"] Lemma globals_unp_init : Forall (fun g => unpoisoned m (fst g) (fst g + snd g)) client_globals.
  Proof.
    destruct HMP as [HM HP]. unfold client_globals.
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MCell (ZLit 2147467780) 1 (ZLit 2)) PC.
      apply (unp_global_cells m 135200 2 2147467780); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; exfalso; change (2 / 8) with 0 in Hi; lia| intros _; change (2147467780 + 2 / 8) with 2147467780; change (2 mod 8) with 2; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467784) 1) ZC. mf V m HM (MCell (ZLit 2147467785) 1 (ZLit 2)) PC.
      apply (unp_global_cells m 135232 10 2147467784); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (10 / 8) with 1 in Hi; apply (zchunk_pointwise_k m 2147467784 1 ZC); lia| intros _; change (2147467784 + 10 / 8) with 2147467785; change (10 mod 8) with 2; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467788) 3) ZC. mf V m HM (MCell (ZLit 2147467791) 1 (ZLit 6)) PC.
      apply (unp_global_cells m 135264 30 2147467788); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (30 / 8) with 3 in Hi; apply (zchunk_pointwise_k m 2147467788 3 ZC); lia| intros _; change (2147467788 + 30 / 8) with 2147467791; change (30 mod 8) with 6; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467796) 3) ZC. mf V m HM (MCell (ZLit 2147467799) 1 (ZLit 4)) PC.
      apply (unp_global_cells m 135328 28 2147467796); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (28 / 8) with 3 in Hi; apply (zchunk_pointwise_k m 2147467796 3 ZC); lia| intros _; change (2147467796 + 28 / 8) with 2147467799; change (28 mod 8) with 4; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467804) 2) ZC. mf V m HM (MCell (ZLit 2147467806) 1 (ZLit 5)) PC.
      apply (unp_global_cells m 135392 21 2147467804); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (21 / 8) with 2 in Hi; apply (zchunk_pointwise_k m 2147467804 2 ZC); lia| intros _; change (2147467804 + 21 / 8) with 2147467806; change (21 mod 8) with 5; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467812) 2) ZC. mf V m HM (MCell (ZLit 2147467814) 1 (ZLit 6)) PC.
      apply (unp_global_cells m 135456 22 2147467812); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (22 / 8) with 2 in Hi; apply (zchunk_pointwise_k m 2147467812 2 ZC); lia| intros _; change (2147467812 + 22 / 8) with 2147467814; change (22 mod 8) with 6; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467820) 3) ZC. mf V m HM (MCell (ZLit 2147467823) 1 (ZLit 1)) PC.
      apply (unp_global_cells m 135520 25 2147467820); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (25 / 8) with 3 in Hi; apply (zchunk_pointwise_k m 2147467820 3 ZC); lia| intros _; change (2147467820 + 25 / 8) with 2147467823; change (25 mod 8) with 1; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MCell (ZLit 2147467828) 1 (ZLit 3)) PC.
      apply (unp_global_cells m 135584 3 2147467828); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; exfalso; change (3 / 8) with 0 in Hi; lia| intros _; change (2147467828 + 3 / 8) with 2147467828; change (3 mod 8) with 3; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467832) 2) ZC. mf V m HM (MCell (ZLit 2147467834) 1 (ZLit 7)) PC.
      apply (unp_global_cells m 135616 23 2147467832); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (23 / 8) with 2 in Hi; apply (zchunk_pointwise_k m 2147467832 2 ZC); lia| intros _; change (2147467832 + 23 / 8) with 2147467834; change (23 mod 8) with 7; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467840) 13) ZC. mf V m HM (MCell (ZLit 2147467853) 1 (ZLit 5)) PC.
      apply (unp_global_cells m 135744 45 2147467848); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (45 / 8) with 5 in Hi; replace (2147467848 + i) with (2147467840 + (8 + i)) by lia; apply (zchunk_pointwise_k m 2147467840 13 ZC); lia| intros _; change (2147467848 + 45 / 8) with 2147467853; change (45 mod 8) with 5; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467860) 3) ZC. mf V m HM (MCell (ZLit 2147467863) 1 (ZLit 7)) PC.
      apply (unp_global_cells m 135840 31 2147467860); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (31 / 8) with 3 in Hi; apply (zchunk_pointwise_k m 2147467860 3 ZC); lia| intros _; change (2147467860 + 31 / 8) with 2147467863; change (31 mod 8) with 7; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MCell (ZLit 2147467868) 1 (ZLit 3)) PC.
      apply (unp_global_cells m 135904 3 2147467868); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; exfalso; change (3 / 8) with 0 in Hi; lia| intros _; change (2147467868 + 3 / 8) with 2147467868; change (3 mod 8) with 3; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MCell (ZLit 2147467872) 1 (ZLit 3)) PC.
      apply (unp_global_cells m 135936 3 2147467872); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; exfalso; change (3 / 8) with 0 in Hi; lia| intros _; change (2147467872 + 3 / 8) with 2147467872; change (3 mod 8) with 3; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467876) 6) ZC. mf V m HM (MCell (ZLit 2147467882) 1 (ZLit 6)) PC.
      apply (unp_global_cells m 135968 54 2147467876); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (54 / 8) with 6 in Hi; apply (zchunk_pointwise_k m 2147467876 6 ZC); lia| intros _; change (2147467876 + 54 / 8) with 2147467882; change (54 mod 8) with 6; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467888) 3) ZC.
      apply (unp_global_cells m 136064 24 2147467888); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (24 / 8) with 3 in Hi; apply (zchunk_pointwise_k m 2147467888 3 ZC); lia| intros X; exfalso; apply X; reflexivity]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467896) 8) ZC. mf V m HM (MCell (ZLit 2147467904) 1 (ZLit 7)) PC.
      apply (unp_global_cells m 136128 71 2147467896); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (71 / 8) with 8 in Hi; apply (zchunk_pointwise_k m 2147467896 8 ZC); lia| intros _; change (2147467896 + 71 / 8) with 2147467904; change (71 mod 8) with 7; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467912) 2) ZC. mf V m HM (MCell (ZLit 2147467914) 1 (ZLit 4)) PC.
      apply (unp_global_cells m 136256 20 2147467912); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (20 / 8) with 2 in Hi; apply (zchunk_pointwise_k m 2147467912 2 ZC); lia| intros _; change (2147467912 + 20 / 8) with 2147467914; change (20 mod 8) with 4; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467920) 5) ZC. mf V m HM (MCell (ZLit 2147467925) 1 (ZLit 5)) PC.
      apply (unp_global_cells m 136320 45 2147467920); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (45 / 8) with 5 in Hi; apply (zchunk_pointwise_k m 2147467920 5 ZC); lia| intros _; change (2147467920 + 45 / 8) with 2147467925; change (45 mod 8) with 5; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467932) 6) ZC.
      apply (unp_global_cells m 136416 48 2147467932); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (48 / 8) with 6 in Hi; apply (zchunk_pointwise_k m 2147467932 6 ZC); lia| intros X; exfalso; apply X; reflexivity]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467944) 5) ZC. mf V m HM (MCell (ZLit 2147467949) 1 (ZLit 7)) PC.
      apply (unp_global_cells m 136512 47 2147467944); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (47 / 8) with 5 in Hi; apply (zchunk_pointwise_k m 2147467944 5 ZC); lia| intros _; change (2147467944 + 47 / 8) with 2147467949; change (47 mod 8) with 7; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467956) 5) ZC. mf V m HM (MCell (ZLit 2147467961) 1 (ZLit 3)) PC.
      apply (unp_global_cells m 136608 43 2147467956); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (43 / 8) with 5 in Hi; apply (zchunk_pointwise_k m 2147467956 5 ZC); lia| intros _; change (2147467956 + 43 / 8) with 2147467961; change (43 mod 8) with 3; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MCell (ZLit 2147467976) 1 (ZLit 7)) PC.
      apply (unp_global_cells m 136768 7 2147467976); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; exfalso; change (7 / 8) with 0 in Hi; lia| intros _; change (2147467976 + 7 / 8) with 2147467976; change (7 mod 8) with 7; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467980) 2) ZC. mf V m HM (MCell (ZLit 2147467982) 1 (ZLit 2)) PC.
      apply (unp_global_cells m 136800 18 2147467980); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (18 / 8) with 2 in Hi; apply (zchunk_pointwise_k m 2147467980 2 ZC); lia| intros _; change (2147467980 + 18 / 8) with 2147467982; change (18 mod 8) with 2; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147467988) 4) ZC. mf V m HM (MCell (ZLit 2147467992) 1 (ZLit 1)) PC.
      apply (unp_global_cells m 136864 33 2147467988); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (33 / 8) with 4 in Hi; apply (zchunk_pointwise_k m 2147467988 4 ZC); lia| intros _; change (2147467988 + 33 / 8) with 2147467992; change (33 mod 8) with 1; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468000) 5) ZC. mf V m HM (MCell (ZLit 2147468005) 1 (ZLit 5)) PC.
      apply (unp_global_cells m 136960 45 2147468000); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (45 / 8) with 5 in Hi; apply (zchunk_pointwise_k m 2147468000 5 ZC); lia| intros _; change (2147468000 + 45 / 8) with 2147468005; change (45 mod 8) with 5; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MCell (ZLit 2147468020) 1 (ZLit 3)) PC.
      apply (unp_global_cells m 137120 3 2147468020); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; exfalso; change (3 / 8) with 0 in Hi; lia| intros _; change (2147468020 + 3 / 8) with 2147468020; change (3 mod 8) with 3; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MCell (ZLit 2147468032) 1 (ZLit 7)) PC.
      apply (unp_global_cells m 137216 7 2147468032); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; exfalso; change (7 / 8) with 0 in Hi; lia| intros _; change (2147468032 + 7 / 8) with 2147468032; change (7 mod 8) with 7; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468036) 3) ZC. mf V m HM (MCell (ZLit 2147468039) 1 (ZLit 1)) PC.
      apply (unp_global_cells m 137248 25 2147468036); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (25 / 8) with 3 in Hi; apply (zchunk_pointwise_k m 2147468036 3 ZC); lia| intros _; change (2147468036 + 25 / 8) with 2147468039; change (25 mod 8) with 1; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468044) 103) ZC.
      apply (unp_global_cells m 138112 24 2147468144); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (24 / 8) with 3 in Hi; replace (2147468144 + i) with (2147468044 + (100 + i)) by lia; apply (zchunk_pointwise_k m 2147468044 103 ZC); lia| intros X; exfalso; apply X; reflexivity]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468152) 8) ZC. mf V m HM (MCell (ZLit 2147468160) 1 (ZLit 7)) PC.
      apply (unp_global_cells m 138176 71 2147468152); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (71 / 8) with 8 in Hi; apply (zchunk_pointwise_k m 2147468152 8 ZC); lia| intros _; change (2147468152 + 71 / 8) with 2147468160; change (71 mod 8) with 7; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468168) 5) ZC.
      apply (unp_global_cells m 138304 40 2147468168); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (40 / 8) with 5 in Hi; apply (zchunk_pointwise_k m 2147468168 5 ZC); lia| intros X; exfalso; apply X; reflexivity]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468180) 6) ZC. mf V m HM (MCell (ZLit 2147468186) 1 (ZLit 3)) PC.
      apply (unp_global_cells m 138400 51 2147468180); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (51 / 8) with 6 in Hi; apply (zchunk_pointwise_k m 2147468180 6 ZC); lia| intros _; change (2147468180 + 51 / 8) with 2147468186; change (51 mod 8) with 3; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468192) 4) ZC. mf V m HM (MCell (ZLit 2147468196) 1 (ZLit 1)) PC.
      apply (unp_global_cells m 138496 33 2147468192); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (33 / 8) with 4 in Hi; apply (zchunk_pointwise_k m 2147468192 4 ZC); lia| intros _; change (2147468192 + 33 / 8) with 2147468196; change (33 mod 8) with 1; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468204) 1) ZC. mf V m HM (MCell (ZLit 2147468205) 1 (ZLit 6)) PC.
      apply (unp_global_cells m 138592 14 2147468204); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (14 / 8) with 1 in Hi; apply (zchunk_pointwise_k m 2147468204 1 ZC); lia| intros _; change (2147468204 + 14 / 8) with 2147468205; change (14 mod 8) with 6; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468208) 8) ZC. mf V m HM (MCell (ZLit 2147468216) 1 (ZLit 2)) PC.
      apply (unp_global_cells m 138624 66 2147468208); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (66 / 8) with 8 in Hi; apply (zchunk_pointwise_k m 2147468208 8 ZC); lia| intros _; change (2147468208 + 66 / 8) with 2147468216; change (66 mod 8) with 2; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468224) 7) ZC. mf V m HM (MCell (ZLit 2147468231) 1 (ZLit 4)) PC.
      apply (unp_global_cells m 138752 60 2147468224); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (60 / 8) with 7 in Hi; apply (zchunk_pointwise_k m 2147468224 7 ZC); lia| intros _; change (2147468224 + 60 / 8) with 2147468231; change (60 mod 8) with 4; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468236) 7) ZC. mf V m HM (MCell (ZLit 2147468243) 1 (ZLit 4)) PC.
      apply (unp_global_cells m 138848 60 2147468236); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (60 / 8) with 7 in Hi; apply (zchunk_pointwise_k m 2147468236 7 ZC); lia| intros _; change (2147468236 + 60 / 8) with 2147468243; change (60 mod 8) with 4; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468248) 8) ZC. mf V m HM (MCell (ZLit 2147468256) 1 (ZLit 3)) PC.
      apply (unp_global_cells m 138944 67 2147468248); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (67 / 8) with 8 in Hi; apply (zchunk_pointwise_k m 2147468248 8 ZC); lia| intros _; change (2147468248 + 67 / 8) with 2147468256; change (67 mod 8) with 3; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468264) 8) ZC. mf V m HM (MCell (ZLit 2147468272) 1 (ZLit 3)) PC.
      apply (unp_global_cells m 139072 67 2147468264); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (67 / 8) with 8 in Hi; apply (zchunk_pointwise_k m 2147468264 8 ZC); lia| intros _; change (2147468264 + 67 / 8) with 2147468272; change (67 mod 8) with 3; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468280) 11) ZC. mf V m HM (MCell (ZLit 2147468291) 1 (ZLit 4)) PC.
      apply (unp_global_cells m 139264 28 2147468288); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (28 / 8) with 3 in Hi; replace (2147468288 + i) with (2147468280 + (8 + i)) by lia; apply (zchunk_pointwise_k m 2147468280 11 ZC); lia| intros _; change (2147468288 + 28 / 8) with 2147468291; change (28 mod 8) with 4; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468296) 11) ZC.
      apply (unp_global_cells m 139392 24 2147468304); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (24 / 8) with 3 in Hi; replace (2147468304 + i) with (2147468296 + (8 + i)) by lia; apply (zchunk_pointwise_k m 2147468296 11 ZC); lia| intros X; exfalso; apply X; reflexivity]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468312) 12) ZC.
      apply (unp_global_cells m 139456 96 2147468312); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (96 / 8) with 12 in Hi; apply (zchunk_pointwise_k m 2147468312 12 ZC); lia| intros X; exfalso; apply X; reflexivity]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468328) 4) ZC. mf V m HM (MCell (ZLit 2147468332) 1 (ZLit 1)) PC.
      apply (unp_global_cells m 139584 33 2147468328); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (33 / 8) with 4 in Hi; apply (zchunk_pointwise_k m 2147468328 4 ZC); lia| intros _; change (2147468328 + 33 / 8) with 2147468332; change (33 mod 8) with 1; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468340) 1) ZC. mf V m HM (MCell (ZLit 2147468341) 1 (ZLit 6)) PC.
      apply (unp_global_cells m 139680 14 2147468340); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (14 / 8) with 1 in Hi; apply (zchunk_pointwise_k m 2147468340 1 ZC); lia| intros _; change (2147468340 + 14 / 8) with 2147468341; change (14 mod 8) with 6; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468344) 5) ZC. mf V m HM (MCell (ZLit 2147468349) 1 (ZLit 2)) PC.
      apply (unp_global_cells m 139712 42 2147468344); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (42 / 8) with 5 in Hi; apply (zchunk_pointwise_k m 2147468344 5 ZC); lia| intros _; change (2147468344 + 42 / 8) with 2147468349; change (42 mod 8) with 2; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468356) 6) ZC. mf V m HM (MCell (ZLit 2147468362) 1 (ZLit 5)) PC.
      apply (unp_global_cells m 139808 53 2147468356); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (53 / 8) with 6 in Hi; apply (zchunk_pointwise_k m 2147468356 6 ZC); lia| intros _; change (2147468356 + 53 / 8) with 2147468362; change (53 mod 8) with 5; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468368) 9) ZC. mf V m HM (MCell (ZLit 2147468377) 1 (ZLit 4)) PC.
      apply (unp_global_cells m 139904 76 2147468368); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (76 / 8) with 9 in Hi; apply (zchunk_pointwise_k m 2147468368 9 ZC); lia| intros _; change (2147468368 + 76 / 8) with 2147468377; change (76 mod 8) with 4; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468384) 8) ZC. mf V m HM (MCell (ZLit 2147468392) 1 (ZLit 2)) PC.
      apply (unp_global_cells m 140032 66 2147468384); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (66 / 8) with 8 in Hi; apply (zchunk_pointwise_k m 2147468384 8 ZC); lia| intros _; change (2147468384 + 66 / 8) with 2147468392; change (66 mod 8) with 2; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468400) 6) ZC. mf V m HM (MCell (ZLit 2147468406) 1 (ZLit 3)) PC.
      apply (unp_global_cells m 140160 51 2147468400); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (51 / 8) with 6 in Hi; apply (zchunk_pointwise_k m 2147468400 6 ZC); lia| intros _; change (2147468400 + 51 / 8) with 2147468406; change (51 mod 8) with 3; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468412) 9) ZC. mf V m HM (MCell (ZLit 2147468421) 1 (ZLit 1)) PC.
      apply (unp_global_cells m 140256 73 2147468412); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (73 / 8) with 9 in Hi; apply (zchunk_pointwise_k m 2147468412 9 ZC); lia| intros _; change (2147468412 + 73 / 8) with 2147468421; change (73 mod 8) with 1; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468428) 4) ZC. mf V m HM (MCell (ZLit 2147468432) 1 (ZLit 2)) PC.
      apply (unp_global_cells m 140384 34 2147468428); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (34 / 8) with 4 in Hi; apply (zchunk_pointwise_k m 2147468428 4 ZC); lia| intros _; change (2147468428 + 34 / 8) with 2147468432; change (34 mod 8) with 2; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468440) 7) ZC. mf V m HM (MCell (ZLit 2147468447) 1 (ZLit 3)) PC.
      apply (unp_global_cells m 140480 59 2147468440); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (59 / 8) with 7 in Hi; apply (zchunk_pointwise_k m 2147468440 7 ZC); lia| intros _; change (2147468440 + 59 / 8) with 2147468447; change (59 mod 8) with 3; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468452) 6) ZC. mf V m HM (MCell (ZLit 2147468458) 1 (ZLit 2)) PC.
      apply (unp_global_cells m 140576 50 2147468452); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (50 / 8) with 6 in Hi; apply (zchunk_pointwise_k m 2147468452 6 ZC); lia| intros _; change (2147468452 + 50 / 8) with 2147468458; change (50 mod 8) with 2; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468464) 4) ZC. mf V m HM (MCell (ZLit 2147468468) 1 (ZLit 4)) PC.
      apply (unp_global_cells m 140672 36 2147468464); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (36 / 8) with 4 in Hi; apply (zchunk_pointwise_k m 2147468464 4 ZC); lia| intros _; change (2147468464 + 36 / 8) with 2147468468; change (36 mod 8) with 4; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468476) 7) ZC. mf V m HM (MCell (ZLit 2147468483) 1 (ZLit 4)) PC.
      apply (unp_global_cells m 140768 60 2147468476); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (60 / 8) with 7 in Hi; apply (zchunk_pointwise_k m 2147468476 7 ZC); lia| intros _; change (2147468476 + 60 / 8) with 2147468483; change (60 mod 8) with 4; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468488) 9) ZC.
      apply (unp_global_cells m 140864 72 2147468488); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (72 / 8) with 9 in Hi; apply (zchunk_pointwise_k m 2147468488 9 ZC); lia| intros X; exfalso; apply X; reflexivity]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468504) 8) ZC. mf V m HM (MCell (ZLit 2147468512) 1 (ZLit 6)) PC.
      apply (unp_global_cells m 140992 70 2147468504); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (70 / 8) with 8 in Hi; apply (zchunk_pointwise_k m 2147468504 8 ZC); lia| intros _; change (2147468504 + 70 / 8) with 2147468512; change (70 mod 8) with 6; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468520) 8) ZC.
      apply (unp_global_cells m 141120 64 2147468520); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (64 / 8) with 8 in Hi; apply (zchunk_pointwise_k m 2147468520 8 ZC); lia| intros X; exfalso; apply X; reflexivity]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468532) 9) ZC. mf V m HM (MCell (ZLit 2147468541) 1 (ZLit 3)) PC.
      apply (unp_global_cells m 141216 75 2147468532); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (75 / 8) with 9 in Hi; apply (zchunk_pointwise_k m 2147468532 9 ZC); lia| intros _; change (2147468532 + 75 / 8) with 2147468541; change (75 mod 8) with 3; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468548) 9) ZC. mf V m HM (MCell (ZLit 2147468557) 1 (ZLit 4)) PC.
      apply (unp_global_cells m 141344 76 2147468548); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (76 / 8) with 9 in Hi; apply (zchunk_pointwise_k m 2147468548 9 ZC); lia| intros _; change (2147468548 + 76 / 8) with 2147468557; change (76 mod 8) with 4; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468564) 8) ZC. mf V m HM (MCell (ZLit 2147468572) 1 (ZLit 7)) PC.
      apply (unp_global_cells m 141472 71 2147468564); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (71 / 8) with 8 in Hi; apply (zchunk_pointwise_k m 2147468564 8 ZC); lia| intros _; change (2147468564 + 71 / 8) with 2147468572; change (71 mod 8) with 7; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468580) 8) ZC. mf V m HM (MCell (ZLit 2147468588) 1 (ZLit 1)) PC.
      apply (unp_global_cells m 141600 65 2147468580); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (65 / 8) with 8 in Hi; apply (zchunk_pointwise_k m 2147468580 8 ZC); lia| intros _; change (2147468580 + 65 / 8) with 2147468588; change (65 mod 8) with 1; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468596) 9) ZC. mf V m HM (MCell (ZLit 2147468605) 1 (ZLit 2)) PC.
      apply (unp_global_cells m 141728 74 2147468596); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (74 / 8) with 9 in Hi; apply (zchunk_pointwise_k m 2147468596 9 ZC); lia| intros _; change (2147468596 + 74 / 8) with 2147468605; change (74 mod 8) with 2; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468612) 12) ZC.
      apply (unp_global_cells m 141856 96 2147468612); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (96 / 8) with 12 in Hi; apply (zchunk_pointwise_k m 2147468612 12 ZC); lia| intros X; exfalso; apply X; reflexivity]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468628) 6) ZC. mf V m HM (MCell (ZLit 2147468634) 1 (ZLit 1)) PC.
      apply (unp_global_cells m 141984 49 2147468628); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (49 / 8) with 6 in Hi; apply (zchunk_pointwise_k m 2147468628 6 ZC); lia| intros _; change (2147468628 + 49 / 8) with 2147468634; change (49 mod 8) with 1; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468640) 7) ZC. mf V m HM (MCell (ZLit 2147468647) 1 (ZLit 1)) PC.
      apply (unp_global_cells m 142080 57 2147468640); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (57 / 8) with 7 in Hi; apply (zchunk_pointwise_k m 2147468640 7 ZC); lia| intros _; change (2147468640 + 57 / 8) with 2147468647; change (57 mod 8) with 1; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468652) 6) ZC.
      apply (unp_global_cells m 142176 48 2147468652); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (48 / 8) with 6 in Hi; apply (zchunk_pointwise_k m 2147468652 6 ZC); lia| intros X; exfalso; apply X; reflexivity]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468664) 12) ZC.
      apply (unp_global_cells m 142272 96 2147468664); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (96 / 8) with 12 in Hi; apply (zchunk_pointwise_k m 2147468664 12 ZC); lia| intros X; exfalso; apply X; reflexivity]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZeroC (ZLit 2147468680) 7) ZC. mf V m HM (MCell (ZLit 2147468687) 1 (ZLit 4)) PC.
      apply (unp_global_cells m 142400 60 2147468680); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (60 / 8) with 7 in Hi; apply (zchunk_pointwise_k m 2147468680 7 ZC); lia| intros _; change (2147468680 + 60 / 8) with 2147468687; change (60 mod 8) with 4; apply c1_pointwise; [exact PC| lia]]. }
    apply Forall_cons.
    { cbn [fst snd]. mf V m HM (MZero (ZLit 2147538530) 682927) ZZ.
      apply (unp_global_cells m 6164608 8 2148221456); [reflexivity| reflexivity| lia| lia| lia| intros i Hi; change (8 / 8) with 1 in Hi; replace (2148221456 + i) with (2147538530 + (682926 + i)) by lia; apply ZZ; lia| intros X; exfalso; apply X; reflexivity]. }
    apply Forall_nil.
  Qed.

  #[using="rc en inp lim w V ms mo AM U HU HMP"] Lemma globals_init : forall (L0 : alayout) (R0 : footprint) (s : PS) (FB : list cblk), globals_P L0 R0 s FB m.
  Proof.
    intros L0 R0 s FB. split; [| exact globals_unp_init]. destruct HMP as [HM HP]. mwr V m HM (ZLit 2147459072) 780288 WR. exact WR.
  Qed.

  #[using="rc en inp lim w V ms mo AM U HU HMP"] Lemma stdinp_init : forall (L0 : alayout) (R0 : footprint) (s : PS) (FB : list cblk), stdinp_P L0 R0 s FB m.
  Proof.
    intros L0 R0 s FB. destruct HMP as [HM HP]. mf V m HM (MZero (ZLit 2147468692) 69278) Z1. unfold stdinp_P.
    eapply (unpoisoned_of_zero m 2147468692 (2147468692 + 69278) (fun _ => 0)).
    - apply shadow_bytes_of_pointwise; [exact Z1| lia| lia].
    - intros; reflexivity.
    - unfold STDIN_P. rewrite shad_div. change AsanEmbed.ASHOFF with 2147450880. vm_compute. discriminate.
    - unfold STDIN_P. rewrite shad_div. change AsanEmbed.ASHOFF with 2147450880. vm_compute. discriminate.
    - unfold STDIN_P. lia.
    - unfold STDIN_P. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="tlsI en inp lim ms mo AM HAT HTLS HU A0I HMP"] Lemma stacksh_init : forall (s : PS) (FB : list cblk), stacksh_P L RNG s FB m.
  Proof.
    intros s FB. destruct HMP as [HM HP]. (pose proof AM as ndP__; nd_pre ndP__ 11%nat; intros _ _ _ _ _ _ _ _ _ _ SH1; nd_post).
    (pose proof (alayout_stack_init V w U HP HAT) as ndP__; nd_pre ndP__ 4%nat; intros _ TPG (TLO & THI) T47; nd_post). pose proof atop_range as AR. pose proof ATOP_pg as PG.
    pose proof (alayout_ok_init V w U HP HU HAT HTLS) as ALO.
    (pose proof (ao_res L ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ RESHI _; nd_post). (pose proof (ao_ctx L ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ CTXHI _; nd_post).
    change (al_res L) with (4096 * V 208%nat) in RESHI. rewrite LV_ctx in CTXHI.
    pose proof (tls_at_tp V HTLS) as HTP. pose proof ATPv_hi as THI0. rewrite HTP in THI0.
    pf V HP (PVar 209 0 15) P209.
    set (T := al_top L) in *. change (2^47) with 140737488355328 in T47.
    assert (E1 : shad (ATOP + 4096) = 2147450880 + (ATOP + 4096) / 8) by (rewrite shad_div; reflexivity).
    assert (E2 : shad T = 2147450880 + T / 8) by (rewrite shad_div; reflexivity).
    unfold stacksh_P. fold T. rewrite E1, E2.
    assert (LEN : 0 < 2147450880 + T / 8 - (2147450880 + (ATOP + 4096) / 8)) by (clear - TLO; Z.div_mod_to_equations; lia).
    destruct (shadow_zero_run V m (2147450880 + (ATOP + 4096) / 8) (2147450880 + T / 8 - (2147450880 + (ATOP + 4096) / 8)) SH1 HM HP LEN) as (Z0 & WR & _).
    { intros a Ha. right. clear - Ha AR T47. Z.div_mod_to_equations. lia. }
    { intros a Ha. change OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReadyA.TwB.ASHOFF with 2147450880.
      split; [clear - Ha AR; Z.div_mod_to_equations; lia|].
      split; [clear - Ha AR RESHI P209; Z.div_mod_to_equations; lia|].
      clear - Ha AR CTXHI; Z.div_mod_to_equations; lia. }
    split; [exact TPG|]. split; [change (2^47) with 140737488355328; clear - TLO T47; lia|].
    split.
    { eapply (unpoisoned_of_zero m (2147450880 + (ATOP + 4096) / 8) (2147450880 + T / 8) (fun _ => 0)).
      - replace (2147450880 + T / 8) with (2147450880 + (ATOP + 4096) / 8 + (2147450880 + T / 8 - (2147450880 + (ATOP + 4096) / 8))) by lia.
        apply shadow_bytes_of_pointwise; [exact Z0| clear - AR; Z.div_mod_to_equations; lia| clear - AR T47; Z.div_mod_to_equations; lia].
      - intros; reflexivity.
      - rewrite shad_div. change AsanEmbed.ASHOFF with 2147450880. lia.
      - rewrite shad_div. change AsanEmbed.ASHOFF with 2147450880. clear - TPG TLO AR. Z.div_mod_to_equations. lia.
      - clear - AR. lia.
      - clear - T47. lia. }
    split; [exact WR|].
    eapply (vis_rng_sh lz AL V U A0I HU 13); [reflexivity| | | |]; cbn [fst snd zv nth_error asan_vis asan_vis_app app]; clear - HAT AR T47 TLO PG; Z.div_mod_to_equations; lia.
  Qed.
End Init.
End CANSEC1.
End TwB.
End StaticsInitA.

(* [comment removed for export] *)
Module TlsObjInitA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport MainFactsAsan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require KnTrans__AS. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainEntry__AS. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainFactsAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.MainLedgerAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepInit_kit__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_E OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Fuzz_ifaceA GioaReal. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require Drv_ifaceA F_main_AA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require GStatKit TlsObjA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_main_AA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.MainEntryA__A3D.MainEntryA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.GStatKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.TlsObjA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section Init.
  Variables (en : ExecEntry) (inp : ProcInput) (lim : Z) (w : bool) (V : nat -> Z) (m : amem) (ms : machine_state) (mo : Model).
  Hypothesis AM : amain_open en inp lim w V m ms mo.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP.
  Hypothesis HTLS : tls_at V.
  Variables (U : list (list Z)) (lz : list (word * word)) (AL : word -> Prop).
  Hypothesis HU : (length U <= Z.to_nat AUMAX)%nat.
  Hypothesis A0I : forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p.

  Notation RNG := (fp_ok lz AL).
  #[local] Notation cblk := (@cblock aptr).
  #[local] Notation PS := (PState aheap aptr).
  Let HMP := me_facts en inp lim w V m ms mo AM.

  #[using="en inp lim w V ms mo AM HTLS U HU A0I HMP"] Lemma tlsobj_init : forall (L0 : alayout) (s : PS) (FB : list cblk), tlsobj_P L0 RNG s FB m.
  Proof.
    intros L0 s FB. destruct HMP as [HM HP].
    pose proof (tls_at_tp V HTLS) as HTP. pose proof atop_range as AR.
    (* The thread block is zero-initialised .bss, so its shadow hull [shad (tp - 248), + 72) is a zero run of the
       image shadow, which is writable and in range as part of the image's shadow window. *)
    mf V m HM (MZero (ZLit 2148221332) 17516) ZT0.
    assert (ZT : forall i, 0 <= i < 72 -> m (wa (2148221592 + i)) = Some (Z_to_bv 8 0)).
    { intros i Hi. replace (2148221592 + i) with (2148221332 + (260 + i)) by lia. apply ZT0. lia. }
    mwr V m HM (ZLit 2147459072) 779776 WR.
    unfold tlsobj_P, ATP. rewrite HTP.
    assert (E : shad (0x5e15b8 + -248) = 2148221592) by (rewrite shad_div; change AsanEmbed.ASHOFF with 2147450880; reflexivity).
    rewrite E.
    split.
    { eapply (unpoisoned_of_zero m 2148221592 (2148221592 + 72) (fun _ => 0)).
      - apply shadow_bytes_of_pointwise; [exact ZT| lia| lia].
      - intros; reflexivity.
      - rewrite shad_div. change AsanEmbed.ASHOFF with 2147450880. Z.div_mod_to_equations. lia.
      - rewrite shad_div. change AsanEmbed.ASHOFF with 2147450880. Z.div_mod_to_equations. lia.
      - lia.
      - lia. }
    split; [eapply Shadow.wr_at_sub; [exact WR| lia| lia]|].
    eapply (vis_rng_sh lz AL V U A0I HU 12); [reflexivity| | | |]; cbn [fst snd zv nth_error asan_vis asan_vis_app app]; clear; Z.div_mod_to_equations; lia.
  Qed.
End Init.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS.MainFactsAsan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.MainLedgerAsan.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_E.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_main_AA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.MainEntryA__A3D.MainEntryA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.GStatKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.TlsObjA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section Init.
  Variables (en : ExecEntry) (inp : ProcInput) (lim : Z) (w : bool) (V : nat -> Z) (m : amem) (ms : machine_state) (mo : Model).
  Hypothesis AM : amain_open en inp lim w V m ms mo.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP.
  Hypothesis HTLS : tls_at V.
  Variables (U : list (list Z)) (lz : list (word * word)) (AL : word -> Prop).
  Hypothesis HU : (length U <= Z.to_nat AUMAX)%nat.
  Hypothesis A0I : forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p.

  Notation RNG := (fp_ok lz AL).
  #[local] Notation cblk := (@cblock aptr).
  #[local] Notation PS := (PState aheap aptr).
  Let HMP := me_facts en inp lim w V m ms mo AM.

  #[using="en inp lim w V ms mo AM HTLS U HU A0I HMP"] Lemma tlsobj_init : forall (L0 : alayout) (s : PS) (FB : list cblk), tlsobj_P L0 RNG s FB m.
  Proof.
    intros L0 s FB. destruct HMP as [HM HP].
    pose proof (tls_at_tp V HTLS) as HTP. pose proof atop_range as AR.
    (* The thread block is zero-initialised .bss, so its shadow hull [shad (tp - 248), + 72) is a zero run of the
       image shadow, which is writable and in range as part of the image's shadow window. *)
    mf V m HM (MZero (ZLit 2148221460) 17900) ZT0.
    assert (ZT : forall i, 0 <= i < 72 -> m (wa (2148221720 + i)) = Some (Z_to_bv 8 0)).
    { intros i Hi. replace (2148221720 + i) with (2148221460 + (260 + i)) by lia. apply ZT0. lia. }
    mwr V m HM (ZLit 2147459072) 780288 WR.
    unfold tlsobj_P, ATP. rewrite HTP.
    assert (E : shad (0x5e19b8 + -248) = 2148221720) by (rewrite shad_div; change AsanEmbed.ASHOFF with 2147450880; reflexivity).
    rewrite E.
    split.
    { eapply (unpoisoned_of_zero m 2148221720 (2148221720 + 72) (fun _ => 0)).
      - apply shadow_bytes_of_pointwise; [exact ZT| lia| lia].
      - intros; reflexivity.
      - rewrite shad_div. change AsanEmbed.ASHOFF with 2147450880. Z.div_mod_to_equations. lia.
      - rewrite shad_div. change AsanEmbed.ASHOFF with 2147450880. Z.div_mod_to_equations. lia.
      - lia.
      - lia. }
    split; [eapply Shadow.wr_at_sub; [exact WR| lia| lia]|].
    eapply (vis_rng_sh lz AL V U A0I HU 12); [reflexivity| | | |]; cbn [fst snd zv nth_error asan_vis asan_vis_app app]; clear; Z.div_mod_to_equations; lia.
  Qed.
End Init.
End CANSEC1.
End TwB.
End TlsObjInitA.
