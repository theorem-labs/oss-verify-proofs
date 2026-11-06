(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AProto AMalloc_iface AFake_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA GioaReal. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA I_ahm I_fflush StdioLawsA StdioCompA Stdio_glueA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_ahm OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fflush OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioCompA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require Drv_ifaceA GStatKit HarnCompA AtxCompA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require DrvKitA__A3D. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require ExitHeapA DrvStatA StaticsA TlsObjA StdioLawsInstA StrerrCompA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.GStatKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.HarnCompA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.AtxCompA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.ExitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ExitHeapA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvStatA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.StaticsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.TlsObjA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.StdioLawsInstA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.StrerrCompA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section AtxIndep.
  Variable AI : AMallocIface.
  Hypothesis AF : AFakeIface AI.
  Hypothesis AI_block_tls : forall L RNG st LB m b, AHEAP AI L RNG st LB m -> In b LB ->
      ab_addr b + ab_size b <= ATP + -200 \/ ATP + -200 + 504 <= ab_addr b.
  #[local] Notation cblk := (@cblock aptr).
  #[local] Notation PS := (PState aheap aptr).

  (* [comment removed for export] *)
  #[using="Type"] Lemma atx_keep_lit : forall a, in_ranges ATX_KEEP a -> (0x5e0c50 <= a < 0x5e0c58) \/ (0x601608 <= a < 0x601828).
  Proof.
    intros a (k & Hk & Rk). unfold ATX_KEEP in Hk.
    destruct Hk as [<-|[<-|[]]]; cbn [fst snd] in Rk; unfold DRV_INIT_FLAG, ATX in Rk; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma atx_dom_lit : forall a, in_ranges ATX_DOM a -> (0x5e0c50 <= a < 0x5e0c58) \/ (0x601608 <= a < 0x601828) \/ (0x601848 <= a < 0x601850).
  Proof.
    intros a (k & Hk & Rk). unfold ATX_DOM, ATX_KEEP in Hk. cbn [app] in Hk.
    destruct Hk as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Rk; unfold DRV_INIT_FLAG, ATX in Rk; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma atx_harn_indep : forall cb, harn_indep (atx_comp cb).
  Proof.
    intros cb. split; cbn [gc_P gc_dom atx_comp]; unfold atx_P, atx_dom.
    - intros L RNG s FB m o HP. exact HP.
    - intros L s FB a Da R. apply atx_dom_lit in Da. unfold OUTFILE_ADDR in R. lia.
  Qed.

  #[using="Type"] Lemma atx_stdio_indep : forall cb, stdio_indep AI (atx_comp cb).
  Proof.
    intros cb. constructor; cbn [gc_P gc_dom atx_comp]; unfold atx_P, atx_dom.
    - intros L RNG s s' FB FB' m HP _ _ _. exact HP.
    - intros L s s' FB FB' a Da _ _. exact Da.
    - intros L RNG s FB m a _ Da X. apply atx_dom_lit in Da. unfold stdio_static in X. lia.
    - intros L RNG s CL FB FL m a AH _ _ Da K. apply atx_dom_lit in Da.
      destruct (fb_block_band AI _ _ _ _ _ _ _ _ AH K) as [X|X]; pose proof atop_range as AR; lia.
  Qed.

  #[using="Type"] Lemma atx_tlsbuf : forall cb, tlsbuf_indep (atx_comp cb).
  Proof.
    intros cb. apply tlsbuf_of_band. cbn [gc_dom atx_comp]. unfold atx_dom. intros L s FB a Da. apply atx_dom_lit in Da. left. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma args_atx : forall USP n, ATOP + 64 <= USP -> USP + n + 8 <= 2^47 -> atx_indep (args_comp USP n).
  Proof.
    intros USP n G1 G3 L s FB a Da R. apply atx_keep_lit in R. cbn [gc_dom args_comp] in Da.
    destruct (args_dom_band USP n G1 G3 a Da) as [B _]. pose proof atop_range as AR. clear - B R AR. Z.div_mod_to_equations. lia.
  Qed.
  #[using="Type"] Lemma unp_atx : atx_indep unp_comp.
  Proof. intros L s FB a Da R. apply atx_keep_lit in R. cbn [gc_dom unp_comp] in Da. unfold unp_dom, AIMSH_LO in Da. lia. Qed.
  #[using="Type"] Lemma exitci_atx : atx_indep exitci_comp.
  Proof.
    intros L s FB a Da R. apply atx_keep_lit in R. cbn [gc_dom exitci_comp] in Da. unfold exitci_dom, exit_dom in Da.
    destruct Da as [D|[(k & Hk & Rk)|D]].
    - pose proof ATPv_img as TI. lia.
    - unfold EXIT_CI_KEEP in Hk. repeat (destruct Hk as [<-|Hk]; [cbn [fst snd] in Rk; lia|]). destruct Hk.
    - unfold AIMSH_LO in D. lia.
  Qed.
  #[using="Type"] Lemma globals_atx : atx_indep globals_comp.
  Proof. intros L s FB a Da R. apply atx_keep_lit in R. cbn [gc_dom globals_comp] in Da. unfold win_dom, AIMSH_LO in Da. lia. Qed.
  #[using="Type"] Lemma stdinp_atx : atx_indep stdinp_comp.
  Proof. intros L s FB a Da R. apply atx_keep_lit in R. cbn [gc_dom stdinp_comp] in Da. unfold win_dom, AIMSH_LO in Da. lia. Qed.
  #[using="Type"] Lemma stacksh_atx : atx_indep stacksh_comp.
  Proof.
    intros L s FB a Da R. apply atx_keep_lit in R. cbn [gc_dom stacksh_comp] in Da. destruct Da as [Da D47].
    destruct (stacksh_band L a Da D47) as [B _]. pose proof atop_range as AR. clear - B R AR. Z.div_mod_to_equations. lia.
  Qed.
  #[using="Type"] Lemma tlsobj_atx : atx_indep tlsobj_comp.
  Proof. intros L s FB a Da R. apply atx_keep_lit in R. cbn [gc_dom tlsobj_comp] in Da. destruct (tlsobj_band a Da) as (B & _). lia. Qed.
  #[using="Type"] Lemma harn_atx : atx_indep harn_comp.
  Proof. intros L s FB a Da R. apply atx_keep_lit in R. cbn [gc_dom harn_comp] in Da. unfold harn_dom, OUTFILE_ADDR in Da. lia. Qed.
  #[using="Type"] Lemma files_atx : atx_indep files_comp.
  Proof.
    intros L s FB a Da R. apply atx_keep_lit in R. cbn [gc_dom files_comp] in Da. unfold files_dom in Da.
    destruct Da as [K|[_ [K _]]]; [unfold stdio_static in K; lia| lia].
  Qed.
  #[using="Type"] Lemma env_atx : atx_indep env_comp.
  Proof.
    intros L s FB a Da R. apply atx_keep_lit in R. cbn [gc_dom env_comp] in Da. unfold env_dom in Da.
    destruct Da as [K|[K|[_ [K _]]]].
    - destruct K as (k & Hk & Rk). unfold STDIO_ENV_CELLS in Hk. repeat (destruct Hk as [<-|Hk]; [cbn [fst snd] in Rk; lia|]). destruct Hk.
    - unfold AIMSH_LO, AIMSH_LEN in K. lia.
    - lia.
  Qed.
  #[using="Type"] Lemma strerr_atx : atx_indep strerr_comp.
  Proof.
    intros L s FB a Da R. apply atx_keep_lit in R. cbn [gc_dom strerr_comp] in Da. unfold strerr_dom in Da.
    pose proof ATPv_img as TI. unfold ATP in *. lia.
  Qed.
End AtxIndep.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.GStatKit.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_ahm.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fflush.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioCompA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.HarnCompA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.AtxCompA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.ExitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ExitHeapA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvStatA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.StaticsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.TlsObjA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.StdioLawsInstA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.StrerrCompA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section AtxIndep.
  Variable AI : AMallocIface.
  Hypothesis AF : AFakeIface AI.
  Hypothesis AI_block_tls : forall L RNG st LB m b, AHEAP AI L RNG st LB m -> In b LB ->
      ab_addr b + ab_size b <= ATP + -200 \/ ATP + -200 + 504 <= ab_addr b.
  #[local] Notation cblk := (@cblock aptr).
  #[local] Notation PS := (PState aheap aptr).

  (* [comment removed for export] *)
  #[using="Type"] Lemma atx_keep_lit : forall a, in_ranges ATX_KEEP a -> (0x5e1050 <= a < 0x5e1058) \/ (0x601a08 <= a < 0x601c28).
  Proof.
    intros a (k & Hk & Rk). unfold ATX_KEEP in Hk.
    destruct Hk as [<-|[<-|[]]]; cbn [fst snd] in Rk; unfold DRV_INIT_FLAG, ATX in Rk; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma atx_dom_lit : forall a, in_ranges ATX_DOM a -> (0x5e1050 <= a < 0x5e1058) \/ (0x601a08 <= a < 0x601c28) \/ (0x601c48 <= a < 0x601c50).
  Proof.
    intros a (k & Hk & Rk). unfold ATX_DOM, ATX_KEEP in Hk. cbn [app] in Hk.
    destruct Hk as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Rk; unfold DRV_INIT_FLAG, ATX in Rk; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma atx_harn_indep : forall cb, harn_indep (atx_comp cb).
  Proof.
    intros cb. split; cbn [gc_P gc_dom atx_comp]; unfold atx_P, atx_dom.
    - intros L RNG s FB m o HP. exact HP.
    - intros L s FB a Da R. apply atx_dom_lit in Da. unfold OUTFILE_ADDR in R. lia.
  Qed.

  #[using="Type"] Lemma atx_stdio_indep : forall cb, stdio_indep AI (atx_comp cb).
  Proof.
    intros cb. constructor; cbn [gc_P gc_dom atx_comp]; unfold atx_P, atx_dom.
    - intros L RNG s s' FB FB' m HP _ _ _. exact HP.
    - intros L s s' FB FB' a Da _ _. exact Da.
    - intros L RNG s FB m a _ Da X. apply atx_dom_lit in Da. unfold stdio_static in X. lia.
    - intros L RNG s CL FB FL m a AH _ _ Da K. apply atx_dom_lit in Da.
      destruct (fb_block_band AI _ _ _ _ _ _ _ _ AH K) as [X|X]; pose proof atop_range as AR; lia.
  Qed.

  #[using="Type"] Lemma atx_tlsbuf : forall cb, tlsbuf_indep (atx_comp cb).
  Proof.
    intros cb. apply tlsbuf_of_band. cbn [gc_dom atx_comp]. unfold atx_dom. intros L s FB a Da. apply atx_dom_lit in Da. left. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma args_atx : forall USP n, ATOP + 64 <= USP -> USP + n + 8 <= 2^47 -> atx_indep (args_comp USP n).
  Proof.
    intros USP n G1 G3 L s FB a Da R. apply atx_keep_lit in R. cbn [gc_dom args_comp] in Da.
    destruct (args_dom_band USP n G1 G3 a Da) as [B _]. pose proof atop_range as AR. clear - B R AR. Z.div_mod_to_equations. lia.
  Qed.
  #[using="Type"] Lemma unp_atx : atx_indep unp_comp.
  Proof. intros L s FB a Da R. apply atx_keep_lit in R. cbn [gc_dom unp_comp] in Da. unfold unp_dom, AIMSH_LO in Da. lia. Qed.
  #[using="Type"] Lemma exitci_atx : atx_indep exitci_comp.
  Proof.
    intros L s FB a Da R. apply atx_keep_lit in R. cbn [gc_dom exitci_comp] in Da. unfold exitci_dom, exit_dom in Da.
    destruct Da as [D|[(k & Hk & Rk)|D]].
    - pose proof ATPv_img as TI. lia.
    - unfold EXIT_CI_KEEP in Hk. repeat (destruct Hk as [<-|Hk]; [cbn [fst snd] in Rk; lia|]). destruct Hk.
    - unfold AIMSH_LO in D. lia.
  Qed.
  #[using="Type"] Lemma globals_atx : atx_indep globals_comp.
  Proof. intros L s FB a Da R. apply atx_keep_lit in R. cbn [gc_dom globals_comp] in Da. unfold win_dom, AIMSH_LO in Da. lia. Qed.
  #[using="Type"] Lemma stdinp_atx : atx_indep stdinp_comp.
  Proof. intros L s FB a Da R. apply atx_keep_lit in R. cbn [gc_dom stdinp_comp] in Da. unfold win_dom, AIMSH_LO in Da. lia. Qed.
  #[using="Type"] Lemma stacksh_atx : atx_indep stacksh_comp.
  Proof.
    intros L s FB a Da R. apply atx_keep_lit in R. cbn [gc_dom stacksh_comp] in Da. destruct Da as [Da D47].
    destruct (stacksh_band L a Da D47) as [B _]. pose proof atop_range as AR. clear - B R AR. Z.div_mod_to_equations. lia.
  Qed.
  #[using="Type"] Lemma tlsobj_atx : atx_indep tlsobj_comp.
  Proof. intros L s FB a Da R. apply atx_keep_lit in R. cbn [gc_dom tlsobj_comp] in Da. destruct (tlsobj_band a Da) as (B & _). lia. Qed.
  #[using="Type"] Lemma harn_atx : atx_indep harn_comp.
  Proof. intros L s FB a Da R. apply atx_keep_lit in R. cbn [gc_dom harn_comp] in Da. unfold harn_dom, OUTFILE_ADDR in Da. lia. Qed.
  #[using="Type"] Lemma files_atx : atx_indep files_comp.
  Proof.
    intros L s FB a Da R. apply atx_keep_lit in R. cbn [gc_dom files_comp] in Da. unfold files_dom in Da.
    destruct Da as [K|[_ [K _]]]; [unfold stdio_static in K; lia| lia].
  Qed.
  #[using="Type"] Lemma env_atx : atx_indep env_comp.
  Proof.
    intros L s FB a Da R. apply atx_keep_lit in R. cbn [gc_dom env_comp] in Da. unfold env_dom in Da.
    destruct Da as [K|[K|[_ [K _]]]].
    - destruct K as (k & Hk & Rk). unfold STDIO_ENV_CELLS in Hk. repeat (destruct Hk as [<-|Hk]; [cbn [fst snd] in Rk; lia|]). destruct Hk.
    - unfold AIMSH_LO, AIMSH_LEN in K. lia.
    - lia.
  Qed.
  #[using="Type"] Lemma strerr_atx : atx_indep strerr_comp.
  Proof.
    intros L s FB a Da R. apply atx_keep_lit in R. cbn [gc_dom strerr_comp] in Da. unfold strerr_dom in Da.
    pose proof ATPv_img as TI. unfold ATP in *. lia.
  Qed.
End AtxIndep.
End CANSEC1.
End TwB.
