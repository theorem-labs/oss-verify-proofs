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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.ImgAny.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AProto AMalloc_iface AFake_iface AFake_arep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA GioaReal. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require Import Drv_ifaceA GStatKit DrvStatA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma flag_ok : rw_bytes_b asegs 0x5e0c50 [Z_to_bv 8 0] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ssp_ok : rw_bytes_b asegs 0x6015f8 (repeat (Z_to_bv 8 0) 8) = true.
Proof. vm_compute. reflexivity. Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma c1_any : forall (m : mem) A, rw_bytes_b asegs A [Z_to_bv 8 0] = true -> 0 <= A -> A + 1 <= 2^64 -> exists b : byte, rw_cells asegs m A [C1 b].
Proof.
  intros m A HB H0 H1. (nd_pre (rw_cells_any asegs m A [Z_to_bv 8 0] HB H0 ltac:(cbn [length]; lia)) 3%nat; intros bs HL HC; nd_post).
  destruct bs as [|b [|b' bs]]; cbn [length] in HL; try discriminate. exists b.
  destruct HC as [[WF B] W]. split; [split; [cbn; auto| exact B]| exact W].
Qed.
#[using="Type"] Lemma c8_any : forall (m : mem) A, rw_bytes_b asegs A (repeat (Z_to_bv 8 0) 8) = true -> 0 <= A -> A + 8 <= 2^64 -> exists w : word, rw_cells asegs m A [C8 w].
Proof.
  intros m A HB H0 H1. (nd_pre (rw_cells_any asegs m A (repeat (Z_to_bv 8 0) 8) HB H0 ltac:(rewrite repeat_length; lia)) 3%nat; intros bs HL HC; nd_post).
  rewrite repeat_length in HL, HC. apply ARepKit.c8_of_junk. apply (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AKitR.junk_of_cb m A 8 bs). exact HC.
Qed.

Section DrvLaws.
  Variable AI : AMallocIface.
  Hypothesis AF : AFakeIface AI.
  Hypothesis AI_block_tls : forall L RNG st LB m b, AHEAP AI L RNG st LB m -> In b LB ->
      ab_addr b + ab_size b <= ATP + -200 \/ ATP + -200 + 504 <= ab_addr b.
  Variables (USP : Z) (SB : list byte).
  Hypothesis USP_lo : ATOP + 64 <= USP.
  Hypothesis SB_16 : 16 <= Z.of_nat (length SB).
  Hypothesis USP_hi : USP + Z.of_nat (length SB) <= 2^47.
  Variable cs : list gcomp.
  Hypothesis CSOK : Forall (gcomp_ok AI) cs.
  Hypothesis CI_RS : exists iv, In iv (aci AI) /\ fst iv <= READ_STAGE /\ READ_STAGE + 65537 <= snd iv.
  Hypothesis IN_ARGS : In (args_comp USP (Z.of_nat (length SB) - 16)) cs.
  Hypothesis IN_UNP : In unp_comp cs.
  #[local] Notation GIOA := (GIOA_real AI (GSTAT_of cs)).

  #[using="AF AI_block_tls USP_lo SB_16 USP_hi CSOK CI_RS IN_ARGS IN_UNP"] Theorem gia_drv_laws_real : gia_drv_laws GIOA USP SB.
  Proof.
    constructor.
    - intros L RNG s CL FB FL m (_ & _ & _ & _ & _ & _ & (ERR & _)). exact ERR.
    - intros L RNG s CL FB FL m (AH & _). pose proof (AI_relro AI _ _ _ _ _ AH) as RO.
      split; [| split]; apply (relro_word m _ _ RO); first [unfold GOT_STDERR, STDERR_P, GOT_FUZZ_INIT, ARELRO_LO, ARELRO_HI; lia | vm_compute; reflexivity].
    - intros L RNG s CL FB FL m (AH & _). pose proof (AI_relro AI _ _ _ _ _ AH) as RO.
      split; [apply (relro_word m _ _ RO); first [unfold ARELRO_LO, ARELRO_HI; lia | vm_compute; reflexivity]|].
      apply c8_any; [exact ssp_ok| lia| lia].
    - intros L RNG s CL FB FL m (_ & _ & _ & _ & _ & _ & (_ & GC)).
      assert (H1 : 0 <= Z.of_nat (length SB) - 16) by lia. assert (H2 : USP + (Z.of_nat (length SB) - 16) + 8 <= 2^47) by lia.
      exact (args_mobjA USP (Z.of_nat (length SB) - 16) USP_lo H1 H2 L RNG s FB m (gconj_In _ _ _ _ _ _ _ GC IN_ARGS)).
    - intros L RNG s CL FB FL m (_ & _ & _ & _ & _ & _ & (_ & GC)). exact (gconj_In _ _ _ _ _ _ _ GC IN_UNP).
    - intros L RNG s CL FB FL m m' W G MU WM FW. eapply (gd_frame_real AI AF); eassumption.
    - intros L RNG s CL FB FL m m' W e G MU WM FW HE. eapply (gd_frame_errno_real AI AF); eassumption.
  Qed.
End DrvLaws.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.ImgAny.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_arep.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.GStatKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvStatA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma flag_ok : rw_bytes_b asegs 0x5e1050 [Z_to_bv 8 0] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ssp_ok : rw_bytes_b asegs 0x6019f8 (repeat (Z_to_bv 8 0) 8) = true.
Proof. vm_compute. reflexivity. Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma c1_any : forall (m : mem) A, rw_bytes_b asegs A [Z_to_bv 8 0] = true -> 0 <= A -> A + 1 <= 2^64 -> exists b : byte, rw_cells asegs m A [C1 b].
Proof.
  intros m A HB H0 H1. (nd_pre (rw_cells_any asegs m A [Z_to_bv 8 0] HB H0 ltac:(cbn [length]; lia)) 3%nat; intros bs HL HC; nd_post).
  destruct bs as [|b [|b' bs]]; cbn [length] in HL; try discriminate. exists b.
  destruct HC as [[WF B] W]. split; [split; [cbn; auto| exact B]| exact W].
Qed.
#[using="Type"] Lemma c8_any : forall (m : mem) A, rw_bytes_b asegs A (repeat (Z_to_bv 8 0) 8) = true -> 0 <= A -> A + 8 <= 2^64 -> exists w : word, rw_cells asegs m A [C8 w].
Proof.
  intros m A HB H0 H1. (nd_pre (rw_cells_any asegs m A (repeat (Z_to_bv 8 0) 8) HB H0 ltac:(rewrite repeat_length; lia)) 3%nat; intros bs HL HC; nd_post).
  rewrite repeat_length in HL, HC. apply A3W.ARepKit.TwB.c8_of_junk. apply (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AKitR.TwB.junk_of_cb m A 8 bs). exact HC.
Qed.

Section DrvLaws.
  Variable AI : AMallocIface.
  Hypothesis AF : AFakeIface AI.
  Hypothesis AI_block_tls : forall L RNG st LB m b, AHEAP AI L RNG st LB m -> In b LB ->
      ab_addr b + ab_size b <= ATP + -200 \/ ATP + -200 + 504 <= ab_addr b.
  Variables (USP : Z) (SB : list byte).
  Hypothesis USP_lo : ATOP + 64 <= USP.
  Hypothesis SB_16 : 16 <= Z.of_nat (length SB).
  Hypothesis USP_hi : USP + Z.of_nat (length SB) <= 2^47.
  Variable cs : list gcomp.
  Hypothesis CSOK : Forall (gcomp_ok AI) cs.
  Hypothesis CI_RS : exists iv, In iv (aci AI) /\ fst iv <= READ_STAGE /\ READ_STAGE + 65537 <= snd iv.
  Hypothesis IN_ARGS : In (args_comp USP (Z.of_nat (length SB) - 16)) cs.
  Hypothesis IN_UNP : In unp_comp cs.
  #[local] Notation GIOA := (GIOA_real AI (GSTAT_of cs)).

  #[using="AF AI_block_tls USP_lo SB_16 USP_hi CSOK CI_RS IN_ARGS IN_UNP"] Theorem gia_drv_laws_real : gia_drv_laws GIOA USP SB.
  Proof.
    constructor.
    - intros L RNG s CL FB FL m (_ & _ & _ & _ & _ & _ & (ERR & _)). exact ERR.
    - intros L RNG s CL FB FL m (AH & _). pose proof (AI_relro AI _ _ _ _ _ AH) as RO.
      split; [| split]; apply (relro_word m _ _ RO); first [unfold GOT_STDERR, STDERR_P, GOT_FUZZ_INIT, ARELRO_LO, ARELRO_HI; lia | vm_compute; reflexivity].
    - intros L RNG s CL FB FL m (AH & _). pose proof (AI_relro AI _ _ _ _ _ AH) as RO.
      split; [apply (relro_word m _ _ RO); first [unfold ARELRO_LO, ARELRO_HI; lia | vm_compute; reflexivity]|].
      apply c8_any; [exact ssp_ok| lia| lia].
    - intros L RNG s CL FB FL m (_ & _ & _ & _ & _ & _ & (_ & GC)).
      assert (H1 : 0 <= Z.of_nat (length SB) - 16) by lia. assert (H2 : USP + (Z.of_nat (length SB) - 16) + 8 <= 2^47) by lia.
      exact (args_mobjA USP (Z.of_nat (length SB) - 16) USP_lo H1 H2 L RNG s FB m (gconj_In _ _ _ _ _ _ _ GC IN_ARGS)).
    - intros L RNG s CL FB FL m (_ & _ & _ & _ & _ & _ & (_ & GC)). exact (gconj_In _ _ _ _ _ _ _ GC IN_UNP).
    - intros L RNG s CL FB FL m m' W G MU WM FW. eapply (gd_frame_real AI AF); eassumption.
    - intros L RNG s CL FB FL m m' W e G MU WM FW HE. eapply (gd_frame_errno_real AI AF); eassumption.
  Qed.
End DrvLaws.
End CANSEC1.
End TwB.
