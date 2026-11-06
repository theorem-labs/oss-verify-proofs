(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memchr__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFake_iface AFake_arep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acallocS__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AInstanceF__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.F_adepot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.FsKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.AInstance OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.AInstanceM OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AInstanceF__A3W.AInstanceF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_gotA GioaReal. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_gotA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section Inst.
Variable CI : list (Z * Z).
Hypothesis CIB : ci_okb CI = true.
Let CI1 : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI := aci_ok1 CI CIB.

#[using="CI1"] Theorem afake_inst : AFakeIface (AI_of CI CIB).
Proof.
  constructor.
  - (* [comment removed for export] *)
    intros L RNG st LB m c F n AH Hin. change (AHEAP (AI_of CI CIB)) with (AHEAP_P AHI) in AH.
    (pose proof AH as ndP__; nd_pre ndP__ 4%nat; intros ALO ARNG _ HFK; nd_post). cbn [AHI ah_fake] in HFK.
    (pose proof (afake_lb L LB m c F n HFK Hin) as ndP__; nd_pre ndP__ 9%nat; intros Hc Hn Npos F64 FLO FHI FK FC _; nd_post).
    (pose proof HFK as ndP__; nd_pre ndP__ 8%nat; intros G _ _ _ _ _ DC2 _; nd_post). (nd_pre G 4%nat; intros G1 G2 G3 _; nd_post).
    (nd_pre ARNG 9%nat; intros _ _ _ _ _ _ RF RSF _; nd_post).
    (pose proof (ablk_lin _ _ G2) as ndP__; nd_pre ndP__ 4%nat; intros GL1 GL2 GL3 GL4; nd_post). unfold FAKESZ, AIMG_HI in *.
    assert (SHG : shad (al_fake L) <= shad F /\ shad F + n / 8 <= shad (al_fake L) + shlen 11571200 /\ 0 <= n / 8).
    { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. clear -G1 GL1 FLO FHI F64 Npos. Z.div_mod_to_equations. lia. }
    (nd_pre SHG 3%nat; intros SH1 SH2 SH3; nd_post).
    split; [exact Hc|]. split; [exact Hn|]. split; [exact F64|]. split; [exact FK|]. split; [exact FC|].
    split; [eapply rng_sub'; [exact RF| clear -FLO FHI; lia]|].
    split; [eapply rng_sub'; [exact RSF| clear -SH1 SH2; lia]|].
    pose proof (dc_sub m (shad (al_fake L)) (shlen 11571200) (shad F) (n / 8) DC2 SH1 SH3 SH2) as [bs DB].
    apply (SysStep.rw_cells_wr_at asegs m _ _ (n / 8) DB). cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by exact SH3. lia.
  - (* [comment removed for export] *)
    intros L RNG st LB m c F n AH Hin. change (AHEAP (AI_of CI CIB)) with (AHEAP_P AHI) in AH.
    (nd_pre (fake_flag_P adepot_iface AQUAR ASEC_of CI CI1 L RNG st LB m c F n AH Hin) 6%nat; intros H1 H2 H3 H4 H5 _; nd_post).
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4| exact H5].
  - (* [comment removed for export] *)
    intros L RNG st LB m AH. change (AHEAP (AI_of CI CIB)) with (AHEAP_P AHI) in AH. (nd_pre AH 3%nat; intros _ ARNG _; nd_post).
    (nd_pre ARNG 10%nat; intros _ _ _ _ _ _ RF RSF RD _; nd_post). unfold afake_rng, FAKESZ. split; [exact RF|]. split; [exact RSF| exact RD].
  - (* [comment removed for export] *)
    intros L RNG st LB m m' c F n spz AH SPZ MU WM FL1. change (AHEAP (AI_of CI CIB)) with (AHEAP_P AHI) in AH |- *.
    exact (fake_release_gen_P adepot_iface AQUAR ASEC_of AHI_laws CI CI1 L RNG st LB m m' c F n spz AH SPZ MU WM FL1).
  - (* [comment removed for export] *)
    intros c SYM HC L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB lo
           AH CNT MI ST BOT LO SPT TP RSTK RIMG RTLS RFK.
    change (AHEAP (AI_of CI CIB)) with (AHEAP_P AHI) in AH |- *.
    destruct HC as [[-> ->]|[-> ->]].
    + eapply evtF_mono; [eapply (stack_malloc_0_P adepot_iface AQUAR ASEC_of AHI_laws CI CI1); eassumption|].
      intros ms' PO. unfold sm_postP in PO. (nd_pre PO 21%nat; intros F t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' j0 j1 j2 junk PO; nd_post).
      (nd_pre PO 13%nat; intros E P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 _; nd_post).
      exists F, t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', j0, j1, j2, junk.
      change (fk_fsize 0) with 64. repeat (split; [assumption|]). assumption.
    + eapply evtF_mono; [eapply (stack_malloc_1_P adepot_iface AQUAR ASEC_of AHI_laws CI CI1); eassumption|].
      intros ms' PO. unfold sm_postP in PO. (nd_pre PO 21%nat; intros F t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' j0 j1 j2 junk PO; nd_post).
      (nd_pre PO 13%nat; intros E P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 _; nd_post).
      exists F, t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', j0, j1, j2, junk.
      change (fk_fsize 1) with 128. repeat (split; [assumption|]). assumption.
  - (* [comment removed for export] *)
    intros L RNG req ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB lo
           AH CNT EA0 REQ REQ8 MI ST BOT LO SPT TP RSTK RIMG RTLS RFK.
    change (AHEAP (AI_of CI CIB)) with (AHEAP_P AHI) in AH |- *.
    eapply evtF_mono; [eapply (stack_malloc_7_P adepot_iface AQUAR ASEC_of AHI_laws CI CI1); eassumption|].
    intros ms' PO. unfold sm7_postP in PO.
    (nd_pre PO 22%nat; intros F t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' j0 j1 j2 junk sjunk PO; nd_post).
    (nd_pre PO 14%nat; intros E P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 _; nd_post).
    exists F, t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', j0, j1, j2, junk, sjunk.
    repeat (split; [assumption|]). assumption.
  - (* [comment removed for export] *)
    intros L RNG req ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB lo F
           AH EA0 EA1 REQ REQ8 LAST MI ST BOT LO SPT RSTK RIMG RTLS RFK.
    change (AHEAP (AI_of CI CIB)) with (AHEAP_P AHI) in AH |- *.
    eapply evtF_mono; [eapply (stack_free_7_P adepot_iface AQUAR ASEC_of AHI_laws CI CI1); eassumption|].
    intros ms' PO. unfold sf7_postP in PO.
    (nd_pre PO 22%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' E P1 P2 P3 P4 _; nd_post).
    exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    repeat (split; [assumption|]). assumption.
Qed.
End Inst.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.F_adepot.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.FsKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.AInstance.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.AInstanceM.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AInstanceF__A3W.AInstanceF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_gotA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section Inst.
Variable CI : list (Z * Z).
Hypothesis CIB : ci_okb CI = true.
Let CI1 : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI := aci_ok1 CI CIB.

#[using="CI1"] Theorem afake_inst : AFakeIface (AI_of CI CIB).
Proof.
  constructor.
  - (* [comment removed for export] *)
    intros L RNG st LB m c F n AH Hin. change (AHEAP (AI_of CI CIB)) with (AHEAP_P AHI) in AH.
    (pose proof AH as ndP__; nd_pre ndP__ 4%nat; intros ALO ARNG _ HFK; nd_post). cbn [AHI ah_fake] in HFK.
    (pose proof (afake_lb L LB m c F n HFK Hin) as ndP__; nd_pre ndP__ 9%nat; intros Hc Hn Npos F64 FLO FHI FK FC _; nd_post).
    (pose proof HFK as ndP__; nd_pre ndP__ 8%nat; intros G _ _ _ _ _ DC2 _; nd_post). (nd_pre G 4%nat; intros G1 G2 G3 _; nd_post).
    (nd_pre ARNG 9%nat; intros _ _ _ _ _ _ RF RSF _; nd_post).
    (pose proof (ablk_lin _ _ G2) as ndP__; nd_pre ndP__ 4%nat; intros GL1 GL2 GL3 GL4; nd_post). unfold FAKESZ, AIMG_HI in *.
    assert (SHG : shad (al_fake L) <= shad F /\ shad F + n / 8 <= shad (al_fake L) + shlen 11571200 /\ 0 <= n / 8).
    { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. clear -G1 GL1 FLO FHI F64 Npos. Z.div_mod_to_equations. lia. }
    (nd_pre SHG 3%nat; intros SH1 SH2 SH3; nd_post).
    split; [exact Hc|]. split; [exact Hn|]. split; [exact F64|]. split; [exact FK|]. split; [exact FC|].
    split; [eapply rng_sub'; [exact RF| clear -FLO FHI; lia]|].
    split; [eapply rng_sub'; [exact RSF| clear -SH1 SH2; lia]|].
    pose proof (dc_sub m (shad (al_fake L)) (shlen 11571200) (shad F) (n / 8) DC2 SH1 SH3 SH2) as [bs DB].
    apply (SysStep.rw_cells_wr_at asegs m _ _ (n / 8) DB). cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by exact SH3. lia.
  - (* [comment removed for export] *)
    intros L RNG st LB m c F n AH Hin. change (AHEAP (AI_of CI CIB)) with (AHEAP_P AHI) in AH.
    (nd_pre (fake_flag_P adepot_iface AQUAR ASEC_of CI CI1 L RNG st LB m c F n AH Hin) 6%nat; intros H1 H2 H3 H4 H5 _; nd_post).
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4| exact H5].
  - (* [comment removed for export] *)
    intros L RNG st LB m AH. change (AHEAP (AI_of CI CIB)) with (AHEAP_P AHI) in AH. (nd_pre AH 3%nat; intros _ ARNG _; nd_post).
    (nd_pre ARNG 10%nat; intros _ _ _ _ _ _ RF RSF RD _; nd_post). unfold afake_rng, FAKESZ. split; [exact RF|]. split; [exact RSF| exact RD].
  - (* [comment removed for export] *)
    intros L RNG st LB m m' c F n spz AH SPZ MU WM FL1. change (AHEAP (AI_of CI CIB)) with (AHEAP_P AHI) in AH |- *.
    exact (fake_release_gen_P adepot_iface AQUAR ASEC_of AHI_laws CI CI1 L RNG st LB m m' c F n spz AH SPZ MU WM FL1).
  - (* [comment removed for export] *)
    intros c SYM HC L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB lo
           AH CNT MI ST BOT LO SPT TP RSTK RIMG RTLS RFK.
    change (AHEAP (AI_of CI CIB)) with (AHEAP_P AHI) in AH |- *.
    destruct HC as [[-> ->]|[-> ->]].
    + eapply evtF_mono; [eapply (stack_malloc_0_P adepot_iface AQUAR ASEC_of AHI_laws CI CI1); eassumption|].
      intros ms' PO. unfold sm_postP in PO. (nd_pre PO 21%nat; intros F t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' j0 j1 j2 junk PO; nd_post).
      (nd_pre PO 13%nat; intros E P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 _; nd_post).
      exists F, t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', j0, j1, j2, junk.
      change (fk_fsize 0) with 64. repeat (split; [assumption|]). assumption.
    + eapply evtF_mono; [eapply (stack_malloc_1_P adepot_iface AQUAR ASEC_of AHI_laws CI CI1); eassumption|].
      intros ms' PO. unfold sm_postP in PO. (nd_pre PO 21%nat; intros F t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' j0 j1 j2 junk PO; nd_post).
      (nd_pre PO 13%nat; intros E P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 _; nd_post).
      exists F, t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', j0, j1, j2, junk.
      change (fk_fsize 1) with 128. repeat (split; [assumption|]). assumption.
  - (* [comment removed for export] *)
    intros L RNG req ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB lo
           AH CNT EA0 REQ REQ8 MI ST BOT LO SPT TP RSTK RIMG RTLS RFK.
    change (AHEAP (AI_of CI CIB)) with (AHEAP_P AHI) in AH |- *.
    eapply evtF_mono; [eapply (stack_malloc_7_P adepot_iface AQUAR ASEC_of AHI_laws CI CI1); eassumption|].
    intros ms' PO. unfold sm7_postP in PO.
    (nd_pre PO 22%nat; intros F t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' j0 j1 j2 junk sjunk PO; nd_post).
    (nd_pre PO 14%nat; intros E P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 _; nd_post).
    exists F, t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', j0, j1, j2, junk, sjunk.
    repeat (split; [assumption|]). assumption.
  - (* [comment removed for export] *)
    intros L RNG req ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB lo F
           AH EA0 EA1 REQ REQ8 LAST MI ST BOT LO SPT RSTK RIMG RTLS RFK.
    change (AHEAP (AI_of CI CIB)) with (AHEAP_P AHI) in AH |- *.
    eapply evtF_mono; [eapply (stack_free_7_P adepot_iface AQUAR ASEC_of AHI_laws CI CI1); eassumption|].
    intros ms' PO. unfold sf7_postP in PO.
    (nd_pre PO 22%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' E P1 P2 P3 P4 _; nd_post).
    exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    repeat (split; [assumption|]). assumption.
Qed.
End Inst.
End CANSEC1.
End TwB.
