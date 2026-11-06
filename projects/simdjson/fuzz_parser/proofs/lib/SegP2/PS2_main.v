(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore CatSim.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Mem Cells Step Frame.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require ExecF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PImg PIosRegs PIosKit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import RMallocRep RMallocTree RMalloc_iface ROpNew_iface ROpNew ROpNew_nt.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require RMalloc_ifaceP RF_free_spec.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad HarnessP ProgP SjStage1 SjS1Bytes SjInv.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import RunDraw PU_iface PC_s12iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg SegLib.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegA Require Import MuslMemP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SFP_sum PFF_sum SFPC_sum PFFC_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2G2 S2WalkVC S2WalkVCok S2TabP S2Entry P2_defs P2_cert PS2_t0 PS2_entry.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import PS2_stmt PS2_xnew.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Import ITree.Exc.
Open Scope Z_scope.
Local Notation u := bv_unsigned.
Local Notation M64 := 18446744073709551616.

Section S.
  Context {rc : runConstT}.
  Hypothesis ONT : opnew_nt_stmt.
  Hypothesis ODA : opdelete_arr_stmt.
  Hypothesis SFPS_ok : forall GP, SP.summ_okH SG GP MMP.hmH MMP.hmA MMP.hmC MMP.hmR SFPS.
  Hypothesis PFFS_ok : forall GP, SP.summ_okH SG GP MMP.hmH MMP.hmA MMP.hmC MMP.hmR PFFS.
  Hypothesis SFPCS_ok : forall GP, SP.summ_okH SG GP MMP.hmH MMP.hmA MMP.hmC MMP.hmR SFPCS.
  Hypothesis PFFCS_ok : forall GP, SP.summ_okH SG GP MMP.hmH MMP.hmA MMP.hmC MMP.hmR PFFCS.

  Ltac canon_regs E' HF' HR' sr :=
    rewrite (regs_ok_canon E' sr _ HF' HR');
    change (sr_get sr 1) with (EVar 0); change (sr_get sr 2) with (EVar 1); change (sr_get sr 3) with (EVar 2);
    change (sr_get sr 4) with (EVar 3); change (sr_get sr 8) with (EVar 4); change (sr_get sr 9) with (EVar 5);
    change (sr_get sr 18) with (EVar 6); change (sr_get sr 19) with (EVar 7); change (sr_get sr 20) with (EVar 8);
    change (sr_get sr 21) with (EVar 9); change (sr_get sr 22) with (EVar 10); change (sr_get sr 23) with (EVar 11);
    change (sr_get sr 24) with (EVar 12); change (sr_get sr 25) with (EVar 13); change (sr_get sr 26) with (EVar 14);
    change (sr_get sr 27) with (EVar 15); cbn [edenot].

  Theorem stage2_proof : stage2_stmt.
  Proof.
    unfold stage2_stmt. intros until jia. intros HR ND Ith Hnim Isi Hnsi Icp Hb1 Hb2 Itp Isb Ioc Hnoc Iia Hnia Hntp8 Hntp Hnsb3 Hnsb Hbuf Hd Hlen
      Hscan HIDX HO8 HO16 HO24 HO40 HO56 HDOC Hspd Hdb Hda HTB HSB HOC HIA HFM HGOT HAUX Hspb HSTK Hlo1 Hlo2 Hsp16 Hsp47 HERR HMI HFRM HTP HA0 HA1.
    pose proof (p2_entry SFPS_ok PFFS_ok ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
       F fc m s LB lo B d idx pim psi pcp ptp psb poc pia THIS ASI ACP ATP ASB AOC AIA DOC BUF nim nsi ncp ntp nsb noc nia x24 x88 jtp jsb joc jia
       HR ND Ith Hnim Isi Hnsi Icp Hb1 Hb2 Itp Isb Ioc Hnoc Iia Hnia Hntp8 Hntp Hnsb3 Hnsb Hbuf Hd Hlen Hscan HIDX
       HO8 HO16 HO24 HO40 HO56 HDOC Hspd Hdb Hda HTB HSB HOC HIA HFM HGOT HAUX Hspb HSTK Hlo1 Hlo2 Hsp16 Hsp47 HMI HFRM HA0 HA1) as HE.
    apply ExecF.evtF_evt in HE.
    eapply implM_evt; [exact HE|]. clear HE.
    intros ms1 (X & E' & m' & R' & F' & fc' & HinX & -> & HZ' & HF' & HR' & HK' & HG' & Hg & Hb & _ & FR & WM & MI' & STK').
    unfold SP.frame_ok in FR. cbn [SP.p_PS P2 SP.PGC] in FR.
    pose proof (s1_n _ _ _ (scan_S1OUT d idx Hscan)) as Sn.
    pose proof Hlo2 as Hlo2'. unfold PS2_STACK, OPNEW_NT_STACK, OPNEW_STACK, RMALLOC_STACK in Hlo2'. atop_facts.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m _ HR Ith) as (Rt1 & Rt2 & Rt3 & Rt4 & Rt5); cbn [blk_addr blk_size fst snd] in *.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m _ HR Itp) as (Rp1 & Rp2 & Rp3 & Rp4 & Rp5); cbn [blk_addr blk_size fst snd] in *.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m _ HR Isb) as (Rs1 & Rs2 & Rs3 & Rs4 & Rs5); cbn [blk_addr blk_size fst snd] in *.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m _ HR Ioc) as (Ro1 & Ro2 & Ro3 & Ro4 & Ro5); cbn [blk_addr blk_size fst snd] in *.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m _ HR Iia) as (Ra1 & Ra2 & Ra3 & Ra4 & Ra5); cbn [blk_addr blk_size fst snd] in *.
    assert (UT : DJ 0x10000 0x99000 THIS 96) by (eapply DJ_sub; [exact (DJ_hull _ _ Rt5 Rt3) | lia..]).
    assert (UP : DJ 0x10000 0x99000 ATP ntp) by (exact (DJ_hull _ _ Rp5 Rp3)).
    assert (US : DJ 0x10000 0x99000 ASB nsb) by (exact (DJ_hull _ _ Rs5 Rs3)).
    assert (UO : DJ 0x10000 0x99000 AOC 8192) by (eapply DJ_sub; [exact (DJ_hull _ _ Ro5 Ro3) | lia..]).
    assert (UA : DJ 0x10000 0x99000 AIA 1024) by (eapply DJ_sub; [exact (DJ_hull _ _ Ra5 Ra3) | lia..]).
    clear Rt5 Rp5 Rs5 Ro5 Ra5.
    pose proof (u_rng' sp) as Rsp.
    assert (HCAPT : 8 * (ntp / 8) = ntp) by (pose proof (Z.div_mod ntp 8 ltac:(lia)); lia).
    pose proof (p2_munch ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                  THIS DOC BUF (zlength d) ASI (zlength idx) ATP (ntp / 8) ASB nsb AOC AIA m m' FR
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as MU.
    rewrite HCAPT in MU.
    cbn [SP.p_ex P2] in HinX. destruct HinX as [<-|[<-|[]]].
    - (* [comment removed for export] *)
      destruct (ev_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E' Hg)
        as (G0 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15).
      unfold SG.gholds in HG'. cbn [ST.t_ghost XRET] in HG'. apply Forall_inv in HG' as GN. cbn [ST.g_id ST.g_args map gp2] in GN.
      destruct idx as [|i0 idx']; [exfalso; unfold zlength in Sn; cbn [length Z.of_nat] in Sn; lia|].
      change (znth ((i0 :: idx') ++ [zlength d; zlength d; 0]) 0) with i0 in GN.
      unfold rn_copy. rewrite GN. apply implM_ret.
      canon_regs E' HF' HR' XRET_regs.
      rewrite G0, G1, G2, G3, G4, G5, G6, G7, G8, G9, G10, G11, G12, G13, G14, G15.
      change (ST.t_pc XRET) with 0x2bc10.
      eapply xret_post with (pim := pim) (ptp := ptp) (psb := psb) (poc := poc) (pia := pia); try eassumption; try lia.
      reflexivity.
    - (* [comment removed for export] *)
      change (ST.t_pc XNEW) with 0x29320.
      eapply (xnew_branch ONT ODA SFPCS_ok PFFCS_ok); eassumption.
  Qed.
End S.

Print Assumptions stage2_proof.
