(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Mem MState Arr Asn1Aux CellsX SysStep ITree Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_vsnp_num.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_PfNum AW_PfVsn AW_PfShared AW_PfEmb AW_B12Pieces.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv AJ AKinvS ASpinS AW_Unwind AW_Unwind2 AW_MmapFixed AW_MmapDie AW_Poison.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_CfgS AW_Populate AW_EmbCfg AW_DepotCfg AW_B12Walk.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AW_B12WalkP () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate.b12_ro"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate.A_EMB"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kEmbBytes"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.EM"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate.A_FMT_OOM1"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate.A_ASAN_NAME"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate.A_PRINTF"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_B12Walk.b12_laws"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_EmbCfg.b12_siteS"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.

#[using="Type"] Lemma ndig_4096 : ndig 10 20 4096 = 4. Proof. vm_compute. reflexivity. Qed.

Section W2.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.

  (* [comment removed for export] *)
  #[using="IMG ALWF"] Lemma pair_present : ltac2:(CDefT.buildp (gd_tbl_AW_B12WalkP ()) "PCS,P,$0.SpPCSOK,(1.VAL,R1.)Pc,$0.PSP0,$0.Plo,$0.Pd,$0.Psz,$0.Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(3.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(4.(2.&8.))P,(5.(6.+1.R22.)(6.R22.+1?.))P,(7.R2.)P,(8.$9.R3.$:.(;.$<.(=.(>.&40.(?.$:.+20.)))(10.$<.)))P,(8.$9.R4.(?.$:.+10.)(;.$<.(=.(>.&40.=))(10.$<.)))P,(8.$9.R5.(?.$:.+20.)(;.$<.(=.(>.&40.R23.))(;.$<.(=.(>.&40.$11.))(;.$<.(=.(>.&40.R22.))(10.$<.)))))P,(12.$9.R6.R24.$11.)P,(13.R2:.R25.$11.)P,(6.+65?000.R26.)P,(6.(?.R27.$11.)R28.)P,(5.(6.=R27.)(6.R27.(14.+3>.+80.)))P,(15.$9.R;.R2:.R2;.)P,(6.+65?000.R2;.)P,(6.R2<.(16.R2=.+450.))P,(6.R2>.(17.+2.+3?.))P,(13.R32.R2>.(16.R2?.R2>.))P,(18.$9.R10.)(19.$9.VAL,R34.Lms',$1:.(1;.$0.Lsz',$0.(1;.(2.&40.)Lt0',(2.&40.)(1;.(2.&40.)Lt1',(2.&40.)(1;.(2.&40.)Lt2',(2.&40.)(1;.(2.&40.)La0',(2.&40.)(1;.(2.&40.)La1',(2.&40.)(1;.(2.&40.)La2',(2.&40.)(1;.(2.&40.)La3',(2.&40.)(1;.(2.&40.)La4',(2.&40.)(1;.(2.&40.)La5',(2.&40.)(1;.(2.&40.)La6',(2.&40.)(1;.(2.&40.)La7',(2.&40.)(1;.(2.&40.)Lt3',(2.&40.)(1;.(2.&40.)Lt4',(2.&40.)(1;.(2.&40.)Lt5',(2.&40.)(1;.(2.&40.)Lt6',(2.&40.)(1;.P,(2.&40.)(4.(2.&8.))Lm',P,(2.&40.)(4.(2.&8.))(5.(1<.$1:.R12.(1=.(1>.(>.&40.+4<><0.)(>.&40.R43.)R3?.R3>.R10.R?.R>.(>.&40.R44.)R3:.R=.R<.R;.R:.R9.R8.R7.R6.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R5.R4.R3.R2.)R25.(>.&40.+4<><0.)R24.(1?.(2.&40.))R1.(20.$9.)))(5.(5.(21.R40.R11.)(6.R11.(?.R40.$22.)))(5.(7.R1.)(5.(8.$9.R1.$:.(;.$<.(=.(>.&40.(?.$:.+20.)))(10.$<.)))(5.(8.$9.R1.(?.$:.+10.)(;.$<.(=.(>.&40.=))(10.$<.)))(5.(8.$9.R1.(?.$:.+20.)(;.$<.(=.(>.&40.R41.))(;.$<.(=.(>.&40.$11.))(;.$<.(=.(>.&40.R11.))(10.$<.)))))(5.(12.$9.R1.R41.$11.)(5.(15.$9.R1.R42.R43.)(5.(23.(;.(24.$0.$0.)(25.$0.$0.R42.R43.)(;.(24.$0.$0.)(25.$0.$0.$:.(?.$:.+38.))(;.(24.$0.$0.)(25.$0.$0.R41.(?.R41.$11.))(10.(24.$0.$0.)))))R23.R1.)(5.(26.$9.R23.R1.)(18.$9.R1.))))))))))))))))))))))))))))(1=.(1>.(>.&40.+4<>4<.)(>.&40.R31.)R2=.R2<.R2;.R2:.R29.(>.&40.R32.)R28.(>.&40.$27.)(>.&40.$28.)R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.)R13.(>.&40.$29.)R12.(1?.(2.&40.))R11.(20.$9.)))")
(* [comment removed for export] *).
  Proof.
    intros CS CSOK. intros until m. intros Hc RO EP EMX EV WRB CRD DLO DHI SZB ST LOIMG SPL SPH SCS MI.
    unfold A_FMT_OOM1, A_ASAN_NAME, A_PRINTF.
    eapply (evtA_cut asegs AL CS).
    { eapply (printf_present AL IMG ALWF CS CSOK 0x221b8 33 SP0 lo d sz); try eassumption; try lia.
      apply (vsn_f1_call AL IMG ALWF CS CSOK). }
    cbn beta. (intros ms' dd_H; ddestruct dd_H as (t0a & t1a & t2a & a0a & a1a & a2a & a3a & a4a & a5a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & -> & RO1 & EP1 & EMX1 & EV1 & WRB1 & ST1 & MU1 & WM1 & MI1)).
    ret_lit.
    eapply (evtA_cut asegs AL CS).
    { eapply (pair_mid AL IMG ALWF CS CSOK c SP0); [exact Hc| exact MI1]. }
    cbn beta. intros ms' (w3 & ->).
    pose proof (bv_unsigned_in_range 64 w3) as W3R. unfold bv_modulus in W3R. change (2 ^ Z.of_N 64) with (2^64) in W3R.
    set (v3 := bv_unsigned w3) in *.
    pose proof (ndig_ge1 10 20 c) as Jc1. pose proof (ndig_le2 10 20 2 c ltac:(lia) ltac:(lia) ltac:(change (10 ^ Z.of_nat 2) with 100; lia)) as Jc2.
    pose proof (ndig_ge1 10 20 v3) as Jv1. pose proof (ndig_le 10 20 v3 ltac:(lia) ltac:(lia)) as Jv2. change (Z.max 1 (Z.of_nat 20)) with 20 in Jv2.
    set (len2 := 56 + ndig 10 20 4096 + ndig 10 20 c + ndig 10 20 v3).
    assert (L2 : 61 <= len2 <= 82) by (unfold len2; rewrite ndig_4096; lia).
    rewrite <- (Z_to_bv_bv_unsigned w3). fold v3.
    eapply (evtA_mono asegs AL CS).
    { eapply (printf_present AL IMG ALWF CS CSOK 0x23fb2 len2 SP0 lo d (33 + sz)); try eassumption; try lia.
      apply (vsn_f2_call AL IMG ALWF CS CSOK 4096 c v3); lia. }
    cbn beta. (intros ms' dd_H; ddestruct dd_H as (t0b & t1b & t2b & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2 & -> & RO2 & EP2 & EMX2 & EV2 & WRB2 & ST2 & MU2 & WM2 & MI2)).
    replace (ret_pc (Z_to_bv 64 315072)) with (Z_to_bv 64 315072) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    exists (len2 + (33 + sz)). eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, m2.
    split; [reflexivity|]. split; [unfold EM; lia|]. split; [exact RO2|]. split; [exact EP2|]. split; [exact EMX2|]. split; [exact EV2|]. split; [exact WRB2|].
    split; [exact ST2|]. split; [eapply munch_trans; [exact MU1| exact MU2]|]. split; [eapply wmono_trans; [exact WM1| exact WM2]| exact MI2].
  Qed.

  (* [comment removed for export] *)
  #[using="IMG ALWF"] Lemma pair_tail : ltac2:(CDefT.buildp (gd_tbl_AW_B12WalkP ()) "PCS,P,$0.SpPCSOK,(1.VAL,R1.)Pc,$0.PSP0,$0.Plo,$0.Pd,$0.Psz1,$0.Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(3.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(4.(2.&8.))Pm,P,(2.&40.)(4.(2.&8.))P,(5.(6.+1.R25.)(6.R25.+1?.))P,(7.R2.)P,(8.$9.R3.$:.(;.$<.(=.(>.&40.(?.$:.+20.)))(10.$<.)))P,(8.$9.R4.(?.$:.+10.)(;.$<.(=.(>.&40.=))(10.$<.)))P,(8.$9.R5.(?.$:.+20.)(;.$<.(=.(>.&40.R26.))(;.$<.(=.(>.&40.$11.))(;.$<.(=.(>.&40.R25.))(10.$<.)))))P,(12.$9.R6.R27.$11.)P,(13.R2=.R28.$11.)P,(6.+65?000.R29.)P,(6.(?.R2:.$11.)R2;.)P,(5.(6.=R2:.)(6.R2:.(?.(14.+3>.+80.)+21.)))P,(15.$9.R;.R2=.R2>.)P,(6.+65?000.R2>.)P,(6.R2?.(16.R30.+450.))P,(6.R31.(17.+2.+3?.))P,(13.R35.R31.(16.R32.R31.))P,(23.(;.(24.$0.$0.)(25.$0.$0.R32.R33.)(;.(24.$0.$0.)(25.$0.$0.$:.(?.$:.+38.))(;.(24.$0.$0.)(25.$0.$0.R31.(?.R31.$11.))(10.(24.$0.$0.)))))R11.R10.)P,(26.$9.R12.R11.)P,(18.$9.R12.)(19.$9.VAL,R39.Lms',$1:.(1;.$0.Lsz',$0.(1;.(2.&40.)Lt0',(2.&40.)(1;.(2.&40.)Lt1',(2.&40.)(1;.(2.&40.)Lt2',(2.&40.)(1;.(2.&40.)La0',(2.&40.)(1;.(2.&40.)La1',(2.&40.)(1;.(2.&40.)La2',(2.&40.)(1;.(2.&40.)La3',(2.&40.)(1;.(2.&40.)La4',(2.&40.)(1;.(2.&40.)La5',(2.&40.)(1;.(2.&40.)La6',(2.&40.)(1;.(2.&40.)La7',(2.&40.)(1;.(2.&40.)Lt3',(2.&40.)(1;.(2.&40.)Lt4',(2.&40.)(1;.(2.&40.)Lt5',(2.&40.)(1;.(2.&40.)Lt6',(2.&40.)(1;.P,(2.&40.)(4.(2.&8.))Lm',P,(2.&40.)(4.(2.&8.))(5.(1<.$1:.R12.(1=.(1>.(>.&40.+4<><0.)(>.&40.R48.)R44.R43.R10.R?.R>.(>.&40.R49.)R3?.R=.R<.R;.R:.R9.R8.R7.R6.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R5.R4.R3.R2.)R28.(>.&40.+4<><0.)R27.(1?.(2.&40.))R1.(20.$9.)))(5.(5.(6.(?.R45.+3=.)R11.)(6.R11.(?.R45.+52.)))(5.(7.R1.)(5.(8.$9.R1.$:.(;.$<.(=.(>.&40.(?.$:.+20.)))(10.$<.)))(5.(8.$9.R1.(?.$:.+10.)(;.$<.(=.(>.&40.=))(10.$<.)))(5.(8.$9.R1.(?.$:.+20.)(;.$<.(=.(>.&40.R46.))(;.$<.(=.(>.&40.$11.))(;.$<.(=.(>.&40.R11.))(10.$<.)))))(5.(12.$9.R1.R46.$11.)(5.(15.$9.R1.R47.R48.)(5.(23.(;.(24.$0.$0.)(25.$0.$0.R47.R48.)(;.(24.$0.$0.)(25.$0.$0.$:.(?.$:.+38.))(;.(24.$0.$0.)(25.$0.$0.R46.(?.R46.$11.))(10.(24.$0.$0.)))))R26.R1.)(5.(26.$9.R26.R1.)(18.$9.R1.))))))))))))))))))))))))))))(1=.(1>.(>.&40.+4<>4<.)(>.&40.R36.)R32.R31.R30.R2?.R2>.(>.&40.R37.)R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.)R16.(>.&40.+4<>4<.)R15.(1?.(2.&40.))R13.(20.$9.)))")
(* [comment removed for export] *).
  Proof.
    intros CS CSOK. intros until m. intros Hc RO1 EP1 EMX1 EV1 WRB1 CRD DLO DHI SZB ST1 LOIMG SPL SPH SCS MU1 WM1 MI1.
    eapply (evtA_cut asegs AL CS).
    { eapply (pair_mid AL IMG ALWF CS CSOK c SP0); [exact Hc| exact MI1]. }
    cbn beta. intros ms' (w3 & ->).
    pose proof (bv_unsigned_in_range 64 w3) as W3R. unfold bv_modulus in W3R. change (2 ^ Z.of_N 64) with (2^64) in W3R.
    set (v3 := bv_unsigned w3) in *.
    pose proof (ndig_ge1 10 20 c) as Jc1. pose proof (ndig_le2 10 20 2 c ltac:(lia) ltac:(lia) ltac:(change (10 ^ Z.of_nat 2) with 100; lia)) as Jc2.
    pose proof (ndig_ge1 10 20 v3) as Jv1. pose proof (ndig_le 10 20 v3 ltac:(lia) ltac:(lia)) as Jv2. change (Z.max 1 (Z.of_nat 20)) with 20 in Jv2.
    set (len2 := 56 + ndig 10 20 4096 + ndig 10 20 c + ndig 10 20 v3).
    assert (L2 : 61 <= len2 <= 82) by (unfold len2; rewrite ndig_4096; lia).
    rewrite <- (Z_to_bv_bv_unsigned w3). fold v3.
    eapply (evtA_mono asegs AL CS).
    { eapply (printf_present AL IMG ALWF CS CSOK 0x23fb2 len2 SP0 lo d sz1); try eassumption; try lia.
      apply (vsn_f2_call AL IMG ALWF CS CSOK 4096 c v3); lia. }
    cbn beta. (intros ms' dd_H; ddestruct dd_H as (t0b & t1b & t2b & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2 & -> & RO2 & EP2 & EMX2 & EV2 & WRB2 & ST2 & MU2 & WM2 & MI2)).
    replace (ret_pc (Z_to_bv 64 315072)) with (Z_to_bv 64 315072) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    exists (len2 + sz1). eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, m2.
    split; [reflexivity|]. split; [lia|]. split; [exact RO2|]. split; [exact EP2|]. split; [exact EMX2|]. split; [exact EV2|]. split; [exact WRB2|].
    split; [exact ST2|]. split; [eapply munch_trans; [exact MU1| exact MU2]|]. split; [eapply wmono_trans; [exact WM1| exact WM2]| exact MI2].
  Qed.

  #[using="IMG ALWF"] Theorem b12_walk_AL : ltac2:(CDefT.buildp (gd_tbl_AW_B12WalkP ()) "PCS00,P,$0.SpPK00,P,$2:.SpPCSx,P,$0.P,$0.SpPKx,P,$0.P,$2:.SpPEP,$0.PEB,$0.PECAP,$0.PESZ,$0.P,(2;.VhAR,VAL,R8.R7.R6.R5.R4.R3.R2.R1.)(2<.VhAR,R9.R8.R6.R5.R4.R3.R2.)")
(* [comment removed for export] *).
  Proof.
    intros CS00 K00 CSx Kx EP EB ECAP ESZ LAWS.
    ddestruct LAWS as (CSOK0 & KL0 & CSOKx & KLx & INC & APART & GRANT & ROOM & EBCS & EWF & GEO).
    unfold b12_siteS. intros Q gp tp x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      SP0 lo0 c F fc m mo Hc STAT ST LOA SPL SPH SPA SCS MI K0 HJ0 CONT.
    destruct STAT as [RO (E1 & E2 & E3 & E4)].
    pose proof aceil_bounds as AC. unfold B12_NEEDX in SPL.
    destruct (Z.eq_dec EB 0) as [EB0|EBN].
    2:{ (* [comment removed for export] *)
      destruct EWF as [_ W2]. ddestruct (W2 EBN) as (-> & -> & SZ0). destruct (GEO EBN) as [GLO GHI]. unfold EM in SZ0.
      eapply (evtA_aevtS_KJ AL CS00 K00 _ Q _ mo KL0 K0); [exact HJ0| |].
      { eapply (pair_present CS00 CSOK0 c SP0 lo0 EB ESZ); try eassumption; try lia. exact (E4 EBN). exact (EBCS EBN). }
      cbn beta. (intros ms' mo' dd_H; ddestruct dd_H as (sz' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & SZ' & RO' & EP' & EMX' & EV' & WRB' & ST' & MU' & WM' & MI'); intros K' MM HJ').
      apply CONT. unfold b12_postS.
      eexists _, mo', None, (A_EMB + 32), EB, kEmbBytes, sz', t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
      split; [reflexivity|]. split; [reflexivity|].
      split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact K'|]. split; [exact HJ'|].
      split; [unfold emb_cells; split; [exact EP'|]; split; [exact EMX'|]; split; [exact EV'| intros _; exact WRB']|].
      split; [unfold emb_step; split; [reflexivity|]; split; [reflexivity|]; split; [exact SZ'|]; right; split; [exact EBN|]; split; reflexivity|].
      intros a Ha. discriminate Ha. }
    (* [comment removed for export] *)
    subst EB. destruct EWF as [W1 _]. ddestruct (W1 eq_refl) as (-> & -> & ->). clear W1 E4 EBCS GEO.
    eapply (evtA_aevtS_KJ AL CS00 K00 _ Q _ mo KL0 K0); [exact HJ0| |].
    { unfold A_FMT_OOM1, A_ASAN_NAME, A_PRINTF.
      eapply (printf_first_pre AL IMG ALWF CS00 CSOK0 0x221b8 33 SP0 lo0); try eassumption; try lia.
      apply (vsn_f1_call AL IMG ALWF CS00 CSOK0). }
    cbn beta. (intros ms3 mo3 dd_H; ddestruct dd_H as (t0' & t1' & t2' & t3' & t4' & t5' & t6' & a6' & mm & -> & FACTS & MU3 & WM3); intros HK3 MM3 HJ3).
    eapply (aevtS_mmap_anon asegs _) with (nZ := 65536) (flags := 0x22).
    { exact (ki_halted KL0 mo3 HK3). }
    { exact (ki_top KL0 mo3 HK3). }
    { unfold mmap_anon_args, areg, MSsvc. cbn [ms_regs]. simp_regs.
      repeat split; try reflexivity; try lia.
      - intros E. apply (f_equal bv_unsigned) in E. vm_compute in E. discriminate E.
      - left. reflexivity. }
    { exact (ROOM mo3 eq_refl HK3). }
    - (* [comment removed for export] *)
      intros e HIn. right. destruct HIn as [<-|[]].
      rewrite nret_MSsvc, mkR_set_a0, apply_mem_none.
      replace (errno_ret ENOMEM) with (Z_to_bv 64 (2^64 - 12)) by (apply bv_eq; vm_compute; reflexivity).
      change (Z_to_bv 64 A_MMAP_ECALL + Z_to_bv 64 4)%bv with (Z_to_bv 64 0x7b260).
      ddestruct FACTS as (fr & j8 & bs1 & F1 & F2 & F3 & EP & EMX & EV & PF & OUT & LB & PR & NUL & RO3 & ST3 & MI3).
      pose proof RO3 as RO3'. unfold b12_ro in RO3'. ddestruct RO3' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEAL & DYI).
      eapply (evtA_spinJ_K asegs AL CS00 K00 _ _ mo3 KL0 HK3).
      { replace (SP0 + -640 + -176) with (SP0 + -640 + -128 + -48) by lia.
        eapply (mmapdie_post_die AL IMG ALWF CS00 CSOK0) with (m0 := mm) (SP := SP0 + -640 + -128) (lo := lo0) (size := 65536) (name := 139685) (raw := 1) (fr := fr);
          try eassumption; try lia; try apply munch_refl; try apply wmono_refl.
        - replace (SP0 + -640 + -128 + -48) with (SP0 + -640 + -176) by lia. exact F1.
        - replace (SP0 + -640 + -128 + -48) with (SP0 + -640 + -176) by lia. exact ST3.
        - intros x Hx. apply SCS. lia. }
      cbn beta. intros ms5 mo5 PO HK5 _. ddestruct PO as (r' & F' & mm' & ->).
      apply spinningJ_at; [cbn; tauto| exact (ki_halted KL0 mo5 HK5)].
    - (* [comment removed for export] *)
      intros a AAL A0 ACE RF.
      rewrite nret_MSsvc, mkR_set_a0, apply_mem_zeros.
      change (Z_to_bv 64 A_MMAP_ECALL + Z_to_bv 64 4)%bv with (Z_to_bv 64 0x7b260).
      pose proof (bv_unsigned_in_range 64 a) as AR. unfold bv_modulus in AR. change (2 ^ Z.of_N 64) with (2^64) in AR.
      ddestruct (GRANT mo3 a eq_refl HK3 AAL A0 ACE RF) as (HK4 & CR4 & UA & PB).
      pose proof (J_anon_grant mm mo3 0x22 a 65536 HJ3 ltac:(clear; lia) ltac:(clear - ACE AC; lia) RF) as HJ4.
      pose proof (APART mo3 a (Z_to_bv 64 65536) HK3 RF) as AP.
      replace (bv_unsigned (Z_to_bv 64 65536)) with 65536 in AP by (symmetry; apply unsigned_lit; lia).
      specialize (AP ltac:(clear; lia) ltac:(clear - ACE; lia)).
      set (ua := bv_unsigned a) in *. unfold kEmbBytes in *.
      assert (Ha : 0 <= ua < 2^64) by lia. assert (Hn : 0 <= 65536 < 2^64) by lia. assert (Han : ua + 65536 <= 2^64) by lia.
      ddestruct FACTS as (fr & j8 & bs1 & FF). dpose FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI3).
      assert (FACTS : pfirst_facts 0x221b8 33 SP0 lo0 (Z_to_bv 64 0x4ce4c) (Z_to_bv 64 c) x9 x18 x19 x20 x21 x22 x23 x24 x25 mm) by (exists fr, j8, bs1; exact FF).
      clear FF.
      rewrite <- (Z_to_bv_bv_unsigned a). fold ua. change (Z_to_bv 64 ua, Z_to_bv 64 65536) with (wa ua, Z_to_bv 64 65536).
      rewrite <- (Z_to_bv_bv_unsigned a) in HJ4. fold ua in HJ4. change (Z_to_bv 64 ua, Z_to_bv 64 65536) with (wa ua, Z_to_bv 64 65536) in HJ4.
      pose proof (munch_zeros mm ua 65536 Ha Hn Han [(ua, ua + 65536)] mm (munch_refl _ mm) ltac:(cbn; lia)) as MUz.
      pose proof (wmono_zeros asegs mm ua 65536 Ha Hn Han mm (wmono_refl asegs mm)) as WMz.
      assert (MIz : mem_inv asegs (apply_zeros mm [(wa ua, Z_to_bv 64 65536)])).
      { eapply (mem_inv_zeros asegs mm ua 65536 Ha Hn Han MI3). intros x Hx.
        destruct (ro_addr asegs x) eqn:E; [|reflexivity]. exfalso. pose proof (asegs_ro_lt x E). lia. }
      pose proof (rw_cells_zeros_new asegs mm ua 65536 Ha Hn Han) as NEWz.
      set (mz := apply_zeros mm [(wa ua, Z_to_bv 64 65536)]) in *. clearbody mz.
      assert (WRz : wr_at asegs mz ua 65536). { destruct NEWz as [_ W]. cbn [cells_size csize] in W. rewrite Nat.add_0_r in W. exact W. }
      pose proof (pfirst_facts_tr 0x221b8 33 SP0 lo0 _ _ _ _ _ _ _ _ _ _ _ ua 65536 mm mz FACTS MUz WMz MIz UA ltac:(lia) ltac:(lia) ltac:(lia)) as FACTSz.
      assert (SCSx : crange (CSx ua) lo0 (SP0 - lo0)) by (intros x Hx; apply INC; apply SCS; exact Hx).
      rewrite <- (Z_to_bv_bv_unsigned a) in HK4. fold ua in HK4.
      eapply (evtA_aevtS_KJ AL (CSx ua) (Kx ua) _ Q _ _ (KLx ua) HK4); [exact HJ4| |].
      { change (Z_to_bv 64 65536) with (Z_to_bv 64 ((65536 + 4095) / 4096 * 4096)).
        replace (SP0 + -640 + -176) with (SP0 + -640 + -128 + -48) by lia.
        eapply (evtA_cut asegs AL (CSx ua)).
        { eapply (printf_first_post AL IMG ALWF (CSx ua) (CSOKx ua) 0x221b8 33 SP0 lo0 (Z_to_bv 64 ua)) with (m0 := m);
            rewrite ?unsigned_lit by lia; unfold kEmbBytes; try eassumption; try lia.
          - eapply munch_trans; [eapply munch_weaken; [| exact MU3]| eapply munch_weaken; [| exact MUz]]; unfold sub_fp; cbn [outside]; intros x Hx; lia.
          - eapply wmono_trans; [exact WM3| exact WMz]. }
        cbn beta. rewrite ?unsigned_lit by lia. unfold kEmbBytes.
        (intros ms' dd_H; ddestruct dd_H as (t0a & t1a & t2a & a0a & a1a & a2a & a3a & a4a & a5a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & -> & RO1 & EP1 & EMX1 & EV1 & WRB1 & ST1 & MU1 & WM1 & MI1)).
        ret_lit.
        eapply (pair_tail (CSx ua) (CSOKx ua) c SP0 lo0 ua 33) with (m0 := m); unfold kEmbBytes; try eassumption; try lia. }
      cbn beta. (intros ms' mo' dd_H; ddestruct dd_H as (sz' & t0q & t1q & t2q & a0q & a1q & a2q & a3q & a4q & a5q & a6q & a7q & t3q & t4q & t5q & t6q & m' & -> & SZ' & RO' & EP' & EMX' & EV' & WRB' & ST' & MU' & WM' & MI'); intros K' MM HJ').
      apply CONT. unfold b12_postS.
      eexists _, mo', (Some ua), (A_EMB + 32), ua, kEmbBytes, sz', t0q, t1q, t2q, a0q, a1q, a2q, a3q, a4q, a5q, a6q, a7q, t3q, t4q, t5q, t6q, m'.
      split; [reflexivity|]. split; [reflexivity|].
      split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact K'|]. split; [exact HJ'|].
      split; [unfold emb_cells; split; [exact EP'|]; split; [exact EMX'|]; split; [exact EV'| intros _; exact WRB']|].
      split. { unfold emb_step. split; [reflexivity|]. split; [reflexivity|]. split; [unfold EM; lia|].
               left. split; [reflexivity|]. exists ua. split; [reflexivity|]. split; [reflexivity| lia]. }
      intros a' Ha'. injection Ha' as <-. unfold kEmbBytes.
      split; [exact UA|]. split; [exact ACE|]. split; [exact PB|]. split; [exact AAL|].
      intros y Hy. apply AP. left. exact Hy.
  Qed.
End W2.

#[using="Type"] Theorem b12_walk : b12_walk_T.
Proof. intros AL IMG ALWF _ CS00 K00 CSx Kx EP EB ECAP ESZ LAWS. exact (b12_walk_AL AL IMG ALWF CS00 K00 CSx Kx EP EB ECAP ESZ LAWS). Qed.

End ARUN_1.
