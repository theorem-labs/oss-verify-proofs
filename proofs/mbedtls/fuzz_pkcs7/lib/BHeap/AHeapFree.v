(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import BackingAlgebra.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModelX. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm AVst AW_Unwind2 HMLib HM HMFrame AHeapR AMallocPost AHeapMalloc AFreePost AJ AJTop.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AHeapFree () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hst"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.HM_i"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.HK_i"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_free"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.htop_i"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.havol_i"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_CALL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hstkhi_i"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hfr_i"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fr_charge"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.and"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.call_postA"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.lb_remove"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hflag_i"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hcs_i"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_free"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.

Section Fr.
  Variable STKLO : Z.
  Hypothesis STKLO_OK : ACEIL <= STKLO.
  Let R := R0 STKLO.
  Local Notation hok := (hok STKLO).
  Local Notation hst := (hst STKLO).
  Local Notation HMi := (HM_i STKLO).
  Local Notation HKi := (HK_i STKLO).
  Local Notation hcs := (hcs_i STKLO).

  Hypothesis FH : freeH_T STKLO.

  #[using="FH"] Theorem free_field : ltac2:(CDefT.buildp (gd_tbl_AHeapFree ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Ps,(4.VhAR,VSTKLO,)PLB,(5.$6.)PLF,(5.$6.)PA,$7.Pn,$7.Plo,$7.Pd,$7.P,(8.VhAR,VSTKLO,R7.R6.R5.R9.)P,(9.VhAR,VSTKLO,R8.R9.)P,(:.(;.$7.$7.)(<.$7.$7.R6.R5.)R8.)P,(=.$>.R<.R5.(?.&40.R2<.))P,(10.(11.VR,)R6.)P,(10.R7.(12.(?.&40.R2>.)(13.VR,)))P,(10.(?.&40.R2?.)(14.VhAR,VSTKLO,R=.))P,(15.$7.(16.(?.&40.R30.)+10.)=)P,(17.$>.R11.)P,(15.(0.&40.)R30.(18.&40.(19.VR,)))P,(15.(0.&40.)R2;.(18.&40.R>.))P,(10.(1:.(1;.VhAR,VSTKLO,R12.)$1<.)$1=.)P,(1>.$>.R15.(11.VR,)(1?.VhAR,VSTKLO,R13.)(?.&40.R2?.)(?.&40.R35.)R=.)P,(10.(1:.(20.VhAR,VSTKLO,R14.)(21.R>.))$22.)(23.$>.Lc,$24.(25.$26.Lms',$26.(25.$3.Lmo',$3.(27.(15.$24.R3.(28.R2.R1.))(29.$>.R3;.R3:.R39.R38.R34.R33.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R1<.R1;.L,(0.&40.)Lm',P,(0.&40.)(2.(0.&8.))(27.(17.$>.R1.)(27.(=.$>.R1.R15.(?.&40.R3<.))(27.(2:.R1;.R3.)(27.(2;.$>.VR,(2<.R17.R19.)R18.(?.&40.R3<.)(11.VR,)(1?.VhAR,VSTKLO,R1:.)(2=.$2>.)R1<.R1.)(25.(4.VhAR,VSTKLO,)Ls',(4.VhAR,VSTKLO,)(27.(15.$7.(14.VhAR,VSTKLO,R1.)(14.VhAR,VSTKLO,R1;.))(27.(15.$7.(1?.VhAR,VSTKLO,R1.)(1?.VhAR,VSTKLO,R1;.))(27.(15.$7.(2?.VhAR,VSTKLO,R1.)(2?.VhAR,VSTKLO,R1;.))(27.(9.VhAR,VSTKLO,R1.R4.)(27.Px,$7.P,(30.VhAR,VSTKLO,R1<.R1.)(30.VhAR,VSTKLO,R3.R2.)(27.(10.(1;.VhAR,VSTKLO,R1.)(1:.(1;.VhAR,VSTKLO,R1;.)$1<.))(27.(10.(20.VhAR,VSTKLO,R1.)(1:.(20.VhAR,VSTKLO,R1;.)(21.R15.)))(8.VhAR,VSTKLO,R1.(2<.R18.R1:.)R19.R2.)))))))))))))R2.))))(28.(31.(32.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.)R19.(18.&40.(33.VR,))R18.(34.(0.&40.))R17.(35.$>.))R16.))")
(* [comment removed for export] *).
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo [h HOK] LB LF A n lo d
      [HM0 [XR0 HA0]] [HK0 GX0] HIN ST LO SPL SPT SPA MI TP A0 BUD CH HFR.
    unfold HK_i, hcs_i, htop_i, hstkhi_i, hflag_i, havol_i, hfr_i in *. cbn [hh arl_stklo arl_free arl_tp arl_need_free R R0] in *.
    unfold ARt.AVOL_CALL, ARt.AVOL_MAX, FR_MAX, fr_charge in *.
    dpose HOK as (EL & AWF & VWF).
    pose proof (hm_J AL0 h m mo HK0 (awf'_bwf h AWF) HA0) as HJ0.   (* [comment removed for export] *)
    eapply aevtS_mono.
    { eapply (FH ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo h LB LF A n lo d HOK HM0 (proj2 (proj2 XR0)) HK0 HJ0 GX0 HIN ST LO SPL SPT SPA MI TP A0);
        [unfold AVOL_MAX; clear - BUD; lia| exact CH| unfold FR_MAXm; clear - HFR; lia]. }
    cbn beta. intros cf PO.
    ddestruct PO as (x5 & x6 & x7 & xa0 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & x28 & x29 & x30 & x31 & m' & mo' & h' & -> &
                    MI' & ST' & FR & HK' & HJ' & GX' & EL' & CSM & VOL & FRB & PRES & IK & HM' & RU').
    assert (HOK' : hok h').
    { split; [rewrite EL'; exact EL|]. split; [exact (proj1 (proj1 HM'))| exact (HK_vwf AL0 h' mo' HK')]. }
    pose proof (J_hm_absent AL0 h' m' mo' HK' (awf'_bwf h' (proj1 (proj1 HM'))) HJ') as HA'.   (* [comment removed for export] *)
    assert (ESP : Z_to_bv 64 (bv_unsigned sp) = sp) by apply Z_to_bv_bv_unsigned.
    deexists 2. split; [reflexivity|].
    unfold call_postA. dexists x5, x6, x7, xa0, xa1, xa2, xa3, xa4, xa5, xa6, xa7, x28, x29, x30, x31, m'.
    split; [rewrite ESP, TP; reflexivity|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact FR|].
    split; [exact PRES|].
    exists (HS STKLO h' HOK'). cbn [hh].
    split; [rewrite EL'; reflexivity|]. split; [rewrite EL'; reflexivity|]. split; [reflexivity|]. split; [exact (conj HK' GX')|].
    split; [exact CSM|].
    split; [clear - VOL; lia|]. split; [clear - FRB; lia|].
    exact (conj HM' (conj (XR_keep m m' XR0 IK) HA')).
  Qed.
End Fr.

End ARUN_1.
