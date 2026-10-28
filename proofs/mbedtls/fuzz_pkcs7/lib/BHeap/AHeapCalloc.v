(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX HeapIface ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw ACnt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import BackingAlgebra.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModelX. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm AVst AW_DepotB AW_DepotTop AW_MallocB HMLib HM HMFrame AHeapR AMallocPost AHeapMalloc ACallocPost AJ AJTop.
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
Local Ltac Stdlib.micromega.Lia.nia ::= nia_ah.
Ltac2 gd_tbl_AHeapCalloc () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hok"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.HMc"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.HK"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.AL0"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.J"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_htop"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_TP"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.vchg"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_stk_hi"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.hfr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.FR_MAXm"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.win24"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.cnt24"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.C24MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "RocqVerifyHarness.AgentSubmission.BHeap.ACallocPost.callocH_post"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.BHeap.ACallocPost.A_WRAP_CALLOC"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hst"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.HM_i"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.HK_i"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_malloc"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.htop_i"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AMAX"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.havol_i"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hstkhi_i"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hfr_i"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fr_charge"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.call_postA"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hflag_i"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hcs_i"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_calloc"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.

(* [comment removed for export] *)
#[using="Type"] Lemma calloc_args_norm : ltac2:(CDefT.buildp (gd_tbl_AHeapCalloc ()) "Pcnt,$0.Psz,$0.P,(1.=R2.)P,(1.=R2.)P,(2.(3.R4.R3.)(4.+2.+1<.))(5.(5.(1.=(6.R5.(4.+2.+40.)))(2.(6.R5.(4.+2.+40.))(4.+2.+40.)))(5.(5.(1.=(6.R4.(4.+2.+40.)))(2.(6.R4.(4.+2.+40.))(4.+2.+40.)))(7.$0.(3.R5.R4.)(3.(6.R5.(4.+2.+40.))(6.R4.(4.+2.+40.))))))")
(* [comment removed for export] *).
Proof.
  intros cnt sz Hc Hs Hp.
  split; [apply Z.mod_pos_bound; lia|]. split; [apply Z.mod_pos_bound; lia|].
  destruct (Z_lt_ge_dec cnt (2^64)) as [Lc|Gc].
  - rewrite (Z.mod_small cnt) by lia. destruct (Z_lt_ge_dec sz (2^64)) as [Ls|Gs]; [rewrite (Z.mod_small sz) by lia; reflexivity|].
    destruct (Z.eq_dec cnt 0) as [->|NE]; [lia|]. exfalso. assert (1 * sz <= cnt * sz) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
  - destruct (Z.eq_dec sz 0) as [->|NE]; [rewrite Z.mul_0_r, Zmod_0_l, Z.mul_0_r; reflexivity|].
    exfalso. assert (cnt * 1 <= cnt * sz) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section M.
  Variable STKLO : Z.
  Hypothesis STKLO_OK : ACEIL <= STKLO.
  Let R := R0 STKLO.
  Local Notation hok := (hok STKLO).
  Local Notation hst := (hst STKLO).
  Local Notation HMi := (HM_i STKLO).
  Local Notation HKi := (HK_i STKLO).
  Local Notation hcs := (hcs_i STKLO).

  (* [comment removed for export] *)
  Definition callocH_T : Prop := ltac2:(CDefT.buildp (gd_tbl_AHeapCalloc ()) "Pra,(8.&40.)Psp,(8.&40.)Pgp,(8.&40.)Ptp,(8.&40.)Pt0,(8.&40.)Pt1,(8.&40.)Pt2,(8.&40.)Ps0,(8.&40.)Ps1,(8.&40.)Pa0,(8.&40.)Pa1,(8.&40.)Pa2,(8.&40.)Pa3,(8.&40.)Pa4,(8.&40.)Pa5,(8.&40.)Pa6,(8.&40.)Pa7,(8.&40.)Ps2,(8.&40.)Ps3,(8.&40.)Ps4,(8.&40.)Ps5,(8.&40.)Ps6,(8.&40.)Ps7,(8.&40.)Ps8,(8.&40.)Ps9,(8.&40.)Ps10,(8.&40.)Ps11,(8.&40.)Pt3,(8.&40.)Pt4,(8.&40.)Pt5,(8.&40.)Pt6,(8.&40.)PF,(9.&5.(8.&40.))Pfc,(8.&20.)Pm,P,(8.&40.)(:.(8.&8.))Pmo,$;.Ph,$<.PLB,(=.(>.$0.$0.))PLF,(=.(>.$0.$0.))Pn,$0.Pcnt0,$0.Psz0,$0.Plo,$0.Pd,$0.P,(?.VhAR,VSTKLO,R8.)P,(10.VhAR,R9.R8.R7.R;.)P,(11.VhAR,$12.R:.R;.)P,(13.R=.R<.)P,(14.$15.R>.R6.(16.&40.R2>.))P,(1.VSTKLO,R7.)P,(1.R8.(17.(16.&40.R30.)+1000.))P,(1.(16.&40.R31.)(18.(19.R?.)))P,(7.$0.(6.(16.&40.R32.)+10.)=)P,(1:.$15.R13.)P,(7.(8.&40.)R32.(1;.&40.$1<.))P,(7.(8.&40.)R2=.(1;.&40.R?.))P,(7.(8.&40.)R2=.(1;.&40.R?.))P,(5.(1.=R11.)(2.R11.(4.+2.+40.)))P,(5.(1.=R11.)(2.R11.(4.+2.+40.)))P,(7.$0.R14.(3.R13.R12.))P,(5.(1.=R15.)(2.R15.(4.+2.+1<.)))P,(1.(1=.(1>.R19.)(1?.R16.))(4.+2.+24.))P,(20.$15.R1<.VSTKLO,(21.(19.R1:.))(16.&40.R36.)(16.&40.R3<.)R13.)P,(1.(1=.(22.R1;.)(1=.R14.+3.))$23.)P,P,(7.$24.(25.R19.)$26.)(2.(27.R1<.)$28.)(29.$15.(2:.VhAR,VSTKLO,R40.R3>.R39.R38.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R21.R20.R1=.R1<.R1;.R1:.R17.R16.(16.&40.R3?.)R1?.R1>.)(2;.(2<.(2=.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.)R21.(1;.&40.$2>.)R20.(2?.(8.&40.))R1?.(30.$15.))R1>.))")
(* [comment removed for export] *).
  Hypothesis CH : callocH_T.

  #[using="CH"] Theorem calloc_field : ltac2:(CDefT.buildp (gd_tbl_AHeapCalloc ()) "Pra,(8.&40.)Psp,(8.&40.)Pgp,(8.&40.)Ptp,(8.&40.)Pt0,(8.&40.)Pt1,(8.&40.)Pt2,(8.&40.)Ps0,(8.&40.)Ps1,(8.&40.)Pa0,(8.&40.)Pa1,(8.&40.)Pa2,(8.&40.)Pa3,(8.&40.)Pa4,(8.&40.)Pa5,(8.&40.)Pa6,(8.&40.)Pa7,(8.&40.)Ps2,(8.&40.)Ps3,(8.&40.)Ps4,(8.&40.)Ps5,(8.&40.)Ps6,(8.&40.)Ps7,(8.&40.)Ps8,(8.&40.)Ps9,(8.&40.)Ps10,(8.&40.)Ps11,(8.&40.)Pt3,(8.&40.)Pt4,(8.&40.)Pt5,(8.&40.)Pt6,(8.&40.)PF,(9.&5.(8.&40.))Pfc,(8.&20.)Pm,P,(8.&40.)(:.(8.&8.))Pmo,$;.Ps,(31.VhAR,VSTKLO,)PLB,(=.$32.)PLF,(=.$32.)Pcnt,$0.Psz,$0.Plo,$0.Pd,$0.P,(33.VhAR,VSTKLO,R7.R6.R5.R9.)P,(34.VhAR,VSTKLO,R8.R9.)P,(14.$15.R;.R4.(16.&40.R2;.))P,(1.(35.VR,)R5.)P,(1.R6.(17.(16.&40.R2=.)(36.VR,)))P,(1.(16.&40.R2>.)(37.VhAR,VSTKLO,R<.))P,(7.$0.(6.(16.&40.R2?.)+10.)=)P,(1:.$15.R10.)P,(7.(8.&40.)R2?.(1;.&40.(38.VR,)))P,(7.(8.&40.)R2:.(1;.&40.R=.))P,(7.(8.&40.)R2:.(1;.&40.R=.))P,(1.=R?.)P,(1.=R?.)P,(2.(3.R11.R10.)$39.)P,(1.(1=.(3:.VhAR,VSTKLO,R15.)(1?.(3.R12.R11.)))$3;.)P,(20.$15.R18.(35.VR,)(3<.VhAR,VSTKLO,R16.)(16.&40.R32.)(16.&40.R38.)R10.)P,(1.(1=.(3=.VhAR,VSTKLO,R17.)(3>.R11.))$3?.)P,P,(7.$24.(25.(3.R15.R14.))$26.)(2.(27.R18.)$28.)(29.$15.Lc,$40.(41.$42.Lms',$42.(41.$;.Lmo',$;.(5.(7.$40.R3.(2;.R2.R1.))(43.$15.R3?.R3>.R3=.R3<.R38.R37.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R20.R1?.Lr,(8.&40.)Lm',P,(8.&40.)(:.(8.&8.))(5.(1:.$15.R1.)(5.(14.$15.R1.R19.(16.&40.R40.))(5.(44.R1?.R3.)(5.(45.$15.R20.R1.)(5.(46.$15.VR,R1=.R1<.(16.&40.R40.)(35.VR,)(3<.VhAR,VSTKLO,R1>.)(47.$48.)R20.R1.)(41.(31.VhAR,VSTKLO,)Ls',(31.VhAR,VSTKLO,)(5.(7.$0.(37.VhAR,VSTKLO,R1.)(37.VhAR,VSTKLO,R1?.))(5.(7.$0.(3<.VhAR,VSTKLO,R1.)(3<.VhAR,VSTKLO,R1?.))(5.(7.$0.(49.VhAR,VSTKLO,R1.)(49.VhAR,VSTKLO,R1?.))(5.(34.VhAR,VSTKLO,R1.R4.)(5.Px,$0.P,(4:.VhAR,VSTKLO,R20.R1.)(4:.VhAR,VSTKLO,R3.R2.)(5.(1.(3:.VhAR,VSTKLO,R1.)(1=.(3:.VhAR,VSTKLO,R1?.)(1?.(3.R1<.R1;.))))(5.(1.(3=.VhAR,VSTKLO,R1.)(1=.(3=.VhAR,VSTKLO,R1?.)(3>.R19.)))(4;.(5.(7.(8.&40.)R3.(1;.&40.=))(33.VhAR,VSTKLO,R1.R1>.R1=.R2.))(41.$0.LA,$0.(5.(7.(8.&40.)R4.(1;.&40.R1.))(5.(7.$0.(6.R1.+10.)=)(5.(4<.VR,R1?.R1>.R1.(3.R1=.R1<.))(5.(4;.(1.(1=.R1.(3.R1=.R1<.))(35.VR,))(1.(3<.VhAR,VSTKLO,R20.)R1.))(5.(33.VhAR,VSTKLO,R2.(4=.(>.$0.$0.)(4>.$0.$0.R1.(3.R1=.R1<.))R1?.)R1>.R3.)(4?.$15.R3.R1.(4=.$50.(51.(52.(3.R1=.R1<.))(53.(8.&8.)(1;.&8.=)(52.(3.R1=.R1<.))))(47.$50.)))))))))))))))))))))))R2.))))(2;.(2<.(2=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.)R1=.(1;.&40.(54.VR,))R1<.(2?.(8.&40.))R1;.(30.$15.))R1:.))")
(* [comment removed for export] *).
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo [h HOK] LB LF cnt sz lo d
      [HM0 [XR0 HA0]] [HK0 GX0] ST LO SPL SPT SPA MI TP A0 A1 C0 S0 NB BUD CH0 HFR XC.
    unfold HK_i, hcs_i, htop_i, hstkhi_i, hflag_i, havol_i, hfr_i in *. cbn [hh arl_stklo arl_calloc arl_tp arl_need_malloc R R0] in *.
    unfold ARt.AVOL_CALL, ARt.AVOL_MAX, AMAX, FR_MAX, fr_charge in *.
    dpose HOK as (EL & AWF & VWF).
    pose proof (hm_J AL0 h m mo HK0 (awf'_bwf h AWF) HA0) as HJ0.   (* [comment removed for export] *)
    ddestruct (calloc_args_norm cnt sz C0 S0 NB) as (CB0 & SZ0 & EN0).
    assert (A0' : a0 = Z_to_bv 64 (cnt mod 2^64)) by (rewrite A0; symmetry; apply Z_to_bv_mod64).
    assert (A1' : a1 = Z_to_bv 64 (sz mod 2^64)) by (rewrite A1; symmetry; apply Z_to_bv_mod64).
    set (n := cnt * sz) in *.
    assert (NB' : 0 <= n < 2^28) by (subst n; clear - NB C0 S0; nia).
    eapply aevtS_mono.
    { change 0x69484 with A_WRAP_CALLOC.
      eapply (CH ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo h LB LF n (cnt mod 2^64) (sz mod 2^64) lo d
                 HOK HM0 HK0 HJ0 ST LO SPL SPT SPA MI TP A0' A1' CB0 SZ0 EN0 NB');
        [clear - BUD; lia| exact CH0| unfold FR_MAXm; clear - HFR; lia| exact XC]. }
    cbn beta. intros cf PO.
    ddestruct PO as (x5 & x6 & x7 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & x28 & x29 & x30 & x31 & m' & mo' & h' & res & -> &
                    MI' & ST' & FR & WM & HK' & HJ' & EL' & GH' & VOL & FRB & CSM & PRES & IK & ARM).
    assert (AWF' : awf' h') by (destruct ARM as [[_ HM']|(_ & _ & _ & HM' & _)]; exact (proj1 (proj1 HM'))).
    assert (HOK' : hok h').
    { split; [rewrite EL'; exact EL|]. split; [exact AWF'| exact (HK_vwf AL0 h' mo' HK')]. }
    pose proof (J_hm_absent AL0 h' m' mo' HK' (awf'_bwf h' AWF') HJ') as HA'.   (* [comment removed for export] *)
    assert (ESP : Z_to_bv 64 (bv_unsigned sp) = sp) by apply Z_to_bv_bv_unsigned.
    deexists 2. split; [reflexivity|].
    unfold call_postA. dexists x5, x6, x7, (Z_to_bv 64 res), xa1, xa2, xa3, xa4, xa5, xa6, xa7, x28, x29, x30, x31, m'.
    split; [rewrite ESP, TP; reflexivity|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact FR|]. split; [exact WM|].
    split; [exact PRES|].
    exists (HS STKLO h' HOK'). cbn [hh].
    split; [rewrite EL'; reflexivity|]. split; [rewrite EL'; reflexivity|]. split; [reflexivity|]. split; [split; [exact HK'| unfold gxok in *; rewrite GH', EL'; exact GX0]|].
    split. { intros x [Hx|Hx]; [left; exact (CSM x Hx)| right]. unfold in_ghost in *. rewrite GH'. exact Hx. }
    split; [clear - VOL; lia|]. split; [clear - FRB; lia|].
    pose proof (XR_keep m m' XR0 IK) as XR'.
    destruct ARM as [[-> HM']|(A16 & FA & HI & HM' & ZK)].
    - left. split; [reflexivity| exact (conj HM' (conj XR' HA'))].
    - right. exists res. split; [reflexivity|]. split; [exact A16|]. split; [exact FA|]. split; [exact HI|].
      split; [exact (conj HM' (conj XR' HA'))| exact ZK].
  Qed.
End M.

End ARUN_1.
