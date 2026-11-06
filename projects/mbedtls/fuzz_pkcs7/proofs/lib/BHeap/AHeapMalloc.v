(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow. From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt. From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw ACnt24.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import BackingAlgebra.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModelX. From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AVmLib. From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm AVst AW_DepotB AW_DepotTop AW_MallocB AW_Populate HMLib HM HMFrame AHeapR AMallocPost AJ AJTop.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AHeapMalloc () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.BHeap.AMallocPost.img_keep"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.BHeap.HMFrame.in_rangesZ"; "OSSVerify.KrLib.BHeap.AMallocPost.awz"; "OSSVerify.KrLib.BHeap.HMLib.kept"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.BHeap.AModel.ahst"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "OSSVerify.KrLib.BHeap.AHeapR.hok"; "OSSVerify.KrLib.BHeap.HM.HMc"; "OSSVerify.KrLib.BHeap.AVst.HK"; "OSSVerify.KrLib.BHeap.AHeapR.AL0"; "OSSVerify.KrLib.BHeap.AJ.J"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.B.AImg.asegs"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.BHeap.AModel.l_htop"; "OSSVerify.KrLib.BHeap.AModel.h_L"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.BHeap.AModel.A_TP"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.BHeap.AModel.h_havol"; "OSSVerify.KrLib.LibB.ARt.vchg"; "OSSVerify.KrLib.LibA.AUnw.uwc"; "OSSVerify.KrLib.BHeap.AModel.l_stk_hi"; "OSSVerify.KrLib.BHeap.AModelX.hfr"; "OSSVerify.KrLib.BHeap.AModelX.FR_MAXm"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.LibA.ACnt24.win24"; "Corelib.Init.Datatypes.true"; "OSSVerify.KrLib.LibA.ACnt24.cnt24"; "OSSVerify.KrLib.LibA.ACnt24.C24MAX"; "OSSVerify.KrLib.LibA.AEvtS.aevtS"; "OSSVerify.KrLib.BHeap.AMallocPost.mallocH_post"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.BHeap.AHeapR.hst"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "OSSVerify.KrLib.BHeap.AHeapR.HM_i"; "OSSVerify.KrLib.BHeap.AHeapR.HK_i"; "OSSVerify.KrLib.LibB.ARt.arl_stklo"; "OSSVerify.KrLib.LibB.ARt.arl_need_malloc"; "OSSVerify.KrLib.BHeap.AHeapR.htop_i"; "OSSVerify.KrLib.LibB.ARt.arl_tp"; "OSSVerify.KrLib.LibB.ARt.AMAX"; "OSSVerify.KrLib.BHeap.AHeapR.havol_i"; "OSSVerify.KrLib.LibB.ARt.AVOL_MAX"; "OSSVerify.KrLib.BHeap.AHeapR.hstkhi_i"; "OSSVerify.KrLib.BHeap.AHeapR.hfr_i"; "OSSVerify.KrLib.LibB.ARt.fr_charge"; "OSSVerify.KrLib.LibB.ARt.FR_MAX"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "OSSVerify.KrLib.LibB.ARt.call_postA"; "OSSVerify.KrLib.Lib.HeapIface.mo_frame"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.LibB.ARt.presA"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.ivl"; "OSSVerify.KrLib.BHeap.AHeapR.hflag_i"; "OSSVerify.KrLib.BHeap.AHeapR.hcs_i"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.LibB.ARt.fresh_apart"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "OSSVerify.KrLib.LibB.ARt.arl_malloc"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma rtc_cells_off_awz : Forall (fun c : rtc_cell => let '(a, n, v) := c in let k := Z.of_nat (cells_size [rtc_mkcell n v]) in
                            0x10000 <= a /\ a + k <= 0x65f000 /\ forall x, a <= x < a + k -> ~ in_rangesZ awz x) rtc_cells.
Proof.
  unfold rtc_cells, awz, A_INSTANCE, A_IA, A_OOM, A_IA_INIT, A_SS, A_DEP_END, A_ERRNO, A_EMB.
  repeat (apply Forall_cons; [cbn; split; [lia| split; [lia| intros x Hx; cbn; lia]]|]). apply Forall_nil.
Qed.

#[using="Type"] Lemma rtc_pristine_off_awz : forall a, rtc_prist a -> 0x10000 <= a < 0x65f000 /\ ~ in_rangesZ awz a.
Proof.
  intros a H. unfold rtc_prist, rtc_pristine, AGLOB_LO, AGLOB_HI in H. unfold awz, A_INSTANCE, A_IA, A_OOM, A_IA_INIT, A_SS, A_DEP_END, A_ERRNO, A_EMB.
  repeat (apply Exists_cons in H; destruct H as [H|H]); [cbn in H ..| inversion H]; cbn; lia.
Qed.

#[using="Type"] Lemma img_keep_kept : ltac2:(CDefT.buildp (gd_tbl_AHeapMalloc ()) "Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))PA,$2.Pn,$2.P,(3.R4.R3.)P,(4.+10000.R3.)P,(4.(5.R4.R3.)+65?000.)P,Px,$2.P,(6.(4.R6.R1.)(7.R1.(5.R6.R5.)))(8.(9.$:.R2.))(;.R8.R7.R6.R5.)")
(* [comment removed for export] *).
Proof. intros m m' A n [K _] H0 H1 H2 x Hx. apply K; [lia| apply H2; exact Hx]. Qed.

#[using="Type"] Lemma XR_keep : forall m m', XR m -> img_keep m m' -> XR m'.
Proof.
  (intros m m' dd_H; ddestruct dd_H as ([RC RP] & SH & XF); intros IK). split; [split| split].
  - apply Forall_forall. intros [[a n] v] Hc. pose proof (proj1 (Forall_forall _ _) RC _ Hc) as H. cbn in H.
    pose proof (proj1 (Forall_forall _ _) rtc_cells_off_awz _ Hc) as (B0 & B1 & B2). cbn beta in B2.
    unfold rtc_holds. eapply keep_ro; [exact H|]. apply (img_keep_kept m m' a _ IK B0 B1 B2).
  - intros a Ha. destruct (rtc_pristine_off_awz a Ha) as [R1 R2]. destruct IK as [K _].
    unfold wa. rewrite (K (Z_to_bv 64 a)); [exact (RP a Ha)| rewrite u64_lit by lia; exact R1| rewrite u64_lit by lia; exact R2].
  - intros g Hg Hv. pose proof (SH g Hg Hv) as B. destruct IK as [_ K].
    unfold IMG_GLO, IMG_GHI, IMG_LO in Hg.
    ddestruct B as (B0 & B1 & B2). split; [exact B0|]. split; [exact B1|]. intros i Hi. cbn in Hi. assert (i = 0%nat) as -> by lia.
    specialize (B2 0%nat ltac:(cbn; lia)). cbn [nth_error] in B2 |- *. rewrite Z.add_0_r in B2 |- *. unfold mrd in B2 |- *.
    unfold shadow_of in *. cbn [al_sb AL0 ALazy.al_sb] in *.
    rewrite (K (wa (2147450880 + 8 * g / 8))); [exact B2|]. unfold wa. rewrite u64_lit by lia. rewrite Z.mul_comm, Z.div_mul by lia. lia.
  - unfold xf_cells in *. eapply keep_ro; [exact XF|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
    apply (img_keep_kept m m' _ _ IK); [unfold A_FLAGS; clear; lia| unfold A_FLAGS; clear; lia|].
    intros x Hx. unfold awz, A_FLAGS, A_INSTANCE, A_IA, A_OOM, A_IA_INIT, A_SS, A_DEP_END, A_ERRNO, A_EMB in *. cbn [in_rangesZ]. clear - Hx. lia.
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
  Definition mallocH_T : Prop := ltac2:(CDefT.buildp (gd_tbl_AHeapMalloc ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(<.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(1.(0.&8.))Pmo,$=.Ph,$>.PLB,(?.(10.$2.$2.))PLF,(?.(10.$2.$2.))Pn,$2.Plo,$2.Pd,$2.P,(11.VhAR,VSTKLO,R6.)P,(12.VhAR,R7.R6.R5.R9.)P,(13.VhAR,$14.R8.R9.)P,(15.R;.R:.)P,(16.$17.R<.R6.(18.&40.R2<.))P,(4.VSTKLO,R7.)P,(4.R8.(19.(18.&40.R2>.)+1000.))P,(4.(18.&40.R2?.)(1:.(1;.R=.)))P,(1<.$2.(1=.(18.&40.R30.)+10.)=)P,(1>.$17.R11.)P,(1<.(0.&40.)R30.(1?.&40.$20.))P,(1<.(0.&40.)R2;.(1?.&40.R>.))P,(6.(4.=R?.)(7.R?.(21.+2.+1<.)))P,(4.(5.(22.R13.)(23.R10.))(21.+2.+24.))P,(24.$17.R16.VSTKLO,(25.(1;.R14.))(18.&40.R30.)(18.&40.R36.)R?.)P,(4.(5.(26.R15.)(5.R10.+3.))$27.)P,P,(1<.$28.(29.R13.)$2:.)(7.(2;.R16.)$2<.)(2=.$17.(2>.VhAR,VSTKLO,R3:.R38.R33.R32.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1;.R1:.R17.R16.R15.R14.R13.R12.(18.&40.R39.)R19.R18.)(2?.(30.(31.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.)R1;.(1?.&40.+69480.)R1:.(32.(0.&40.))R19.(33.$17.))R18.))")
(* [comment removed for export] *).
  Hypothesis MH : mallocH_T.

  #[using="MH"] Theorem malloc_field : ltac2:(CDefT.buildp (gd_tbl_AHeapMalloc ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(<.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(1.(0.&8.))Pmo,$=.Ps,(34.VhAR,VSTKLO,)PLB,(?.$35.)PLF,(?.$35.)Pn,$2.Plo,$2.Pd,$2.P,(36.VhAR,VSTKLO,R6.R5.R4.R8.)P,(37.VhAR,VSTKLO,R7.R8.)P,(16.$17.R:.R4.(18.&40.R2:.))P,(4.(38.VR,)R5.)P,(4.R6.(19.(18.&40.R2<.)(39.VR,)))P,(4.(18.&40.R2=.)(3:.VhAR,VSTKLO,R;.))P,(1<.$2.(1=.(18.&40.R2>.)+10.)=)P,(1>.$17.R?.)P,(1<.(0.&40.)R2>.(1?.&40.(3;.VR,)))P,(1<.(0.&40.)R29.(1?.&40.R<.))P,(6.(4.=R=.)(7.R=.$3<.))P,(4.(5.(3=.VhAR,VSTKLO,R11.)(23.R>.))$3>.)P,(24.$17.R14.(38.VR,)(3?.VhAR,VSTKLO,R12.)(18.&40.R2>.)(18.&40.R34.)R=.)P,(4.(5.(40.VhAR,VSTKLO,R13.)(41.R>.))$42.)P,P,(1<.$28.(29.R11.)$2:.)(7.(2;.R14.)$2<.)(2=.$17.Lc,$43.(44.$45.Lms',$45.(44.$=.Lmo',$=.(6.(1<.$43.R3.(2?.R2.R1.))(46.$17.R3;.R3:.R39.R38.R34.R33.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R1<.R1;.Lr,(0.&40.)Lm',P,(0.&40.)(1.(0.&8.))(6.(1>.$17.R1.)(6.(16.$17.R1.R16.(18.&40.R3<.))(6.(47.R1;.R3.)(6.(48.$17.R1<.R1.)(6.(49.$17.VR,R19.R18.(18.&40.R3<.)(38.VR,)(3?.VhAR,VSTKLO,R1:.)(4:.$4;.)R1<.R1.)(44.(34.VhAR,VSTKLO,)Ls',(34.VhAR,VSTKLO,)(6.(1<.$2.(3:.VhAR,VSTKLO,R1.)(3:.VhAR,VSTKLO,R1;.))(6.(1<.$2.(3?.VhAR,VSTKLO,R1.)(3?.VhAR,VSTKLO,R1;.))(6.(1<.$2.(4<.VhAR,VSTKLO,R1.)(4<.VhAR,VSTKLO,R1;.))(6.(37.VhAR,VSTKLO,R1.R4.)(6.Px,$2.P,(4=.VhAR,VSTKLO,R1<.R1.)(4=.VhAR,VSTKLO,R3.R2.)(6.(4.(3=.VhAR,VSTKLO,R1.)(5.(3=.VhAR,VSTKLO,R1;.)(23.R18.)))(6.(4.(40.VhAR,VSTKLO,R1.)(5.(40.VhAR,VSTKLO,R1;.)(41.R16.)))(4>.(6.(1<.(0.&40.)R3.(1?.&40.=))(36.VhAR,VSTKLO,R1.R1:.R19.R2.))(44.$2.LA,$2.(44.(?.(0.&8.))Ljunk,(?.(0.&8.))(6.(1<.(0.&40.)R5.(1?.&40.R2.))(6.(1<.$2.(1=.R2.+10.)=)(6.(4?.VR,R1<.R1;.R2.R1:.)(6.(4>.(4.(5.R2.R1:.)(38.VR,))(4.(3?.VhAR,VSTKLO,R1=.)R2.))(6.(36.VhAR,VSTKLO,R3.(50.(10.$2.$2.)(51.$2.$2.R2.R1:.)R1<.)R1;.R4.)(52.$17.R4.R2.(50.$53.(54.(55.R1:.)R1.)(4:.$53.))))))))))))))))))))))))R2.))))(2?.(30.(31.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.)R19.(1?.&40.(56.VR,))R18.(32.(0.&40.))R17.(33.$17.))R16.))")
(* [comment removed for export] *).
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo [h HOK] LB LF n lo d
      [HM0 [XR0 HA0]] [HK0 GX0] ST LO SPL SPT SPA MI TP A0 NB BUD CH HFR XC.
    unfold HK_i, hcs_i, htop_i, hstkhi_i, hflag_i, havol_i, hfr_i in *. cbn [hh arl_stklo arl_malloc arl_tp arl_need_malloc R R0] in *.
    unfold ARt.AVOL_CALL, ARt.AVOL_MAX, AMAX, FR_MAX, fr_charge in *.
    dpose HOK as (EL & AWF & VWF).
    pose proof (hm_J AL0 h m mo HK0 (awf'_bwf h AWF) HA0) as HJ0.   (* [comment removed for export] *)
    eapply aevtS_mono.
    { eapply (MH ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo h LB LF n lo d HOK HM0 HK0 HJ0 ST LO SPL SPT SPA MI TP A0);
        [clear - NB; lia| clear - BUD; lia| exact CH| unfold FR_MAXm; clear - HFR; lia| exact XC]. }
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
    destruct ARM as [[-> HM']|(A16 & FA & HI & HM' & junk & JK)].
    - left. split; [reflexivity| exact (conj HM' (conj XR' HA'))].
    - right. dexists res, junk. split; [reflexivity|]. split; [exact A16|]. split; [exact FA|]. split; [exact HI|].
      split; [exact (conj HM' (conj XR' HA'))| exact JK].
  Qed.
End M.

End ARUN_1.
