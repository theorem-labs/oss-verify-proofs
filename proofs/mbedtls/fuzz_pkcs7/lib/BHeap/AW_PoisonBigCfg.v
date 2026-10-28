(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux SysStep ITree Nodes CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ASpin ASpinS AW_Unwind AW_MmapFixed AW_MmapDie AW_MmapFixedNR AW_Poison AKinv AJ AKinvS.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_PoisonBig.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AW_PoisonBigCfg () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Lists.ListDef.repeat"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "LinuxProcessSemantics.LinuxProcessSem.Run.apply_zeros"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.J"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Poison.poison_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_PoisonBig.rsmr_statics"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Stdlib.ZArith.BinInt.Z.modulo"; "ARUN_1.PoisonCfg.poison0_postS"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Poison.A_POISON"; "RocqVerifyHarness.AgentSubmission.BHeap.AKinv.kinv"; "Corelib.Init.Logic.or"; "ARUN_1.PoisonCfg.poison0_siteS"].

Section ARUN_1. Context {hAR : arun}.
#[using="Type"] Lemma cb_zeros_join3 : ltac2:(CDefT.buildp (gd_tbl_AW_PoisonBigCfg ()) "Pm,P,(0.&40.)(1.(0.&8.))PS,$2.PPB,$2.PPE,$2.Pk,$2.P,(3.R4.R3.)P,(3.R4.R3.)P,(3.R4.(4.R6.R3.))P,(5.$6.R8.R7.(7.$8.(9.(:.(;.R6.R7.))(<.(0.&8.)(=.&8.=)(:.(;.R6.R7.))))(>.$8.)))P,(5.$6.R9.R7.(7.$8.(9.(:.(;.R6.R7.))(<.(0.&8.)(=.&8.=)(:.(;.R6.R7.))))(>.$8.)))P,(5.$6.R:.R7.(7.$8.(9.(:.(;.(4.R9.R6.)R7.))(<.(0.&8.)(=.&8.=)(:.(;.(4.R9.R6.)R7.))))(>.$8.)))(5.$6.R;.R:.(7.$8.(9.(:.R7.)(<.(0.&8.)(=.&8.=)(:.R7.)))(>.$8.)))")
(* [comment removed for export] *).
Proof.
  intros m S PB PE k H1 H2 H3 RA RB RC.
  pose proof (cb_join m PB (PE - PB) (S + k - PE) _ _ RB ltac:(replace (PB + (PE - PB)) with PE by lia; exact RC) ltac:(lia) ltac:(lia)) as J2.
  rewrite <- repeat_app', <- Z2Nat.inj_add in J2 by lia.
  pose proof (cb_join m S (PB - S) (PE - PB + (S + k - PE)) _ _ RA ltac:(replace (S + (PB - S)) with PB by lia; exact J2) ltac:(lia) ltac:(lia)) as J1.
  rewrite <- repeat_app', <- Z2Nat.inj_add in J1 by lia.
  replace (PB - S + (PE - PB + (S + k - PE))) with k in J1 by lia. exact J1.
Qed.

#[using="Type"] Lemma firstn_repeat_le : forall (A : Type) (x : A) a b, (a <= b)%nat -> firstn a (repeat x b) = repeat x a.
Proof. induction a as [|a IH]; intros [|b] H; cbn; try reflexivity; try lia. f_equal. apply IH. lia. Qed.
#[using="Type"] Lemma skipn_repeat_sub : forall (A : Type) (x : A) a b, skipn a (repeat x b) = repeat x (b - a).
Proof. induction a as [|a IH]; intros [|b]; cbn; try reflexivity. apply IH. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cb_zeros_rezero : ltac2:(CDefT.buildp (gd_tbl_AW_PoisonBigCfg ()) "Pm,P,(0.&40.)(1.(0.&8.))PS,$2.Pk,$2.PPB,$2.PnZ,$2.P,(?.(3.=R2.)(10.R2.(11.+2.+40.)))P,(?.(3.=R2.)(10.R2.(11.+2.+40.)))P,(3.(4.R4.R3.)(11.+2.+40.))P,(3.R7.R5.)P,(3.(4.R6.R5.)(4.R8.R7.))P,(5.$6.R:.R9.(7.$8.(9.(:.R8.)(<.(0.&8.)(=.&8.=)(:.R8.)))(>.$8.)))(5.$6.(12.R;.(7.(13.(0.&40.)(0.&40.))(14.(0.&40.)(0.&40.)(15.R8.)(=.&40.R7.))(>.(13.(0.&40.)(0.&40.)))))R:.(7.$8.(9.(:.R9.)(<.(0.&8.)(=.&8.=)(:.R9.)))(>.$8.)))")
(* [comment removed for export] *).
Proof.
  intros m S k PB nZ Ha Hn Han H1 H2 SH.
  pose proof (firstn_repeat_le byte (Z_to_bv 8 0)) as FS. pose proof (skipn_repeat_sub byte (Z_to_bv 8 0)) as SK.
  destruct (AW_PoisonBig.cb_split m S k (PB - S) _ SH ltac:(lia)) as [RA R23].
  rewrite FS in RA by lia. rewrite SK in R23. replace (S + (PB - S)) with PB in R23 by lia.
  rewrite <- Z2Nat.inj_sub in R23 by lia.
  destruct (AW_PoisonBig.cb_split m PB (k - (PB - S)) nZ _ R23 ltac:(lia)) as [RB RC].
  rewrite SK in RC. rewrite <- Z2Nat.inj_sub in RC by lia.
  replace (k - (PB - S) - nZ) with (S + k - (PB + nZ)) in RC by lia.
  apply (cb_zeros_join3 _ S PB (PB + nZ) k); [lia| lia| lia| | |].
  - apply (rw_cells_zeros_other asegs m PB nZ Ha Hn Han _ _ RA). cbn. rewrite ?Nat.add_0_r. rewrite Z2Nat.id by lia. lia.
  - replace (PB + nZ - PB) with nZ by lia. exact (rw_cells_zeros_new asegs m PB nZ Ha Hn Han).
  - apply (rw_cells_zeros_other asegs m PB nZ Ha Hn Han _ _ RC). cbn. lia.
Qed.

Section PoisonCfg.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Hypothesis ASB : al_sb AL = 0x7fff8000.

  (* [comment removed for export] *)
  Definition poison0_postS (ra : word) (SP : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (S k lo : Z) (m0 : mem) (K : Model -> Prop) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_PoisonBigCfg ()) "Lc,$16.(17.$18.Lms',$18.(17.$19.Lmo',$19.(17.(0.&40.)Lt0,(0.&40.)(17.(0.&40.)Lt1,(0.&40.)(17.(0.&40.)Lt2,(0.&40.)(17.(0.&40.)La0,(0.&40.)(17.(0.&40.)La1,(0.&40.)(17.(0.&40.)La2,(0.&40.)(17.(0.&40.)La3,(0.&40.)(17.(0.&40.)La4,(0.&40.)(17.(0.&40.)La5,(0.&40.)(17.(0.&40.)La6,(0.&40.)(17.(0.&40.)La7,(0.&40.)(17.(0.&40.)Lt3,(0.&40.)(17.(0.&40.)Lt4,(0.&40.)(17.(0.&40.)Lt5,(0.&40.)(17.(0.&40.)Lt6,(0.&40.)(17.P,(0.&40.)(1.(0.&8.))Lmm,P,(0.&40.)(1.(0.&8.))(?.(1:.$16.R13.(1;.R12.R11.))(?.(1:.$18.R12.(1<.(1=.O17.(=.&40.O16.)O15.O14.R10.R?.R>.O13.O12.R=.R<.R;.R:.R9.R8.R7.R6.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.R5.R4.R3.R2.)O7.(1>.O17.)O6.(1?.(0.&40.))R1.(20.$6.)))(?.(21.(7.(13.$2.$2.)(14.$2.$2.O3.O16.)(7.(13.$2.$2.)(14.$2.$2.O5.(4.O5.O4.))(>.(13.$2.$2.))))O2.R1.)(?.(22.$6.O2.R1.)(?.(23.$6.R1.)(?.(5.$6.R1.O5.(7.$8.(9.(:.O4.)(<.(0.&8.)(=.&8.=)(:.O4.)))(>.$8.)))(?.(24.$6.R1.O3.O16.)(?.A1.O1.R11.(25.R1.R11.)))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Definition poison0_siteS (K : Model -> Prop) (A n : Z) (can : word) (dd madv : byte) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_PoisonBigCfg ()) "PQ,P,$16.SpPra,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PSP,$2.Plo,$2.PF,(26.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(1.(0.&8.))Pmo,$19.Pjunk,(27.(0.&8.))ZS,$2.(4.+7???8000.(28.O5.+8.))Zk,$2.(28.O4.+8.)P,(29.VCS,O5.O4.)P,(5.$6.R6.R3.(7.$8.(9.(:.R2.)R4.)(>.$8.)))P,(2:.R7.)P,(2;.R8.O3.O2.O1.)P,(24.$6.R9.R<.R=.)P,(3.(2<.VhAR,)R=.)P,(3.R>.(;.R?.+290.))P,(3.R10.(11.+2.+3>.))P,(1:.$2.(2=.R11.+10.)=)P,(29.VCS,R11.(;.R12.R11.))P,(23.$6.R?.)P,A1.O6.R?.P,(25.R11.R10.)P,Pc',$16.P,(2>.R32.R17.R31.R30.R2<.R2;.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R15.R14.R10.R?.R16.R13.O6.R1.)(2?.$6.R34.R2.)(2?.$6.R33.(1;.(1<.(1=.R32.(=.&40.R17.)R31.R30.R2?.R2>.R2=.R2<.R2;.(=.&40.O5.)(=.&40.O4.)(=.&40.=)R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.)R15.(=.&40.$30.)R14.(1?.(0.&40.))R13.(20.$6.))R12.))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK ASB"] Lemma poison0_S : ltac2:(CDefT.buildp (gd_tbl_AW_PoisonBigCfg ()) "PK,P,$19.SpPA,$2.Pn,$2.Pcan,(0.&40.)Pdd,(0.&8.)Pmadv,(0.&8.)P,(31.VhAR,VAL,VCS,R6.)P,(1:.$2.(2=.R6.+8.)=)P,(1:.$2.(2=.R6.+8.)=)P,(3.=R7.)P,(32.(?.(3.+8.R9.)(?.(3.R9.+7???7??8.)(3.(4.R9.R8.)+7???8000.)))(?.(3.+10007???8000.R9.)(?.(3.+10007???8008.(4.R9.R8.))(?.(3.R9.+7??????????8.)(3.(4.R9.R8.)+800000000000.)))))(33.R;.R:.R9.R8.R7.R6.)")
(* [comment removed for export] *).
  Proof.
    intros K A n can dd madv KL AAL NAL N0 RNG Q ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP lo F fc m mo junk S k
      ACS SH PS RS ST LOIMG SPL SPH SPA SCS MI HK HJ HS.
    eapply (evtA_aevtS_KJ AL CS K _ Q _ mo KL HK); [exact HJ| |].
    { eapply (poison_spec_any AL IMG ALWF CS CSOK ASB ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP A n 0 lo F fc m m [] junk);
        first [exact AAL | exact NAL | exact N0 | clear; lia | exact RNG | exact ACS | exact SH | exact PS | exact ST | exact LOIMG
              | clear -SPL; lia | clear -SPH; lia | exact SPA | exact SCS | apply munch_refl | apply wmono_refl | exact MI]. }
    cbn beta. intros ms1 mo1 PO HK1 MM1 HJ1.
    ddestruct PO as (x5 & x6 & x7 & xa0 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & x28 & x29 & x30 & x31 & mm & -> & MU & WM & MI1 & SHZ & ST1).
    apply HS. unfold poison0_postS. deexists 18. split; [reflexivity|]. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact SHZ|]. split; [exact ST1|]. split; [exact HK1| exact HJ1].
  Qed.

  (* [comment removed for export] *)
  
End PoisonCfg.

End ARUN_1.
