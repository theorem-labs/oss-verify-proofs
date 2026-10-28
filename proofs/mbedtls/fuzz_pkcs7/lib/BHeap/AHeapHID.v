(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Mem MState Arr Asn1Aux CellsX HeapIface Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw SRz. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARtDrv. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import BackingAlgebra.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_exit_lib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModelX APop. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AFreeSlot AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm AVst HMLib HM HMFrame
     AHeapL0 AW_FakeDefs AW_FakeRep AHeapR AHeapK AHeapB AHeapZ AHeapZW AHeapM AHeapL AMallocPost AHeapMalloc AFreePost AHeapFree AHeapFreeNull AW_Populate AHeapMallocH
     AW_MmapDie AW_MapOrDie AW_MallocSecS AHeapMallocS ACallocPost AHeapCalloc AHeapCallocH AW_MallocGenLib AW_ClassId AHeapHIA
     AMallocSplitPost AW_LargeSplit AW_MallocSecSplit ARoomL AInstSecRoom AHit AHeapMallocSSplit
     AHeapMallocPSplit AHeapMallocPISplit AJ AJTop.
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
Ltac2 gd_tbl_AHeapHID () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.TSet"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_malloc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AMAX"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AMAX_SEC"; "ARUN_1.HID.hfresh_i"; "ARUN_1.HID.pclass_i"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_CALL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibB.ARtDrv.AVOL_SPLIT"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fr_charge"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.win24"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.cnt24"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.C24MAX"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.LibA.SRz.srealizesJ"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_malloc"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_alt2"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_free"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.call_postA"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.lb_remove"; "RocqVerifyHarness.AgentSubmission.LibB.ARtDrv.KBATCH"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_free"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_mapped_user"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_reg"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hh"; "RocqVerifyHarness.AgentSubmission.LibB.ARtDrv.hfresh"; "ARUN_1.HID.artD_i"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.

(* [comment removed for export] *)
#[using="Type"] Lemma wr_at_mapped : forall m A n lo hi, wr_at asegs m A n -> 0x65f000 <= A -> A <= lo -> hi <= A + n -> mapped m lo hi.
Proof.
  (intros m A n lo hi dd_H; ddestruct dd_H as (W0 & W1 & W); intros HA Hlo Hhi x Hx).
  specialize (W (x - A) ltac:(lia)). replace (A + (x - A)) with x in W by lia.
  unfold wview in W. destruct (m (wa x)) as [b|] eqn:E; [exists b; reflexivity|].
  exfalso. rewrite wa_unsigned in W by lia. rewrite (asegs_none x 1) in W by lia. apply W. reflexivity.
Qed.

Section HID.
  Variable STKLO : Z.
  Hypothesis STKLO_OK : ACEIL <= STKLO.
  Hypothesis B12 : b12_T.
  Hypothesis MOD_DIE : mod_die_T.
  Hypothesis FH : freeH_T STKLO.
  Let R := R0 STKLO.
  Let HIA : artA asegs R := artA_i STKLO STKLO_OK B12 MOD_DIE FH.

  (* [comment removed for export] *)
  Definition hfresh_i (s : ARt.HST asegs R HIA) (c : Z) : Prop := r_mapped_user (h_reg (hh STKLO s) c) = 0.
  Definition pclass_i (n : Z) : Z := pclass n.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition malloc_split_T : Prop := ltac2:(CDefT.buildp (gd_tbl_AHeapHID ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Ph,(4.$5.VR,VHIA,)PLB,(6.$7.)PLF,(6.$7.)Pn,$8.Plo,$8.Pd,$8.PA,$9.PB,$9.P,(:.$5.VR,VHIA,R8.R7.R6.R:.)P,(;.$5.VR,VHIA,R9.R:.)P,(<.$5.R<.R6.(=.&40.R2<.))P,(>.(?.VR,)R7.)P,(>.R8.(10.(=.&40.R2>.)(11.VR,)))P,(>.(=.&40.R2?.)(12.$5.VR,VHIA,R=.))P,(13.$8.(14.(=.&40.R30.)+10.)=)P,(15.$5.R11.)P,(13.(0.&40.)R30.(16.&40.(17.VR,)))P,(13.(0.&40.)R2;.(16.&40.R>.))P,(18.(>.=R?.)(19.R?.$1:.))P,(1;.(>.$1<.R10.)(1=.R13.(1>.R10.)))P,(>.(1?.(20.$5.VR,VHIA,R14.)(1?.(21.+2.R11.)$22.))$23.)P,(>.(1?.(20.$5.VR,VHIA,R15.)(1?.(21.+2.R12.)$22.))$24.)P,(25.$5.R18.(?.VR,)(26.$5.VR,VHIA,R16.)(=.&40.R32.)(=.&40.R38.)R11.)P,(>.(1?.(27.$5.VR,VHIA,R17.)(28.R12.))$29.)P,P,(13.$2:.(2;.R15.)$2<.)(19.(2=.R18.)$2>.)P,A1.R13.(2?.$30.)P,A1.R13.(2?.$30.)P,Pt0',(0.&40.)Pt1',(0.&40.)Pt2',(0.&40.)Pa1',(0.&40.)Pa2',(0.&40.)Pa3',(0.&40.)Pa4',(0.&40.)Pa5',(0.&40.)Pa6',(0.&40.)Pa7',(0.&40.)Pt3',(0.&40.)Pt4',(0.&40.)Pt5',(0.&40.)Pt6',(0.&40.)Pm',P,(0.&40.)(2.(0.&8.))Pmo',$3.Ph',(4.$5.VR,VHIA,)P,(15.$5.R3.)P,(<.$5.R4.R29.(=.&40.R4?.))P,(31.R2?.R4.)P,(32.$5.R31.R6.)P,(33.$5.VR,R2?.R2>.(=.&40.R52.)(?.VR,)(26.$5.VR,VHIA,R30.)(2?.$34.)R32.R7.)P,(13.$8.(12.$5.VR,VHIA,R6.)(12.$5.VR,VHIA,R31.))P,(13.$8.(26.$5.VR,VHIA,R7.)(26.$5.VR,VHIA,R32.))P,(13.$8.(35.$5.VR,VHIA,R8.)(35.$5.VR,VHIA,R33.))P,(;.$5.VR,VHIA,R9.R:.)P,Px,$8.P,(36.$5.VR,VHIA,R36.R1.)(36.$5.VR,VHIA,R<.R2.)P,(>.(20.$5.VR,VHIA,R;.)(1?.(20.$5.VR,VHIA,R36.)(1?.(21.+2.R33.)$22.)))P,(>.(27.$5.VR,VHIA,R<.)(1?.(27.$5.VR,VHIA,R37.)(28.R32.)))P,Pc,$8.P,(1;.(>.$1<.R36.)(37.(13.$8.R1.(1>.R36.))))P,(1=.R3:.R2.)(1=.R10.R3.)P,(:.$5.VR,VHIA,R>.R38.R37.R10.)(38.$5.(39.(3:.(3;.R5=.R5<.R5;.R5:.R1?.R1>.R1=.R56.R55.(16.&40.=)R1<.R1;.R1:.R19.R18.R17.R16.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R15.R14.R13.R12.)R3>.(3<.R5=.)R3=.(3=.(0.&40.))R11.(3>.$5.))R10.)R34.)P,Pt0',(0.&40.)Pt1',(0.&40.)Pt2',(0.&40.)Pa1',(0.&40.)Pa2',(0.&40.)Pa3',(0.&40.)Pa4',(0.&40.)Pa5',(0.&40.)Pa6',(0.&40.)Pa7',(0.&40.)Pt3',(0.&40.)Pt4',(0.&40.)Pt5',(0.&40.)Pt6',(0.&40.)Pm',P,(0.&40.)(2.(0.&8.))Pmo',$3.Ph',(4.$5.VR,VHIA,)PAb,$8.Pjunk,(6.(0.&8.))P,(15.$5.R5.)P,(<.$5.R6.R2<.(=.&40.R52.))P,(31.R32.R6.)P,(32.$5.R34.R8.)P,(33.$5.VR,R32.R31.(=.&40.R55.)(?.VR,)(26.$5.VR,VHIA,R33.)(2?.$34.)R35.R9.)P,(13.$8.(12.$5.VR,VHIA,R8.)(12.$5.VR,VHIA,R34.))P,(13.$8.(26.$5.VR,VHIA,R9.)(26.$5.VR,VHIA,R35.))P,(13.$8.(35.$5.VR,VHIA,R:.)(35.$5.VR,VHIA,R36.))P,(;.$5.VR,VHIA,R;.R<.)P,Px,$8.P,(36.$5.VR,VHIA,R39.R1.)(36.$5.VR,VHIA,R>.R2.)P,(>.(20.$5.VR,VHIA,R=.)(1?.(20.$5.VR,VHIA,R39.)(1?.(21.+2.R36.)$22.)))P,(>.(27.$5.VR,VHIA,R>.)(1?.(27.$5.VR,VHIA,R3:.)(28.R35.)))P,Pc,$8.P,(1;.(>.$1<.R39.)(37.(13.$8.R1.(1>.R39.))))P,(1=.R3=.R2.)(1=.R12.R3.)P,(13.$8.(14.R?.+10.)=)P,(3?.VR,R3<.R3;.R10.R3:.)P,(1;.(>.(1?.R11.R3;.)(?.VR,))(>.(26.$5.VR,VHIA,R3>.)R11.))P,(:.$5.VR,VHIA,R13.(40.(41.$8.$8.)(42.$8.$8.R12.R3<.)R3>.)R3=.R15.)P,(43.$5.R16.R13.(40.$44.(45.(46.R3=.)R12.)(2?.$44.)))(38.$5.(39.(3:.(3;.R64.R63.R62.R61.R25.R24.R23.R5=.R5<.(16.&40.R14.)R22.R21.R20.R1?.R1>.R1=.R1<.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R1;.R1:.R19.R18.)R45.(3<.R64.)R44.(3=.(0.&40.))R17.(3>.$5.))R16.)R3:.)(38.$5.(39.(3:.(3;.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.)R21.(16.&40.(47.VR,))R20.(3=.(0.&40.))R1?.(3>.$5.))R1>.)(48.R17.R16.))")
(* [comment removed for export] *).

  Definition freeD_T : Prop := ltac2:(CDefT.buildp (gd_tbl_AHeapHID ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Ph,(4.$5.VR,VHIA,)PLB,(6.$7.)PLF,(6.$7.)PA,$8.Pn,$8.Plo,$8.Pd,$8.P,(:.$5.VR,VHIA,R7.R6.R5.R9.)P,(;.$5.VR,VHIA,R8.R9.)P,(49.(41.$8.$8.)(42.$8.$8.R6.R5.)R8.)P,(<.$5.R<.R5.(=.&40.R2<.))P,(>.(?.VR,)R6.)P,(>.R7.(10.(=.&40.R2>.)(4:.VR,)))P,(>.(=.&40.R2?.)(12.$5.VR,VHIA,R=.))P,(13.$8.(14.(=.&40.R30.)+10.)=)P,(15.$5.R11.)P,(13.(0.&40.)R30.(16.&40.(17.VR,)))P,(13.(0.&40.)R2;.(16.&40.R>.))P,(>.(1?.(20.$5.VR,VHIA,R12.)$22.)$23.)P,(25.$5.R15.(?.VR,)(26.$5.VR,VHIA,R13.)(=.&40.R2?.)(=.&40.R35.)R=.)P,(>.(1?.(27.$5.VR,VHIA,R14.)(28.R>.))$29.)(4;.$5.Lc,$4<.(4=.$4>.Lms',$4>.(4=.$3.Lmo',$3.(18.(13.$4<.R3.(39.R2.R1.))(4?.$5.R3;.R3:.R39.R38.R34.R33.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R1<.R1;.L,(0.&40.)Lm',P,(0.&40.)(2.(0.&8.))(18.(15.$5.R1.)(18.(<.$5.R1.R15.(=.&40.R3<.))(18.(31.R1;.R3.)(18.(33.$5.VR,(50.R17.R19.)R18.(=.&40.R3<.)(?.VR,)(26.$5.VR,VHIA,R1:.)(2?.$34.)R1<.R1.)(4=.(4.$5.VR,VHIA,)Lh',(4.$5.VR,VHIA,)(18.(13.$8.(12.$5.VR,VHIA,R1.)(12.$5.VR,VHIA,R1;.))(18.(13.$8.(26.$5.VR,VHIA,R1.)(26.$5.VR,VHIA,R1;.))(18.(13.$8.(35.$5.VR,VHIA,R1.)(35.$5.VR,VHIA,R1;.))(18.(;.$5.VR,VHIA,R1.R4.)(18.Px,$8.P,(36.$5.VR,VHIA,R1<.R1.)(36.$5.VR,VHIA,R3.R2.)(18.(>.(20.$5.VR,VHIA,R1.)(1?.(20.$5.VR,VHIA,R1;.)$22.))(18.(>.(27.$5.VR,VHIA,R1.)(1?.(27.$5.VR,VHIA,R1;.)(28.R15.)))(18.Pc,$8.P,(37.(13.$8.R1.$51.))P,(1=.R1=.R2.)(1=.R4.R3.)(:.$5.VR,VHIA,R1.(50.R18.R1:.)R19.R2.))))))))))))))R2.))))(39.(3:.(3;.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.)R19.(16.&40.(52.VR,))R18.(3=.(0.&40.))R17.(3>.$5.))R16.))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition malloc_split_primT : Prop := ltac2:(CDefT.buildp (gd_tbl_AHeapHID ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Ph,(4.$5.VR,VHIA,)PLB,(6.$7.)PLF,(6.$7.)Pn,$8.Plo,$8.Pd,$8.PA,$9.PB,$9.P,(:.$5.VR,VHIA,R8.R7.R6.R:.)P,(;.$5.VR,VHIA,R9.R:.)P,(<.$5.R<.R6.(=.&40.R2<.))P,(>.(?.VR,)R7.)P,(>.R8.(10.(=.&40.R2>.)(11.VR,)))P,(>.(=.&40.R2?.)(12.$5.VR,VHIA,R=.))P,(13.$8.(14.(=.&40.R30.)+10.)=)P,(15.$5.R11.)P,(13.(0.&40.)R30.(16.&40.(17.VR,)))P,(13.(0.&40.)R2;.(16.&40.R>.))P,(18.(>.=R?.)(19.R?.$1<.))P,(1=.R13.(1>.R10.))P,(>.(1?.(20.$5.VR,VHIA,R14.)(1?.(21.+2.R11.)$22.))$23.)P,(>.(1?.(20.$5.VR,VHIA,R15.)(1?.(21.+2.R12.)$22.))$24.)P,(25.$5.R18.(?.VR,)(26.$5.VR,VHIA,R16.)(=.&40.R32.)(=.&40.R38.)R11.)P,(>.(1?.(27.$5.VR,VHIA,R17.)(28.R12.))$29.)P,P,(13.$2:.(2;.R15.)$2<.)(19.(2=.R18.)$2>.)P,A1.R13.(2?.$30.)P,A1.R13.(2?.$30.)P,Pt0',(0.&40.)Pt1',(0.&40.)Pt2',(0.&40.)Pa1',(0.&40.)Pa2',(0.&40.)Pa3',(0.&40.)Pa4',(0.&40.)Pa5',(0.&40.)Pa6',(0.&40.)Pa7',(0.&40.)Pt3',(0.&40.)Pt4',(0.&40.)Pt5',(0.&40.)Pt6',(0.&40.)Pm',P,(0.&40.)(2.(0.&8.))Pmo',$3.Ph',(4.$5.VR,VHIA,)P,(15.$5.R3.)P,(<.$5.R4.R29.(=.&40.R4?.))P,(31.R2?.R4.)P,(32.$5.R31.R6.)P,(33.$5.VR,R2?.R2>.(=.&40.R52.)(?.VR,)(26.$5.VR,VHIA,R30.)(2?.$34.)R32.R7.)P,(13.$8.(12.$5.VR,VHIA,R6.)(12.$5.VR,VHIA,R31.))P,(13.$8.(26.$5.VR,VHIA,R7.)(26.$5.VR,VHIA,R32.))P,(13.$8.(35.$5.VR,VHIA,R8.)(35.$5.VR,VHIA,R33.))P,(;.$5.VR,VHIA,R9.R:.)P,Px,$8.P,(36.$5.VR,VHIA,R36.R1.)(36.$5.VR,VHIA,R<.R2.)P,(>.(20.$5.VR,VHIA,R;.)(1?.(20.$5.VR,VHIA,R36.)(1?.(21.+2.R33.)$22.)))P,(>.(27.$5.VR,VHIA,R<.)(1?.(27.$5.VR,VHIA,R37.)(28.R32.)))P,Pc,$8.P,(1;.(>.$1<.R36.)(37.(13.$8.R1.(1>.R36.))))P,(1=.R3:.R2.)(1=.R10.R3.)P,(:.$5.VR,VHIA,R>.R38.R37.R10.)(38.$5.(39.(3:.(3;.R5=.R5<.R5;.R5:.R1?.R1>.R1=.R56.R55.(16.&40.=)R1<.R1;.R1:.R19.R18.R17.R16.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R15.R14.R13.R12.)R3>.(3<.R5=.)R3=.(3=.(0.&40.))R11.(3>.$5.))R10.)R34.)P,Pt0',(0.&40.)Pt1',(0.&40.)Pt2',(0.&40.)Pa1',(0.&40.)Pa2',(0.&40.)Pa3',(0.&40.)Pa4',(0.&40.)Pa5',(0.&40.)Pa6',(0.&40.)Pa7',(0.&40.)Pt3',(0.&40.)Pt4',(0.&40.)Pt5',(0.&40.)Pt6',(0.&40.)Pm',P,(0.&40.)(2.(0.&8.))Pmo',$3.Ph',(4.$5.VR,VHIA,)PAb,$8.Pjunk,(6.(0.&8.))P,(15.$5.R5.)P,(<.$5.R6.R2<.(=.&40.R52.))P,(31.R32.R6.)P,(32.$5.R34.R8.)P,(33.$5.VR,R32.R31.(=.&40.R55.)(?.VR,)(26.$5.VR,VHIA,R33.)(2?.$34.)R35.R9.)P,(13.$8.(12.$5.VR,VHIA,R8.)(12.$5.VR,VHIA,R34.))P,(13.$8.(26.$5.VR,VHIA,R9.)(26.$5.VR,VHIA,R35.))P,(13.$8.(35.$5.VR,VHIA,R:.)(35.$5.VR,VHIA,R36.))P,(;.$5.VR,VHIA,R;.R<.)P,Px,$8.P,(36.$5.VR,VHIA,R39.R1.)(36.$5.VR,VHIA,R>.R2.)P,(>.(20.$5.VR,VHIA,R=.)(1?.(20.$5.VR,VHIA,R39.)(1?.(21.+2.R36.)$22.)))P,(>.(27.$5.VR,VHIA,R>.)(1?.(27.$5.VR,VHIA,R3:.)(28.R35.)))P,Pc,$8.P,(1;.(>.$1<.R39.)(37.(13.$8.R1.(1>.R39.))))P,(1=.R3=.R2.)(1=.R12.R3.)P,(13.$8.(14.R?.+10.)=)P,(3?.VR,R3<.R3;.R10.R3:.)P,(1;.(>.(1?.R11.R3;.)(?.VR,))(>.(26.$5.VR,VHIA,R3>.)R11.))P,(:.$5.VR,VHIA,R13.(40.(41.$8.$8.)(42.$8.$8.R12.R3<.)R3>.)R3=.R15.)P,(43.$5.R16.R13.(40.$44.(45.(46.R3=.)R12.)(2?.$44.)))(38.$5.(39.(3:.(3;.R64.R63.R62.R61.R25.R24.R23.R5=.R5<.(16.&40.R14.)R22.R21.R20.R1?.R1>.R1=.R1<.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R1;.R1:.R19.R18.)R45.(3<.R64.)R44.(3=.(0.&40.))R17.(3>.$5.))R16.)R3:.)(38.$5.(39.(3:.(3;.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.)R21.(16.&40.(47.VR,))R20.(3=.(0.&40.))R1?.(3>.$5.))R1>.)(48.R17.R16.))")
(* [comment removed for export] *).


  (* [comment removed for export] *)
  #[using="Type"] Lemma MSPLIT_PRIM : malloc_split_primT.
  Proof.
    unfold malloc_split_primT.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo s LB LF n lo d QA QB
      HM HK ST LO SPL SPT SPA MI TP A0 NB FR BUD BUD32 CH HFR XC A0n B0n HA HB.
    destruct s as [h HOK]. destruct HM as [HM0 [XR0 HA0]]. destruct HK as [HK0 GX0].
    revert HA HB. cbv delta [HIA artA_i] in *. cbn [ARt.HST ARt.HM ARt.HK ARt.hcs ARt.htop ARt.hstkhi ARt.hflag ARt.havol ARt.hfr] in *.
    unfold HK_i, hcs_i, htop_i, hstkhi_i, hflag_i, havol_i, hfr_i, hfresh_i, pclass_i in *. cbn [hh arl_stklo arl_malloc arl_tp arl_need_malloc R R0] in *.
    unfold ARt.AVOL_CALL, ARt.AVOL_MAX, ARt.AMAX, ARt.FR_MAX, ARt.fr_charge, AVOL_SPLIT in *.
    intros HA HB.
    dpose HOK as (EL & AWF & VWF).
    pose proof (hm_J AL0 h m mo HK0 (awf'_bwf h AWF) HA0) as HJ0.   (* [comment removed for export] *)
    assert (FP : from_primary n = true) by (apply (proj2 (from_primary_iff n ltac:(clear - NB; lia))); unfold AMAX_SEC in NB; clear - NB; lia).
    assert (ESP : Z_to_bv 64 (bv_unsigned sp) = sp) by apply Z_to_bv_bv_unsigned.
    change 0x69480 with A_WRAP_MALLOC.
    destruct (h_cinit h) eqn:CI.
    - eapply (malloc_prim_splitH STKLO QA QB ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo h LB LF n lo d
                HOK HM0 HK0 HJ0 ST LO SPL SPT SPA MI TP A0 ltac:(unfold AMAX_SEC in NB; clear - NB; lia) ltac:(clear - BUD; lia) CH ltac:(unfold FR_MAXm; clear - HFR; lia) XC FP CI FR A0n B0n).
      { (* [comment removed for export] *)
        intros cf PO.
        ddestruct PO as (x5 & x6 & x7 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & x28 & x29 & x30 & x31 & m' & mo' & h' & -> &
                        MI' & ST' & FR' & WM & HK' & HJ' & EL' & GH' & VOL & FRB & CSM & PRES & IK & RK & HM').
        assert (HOK' : hok STKLO h').
        { split; [rewrite EL'; exact EL|]. split; [exact (proj1 (proj1 HM'))| exact (HK_vwf AL0 h' mo' HK')]. }
        rewrite ESP, <- TP.
        apply (HA x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31 m' mo' (HS STKLO h' HOK')); cbn [hh].
        + exact MI'. + exact ST'. + exact FR'. + exact WM. + exact PRES.
        + rewrite EL'; reflexivity. + rewrite EL'; reflexivity. + reflexivity.
        + split; [exact HK'| unfold gxok in *; rewrite GH', EL'; exact GX0].
        + intros x [Hx|Hx]; [left; exact (CSM x Hx)| right]. unfold in_ghost in *. rewrite GH'. exact Hx.
        + clear - VOL; lia. + clear - FRB; lia.
        + intros c [BIG|NE] Hf; [exfalso; clear - BIG NB; unfold AMAX_SEC in *; lia| rewrite (RK c (or_intror NE)); exact Hf].
        + exact (conj HM' (conj (XR_keep m m' XR0 IK) (J_hm_absent AL0 h' m' mo' HK' (awf'_bwf h' (proj1 (proj1 HM'))) HJ'))).   (* [comment removed for export] *) }
      (* [comment removed for export] *)
      intros cf PO.
      ddestruct PO as (x5 & x6 & x7 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & x28 & x29 & x30 & x31 & m' & mo' & h' & res & -> &
                      MI' & ST' & FR' & WM & HK' & HJ' & EL' & GH' & VOL & FRB & CSM & PRES & IK & RK & (A16 & FA & HI & HM' & junk & JK)).
      assert (HOK' : hok STKLO h').
      { split; [rewrite EL'; exact EL|]. split; [exact (proj1 (proj1 HM'))| exact (HK_vwf AL0 h' mo' HK')]. }
      rewrite ESP, <- TP.
      apply (HB x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31 m' mo' (HS STKLO h' HOK') res junk); cbn [hh].
      + exact MI'. + exact ST'. + exact FR'. + exact WM. + exact PRES.
      + rewrite EL'; reflexivity. + rewrite EL'; reflexivity. + reflexivity.
      + split; [exact HK'| unfold gxok in *; rewrite GH', EL'; exact GX0].
      + intros x [Hx|Hx]; [left; exact (CSM x Hx)| right]. unfold in_ghost in *. rewrite GH'. exact Hx.
      + clear - VOL; lia. + clear - FRB; lia.
      + intros c [BIG|NE] Hf; [exfalso; clear - BIG NB; unfold AMAX_SEC in *; lia| rewrite (RK c (or_intror NE)); exact Hf].
      + exact A16. + exact FA. + exact HI.
      + exact (conj HM' (conj (XR_keep m m' XR0 IK) (J_hm_absent AL0 h' m' mo' HK' (awf'_bwf h' (proj1 (proj1 HM'))) HJ'))).   (* [comment removed for export] *)
      + exact JK.
    - eapply (malloc_prim_init_splitH STKLO QA QB ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo h LB LF n lo d
                HOK HM0 HK0 HJ0 ST LO SPL SPT SPA MI TP A0 ltac:(unfold AMAX_SEC in NB; clear - NB; lia) ltac:(clear - BUD; lia) CH ltac:(unfold FR_MAXm; clear - HFR; lia) XC FP CI FR A0n B0n).
      { (* [comment removed for export] *)
        intros cf PO.
        ddestruct PO as (x5 & x6 & x7 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & x28 & x29 & x30 & x31 & m' & mo' & h' & -> &
                        MI' & ST' & FR' & WM & HK' & HJ' & EL' & GH' & VOL & FRB & CSM & PRES & IK & RK & HM').
        assert (HOK' : hok STKLO h').
        { split; [rewrite EL'; exact EL|]. split; [exact (proj1 (proj1 HM'))| exact (HK_vwf AL0 h' mo' HK')]. }
        rewrite ESP, <- TP.
        apply (HA x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31 m' mo' (HS STKLO h' HOK')); cbn [hh].
        + exact MI'. + exact ST'. + exact FR'. + exact WM. + exact PRES.
        + rewrite EL'; reflexivity. + rewrite EL'; reflexivity. + reflexivity.
        + split; [exact HK'| unfold gxok in *; rewrite GH', EL'; exact GX0].
        + intros x [Hx|Hx]; [left; exact (CSM x Hx)| right]. unfold in_ghost in *. rewrite GH'. exact Hx.
        + clear - VOL; lia. + clear - FRB; lia.
        + intros c [BIG|NE] Hf; [exfalso; clear - BIG NB; unfold AMAX_SEC in *; lia| rewrite (RK c (or_intror NE)); exact Hf].
        + exact (conj HM' (conj (XR_keep m m' XR0 IK) (J_hm_absent AL0 h' m' mo' HK' (awf'_bwf h' (proj1 (proj1 HM'))) HJ'))).   (* [comment removed for export] *) }
      (* [comment removed for export] *)
      intros cf PO.
      ddestruct PO as (x5 & x6 & x7 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & x28 & x29 & x30 & x31 & m' & mo' & h' & res & -> &
                      MI' & ST' & FR' & WM & HK' & HJ' & EL' & GH' & VOL & FRB & CSM & PRES & IK & RK & (A16 & FA & HI & HM' & junk & JK)).
      assert (HOK' : hok STKLO h').
      { split; [rewrite EL'; exact EL|]. split; [exact (proj1 (proj1 HM'))| exact (HK_vwf AL0 h' mo' HK')]. }
      rewrite ESP, <- TP.
      apply (HB x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31 m' mo' (HS STKLO h' HOK') res junk); cbn [hh].
      + exact MI'. + exact ST'. + exact FR'. + exact WM. + exact PRES.
      + rewrite EL'; reflexivity. + rewrite EL'; reflexivity. + reflexivity.
      + split; [exact HK'| unfold gxok in *; rewrite GH', EL'; exact GX0].
      + intros x [Hx|Hx]; [left; exact (CSM x Hx)| right]. unfold in_ghost in *. rewrite GH'. exact Hx.
      + clear - VOL; lia. + clear - FRB; lia.
      + intros c [BIG|NE] Hf; [exfalso; clear - BIG NB; unfold AMAX_SEC in *; lia| rewrite (RK c (or_intror NE)); exact Hf].
      + exact A16. + exact FA. + exact HI.
      + exact (conj HM' (conj (XR_keep m m' XR0 IK) (J_hm_absent AL0 h' m' mo' HK' (awf'_bwf h' (proj1 (proj1 HM'))) HJ'))).   (* [comment removed for export] *)
      + exact JK.
  Qed.

  (* [comment removed for export] *)
  #[using="hAR"] Lemma from_primary_sec : forall n, 0 <= n -> AMAX_SEC <= n -> from_primary n = false.
  Proof.
    intros n N0 HS. unfold AMAX_SEC in HS. unfold from_primary, needed, rounded, round_up, rz_size, rz_log, kMaxSize.
    repeat (replace (n <? _) with false by (symmetry; apply Z.ltb_ge; lia)).
    apply Z.leb_gt. pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma MSPLIT : malloc_split_T.
  Proof.
    unfold malloc_split_T.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo s LB LF n lo d QA QB
      HM HK ST LO SPL SPT SPA MI TP A0 NB DN BUD BUD32 CH HFR XC A0n B0n HA HB.
    destruct (Z_lt_le_dec n AMAX_SEC) as [SMALL|BIG].
    { destruct DN as [DN|FR]; [exfalso; clear - DN SMALL; lia|].
      exact (MSPLIT_PRIM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo s LB LF n lo d QA QB
               HM HK ST LO SPL SPT SPA MI TP A0 ltac:(clear - NB SMALL; lia) FR BUD BUD32 CH HFR XC A0n B0n HA HB). }
    (* [comment removed for export] *)
    destruct s as [h HOK]. destruct HM as [HM0 [XR0 HA0]]. destruct HK as [HK0 GX0].
    revert HA HB. cbv delta [HIA artA_i] in *. cbn [ARt.HST ARt.HM ARt.HK ARt.hcs ARt.htop ARt.hstkhi ARt.hflag ARt.havol ARt.hfr] in *.
    unfold HK_i, hcs_i, htop_i, hstkhi_i, hflag_i, havol_i, hfr_i, hfresh_i, pclass_i in *. cbn [hh arl_stklo arl_malloc arl_tp arl_need_malloc R R0] in *.
    unfold ARt.AVOL_CALL, ARt.AVOL_MAX, ARt.AMAX, ARt.FR_MAX, ARt.fr_charge, AVOL_SPLIT in *.
    intros HA HB.
    dpose HOK as (EL & AWF & VWF).
    pose proof (hm_J AL0 h m mo HK0 (awf'_bwf h AWF) HA0) as HJ0.   (* [comment removed for export] *)
    pose proof (from_primary_sec n ltac:(clear - NB; lia) BIG) as FP.
    assert (ESP : Z_to_bv 64 (bv_unsigned sp) = sp) by apply Z_to_bv_bv_unsigned.
    change 0x69480 with A_WRAP_MALLOC.
    eapply (malloc_sec_splitH STKLO MOD_DIE QA QB ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo h LB LF n lo d
              HOK HM0 HK0 HJ0 ST LO SPL SPT SPA MI TP A0 ltac:(clear - NB; lia) ltac:(clear - BUD; lia) ltac:(clear - BUD32; lia) CH ltac:(unfold FR_MAXm; clear - HFR; lia) FP A0n B0n).
    - (* [comment removed for export] *)
      intros cf PO.
      ddestruct PO as (x5 & x6 & x7 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & x28 & x29 & x30 & x31 & m' & mo' & h' & -> &
                      MI' & ST' & FR & WM & HK' & HJ' & EL' & GH' & VOL & FRB & CSM & PRES & IK & RK & HM').
      assert (HOK' : hok STKLO h').
      { split; [rewrite EL'; exact EL|]. split; [exact (proj1 (proj1 HM'))| exact (HK_vwf AL0 h' mo' HK')]. }
      rewrite ESP, <- TP.
      apply (HA x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31 m' mo' (HS STKLO h' HOK')); cbn [hh].
      + exact MI'. + exact ST'. + exact FR. + exact WM. + exact PRES.
      + rewrite EL'; reflexivity. + rewrite EL'; reflexivity. + reflexivity.
      + split; [exact HK'| unfold gxok in *; rewrite GH', EL'; exact GX0].
      + intros x [Hx|Hx]; [left; exact (CSM x Hx)| right]. unfold in_ghost in *. rewrite GH'. exact Hx.
      + clear - VOL; lia. + clear - FRB; lia.
      + intros c _ Hf. rewrite (RK c (or_introl FP)). exact Hf.
      + exact (conj HM' (conj (XR_keep m m' XR0 IK) (J_hm_absent AL0 h' m' mo' HK' (awf'_bwf h' (proj1 (proj1 HM'))) HJ'))).   (* [comment removed for export] *)
    - (* [comment removed for export] *)
      intros cf PO.
      ddestruct PO as (x5 & x6 & x7 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & x28 & x29 & x30 & x31 & m' & mo' & h' & res & -> &
                      MI' & ST' & FR & WM & HK' & HJ' & EL' & GH' & VOL & FRB & CSM & PRES & IK & RK & (A16 & FA & HI & HM' & junk & JK)).
      assert (HOK' : hok STKLO h').
      { split; [rewrite EL'; exact EL|]. split; [exact (proj1 (proj1 HM'))| exact (HK_vwf AL0 h' mo' HK')]. }
      rewrite ESP, <- TP.
      apply (HB x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31 m' mo' (HS STKLO h' HOK') res junk); cbn [hh].
      + exact MI'. + exact ST'. + exact FR. + exact WM. + exact PRES.
      + rewrite EL'; reflexivity. + rewrite EL'; reflexivity. + reflexivity.
      + split; [exact HK'| unfold gxok in *; rewrite GH', EL'; exact GX0].
      + intros x [Hx|Hx]; [left; exact (CSM x Hx)| right]. unfold in_ghost in *. rewrite GH'. exact Hx.
      + clear - VOL; lia. + clear - FRB; lia.
      + intros c _ Hf. rewrite (RK c (or_introl FP)). exact Hf.
      + exact A16. + exact FA. + exact HI.
      + exact (conj HM' (conj (XR_keep m m' XR0 IK) (J_hm_absent AL0 h' m' mo' HK' (awf'_bwf h' (proj1 (proj1 HM'))) HJ'))).   (* [comment removed for export] *)
      + exact JK.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma FREED : freeD_T.
  Proof.
    unfold freeD_T.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo [h HOK] LB LF A n lo d
      [HM0 [XR0 HA0]] [HK0 GX0] HIN ST LO SPL SPT SPA MI TP A0 BUD CH HFR.
    cbv delta [HIA artA_i] in *. cbn [ARt.HST ARt.HM ARt.HK ARt.hcs ARt.htop ARt.hstkhi ARt.hflag ARt.havol ARt.hfr] in *.
    unfold HK_i, hcs_i, htop_i, hstkhi_i, hflag_i, havol_i, hfr_i, hfresh_i in *. cbn [hh arl_stklo arl_free arl_tp arl_need_free R R0] in *.
    unfold ARt.AVOL_CALL, ARt.AVOL_MAX, ARt.FR_MAX, ARt.fr_charge, KBATCH in *.
    dpose HOK as (EL & AWF & VWF).
    pose proof (hm_J AL0 h m mo HK0 (awf'_bwf h AWF) HA0) as HJ0.   (* [comment removed for export] *)
    eapply aevtS_mono.
    { eapply (FH ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo h LB LF A n lo d HOK HM0 (proj2 (proj2 XR0)) HK0 HJ0 GX0 HIN ST LO SPL SPT SPA MI TP A0);
        [unfold AVOL_MAX; clear - BUD; lia| exact CH| unfold FR_MAXm; clear - HFR; lia]. }
    cbn beta. intros cf PO.
    ddestruct PO as (x5 & x6 & x7 & xa0 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & x28 & x29 & x30 & x31 & m' & mo' & h' & -> &
                    MI' & ST' & FR & HK' & HJ' & GX' & EL' & CSM & VOL & FRB & PRES & IK & HM' & RU').
    assert (HOK' : hok STKLO h').
    { split; [rewrite EL'; exact EL|]. split; [exact (proj1 (proj1 HM'))| exact (HK_vwf AL0 h' mo' HK')]. }
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
    split. { intros c Hc Hf. rewrite (RU' c ltac:(unfold kBatchClass; exact Hc)). exact Hf. }
    exact (conj HM' (conj (XR_keep m m' XR0 IK) (J_hm_absent AL0 h' m' mo' HK' (awf'_bwf h' (proj1 (proj1 HM'))) HJ'))).   (* [comment removed for export] *)
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma hd_rtc_i : forall m, arl_rtc R m -> asan_rtc m.
  Proof. intros m H. exact H. Qed.

  #[using="Type"] Lemma hd_static_i : forall a, drv_static a -> cstatic R a.
  Proof.
    intros a H. unfold cstatic, drv_static in *. cbn [arl_L R R0 hl_data_lo hl_data_hi hl_static HL0].
    unfold RT. cbn [in_rangesZ fst snd]. clear - H. lia.
  Qed.

  #[using="Type"] Lemma hd_needs_i : 0 <= arl_need_malloc R <= 4096 /\ 0 <= arl_need_free R <= 4096 /\ 0 <= arl_need_amem R <= 4096.
  Proof. cbn. lia. Qed.

  #[using="Type"] Lemma hd_ceil_i : @alloc_ceiling (arl_L R) + 8 <= 0x7fffffffffff.
  Proof. cbn [arl_L R R0]. rewrite HL0_ceil. pose proof aceil_le_max as X. unfold ACEIL_MAX in X. clear - X. lia. Qed.

  #[using="Type"] Lemma hd_blk_band_i : ltac2:(CDefT.buildp (gd_tbl_AHeapHID ()) "Ph,(4.$5.VR,VHIA,)PLB,(6.$7.)PLF,(6.$7.)Pm,P,(0.&40.)(2.(0.&8.))PA,$8.Pn,$8.P,(:.$5.VR,VHIA,R6.R5.R4.R3.)P,(49.(41.$8.$8.)(42.$8.$8.R3.R2.)R6.)(18.(>.+65?000.R4.)(18.(>.(1?.R4.R3.)(53.(54.VR,)))(1;.(>.(1?.R4.R3.)+7???7000.)(>.+10007???8000.R4.))))")
(* [comment removed for export] *).
  Proof.
    intros [h HOK] LB LF m A n [HM0 _] HIn. cbn [arl_L R R0]. rewrite HL0_ceil.
    dpose (block_bounds STKLO h LB LF m HOK HM0 A n HIn) as (B1 & B2 & B3 & B4). unfold kHighMemBeg in B4. clear - B1 B2 B3 B4. lia.
  Qed.

  #[using="Type"] Lemma hd_lowsh_i : forall h LB LF m, ARt.HM asegs R HIA h LB LF m -> mapped m 0x7fffa000 0x800d3000.
  Proof.
    intros [h HOK] LB LF m [HM0 _]. dpose HM0 as (_ & GM & _). destruct GM as (LOW & _).
    eapply (wr_at_mapped m 0x7fff7000 0x10000000); [exact LOW| lia| lia| lia].
  Qed.

  #[using="hAR"] Lemma class_of_big : forall s, 2^14 <= s -> 26 <= class_of s.
  Proof.
    intros s Hs. unfold class_of. replace (s <=? 512) with false by (symmetry; apply Z.leb_gt; lia).
    assert (L : 14 <= Z.log2 s) by (apply Z.log2_le_pow2; lia).
    pose proof (Z.mod_pos_bound (s / 2 ^ (Z.log2 s - 1)) 2 ltac:(lia)) as M.
    destruct (s mod 2 ^ (Z.log2 s - 1) =? 0); lia.
  Qed.

  #[using="hAR"] Lemma hd_pclass_batch_i : forall n, pclass_i n = KBATCH -> 5889 <= n <= 7936.
  Proof.
    intros n H. unfold pclass_i, KBATCH in H.
    destruct (Z_lt_le_dec n 1) as [N0|N1].
    { exfalso. unfold pclass, needed, rounded, round_up, rz_size, rz_log in H.
      replace (Z.max n 8) with 8 in H by lia. replace (n <? 49) with true in H by (symmetry; apply Z.ltb_lt; lia).
      cbn in H. discriminate H. }
    destruct (Z_lt_le_dec n (2^14)) as [N2|N3].
    - pose proof (zall_spec (fun y => negb (pclass y =? 24) || ((5889 <=? y) && (y <=? 7936))) (Z.to_nat (2^14 - 1)) 1
                    ltac:(vm_compute; reflexivity) n ltac:(lia)) as E. cbn beta in E.
      rewrite H, Z.eqb_refl in E. cbn [negb orb] in E. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
    - exfalso. unfold pclass in H.
      assert (NN : 2^14 <= needed n).
      { unfold needed, rounded, round_up, rz_size. pose proof (Z.pow_pos_nonneg 2 (rz_log n) ltac:(lia) ltac:(unfold rz_log; repeat (destruct (n <? _)); lia)).
        pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)). lia. }
      pose proof (class_of_big (needed n) NN). lia.
  Qed.

  Definition artD_i : artD asegs R HIA.
  Proof.
    unshelve eapply (ARTD asegs R HIA hfresh_i pclass_i).
    - exact hd_rtc_i.
    - exact hd_static_i.
    - exact hd_needs_i.
    - exact hd_ceil_i.
    - exact hd_blk_band_i.
    - exact hd_lowsh_i.
    - exact hd_pclass_batch_i.
    - exact MSPLIT.
    - exact FREED.
  Defined.

  (* [comment removed for export] *)
  #[using="Type"] Lemma HID_fresh : ltac2:(CDefT.buildp (gd_tbl_AHeapHID ()) "Ph,(4.$5.VR,VHIA,)Pc,$8.P,(13.$8.(55.(56.(57.VhAR,VSTKLO,R2.)R1.))=)(58.$5.VR,VHIA,$59.R3.R2.)")
(* [comment removed for export] *).
  Proof. intros h c H. exact H. Qed.
End HID.

End ARUN_1.
