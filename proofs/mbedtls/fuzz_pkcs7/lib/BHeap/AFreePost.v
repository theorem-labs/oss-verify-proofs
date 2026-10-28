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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModelX. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm AVst AW_Unwind2 HMLib HM HMFrame AHeapR AMallocPost AJ.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AFreePost () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.HK"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.AL0"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.J"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.gxok"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.alayout"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hcsA"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_havol"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.hfr"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.lb_remove"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_stk_hi"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.BHeap.AMallocPost.img_keep"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.HMc"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kBatchClass"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_mapped_user"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_reg"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hok"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_FLAGS"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.pair"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_htop"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.FR_MAXm"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "ARUN_1.Post.freeH_post"].

Section ARUN_1. Context {hAR : arun}.

Section Post.
  Variable STKLO : Z.
  Let R := R0 STKLO.

  (* [comment removed for export] *)
  Definition freeH_post (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (h : ahst) (LB LF : list (Z * Z)) (A lo d SP : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_AFreePost ()) "Lcf,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.$5.Lh',$5.(6.(7.$0.R13.(8.(9.(:.O19.(;.&40.O3.)O18.(;.&40.$<.)R12.R11.R10.O17.O16.R?.R>.R=.R<.R;.R:.R9.R8.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.R7.R6.R5.R4.)O;.(=.O19.)O:.(>.(2.&40.))R3.(?.$10.))R2.))(6.(11.$10.R3.)(6.(12.$10.R3.O5.O3.)(6.(13.O1.R2.)(6.(14.VhAR,$15.R1.R2.)(6.(16.R3.R2.)(6.(17.R1.)(6.(7.$18.(19.R1.)(19.O9.))(6.Px,$1:.P,(1;.O9.R1.)(1;.R3.R2.)(6.(7.$1:.(1<.R1.)(1<.O9.))(6.(1=.(1>.R1.)(1?.(1>.O9.)(1?.O4.+3.)))(6.(20.$10.VR,(21.O6.O8.)O7.O3.VSTKLO,(22.(19.O9.))(23.$24.)O2.R3.)(6.(25.O2.R3.)(6.(26.VhAR,R1.(21.O6.O8.)O7.R3.)Pc,$1:.P,(27.(7.$1:.R1.$28.))(7.$1:.(29.(2:.R3.R2.))(29.(2:.O9.R2.)))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition freeH_T : Prop := ltac2:(CDefT.buildp (gd_tbl_AFreePost ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(2;.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Ph,$5.PLB,(2<.(2=.$1:.$1:.))PLF,(2<.(2=.$1:.$1:.))PA,$1:.Pn,$1:.Plo,$1:.Pd,$1:.P,(2>.VhAR,VSTKLO,R7.)P,(26.VhAR,R8.R7.R6.R:.)P,(2?.$10.R;.(1?.$30.+30.)(31.$32.(33.(;.&40.=))(23.$32.)))P,(14.VhAR,$15.R:.R;.)P,(16.R=.R<.)P,(17.R<.)P,(34.(2=.$1:.$1:.)(35.$1:.$1:.R:.R9.)R<.)P,(12.$10.R10.R9.(36.&40.R30.))P,(1=.VSTKLO,R:.)P,(1=.R;.(37.(36.&40.R32.)+1000.))P,(1=.(36.&40.R33.)(38.(19.R11.)))P,(7.$1:.(39.(36.&40.R34.)+10.)=)P,(11.$10.R15.)P,(7.(2.&40.)R34.(;.&40.$<.))P,(7.(2.&40.)R2?.(;.&40.R12.))P,(1=.(1<.R16.)$3:.)P,(3;.$10.R19.VSTKLO,(22.(19.R17.))(36.&40.R33.)(36.&40.R39.)R11.)P,(1=.(1?.(1>.R18.)(1?.R12.+3.))$3<.)(3=.$10.(3>.R3<.R3:.R35.R34.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R1=.R1<.R19.R18.R17.R16.R14.R13.(36.&40.R3;.)R1;.R1:.)(8.(9.(:.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.)R1=.(;.&40.+6947<.)R1<.(>.(2.&40.))R1;.(?.$10.))R1:.))")
(* [comment removed for export] *).
End Post.

End ARUN_1.
