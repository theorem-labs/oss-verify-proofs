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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModelX. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm AVst AW_DepotB AW_DepotTop AW_MallocB HMLib HM HMFrame AHeapR AMallocPost AW_CallocA AJ.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_ACallocPost () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_CallocA.A_CALLOC"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "ARUN_1.A_WRAP_CALLOC"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "Corelib.Init.Logic.and"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_TP"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.HK"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.AL0"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.J"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.alayout"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_sech"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_acct"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_havol"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.vchg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.hfr"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vcs"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.vst_of"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_stk_hi"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.BHeap.AMallocPost.img_keep"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.HMc"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.repeat"].

Section ARUN_1. Context {hAR : arun}.

Definition A_WRAP_CALLOC : Z := 0x69484.   (* [comment removed for export] *)

Section W.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  (* [comment removed for export] *)
  #[using="IMG ALWF"] Lemma cwrap_step : ltac2:(CDefT.buildp (gd_tbl_ACallocPost ()) "PCS,P,$0.SpPra,(1.&40.)Psp,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)PF,(2.&5.(1.&40.))Pfc,(1.&20.)Pm,P,(1.&40.)(3.(1.&8.))P,(4.VAL,R23.)(5.$6.VAL,R24.Lms',$7.(8.$7.R1.(9.(:.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.)R5.(;.&40.$<.)R4.(=.(1.&40.))R3.(>.$6.)))(9.(:.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.)R4.(;.&40.$?.)R3.(=.(1.&40.))R2.(>.$6.)))")
(* [comment removed for export] *).
  Proof.
    intros until m. intros CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    unfold A_WRAP_CALLOC, A_CALLOC. zstep. apply evtA_done. reflexivity.
  Qed.
End W.

Section Post.
  Variable STKLO : Z.
  Let R := R0 STKLO.

  (* [comment removed for export] *)
  Definition callocH_post (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (h : ahst) (LB LF : list (Z * Z)) (n lo d SP : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_ACallocPost ()) "Lcf,$10.(11.(1.&40.)Lt0,(1.&40.)(11.(1.&40.)Lt1,(1.&40.)(11.(1.&40.)Lt2,(1.&40.)(11.(1.&40.)La1,(1.&40.)(11.(1.&40.)La2,(1.&40.)(11.(1.&40.)La3,(1.&40.)(11.(1.&40.)La4,(1.&40.)(11.(1.&40.)La5,(1.&40.)(11.(1.&40.)La6,(1.&40.)(11.(1.&40.)La7,(1.&40.)(11.(1.&40.)Lt3,(1.&40.)(11.(1.&40.)Lt4,(1.&40.)(11.(1.&40.)Lt5,(1.&40.)(11.(1.&40.)Lt6,(1.&40.)(11.P,(1.&40.)(3.(1.&8.))Lm',P,(1.&40.)(3.(1.&8.))(11.$12.Lmo',$12.(11.$13.Lh',$13.(11.$0.Lres,$0.(14.(8.$10.R13.(15.(9.(:.O19.(;.&40.O3.)O18.(;.&40.$16.)R12.R11.R10.O17.O16.(;.&40.R1.)R?.R>.R=.R<.R;.R:.R9.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.R8.R7.R6.R5.)O;.(17.O19.)O:.(=.(1.&40.))R4.(>.$6.))R3.))(14.(18.$6.R4.)(14.(19.$6.R4.O5.O3.)(14.(1:.O1.R3.)(14.(1;.$6.O2.R4.)(14.(1<.VhAR,$1=.R2.R3.)(14.(1>.R4.R3.)(14.(8.$1?.(20.R2.)(20.O9.))(14.(8.(21.(22.$0.$0.))(23.(24.R2.))(23.(24.O9.)))(14.(25.(26.R2.)(27.(26.O9.)(28.O6.)))(14.(25.(29.R2.)(27.(29.O9.)(27.O4.+3.)))(14.Px,$0.P,(2:.$1=.(2;.O9.)R1.)(2:.$1=.(2;.R4.)R2.)(14.(2<.$6.VR,O8.O7.O3.VSTKLO,(2=.(20.O9.))(2>.$2?.)O2.R4.)(14.(30.O2.R4.)(31.(14.(8.$0.R1.=)(32.VhAR,R2.O8.O7.R4.))(14.(8.$0.(33.R1.+10.)=)(14.(34.VR,O8.O7.R1.O6.)(14.(31.(25.(27.R1.O6.)VSTKLO,)(25.(2=.(20.O9.))R1.))(14.(32.VhAR,R2.(35.(22.$0.$0.)(36.$0.$0.R1.O6.)O8.)O7.R4.)(37.$6.R4.R1.(35.$38.(39.(3:.O6.)(3;.(1.&8.)(;.&8.=)(3:.O6.)))(2>.$38.))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).
End Post.

End ARUN_1.
