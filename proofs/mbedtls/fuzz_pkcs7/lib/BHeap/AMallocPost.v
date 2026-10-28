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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModelX. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm AVst AW_DepotB AW_DepotTop AW_MallocB AW_Populate HMLib HM HMFrame AHeapR AJ.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AMallocPost () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_IA"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.A_OOM"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_IA_INIT"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotB.A_SS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotTop.A_DEP_END"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MallocB.A_ERRNO"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate.A_EMB"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.and"; "stdpp.bitvector.definitions.bv"; "Stdlib.ZArith.BinInt.Z.le"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.in_rangesZ"; "ARUN_1.awz"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_TP"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.HK"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.AL0"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.J"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.alayout"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_sech"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_acct"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.vchg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.hfr"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vcs"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.vst_of"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_stk_hi"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "ARUN_1.img_keep"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.HMc"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"].


(* [comment removed for export] *)
Lemma vchg_sec : forall n, 0 <= n -> from_primary n = false -> vchg n = 2 * n.
Proof.
  intros n Hn FP. unfold vchg, ARt.AVOL_CALL. destruct (n <? ARt.AMAX_SEC) eqn:E; [| lia].
  apply Z.ltb_lt in E. unfold AMAX_SEC in E.
  assert (X : from_primary n = true) by (apply (from_primary_iff n Hn); lia). congruence.
Qed.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
Section ARUN_1. Context {hAR : arun}.

(* [comment removed for export] *)
Definition awz : list (Z * Z) := ltac2:(CDefT.buildp (gd_tbl_AMallocPost ()) "(0.(1.$2.$2.)(3.$2.$2.$4.(5.$4.+3>8.))(0.(1.$2.$2.)(3.$2.$2.$6.(5.$6.+81030.))(0.(1.$2.$2.)(3.$2.$2.$7.(5.$7.+1.))(0.(1.$2.$2.)(3.$2.$2.$8.(5.$8.+4.))(0.(1.$2.$2.)(3.$2.$2.$9.$:.)(0.(1.$2.$2.)(3.$2.$2.$;.(5.$;.+4.))(0.(1.$2.$2.)(3.$2.$2.$<.(5.$<.+38.))(=.(1.$2.$2.)))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition img_keep (m m' : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_AMallocPost ()) "(>.Px,(?.&40.)P,(>.(10.+10000.(11.&40.R1.))(12.(11.&40.R1.)+65?000.))P,(13.(14.$15.(11.&40.R2.)))(16.(17.(?.&8.))A1.O1.R3.A1.O2.R3.)Px,(?.&40.)P,(>.(10.+7???:000.(11.&40.R1.))(12.(11.&40.R1.)+800<3>00.))(16.(17.(?.&8.))A1.O1.R2.A1.O2.R2.))")
(* [comment removed for export] *).


Section Post.
  Variable STKLO : Z.
  Let R := R0 STKLO.

  (* [comment removed for export] *)
  Definition mallocH_post (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (h : ahst) (LB LF : list (Z * Z)) (n lo d SP : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_AMallocPost ()) "Lcf,$18.(19.(?.&40.)Lt0,(?.&40.)(19.(?.&40.)Lt1,(?.&40.)(19.(?.&40.)Lt2,(?.&40.)(19.(?.&40.)La1,(?.&40.)(19.(?.&40.)La2,(?.&40.)(19.(?.&40.)La3,(?.&40.)(19.(?.&40.)La4,(?.&40.)(19.(?.&40.)La5,(?.&40.)(19.(?.&40.)La6,(?.&40.)(19.(?.&40.)La7,(?.&40.)(19.(?.&40.)Lt3,(?.&40.)(19.(?.&40.)Lt4,(?.&40.)(19.(?.&40.)Lt5,(?.&40.)(19.(?.&40.)Lt6,(?.&40.)(19.P,(?.&40.)(17.(?.&8.))Lm',P,(?.&40.)(17.(?.&8.))(19.$1:.Lmo',$1:.(19.$1;.Lh',$1;.(19.$2.Lres,$2.(>.(16.$18.R13.(1<.(1=.(1>.O19.(1?.&40.O3.)O18.(1?.&40.$20.)R12.R11.R10.O17.O16.(1?.&40.R1.)R?.R>.R=.R<.R;.R:.R9.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.R8.R7.R6.R5.)O;.(21.O19.)O:.(22.(?.&40.))R4.(23.$24.))R3.))(>.(25.$24.R4.)(>.(26.$24.R4.O5.O3.)(>.(27.O1.R3.)(>.(28.$24.O2.R4.)(>.(29.VhAR,$2:.R2.R3.)(>.(2;.R4.R3.)(>.(16.$2<.(2=.R2.)(2=.O9.))(>.(16.(2>.(1.$2.$2.))(2?.(30.R2.))(2?.(30.O9.)))(>.(10.(31.R2.)(5.(31.O9.)(32.O6.)))(>.(10.(33.R2.)(5.(33.O9.)(5.O4.+3.)))(>.Px,$2.P,(34.$2:.(35.O9.)R1.)(34.$2:.(35.R4.)R2.)(>.(36.$24.VR,O8.O7.O3.VSTKLO,(37.(2=.O9.))(=.$38.)O2.R4.)(>.(39.O2.R4.)(3:.(>.(16.$2.R1.=)(3;.VhAR,R2.O8.O7.R4.))(>.(16.$2.(3<.R1.+10.)=)(>.(3=.VR,O8.O7.R1.O6.)(>.(3:.(10.(5.R1.O6.)VSTKLO,)(10.(37.(2=.O9.))R1.))(>.(3;.VhAR,R2.(0.(1.$2.$2.)(3.$2.$2.R1.O6.)O8.)O7.R4.)(19.(2>.(?.&8.))Ljunk,(2>.(?.&8.))(3>.$24.R5.R2.(0.$3?.(40.(41.O6.)R1.)(=.$3?.)))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).
End Post.

End ARUN_1.
