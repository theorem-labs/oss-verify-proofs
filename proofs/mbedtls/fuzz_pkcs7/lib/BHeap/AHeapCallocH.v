(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw ACnt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModelX. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm AVst HMLib HM HMFrame AHeapR AMallocPost AHeapMalloc ACallocPost AHeapCalloc
     AW_Populate AW_MmapDie AW_MapOrDie AW_MallocSecS AHeapCallocP AHeapCallocPI AHeapCallocS.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AInstEmb AJ.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AHeapCallocH () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.AL0"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MallocSecS.dstat"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MallocSecS.DIE_NEED"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapDie.die_post"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapDie.A_SPIN_MMAPDIE"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MapOrDie.mod_answered"].

Section ARUN_1. Context {hAR : arun}.
Section CH.
  Variable STKLO : Z.

  Hypothesis B12C : b12_siteT.   (* [comment removed for export] *)
  Hypothesis MOD_DIE : ltac2:(CDefT.buildp (gd_tbl_AHeapCallocH ()) "PCS,P,$0.SpPgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)Pa6,(1.&40.)Pra,(1.&40.)PSP0,$0.PF,(2.&5.(1.&40.))Pfc,(1.&20.)Pm0,P,(1.&40.)(3.(1.&8.))Pmm,P,(1.&40.)(3.(1.&8.))Paddr,$0.Psize,$0.Plo0,$0.Pfr,(4.(1.&8.))P,(5.$6.R21.)P,(7.(8.=R5.)(9.R5.(:.+2.+2?.)))P,(7.(9.=R5.)(8.R5.(:.+2.+28.)))P,(;.$<.R8.(=.R<.-60.)(>.$?.(10.(11.&40.+32.))(>.$?.(12.#2<.R4.)(>.$?.(13.R1:.)(>.$?.(13.R1;.)(>.$?.(13.R1<.)(>.$?.(13.R1=.)(>.$?.(13.R1>.)(>.$?.(13.R=.)(14.$?.))))))))))P,(15.R9.)P,(16.$<.R:.R7.(=.R>.-60.))P,(8.+65?000.R8.)P,(8.R9.(17.R10.$18.))P,(8.R11.(:.+2.+3?.))P,(19.(>.(1:.$0.$0.)(1;.$0.$0.R;.R12.)(14.(1:.$0.$0.)))R?.R>.)P,(1<.$<.R10.R?.)P,(1=.$<.R10.)P,(1>.R2=.R>.(17.R15.R>.))(1?.$<.$6.R2>.(20.R14.$21.)(22.(11.&40.(17.(:.+2.+40.)+<.))R16.R2=.R2<.R2;.R2:.R29.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R15.R14.R11.R10.R12.))")
(* [comment removed for export] *).

  #[using="B12C MOD_DIE"] Theorem callocH_of_parts : callocH_T STKLO.
  Proof.
    unfold callocH_T.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo h LB LF n cnt0 sz0 lo d
      HOK HM0 HK0 HJ0 ST LO SPL SPT SPA MI TP A0 A1 CB0 SZ0 EN0 NB BUD CH HFR XC.
    destruct (from_primary n) eqn:FP.
    - destruct (h_cinit h) eqn:CI.
      + exact (calloc_prim_fieldH STKLO B12C ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo h LB LF n cnt0 sz0 lo d
                 HOK HM0 HK0 HJ0 ST LO SPL SPT SPA MI TP A0 A1 CB0 SZ0 EN0 NB BUD CH HFR XC FP CI).
      + exact (calloc_prim_init_fieldH STKLO B12C ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo h LB LF n cnt0 sz0 lo d
                 HOK HM0 HK0 HJ0 ST LO SPL SPT SPA MI TP A0 A1 CB0 SZ0 EN0 NB BUD CH HFR XC FP CI).
    - rewrite (vchg_sec n (proj1 NB) FP) in BUD.   (* [comment removed for export] *)
      exact (calloc_sec_fieldH STKLO MOD_DIE ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo h LB LF n cnt0 sz0 lo d
               HOK HM0 HK0 HJ0 ST LO SPL SPT SPA MI TP A0 A1 CB0 SZ0 EN0 NB BUD CH HFR FP).
  Qed.
End CH.

End ARUN_1.
