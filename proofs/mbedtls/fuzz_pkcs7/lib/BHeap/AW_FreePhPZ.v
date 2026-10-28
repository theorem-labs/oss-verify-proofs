(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Mem Arr Asn1Aux CellsX HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX APop AW_FreeP AW_FreeK AW_FreeRM AW_FreePM.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AHeapR AFreePost AW_FreeH AW_FreePhP AW_FreePhP2 AW_FreePhP3 AW_FreePhP3I.
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
Ltac2 gd_tbl_AW_FreePhPZ () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.batch"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.q_batches"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_tq"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.ex"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.b_elems"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.pc_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_cache"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kBatchClass"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.

Section PHPZ.
  Variable STKLO : Z.
  Hypothesis STKLO_OK : ACEIL <= STKLO.

  (* [comment removed for export] *)
  Definition armE3 (h : ahst) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_FreePhPZ ()) "(0.(1.(2.(3.$4.)(5.(6.O1.))(7.$4.))(8.(3.$4.)Ltq0,(3.$4.)(8.$4.Llb,$4.(0.(2.(3.$4.)(5.(6.O1.))(9.$4.R2.(:.$4.R1.(7.$4.))))(2.$;.(<.$=.(>.R1.))#3?=.)))))(2.(3.$=.)(?.(10.O1.$11.))(7.$=.)))")
(* [comment removed for export] *).
  #[using="STKLO_OK"] Lemma PHP3 : phaseP_Tc STKLO armE3.   (* [comment removed for export] *)
  Proof.
    intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo h LB LF A n lo d
      ARMC HOK HM0 XF0 HK0 HJ0 HIN ST LOL SPL SPT SPA MI TP A0 HV CH HFR CONT.
    destruct (h_cinit h) eqn:CI.
    - exact (phaseP_E3a STKLO STKLO_OK Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo h LB LF A n lo d
               (conj ARMC CI) HOK HM0 XF0 HK0 HJ0 HIN ST LOL SPL SPT SPA MI TP A0 HV CH HFR CONT).
    - exact (phaseP_E3b STKLO STKLO_OK Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo h LB LF A n lo d
               (conj ARMC CI) HOK HM0 XF0 HK0 HJ0 HIN ST LOL SPL SPT SPA MI TP A0 HV CH HFR CONT).
  Qed.

  #[using="Type"] Lemma arms_cover : forall h, awf' h -> armE1 h \/ armE2 h \/ armE3 h.
  Proof.
    intros h WF. dpose WF as (_ & _ & _ & _ & WQ & _). dpose WQ as ((T1 & _ & _) & _).
    assert (NEWB : (exists tq0 lb, q_batches (h_tq h) = tq0 ++ [lb] /\ (length (b_elems lb) < 1021)%nat)
                   \/ (q_batches (h_tq h) = [] \/ exists tq0 lb, q_batches (h_tq h) = tq0 ++ [lb] /\ length (b_elems lb) = 1021%nat)).
    { destruct (snoc_case (q_batches (h_tq h))) as [E|(tq0 & lb & E)]; [right; left; exact E|].
      pose proof (proj1 (Forall_forall _ _) T1 lb ltac:(rewrite E; apply in_app_iff; right; left; reflexivity)) as (B1 & _). unfold b_count, kBatchCap in B1.
      destruct (Nat.lt_ge_cases (length (b_elems lb)) 1021) as [LT|GE]; [left; dexists tq0, lb; exact (conj E LT)|].
      right. right. dexists tq0, lb. split; [exact E| clear - B1 GE; lia]. }
    destruct NEWB as [A|A]; [left; exact A|].
    destruct (pc_chunks (h_cache h kBatchClass)) eqn:PC; [right; right| right; left]; (split; [exact A|]); rewrite PC; [reflexivity| discriminate].
  Qed.

  #[using="STKLO_OK"] Theorem phaseP : phaseP_T STKLO.
  Proof. exact (phaseP_of_arms STKLO armE1 armE2 armE3 arms_cover (phaseP_E1 STKLO STKLO_OK) (phaseP_E2 STKLO STKLO_OK) PHP3). Qed.

  (* [comment removed for export] *)
  #[using="STKLO_OK"] Theorem freeH : freeH_T STKLO.
  Proof. exact (freeH_of_phases STKLO phaseP). Qed.
End PHPZ.
End ARUN_1.
