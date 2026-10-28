(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux SysStep ITree Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_MmapFixed AKinv AJ AKinvS.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AW_CfgS () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LibA.ALazy.asan_layout"; "Corelib.Init.Datatypes.bool"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "RocqVerifyHarness.AgentSubmission.BHeap.AKinv.kinv"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.J"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_mem"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.mo_mat"; "ARUN_1.orS"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"].

Section ARUN_1. Context {hAR : arun}.
Definition orS (segs : list Segment) (ok : bool) (Q : config -> Prop) (c : config) : Prop :=
  if ok then aevtS segs Q c else aevtS segs Q c \/ spinningJ segs c.

#[using="Type"] Lemma orS_weaken : forall segs ok Q c, aevtS segs Q c -> orS segs ok Q c.
Proof. intros segs [|] Q c H; [exact H| left; exact H]. Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma evtA_contS_KJ : ltac2:(CDefT.buildp (gd_tbl_AW_CfgS ()) "PL,$0.Pok,$1.PCS,P,$2.SpPK,P,$3.SpPP,P,$4.SpPQ,P,$5.SpPms,$4.Pmo,$3.P,(6.VhAR,R8.R6.R5.)P,A1.R6.R2.P,(7.(8.R4.)R3.)P,(9.$:.R;.R9.R7.R5.)P,Pms',$4.Pmo',$3.P,A1.R:.R2.P,A1.R<.R2.P,(;.R9.R3.)P,(7.(8.R5.)R4.)(<.$:.R11.R=.(=.R6.R5.))(<.$:.R<.R8.(=.R7.R6.))")
(* [comment removed for export] *).
Proof.
  intros L [|] CS K P Q ms mo KL HK HJ EV CONT; cbn [orS] in *.
  - eapply evtA_aevtS_KJ; eassumption.
  - eapply evtA_orS_KJ; eassumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma kinv_mono : forall L (CS CS' : Z -> Prop) K, (forall x, CS x -> CS' x) -> kinv L CS' K -> kinv L CS K.
Proof.
  intros L CS CS' K HS KL. split.
  - intros mo HK. exact (ki_halted KL mo HK).
  - intros mo HK. exact (ki_top KL mo HK).
  - intros mo acc HK OK. exact (ki_mat KL mo acc HK (acc_ok_mono L CS CS' acc HS OK)).
Qed.

#[using="Type"] Lemma crange_imp : forall (P Q : Z -> Prop) A n, (forall x, P x -> Q x) -> crange P A n -> crange Q A n.
Proof. intros P Q A n PQ CR x Hx. apply PQ, CR, Hx. Qed.

End ARUN_1.
