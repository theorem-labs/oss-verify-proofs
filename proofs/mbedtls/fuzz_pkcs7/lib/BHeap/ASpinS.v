(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import DivergeSim.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import StepA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ASpin.
Import ListNotations.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_ASpinS () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.BHeap.ASpin.spin_pcs"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.LibA.SRz.spinningJ"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].

Section ARUN_1. Context {hAR : arun}.
#[using="Type"] Lemma spinningJ_at : ltac2:(CDefT.buildp (gd_tbl_ASpinS ()) "Ppc,$0.Pr,(1.&5.(2.&40.))PF,(1.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.P,(5.$0.R6.$6.)P,(7.(3.(2.&40.))(8.R2.)(9.(2.&40.)))(:.$;.(<.(=.R7.R6.(>.&40.R8.)R5.(9.(2.&40.))R4.(?.$;.))R3.))")
(* [comment removed for export] *).
Proof.
  intros pc r F fc m mo IN HALT. cbn in IN.
  repeat match type of IN with _ \/ _ => destruct IN as [<-|IN] | False => destruct IN end;
  (apply spinningJ_here; [reflexivity | vm_compute; reflexivity | exact HALT]).
Qed.

End ARUN_1.
