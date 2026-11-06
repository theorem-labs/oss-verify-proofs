(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import DivergeSim.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import StepA.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASpin.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_ASpinS () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Stdlib.Lists.List.In"; "OSSVerify.KrLib.AHeap.ASpin.spin_pcs"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.LibA.SRz.spinningJ"; "OSSVerify.KrLib.A.AImg.asegs"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "OSSVerify.KrLib.Lib.MState.MS"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"].

Section ARUN_1. Context {hAR : arun}.
#[using="Type"] Lemma spinningJ_at : ltac2:(CDefT.buildp (gd_tbl_ASpinS ()) "Ppc,$0.Pr,(1.&5.(2.&40.))PF,(1.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.P,(5.$0.R6.$6.)P,(7.(3.(2.&40.))(8.R2.)(9.(2.&40.)))(:.$;.(<.(=.R7.R6.(>.&40.R8.)R5.(9.(2.&40.))R4.(?.$;.))R3.))")
(* [comment removed for export] *).
Proof.
  intros pc r F fc m mo IN HALT. cbn in IN.
  repeat match type of IN with _ \/ _ => destruct IN as [<-|IN] | False => destruct IN end;
  (apply spinningJ_here; [reflexivity | vm_compute; reflexivity | exact HALT]).
Qed.

End ARUN_1.
