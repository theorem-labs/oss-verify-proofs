(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode Arr SFMisc.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_entry MallocTree MallocKit_A.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import MallocKit_AB.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import Malloc_fp MallocKit_A2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocKit_A3.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require ASlot_W10.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp.ASlot_W1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W10.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section STC.
Variables (szc cnt : Z).
Hypothesis SZC : 1 <= szc <= 8191.
Hypothesis CR : 1 <= cnt <= 32.
Hypothesis SMALL : szc * 16 * cnt + 16 <= 2048.
Let n' := szc * 16 * cnt + 12.
Let j := size_to_class n'.

Lemma stc_q_eq : j = stc_q (szc * cnt).
Proof.
  unfold j, n'. rewrite size_to_class_q by nia. f_equal. Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
End STC.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

End ACeilS1.
