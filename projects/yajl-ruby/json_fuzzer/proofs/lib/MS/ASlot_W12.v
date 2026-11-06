(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_entry MallocTree MallocKit_A.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocKit_AB.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl Monad RawAlloc.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import Malloc_fp MallocKit_A2.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocKit_A3 ASlot_W1 ASlot_W10.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Export MallocVocab MallocOracle.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
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
End STC.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition nest_frame (j gm cnt size sc : Z) (s4v s3v s2v s1v s0v rav : word) : list cell :=
  [C8 (wz j); C8 (Z_to_bv 64 gm); C8 (wz cnt); C8 (wz cnt); C8 (wz size); C8 (Z_to_bv 64 (sc + 58)); C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].
End RC__1.
