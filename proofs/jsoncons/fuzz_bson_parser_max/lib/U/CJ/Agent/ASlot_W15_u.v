(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr Bytes.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.CJ.Agent Require Import F_syscalls_u MallocRep_u F_malloc_free_u F_malloc_fast_u F_malloc_entry_u F_malloc_enframe_u MallocTree_u MallocKit_A_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.CJ.Agent Require Import MallocKit_AB_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.CJ.Agent Require Import Malloc_fp_u MallocKit_A2_u F_malloc_bigw_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.CJ.Agent Require Import MallocKit_A3_u.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lxor_b2z_1 b : Z.lxor (Z.b2z b) 1 = Z.b2z (negb b).
Proof. destruct b; reflexivity. Qed.

Lemma signed_lit_small z : -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros Hz. rewrite zb_signed, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  destruct (Z.ltb_spec (z mod 2^64) (2^63)); Z.div_mod_to_equations; lia.
Qed.

Lemma ltb99_leb100 b : (99 <? b) = (100 <=? b).
Proof. destruct (Z.ltb_spec 99 b), (Z.leb_spec 100 b); try reflexivity; lia. Qed.
End CEIL_WRAP_1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
