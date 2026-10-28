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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.CJ.Agent Require Import F_syscalls_u MallocRep_u F_malloc_free_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.CJ.Agent Require Import MallocTree_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.CJ.Agent Require Import MallocKit_B_u.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
Definition fm_facts (st : mstate) (g : aptr) : Prop :=
  forall head, c_free_meta_head (ctx st) = Some head ->
    head <> g /\ meta_slot st head /\
    exists pv, m_prev (get_meta_rec st head) = Some pv /\ pv <> g /\ meta_slot st pv.

Lemma meta_word_meta0 : meta_word meta0 = 0. Proof. reflexivity. Qed.
End CEIL_WRAP_1.


(* [comment removed for export] *)
Ltac meta_open cq MUq WMq :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(cq, cq + 40)]%Z mX) as MUq;
    pose proof (wmono_refl asegs mX) as WMq end.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
