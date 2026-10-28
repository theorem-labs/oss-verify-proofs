(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface RAligned_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG CtSizes CtWire CtTime.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Printf_lib F_vsnprintf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApWalkTac W_bio_push W_bio_write W_bio_printf W_asn1_string W_crypto_realloc.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnU Require Import PrnTimeIface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeU Require Import W_time_from_tm W_gentime_adj W_crypto_realloc3 W_asn1_string_copy W_time_to_tm_A
     W_gentime_set_string W_time_print.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition TIME_STACK : Z := 8464.

Lemma TIME_STACK_adj : TIME_STACK = GENTIME_ADJ_STACK. Proof. reflexivity. Qed.
Lemma TIME_STACK_setstr : GENTIME_SETSTR_STACK <= TIME_STACK. Proof. cbv. discriminate. Qed.
Lemma TIME_STACK_print : GENTIME_PRINT_STACK <= TIME_STACK. Proof. cbv. discriminate. Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Theorem time_adj_ok : rmalloc_stmt -> gentime_adj_ok_stmt TIME_STACK.
Proof. intros HM. rewrite TIME_STACK_adj. exact (gentime_adj_ok HM). Qed.

Theorem time_adj_fail : gentime_adj_fail_stmt TIME_STACK.
Proof. rewrite TIME_STACK_adj. exact gentime_adj_fail. Qed.

Theorem time_setstr_ok : gentime_setstr_ok_stmt TIME_STACK.
Proof.
  pose proof TIME_STACK_setstr as LE. unfold gentime_setstr_ok_stmt. intros. eapply gentime_setstr_ok; try eassumption. lia.
Qed.

Theorem time_setstr_fail : gentime_setstr_fail_stmt TIME_STACK.
Proof.
  pose proof TIME_STACK_setstr as LE. unfold gentime_setstr_fail_stmt. intros. eapply gentime_setstr_fail; try eassumption. lia.
Qed.

Theorem time_print : gentime_print_stmt TIME_STACK.
Proof.
  pose proof TIME_STACK_print as LE. unfold gentime_print_stmt. intros. eapply gentime_print; try eassumption. lia.
Qed.

End WithCeiling0.
