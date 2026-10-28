(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_s_base RZ_seq_s_lbase RZ_seq_s_xat RZ_seq_s_a2_at RZ_seq_s_a2_dec RZ_seq_s_a2_rl1 RZ_seq_s_a2_rl2 RZ_seq_s_a2_upd RZ_seq_s_a2_exlit RZ_seq_s_a2_exmat RZ_seq_s_a2_exclose RZ_seq_s_a2_slow RZ_seq_s_a2_tail.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma a2_loop_step : zd_execend_stmt -> forall P OEND LLO LEND LOCV K,
  seqs_static P OEND LLO LEND LOCV -> 1 <= K <= v_nbSeq P -> seqs_at_err P OEND LLO LEND LOCV -> seqs_at_lexit P OEND LLO LEND LOCV -> 
  (forall K', 1 <= K' < K -> a2_head P OEND LLO LEND LOCV K') -> a2_head P OEND LLO LEND LOCV K.
Proof.
  intros EXE P OEND LLO LEND LOCV K ST HK A_err A_lexit  IH.
  pose proof (a2_tail_ok P OEND LLO LEND LOCV K ST HK A_err IH A_lexit) as A_tail.
  pose proof (a2_closeloop_ok P OEND LLO LEND LOCV K ST HK A_tail) as A_closeloop.
  pose proof (a2_exec7 P OEND LLO LEND LOCV K ST HK A_tail A_closeloop) as A_close8.
  pose proof (a2_exec6 P OEND LLO LEND LOCV K ST HK A_close8) as A_close.
  pose proof (a2_matloop_ok P OEND LLO LEND LOCV K ST HK A_tail) as A_matloop.
  pose proof (a2_exec3 P OEND LLO LEND LOCV K ST HK A_err A_tail A_matloop A_close) as A_match.
  pose proof (a2_litloop_ok P OEND LLO LEND LOCV K ST HK A_match) as A_litloop.
  pose proof (a2_exec1 P OEND LLO LEND LOCV K ST HK A_match A_litloop) as A_lit1.
  pose proof (a2_slow_ok EXE P OEND LLO LEND LOCV K ST HK  A_tail) as A_slow.
  pose proof (a2_exec0b P OEND LLO LEND LOCV K ST HK A_slow A_lit1) as A_execb.
  pose proof (a2_exec0 P OEND LLO LEND LOCV K ST HK A_slow A_execb) as A_exec.
  pose proof (a2_reload2 P OEND LLO LEND LOCV K ST HK A_exec A_execb A_slow) as A_upd.
  pose proof (a2_update P OEND LLO LEND LOCV K ST HK A_upd A_exec) as A_rl1.
  pose proof (a2_reload1 P OEND LLO LEND LOCV K ST HK A_rl1) as A_dec.
  exact (a2_decode P OEND LLO LEND LOCV K ST HK A_dec).
Qed.

Theorem a2_loop : zd_execend_stmt -> forall P OEND LLO LEND LOCV,
  seqs_static P OEND LLO LEND LOCV -> seqs_at_err P OEND LLO LEND LOCV -> seqs_at_lexit P OEND LLO LEND LOCV -> 
  forall K, 1 <= K <= v_nbSeq P -> a2_head P OEND LLO LEND LOCV K.
Proof.
  intros EXE P OEND LLO LEND LOCV ST A_err A_lexit .
  assert (ALL : forall n : nat, forall K, 1 <= K <= v_nbSeq P -> K <= Z.of_nat n -> a2_head P OEND LLO LEND LOCV K).
  { induction n as [|n IHn]; intros K HK HN; [exfalso; lia|].
    apply (a2_loop_step EXE P OEND LLO LEND LOCV K ST HK A_err A_lexit ). intros K' HK'. apply IHn; lia. }
  intros K HK. apply (ALL (Z.to_nat K) K HK). lia.
Qed.
