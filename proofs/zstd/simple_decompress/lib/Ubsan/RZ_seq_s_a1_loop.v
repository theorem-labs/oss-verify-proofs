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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_s_base RZ_seq_s_lbase RZ_seq_s_xat RZ_seq_s_a1_at RZ_seq_s_a1_dec RZ_seq_s_a1_rl1 RZ_seq_s_a1_rl2 RZ_seq_s_a1_upd RZ_seq_s_a1_exlit RZ_seq_s_a1_exmat RZ_seq_s_a1_exclose RZ_seq_s_a1_slow RZ_seq_s_a1_tail.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma a1_loop_step : zd_execend_split_stmt -> forall P OEND LLO LEND LOCV K,
  seqs_static P OEND LLO LEND LOCV -> 1 <= K <= v_nbSeq P -> seqs_at_err P OEND LLO LEND LOCV -> seqs_at_lexit P OEND LLO LEND LOCV ->  wnth (v_ws P) H5_litBufferEnd = Z_to_bv 64 LEND -> LOCV = 2 -> (forall K0, 1 <= K0 <= v_nbSeq P -> a1_brk P OEND LLO LEND LOCV K0) ->
  (forall K', 1 <= K' < K -> a1_head P OEND LLO LEND LOCV K') -> a1_head P OEND LLO LEND LOCV K.
Proof.
  intros EXE P OEND LLO LEND LOCV K ST HK A_err A_lexit HLBE HLOC A_brkall IH.
  pose proof (a1_tail_ok P OEND LLO LEND LOCV K ST HK A_err IH A_lexit) as A_tail.
  pose proof (a1_closeloop_ok P OEND LLO LEND LOCV K ST HK A_tail) as A_closeloop.
  pose proof (a1_exec7 P OEND LLO LEND LOCV K ST HK A_tail A_closeloop) as A_close8.
  pose proof (a1_exec6 P OEND LLO LEND LOCV K ST HK A_close8) as A_close.
  pose proof (a1_matloop_ok P OEND LLO LEND LOCV K ST HK A_tail) as A_matloop.
  pose proof (a1_exec3 P OEND LLO LEND LOCV K ST HK A_err A_tail A_matloop A_close) as A_match.
  pose proof (a1_litloop_ok P OEND LLO LEND LOCV K ST HK A_match) as A_litloop.
  pose proof (a1_exec1 P OEND LLO LEND LOCV K ST HK A_match A_litloop) as A_lit1.
  pose proof (a1_slow_ok EXE P OEND LLO LEND LOCV K ST HK HLOC A_tail) as A_slow.
  pose proof (a1_exec0 P OEND LLO LEND LOCV K ST HK HLOC A_slow A_lit1) as A_exec.
  pose proof (a1_reload2 P OEND LLO LEND LOCV K ST HK HLBE A_exec (A_brkall K HK)) as A_upd.
  pose proof (a1_update P OEND LLO LEND LOCV K ST HK HLBE A_upd A_exec (A_brkall K HK)) as A_rl1.
  pose proof (a1_reload1 P OEND LLO LEND LOCV K ST HK A_rl1) as A_dec.
  exact (a1_decode P OEND LLO LEND LOCV K ST HK A_dec).
Qed.

Theorem a1_loop : zd_execend_split_stmt -> forall P OEND LLO LEND LOCV,
  seqs_static P OEND LLO LEND LOCV -> seqs_at_err P OEND LLO LEND LOCV -> seqs_at_lexit P OEND LLO LEND LOCV ->  wnth (v_ws P) H5_litBufferEnd = Z_to_bv 64 LEND -> LOCV = 2 -> (forall K0, 1 <= K0 <= v_nbSeq P -> a1_brk P OEND LLO LEND LOCV K0) ->
  forall K, 1 <= K <= v_nbSeq P -> a1_head P OEND LLO LEND LOCV K.
Proof.
  intros EXE P OEND LLO LEND LOCV ST A_err A_lexit HLBE HLOC A_brkall.
  assert (ALL : forall n : nat, forall K, 1 <= K <= v_nbSeq P -> K <= Z.of_nat n -> a1_head P OEND LLO LEND LOCV K).
  { induction n as [|n IHn]; intros K HK HN; [exfalso; lia|].
    apply (a1_loop_step EXE P OEND LLO LEND LOCV K ST HK A_err A_lexit HLBE HLOC A_brkall). intros K' HK'. apply IHn; lia. }
  intros K HK. apply (ALL (Z.to_nat K) K HK). lia.
Qed.
