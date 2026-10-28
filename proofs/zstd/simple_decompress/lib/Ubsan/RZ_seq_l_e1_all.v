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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_xat RZ_seq_l_e1_at RZ_seq_l_e1_exlit RZ_seq_l_e1_exmat RZ_seq_l_e1_exclose RZ_seq_l_e1_slow.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma e1_exec_ok : zd_execend_stmt -> forall P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P -> LLO = y_DCTX P + 30372 -> LEND = y_DCTX P + 95908 ->
  seql_at_err P OEND LLO LEND LOCV -> e1_tail P OEND LLO LEND LOCV K -> e1_exec P OEND LLO LEND LOCV K.
Proof.
  intros EXE P OEND LLO LEND LOCV K ST HK HX HXE A_err A_tail.
  pose proof (e1_closeloop_ok P OEND LLO LEND LOCV K ST HK A_tail) as A_closeloop.
  pose proof (e1_exec7 P OEND LLO LEND LOCV K ST HK A_tail A_closeloop) as A_close8.
  pose proof (e1_exec6 P OEND LLO LEND LOCV K ST HK A_close8) as A_close.
  pose proof (e1_matloop_ok P OEND LLO LEND LOCV K ST HK A_tail) as A_matloop.
  pose proof (e1_exec3 P OEND LLO LEND LOCV K ST HK A_err A_tail A_matloop A_close) as A_match.
  pose proof (e1_litloop_ok P OEND LLO LEND LOCV K ST HK HX A_match) as A_litloop.
  pose proof (e1_exec1 P OEND LLO LEND LOCV K ST HK HX A_match A_litloop) as A_lit1.
  pose proof (e1_slow_ok EXE P OEND LLO LEND LOCV K ST HK HXE A_tail A_err) as A_slow.
  exact (e1_exec0 P OEND LLO LEND LOCV K ST HK HX A_slow A_lit1).
Qed.
