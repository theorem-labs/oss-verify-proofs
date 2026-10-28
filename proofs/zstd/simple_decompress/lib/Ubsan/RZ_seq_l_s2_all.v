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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_xat RZ_seq_l_s2_at RZ_seq_l_s2_exlit RZ_seq_l_s2_exmat RZ_seq_l_s2_exclose RZ_seq_l_s2_slow.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma s2_exec_ok : zd_execend_split_stmt -> forall P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P -> LOCV = 2 ->
  seql_at_err P OEND LLO LEND LOCV -> s2_tail P OEND LLO LEND LOCV K -> s2_stail P OEND LLO LEND LOCV K -> s2_tail2 P OEND LLO LEND LOCV K -> s2_exec P OEND LLO LEND LOCV K.
Proof.
  intros EXE P OEND LLO LEND LOCV K ST HK HLOC A_err A_tail A_stail A_tail2.
  pose proof (s2_closeloop_ok P OEND LLO LEND LOCV K ST HK A_stail) as A_closeloop.
  pose proof (s2_exec7 P OEND LLO LEND LOCV K ST HK A_stail A_closeloop) as A_close8.
  pose proof (s2_exec6 P OEND LLO LEND LOCV K ST HK A_close8) as A_close.
  pose proof (s2_matloop_ok P OEND LLO LEND LOCV K ST HK A_tail) as A_matloop.
  pose proof (s2_exec3 P OEND LLO LEND LOCV K ST HK A_err A_tail A_matloop A_close) as A_match.
  pose proof (s2_litloop_ok P OEND LLO LEND LOCV K ST HK  A_match) as A_litloop.
  pose proof (s2_exec1 P OEND LLO LEND LOCV K ST HK  A_match A_litloop) as A_lit1.
  pose proof (s2_slow_ok EXE P OEND LLO LEND LOCV K ST HK HLOC A_err A_tail2) as A_slow.
  exact (s2_exec0 P OEND LLO LEND LOCV K ST HK HLOC A_slow A_lit1).
Qed.
