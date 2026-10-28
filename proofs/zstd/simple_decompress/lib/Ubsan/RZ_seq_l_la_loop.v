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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_xat RZ_seq_l_la_at RZ_seq_l_la_at2 RZ_seq_l_md_at RZ_seq_l_lf_at RZ_seq_l_la_dec RZ_seq_l_la_rl1 RZ_seq_l_la_upd RZ_seq_l_la_rl2 RZ_seq_l_la_store RZ_seq_l_la_done RZ_seq_l_lf_loop.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma la_step : forall P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P ->
  la_done P OEND LLO LEND LOCV -> (forall K', 1 <= K' < K -> la_head P OEND LLO LEND LOCV K') -> la_head P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK A_done IH.
  pose proof (la_store_ok P OEND LLO LEND LOCV K ST HK IH A_done) as A_store.
  pose proof (la_reload2 P OEND LLO LEND LOCV K ST HK A_store) as A_upd.
  pose proof (la_update P OEND LLO LEND LOCV K ST HK A_upd A_store) as A_rl1.
  pose proof (la_reload1 P OEND LLO LEND LOCV K ST HK A_rl1) as A_dec.
  exact (la_decode P OEND LLO LEND LOCV K ST HK A_dec).
Qed.

Theorem la_loop : forall P OEND LLO LEND LOCV, seql_static P OEND LLO LEND LOCV -> la_done P OEND LLO LEND LOCV ->
  forall K, 1 <= K <= y_nbSeq P -> la_head P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV ST A_done.
  assert (ALL : forall n : nat, forall K, 1 <= K <= y_nbSeq P -> K <= Z.of_nat n -> la_head P OEND LLO LEND LOCV K).
  { induction n as [|n IHn]; intros K HK HNn; [exfalso; lia|].
    apply (la_step P OEND LLO LEND LOCV K ST HK A_done). intros K' HK'. apply IHn; lia. }
  intros K HK. apply (ALL (Z.to_nat K) K HK). lia.
Qed.

(* [comment removed for export] *)
Theorem seql_loops_n : zd_execend_stmt -> forall P OEND LLO LEND LOCV,
  seql_static P OEND LLO LEND LOCV -> LOCV <> 2 -> seql_at_err P OEND LLO LEND LOCV -> lf_end P OEND LLO LEND LOCV ->
  forall K, 1 <= K <= y_nbSeq P -> la_head P OEND LLO LEND LOCV K.
Proof.
  intros EXE P OEND LLO LEND LOCV ST HN A_err A_end.
  exact (la_loop P OEND LLO LEND LOCV ST (la_done_ok P OEND LLO LEND LOCV ST (seql_nb1 P OEND LLO LEND LOCV ST) A_err (lf_loop_n EXE P OEND LLO LEND LOCV ST HN A_err A_end) (lm_all_n EXE P OEND LLO LEND LOCV ST HN A_err A_end))).
Qed.

Theorem seql_loops_s : zd_execend_stmt -> zd_execend_split_stmt -> forall P OEND LLO LEND,
  seql_static P OEND LLO LEND 2 -> seql_static P OEND (y_DCTX P + 30372) (y_DCTX P + 95908) 0 ->
  wnth (y_ws P) H5_litBufferEnd = Z_to_bv 64 LEND ->
  seql_at_err P OEND LLO LEND 2 -> seql_at_err P OEND (y_DCTX P + 30372) (y_DCTX P + 95908) 0 -> lf_end P OEND LLO LEND 2 -> lf_end P OEND (y_DCTX P + 30372) (y_DCTX P + 95908) 0 ->
  forall K, 1 <= K <= y_nbSeq P -> la_head P OEND LLO LEND 2 K.
Proof.
  intros EXE EXS P OEND LLO LEND ST1 ST2 HLBE A_err1 A_err2 A_end1 A_end2.
  exact (la_loop P OEND LLO LEND 2 ST1 (la_done_ok P OEND LLO LEND 2 ST1 (seql_nb1 P OEND LLO LEND 2 ST1) A_err1
           (lf_loop_s EXE EXS P OEND LLO LEND ST1 ST2 HLBE A_err1 A_err2 A_end1 A_end2)
           (lm_all_s EXE EXS P OEND LLO LEND ST1 ST2 HLBE A_err1 A_err2 A_end1 A_end2))).
Qed.
