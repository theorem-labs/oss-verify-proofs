(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_d_base RZ_seq_d_lbase RZ_seq_d_lbase2 RZ_seq_d_lbase3 RZ_seq_d_dec RZ_seq_d_rl1 RZ_seq_d_rl2 RZ_seq_d_upd RZ_seq_d_exlit RZ_seq_d_exmat RZ_seq_d_exclose RZ_seq_d_slow RZ_seq_d_tail RZ_seq_d_exit.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma seqd_loop_step : zd_execend_stmt -> forall P OEND LEND K,
  seqd_static P OEND LEND -> seqd_ranges P -> seqd_sep P -> 1 <= K <= q_nbSeq P ->
  (forall K', 1 <= K' < K -> at_head P OEND LEND K') -> at_head P OEND LEND K.
Proof.
  intros EXE P OEND LEND K ST RG SEP HK IH.
  pose proof (seqd_bfa4 P OEND LEND K ST RG) as A_bfa4.
  pose proof (seqd_exit P OEND LEND K ST RG SEP) as A_exit.
  pose proof (seqd_tail P OEND LEND K ST HK A_bfa4 IH A_exit) as A_bb64.
  pose proof (seqd_closeloop P OEND LEND K ST HK A_bb64) as A_be48.
  pose proof (seqd_exec7 P OEND LEND K ST HK A_bb64 A_be48) as A_be28.
  pose proof (seqd_exec6 P OEND LEND K ST HK A_be28) as A_bca4.
  pose proof (seqd_matloop P OEND LEND K ST HK A_bb64) as A_bb28.
  pose proof (seqd_exec3 P OEND LEND K ST HK A_bfa4 A_bb64 A_bb28 A_bca4) as A_bab4.
  pose proof (seqd_litloop P OEND LEND K ST HK A_bab4) as A_bc74.
  pose proof (seqd_exec1 P OEND LEND K ST HK A_bab4 A_bc74) as A_baac.
  pose proof (seqd_slow EXE P OEND LEND K ST HK A_bb64) as A_bb80.
  pose proof (seqd_exec0 P OEND LEND K ST HK A_bb80 A_baac) as A_ba80.
  pose proof (seqd_reload2 P OEND LEND K ST HK A_ba80) as A_b93c.
  pose proof (seqd_update P OEND LEND K ST HK A_b93c A_ba80) as A_b898.
  pose proof (seqd_reload1 P OEND LEND K ST HK A_b898) as A_b884.
  exact (seqd_decode P OEND LEND K ST HK A_b884).
Qed.

Theorem seqd_loop : zd_execend_stmt -> forall P OEND LEND,
  seqd_static P OEND LEND -> seqd_ranges P -> seqd_sep P ->
  forall K, 1 <= K <= q_nbSeq P -> at_head P OEND LEND K.
Proof.
  intros EXE P OEND LEND ST RG SEP.
  assert (ALL : forall n : nat, forall K, 1 <= K <= q_nbSeq P -> K <= Z.of_nat n -> at_head P OEND LEND K).
  { induction n as [|n IHn]; intros K HK HN; [exfalso; lia|].
    apply (seqd_loop_step EXE P OEND LEND K ST RG SEP HK). intros K' HK'. apply IHn; lia. }
  intros K HK. apply (ALL (Z.to_nat K) K HK). lia.
Qed.
