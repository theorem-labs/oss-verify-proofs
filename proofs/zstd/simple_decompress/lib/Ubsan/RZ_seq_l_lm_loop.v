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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_xat RZ_seq_l_md_at RZ_seq_l_lm_at RZ_seq_l_lx_at RZ_seq_l_n1_at RZ_seq_l_s1_at RZ_seq_l_e1_at RZ_seq_l_t1_at RZ_seq_l_md_dec RZ_seq_l_md_rl1 RZ_seq_l_md_upd RZ_seq_l_md_rl2 RZ_seq_l_lm_mode RZ_seq_l_lm_split RZ_seq_l_n1_all RZ_seq_l_s1_all RZ_seq_l_e1_all RZ_seq_l_n1_tail RZ_seq_l_s1_tail RZ_seq_l_e1_tail RZ_seq_l_t1 RZ_seq_l_t1_sw RZ_seq_l_t1_sw0.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma lm_step : zd_execend_stmt -> forall P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P ->
  seql_at_err P OEND LLO LEND LOCV -> lx_done P OEND LLO LEND LOCV -> lm_msplit P OEND LLO LEND LOCV K ->
  (forall K', 1 <= K' < K -> md_head P OEND LLO LEND LOCV K') -> md_head P OEND LLO LEND LOCV K.
Proof.
  intros EXE P OEND LLO LEND LOCV K ST HK A_err A_done A_msplit IH.
  pose proof (n1_tail_ok P OEND LLO LEND LOCV K ST HK A_err IH A_done) as A_ntail.
  pose proof (n1_exec_ok EXE P OEND LLO LEND LOCV K ST HK A_err A_ntail) as A_nexec.
  pose proof (lm_mnorm_ok P OEND LLO LEND LOCV K ST HK A_nexec) as A_mnorm.
  pose proof (lm_mode_ok P OEND LLO LEND LOCV K ST HK A_msplit A_mnorm) as A_exec.
  pose proof (md_reload2 P OEND LLO LEND LOCV K ST HK A_exec A_msplit A_mnorm) as A_upd.
  pose proof (md_update P OEND LLO LEND LOCV K ST HK A_upd A_exec) as A_rl1.
  pose proof (md_reload1 P OEND LLO LEND LOCV K ST HK A_rl1) as A_dec.
  exact (md_decode P OEND LLO LEND LOCV K ST HK A_dec).
Qed.

Lemma lm_msplit_vac : forall P OEND LLO LEND LOCV K, LOCV <> 2 -> lm_msplit P OEND LLO LEND LOCV K.
Proof. intros P OEND LLO LEND LOCV K HN. unfold lm_msplit. intros. exfalso. lia. Qed.

(* [comment removed for export] *)
Theorem lm_loop_n : zd_execend_stmt -> forall P OEND LLO LEND LOCV,
  seql_static P OEND LLO LEND LOCV -> LOCV <> 2 -> seql_at_err P OEND LLO LEND LOCV -> lx_done P OEND LLO LEND LOCV ->
  forall K, 1 <= K <= y_nbSeq P -> md_head P OEND LLO LEND LOCV K.
Proof.
  intros EXE P OEND LLO LEND LOCV ST HN A_err A_done.
  assert (ALL : forall n : nat, forall K, 1 <= K <= y_nbSeq P -> K <= Z.of_nat n -> md_head P OEND LLO LEND LOCV K).
  { induction n as [|n IHn]; intros K HK HNn; [exfalso; lia|].
    apply (lm_step EXE P OEND LLO LEND LOCV K ST HK A_err A_done (lm_msplit_vac P OEND LLO LEND LOCV K HN)). intros K' HK'. apply IHn; lia. }
  intros K HK. apply (ALL (Z.to_nat K) K HK). lia.
Qed.

(* [comment removed for export] *)
Lemma lm_msplit_all : zd_execend_stmt -> zd_execend_split_stmt -> forall P OEND LLO LEND K,
  seql_static P OEND LLO LEND 2 -> seql_static P OEND (y_DCTX P + 30372) (y_DCTX P + 95908) 0 -> 1 <= K <= y_nbSeq P ->
  wnth (y_ws P) H5_litBufferEnd = Z_to_bv 64 LEND ->
  seql_at_err P OEND LLO LEND 2 -> seql_at_err P OEND (y_DCTX P + 30372) (y_DCTX P + 95908) 0 -> lx_done P OEND LLO LEND 2 -> lx_done P OEND (y_DCTX P + 30372) (y_DCTX P + 95908) 0 ->
  (forall K', 1 <= K' < K -> md_head P OEND LLO LEND 2 K') -> lm_msplit P OEND LLO LEND 2 K.
Proof.
  intros EXE EXS P OEND LLO LEND K ST1 ST2 HK HLBE A_err1 A_err2 A_done1 A_done2 IH.
  assert (N02 : 0 <> 2) by lia.
  pose proof (lm_loop_n EXE P _ _ _ _ ST2 N02 A_err2 A_done2) as LOOP2.
  assert (IH2 : forall K', 1 <= K' < K -> md_head P OEND (y_DCTX P + 30372) (y_DCTX P + 95908) 0 K') by (intros K' HK'; apply LOOP2; lia).
  pose proof (e1_tail_ok P OEND (y_DCTX P + 30372) (y_DCTX P + 95908) 0 K ST2 HK eq_refl A_err2 IH2 A_done2) as A_etail.
  pose proof (e1_exec_ok EXE P OEND (y_DCTX P + 30372) (y_DCTX P + 95908) 0 K ST2 HK eq_refl eq_refl A_err2 A_etail) as A_eexec.
  pose proof (t1_sw0_ok P OEND LLO LEND K ST1 HK A_eexec) as A_sw0.
  pose proof (t1_sw_ok P OEND LLO LEND 2 K ST1 HK eq_refl A_sw0) as A_sw.
  pose proof (t1_brk_ok P OEND LLO LEND 2 K ST1 HK eq_refl A_err1 A_sw0 A_sw) as A_brk.
  pose proof (s1_tail_ok P OEND LLO LEND 2 K ST1 HK A_err1 IH A_done1) as A_stail.
  pose proof (s1_exec_ok EXS P OEND LLO LEND 2 K ST1 HK eq_refl A_err1 A_stail) as A_sexec.
  exact (lm_msplit_ok P OEND LLO LEND 2 K ST1 HK HLBE A_sexec A_brk).
Qed.

Theorem lm_loop_s : zd_execend_stmt -> zd_execend_split_stmt -> forall P OEND LLO LEND,
  seql_static P OEND LLO LEND 2 -> seql_static P OEND (y_DCTX P + 30372) (y_DCTX P + 95908) 0 ->
  wnth (y_ws P) H5_litBufferEnd = Z_to_bv 64 LEND ->
  seql_at_err P OEND LLO LEND 2 -> seql_at_err P OEND (y_DCTX P + 30372) (y_DCTX P + 95908) 0 -> lx_done P OEND LLO LEND 2 -> lx_done P OEND (y_DCTX P + 30372) (y_DCTX P + 95908) 0 ->
  forall K, 1 <= K <= y_nbSeq P -> md_head P OEND LLO LEND 2 K.
Proof.
  intros EXE EXS P OEND LLO LEND ST1 ST2 HLBE A_err1 A_err2 A_done1 A_done2.
  assert (ALL : forall n : nat, forall K, 1 <= K <= y_nbSeq P -> K <= Z.of_nat n -> md_head P OEND LLO LEND 2 K).
  { induction n as [|n IHn]; intros K HK HNn; [exfalso; lia|].
    assert (IH : forall K', 1 <= K' < K -> md_head P OEND LLO LEND 2 K') by (intros K' HK'; apply IHn; lia).
    apply (lm_step EXE P OEND LLO LEND 2 K ST1 HK A_err1 A_done1 (lm_msplit_all EXE EXS P OEND LLO LEND K ST1 ST2 HK HLBE A_err1 A_err2 A_done1 A_done2 IH) IH). }
  intros K HK. apply (ALL (Z.to_nat K) K HK). lia.
Qed.
