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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_xat RZ_seq_l_md_at RZ_seq_l_lx_at RZ_seq_l_lf_at RZ_seq_l_n2_at RZ_seq_l_s2_at RZ_seq_l_e2_at RZ_seq_l_t2_at RZ_seq_l_lf_mode RZ_seq_l_lf_split RZ_seq_l_n2_all RZ_seq_l_s2_all RZ_seq_l_e2_all RZ_seq_l_n2_tail RZ_seq_l_s2_tail RZ_seq_l_e2_tail RZ_seq_l_t2 RZ_seq_l_t2_sw RZ_seq_l_t2_sw0 RZ_seq_l_lx_done RZ_seq_l_lm_loop.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma lf_step : zd_execend_stmt -> forall P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P ->
  seql_at_err P OEND LLO LEND LOCV -> lf_end P OEND LLO LEND LOCV -> lf_fsplit P OEND LLO LEND LOCV K ->
  (forall K', 1 <= K' < K -> lf_head P OEND LLO LEND LOCV K') -> lf_head P OEND LLO LEND LOCV K.
Proof.
  intros EXE P OEND LLO LEND LOCV K ST HK A_err A_end A_fsplit IH.
  pose proof (n2_tail_ok P OEND LLO LEND LOCV K ST HK A_err IH A_end) as A_tail.
  pose proof (n2_mtail_ok P OEND LLO LEND LOCV K ST HK A_err IH A_end) as A_mtail.
  pose proof (n2_stail_ok P OEND LLO LEND LOCV K ST HK A_err IH A_end) as A_stail.
  pose proof (n2_exec_ok EXE P OEND LLO LEND LOCV K ST HK A_err A_tail A_mtail A_stail) as A_nexec.
  pose proof (lf_fnorm_ok P OEND LLO LEND LOCV K ST HK A_nexec) as A_fnorm.
  exact (lf_mode_ok P OEND LLO LEND LOCV K ST HK A_fsplit A_fnorm).
Qed.

Lemma lf_fsplit_vac : forall P OEND LLO LEND LOCV K, LOCV <> 2 -> lf_fsplit P OEND LLO LEND LOCV K.
Proof. intros P OEND LLO LEND LOCV K HN. unfold lf_fsplit. intros. exfalso. lia. Qed.

Theorem lf_loop_n : zd_execend_stmt -> forall P OEND LLO LEND LOCV,
  seql_static P OEND LLO LEND LOCV -> LOCV <> 2 -> seql_at_err P OEND LLO LEND LOCV -> lf_end P OEND LLO LEND LOCV ->
  forall K, 1 <= K <= y_nbSeq P -> lf_head P OEND LLO LEND LOCV K.
Proof.
  intros EXE P OEND LLO LEND LOCV ST HN A_err A_end.
  assert (ALL : forall n : nat, forall K, 1 <= K <= y_nbSeq P -> K <= Z.of_nat n -> lf_head P OEND LLO LEND LOCV K).
  { induction n as [|n IHn]; intros K HK HNn; [exfalso; lia|].
    apply (lf_step EXE P OEND LLO LEND LOCV K ST HK A_err A_end (lf_fsplit_vac P OEND LLO LEND LOCV K HN)). intros K' HK'. apply IHn; lia. }
  intros K HK. apply (ALL (Z.to_nat K) K HK). lia.
Qed.

Lemma lf_fsplit_all : zd_execend_stmt -> zd_execend_split_stmt -> forall P OEND LLO LEND K,
  seql_static P OEND LLO LEND 2 -> seql_static P OEND (y_DCTX P + 30372) (y_DCTX P + 95908) 0 -> 1 <= K <= y_nbSeq P ->
  wnth (y_ws P) H5_litBufferEnd = Z_to_bv 64 LEND ->
  seql_at_err P OEND LLO LEND 2 -> seql_at_err P OEND (y_DCTX P + 30372) (y_DCTX P + 95908) 0 -> lf_end P OEND LLO LEND 2 -> lf_end P OEND (y_DCTX P + 30372) (y_DCTX P + 95908) 0 ->
  (forall K', 1 <= K' < K -> lf_head P OEND LLO LEND 2 K') -> lf_fsplit P OEND LLO LEND 2 K.
Proof.
  intros EXE EXS P OEND LLO LEND K ST1 ST2 HK HLBE A_err1 A_err2 A_end1 A_end2 IH.
  assert (N02 : 0 <> 2) by lia.
  pose proof (lf_loop_n EXE P _ _ _ _ ST2 N02 A_err2 A_end2) as LOOP2.
  assert (IH2 : forall K', 1 <= K' < K -> lf_head P OEND (y_DCTX P + 30372) (y_DCTX P + 95908) 0 K') by (intros K' HK'; apply LOOP2; lia).
  pose proof (e2_tail_ok P OEND (y_DCTX P + 30372) (y_DCTX P + 95908) 0 K ST2 HK eq_refl eq_refl A_err2 IH2 A_end2) as A_etail.
  pose proof (e2_stail_ok P OEND (y_DCTX P + 30372) (y_DCTX P + 95908) 0 K ST2 HK eq_refl eq_refl A_err2 IH2 A_end2) as A_estail.
  pose proof (e2_exec_ok EXE P OEND (y_DCTX P + 30372) (y_DCTX P + 95908) 0 K ST2 HK eq_refl eq_refl A_err2 A_etail A_estail) as A_eexec.
  pose proof (t2_sw0_ok P OEND LLO LEND K ST1 HK A_eexec) as A_sw0.
  pose proof (t2_sw_ok P OEND LLO LEND 2 K ST1 HK A_sw0) as A_sw.
  pose proof (t2_brk_ok P OEND LLO LEND 2 K ST1 HK A_err1 A_sw0 A_sw) as A_brk.
  pose proof (s2_tail_ok P OEND LLO LEND 2 K ST1 HK A_err1 IH A_end1) as A_tail.
  pose proof (s2_stail_ok P OEND LLO LEND 2 K ST1 HK A_err1 IH A_end1) as A_stail.
  pose proof (s2_tail2_ok P OEND LLO LEND 2 K ST1 HK A_err1 IH A_end1) as A_tail2.
  pose proof (s2_exec_ok EXS P OEND LLO LEND 2 K ST1 HK eq_refl A_err1 A_tail A_stail A_tail2) as A_sexec.
  exact (lf_fsplit_ok P OEND LLO LEND 2 K ST1 HK HLBE A_sexec A_brk).
Qed.

Theorem lf_loop_s : zd_execend_stmt -> zd_execend_split_stmt -> forall P OEND LLO LEND,
  seql_static P OEND LLO LEND 2 -> seql_static P OEND (y_DCTX P + 30372) (y_DCTX P + 95908) 0 ->
  wnth (y_ws P) H5_litBufferEnd = Z_to_bv 64 LEND ->
  seql_at_err P OEND LLO LEND 2 -> seql_at_err P OEND (y_DCTX P + 30372) (y_DCTX P + 95908) 0 -> lf_end P OEND LLO LEND 2 -> lf_end P OEND (y_DCTX P + 30372) (y_DCTX P + 95908) 0 ->
  forall K, 1 <= K <= y_nbSeq P -> lf_head P OEND LLO LEND 2 K.
Proof.
  intros EXE EXS P OEND LLO LEND ST1 ST2 HLBE A_err1 A_err2 A_end1 A_end2.
  assert (ALL : forall n : nat, forall K, 1 <= K <= y_nbSeq P -> K <= Z.of_nat n -> lf_head P OEND LLO LEND 2 K).
  { induction n as [|n IHn]; intros K HK HNn; [exfalso; lia|].
    assert (IH : forall K', 1 <= K' < K -> lf_head P OEND LLO LEND 2 K') by (intros K' HK'; apply IHn; lia).
    apply (lf_step EXE P OEND LLO LEND 2 K ST1 HK A_err1 A_end1 (lf_fsplit_all EXE EXS P OEND LLO LEND K ST1 ST2 HK HLBE A_err1 A_err2 A_end1 A_end2 IH) IH). }
  intros K HK. apply (ALL (Z.to_nat K) K HK). lia.
Qed.

(* [comment removed for export] *)
Lemma seql_nb1 : forall P OEND LLO LEND LOCV, seql_static P OEND LLO LEND LOCV -> 1 <= y_nbSeq P.
Proof. intros P OEND LLO LEND LOCV ST. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws]. cbn [seql_static y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in *. sd_static_open ST. lia. Qed.

Theorem lx_done_n : zd_execend_stmt -> forall P OEND LLO LEND LOCV,
  seql_static P OEND LLO LEND LOCV -> LOCV <> 2 -> seql_at_err P OEND LLO LEND LOCV -> lf_end P OEND LLO LEND LOCV -> lx_done P OEND LLO LEND LOCV.
Proof.
  intros EXE P OEND LLO LEND LOCV ST HN A_err A_end.
  exact (lx_done_ok P OEND LLO LEND LOCV ST (seql_nb1 P OEND LLO LEND LOCV ST) A_err (lf_loop_n EXE P OEND LLO LEND LOCV ST HN A_err A_end)).
Qed.

Theorem lx_done_s : zd_execend_stmt -> zd_execend_split_stmt -> forall P OEND LLO LEND,
  seql_static P OEND LLO LEND 2 -> seql_static P OEND (y_DCTX P + 30372) (y_DCTX P + 95908) 0 ->
  wnth (y_ws P) H5_litBufferEnd = Z_to_bv 64 LEND ->
  seql_at_err P OEND LLO LEND 2 -> seql_at_err P OEND (y_DCTX P + 30372) (y_DCTX P + 95908) 0 -> lf_end P OEND LLO LEND 2 -> lf_end P OEND (y_DCTX P + 30372) (y_DCTX P + 95908) 0 -> lx_done P OEND LLO LEND 2.
Proof.
  intros EXE EXS P OEND LLO LEND ST1 ST2 HLBE A_err1 A_err2 A_end1 A_end2.
  exact (lx_done_ok P OEND LLO LEND 2 ST1 (seql_nb1 P OEND LLO LEND 2 ST1) A_err1 (lf_loop_s EXE EXS P OEND LLO LEND ST1 ST2 HLBE A_err1 A_err2 A_end1 A_end2)).
Qed.

(* [comment removed for export] *)
Theorem lm_all_n : zd_execend_stmt -> forall P OEND LLO LEND LOCV,
  seql_static P OEND LLO LEND LOCV -> LOCV <> 2 -> seql_at_err P OEND LLO LEND LOCV -> lf_end P OEND LLO LEND LOCV ->
  forall K, 1 <= K <= y_nbSeq P -> md_head P OEND LLO LEND LOCV K.
Proof.
  intros EXE P OEND LLO LEND LOCV ST HN A_err A_end.
  exact (lm_loop_n EXE P OEND LLO LEND LOCV ST HN A_err (lx_done_n EXE P OEND LLO LEND LOCV ST HN A_err A_end)).
Qed.

Theorem lm_all_s : zd_execend_stmt -> zd_execend_split_stmt -> forall P OEND LLO LEND,
  seql_static P OEND LLO LEND 2 -> seql_static P OEND (y_DCTX P + 30372) (y_DCTX P + 95908) 0 ->
  wnth (y_ws P) H5_litBufferEnd = Z_to_bv 64 LEND ->
  seql_at_err P OEND LLO LEND 2 -> seql_at_err P OEND (y_DCTX P + 30372) (y_DCTX P + 95908) 0 -> lf_end P OEND LLO LEND 2 -> lf_end P OEND (y_DCTX P + 30372) (y_DCTX P + 95908) 0 ->
  forall K, 1 <= K <= y_nbSeq P -> md_head P OEND LLO LEND 2 K.
Proof.
  intros EXE EXS P OEND LLO LEND ST1 ST2 HLBE A_err1 A_err2 A_end1 A_end2.
  assert (N02 : 0 <> 2) by lia.
  exact (lm_loop_s EXE EXS P OEND LLO LEND ST1 ST2 HLBE A_err1 A_err2
           (lx_done_s EXE EXS P OEND LLO LEND ST1 ST2 HLBE A_err1 A_err2 A_end1 A_end2)
           (lx_done_n EXE P _ _ _ _ ST2 N02 A_err2 A_end2)).
Qed.
