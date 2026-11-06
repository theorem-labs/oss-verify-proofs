(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec S2B2BStmt.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLia.
Section ACeilS1. Context {ACEIL__ : ACeil}.


Lemma bz_crc_table_bytes_eq : bz_crc_table_bytes = crc_table_bytes.
Proof. reflexivity. Qed.
Lemma bz_rnums_table_bytes_eq : bz_rnums_table_bytes = rnums_table_bytes.
Proof. reflexivity. Qed.

Section Conv.
  Variable segs : list Segment.
  Lemma crc_tab_u32arr : forall m A, rw_cells segs m A [CB CRC_BYTES crc_table_bytes] -> u32arr segs m A crc_words.
  Proof. rewrite <- bz_crc_table_bytes_eq. intros m A H. eapply cb_u32arr; [apply crc_words_bytes| reflexivity| exact H]. Qed.
  Lemma crc_tab_cells : forall m A, u32arr segs m A crc_words -> rw_cells segs m A [CB CRC_BYTES crc_table_bytes].
  Proof. rewrite <- bz_crc_table_bytes_eq. intros m A H. eapply u32arr_cb; [apply crc_words_bytes| reflexivity| exact H]. Qed.
  Lemma rnums_tab_u32arr : forall m A, rw_cells segs m A [CB RNUMS_BYTES rnums_table_bytes] -> u32arr segs m A rnums_words.
  Proof. rewrite <- bz_rnums_table_bytes_eq. intros m A H. eapply cb_u32arr; [apply rnums_words_bytes| reflexivity| exact H]. Qed.
  Lemma rnums_tab_cells : forall m A, u32arr segs m A rnums_words -> rw_cells segs m A [CB RNUMS_BYTES rnums_table_bytes].
  Proof. rewrite <- bz_rnums_table_bytes_eq. intros m A H. eapply u32arr_cb; [apply rnums_words_bytes| reflexivity| exact H]. Qed.
End Conv.

End ACeilS1.
