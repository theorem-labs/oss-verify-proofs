(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import ZdTbl.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition PZD_LL_DEFAULT : Z := 0x1084c.    (* [comment removed for export] *)
Definition PZD_OF_DEFAULT : Z := 0x10af4.    (* [comment removed for export] *)
Definition PZD_ML_DEFAULT : Z := 0x10d08.    (* [comment removed for export] *)

Lemma img_bytes_at : forall (m : word -> option byte) A (bs : list byte),
  mem_inv usegs m -> ro_bytes_b usegs A bs = true -> 0 <= A -> A + Z.of_nat (length bs) <= 2^64 -> bytes_at usegs m A bs.
Proof.
  intros m A bs MI RB H0 H1. pose proof (ro_cells_image usegs m A bs MI RB H0 H1) as [_ H].
  cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H.
Qed.

Lemma pll_default_at : forall m, mem_inv usegs m -> bytes_at usegs m PZD_LL_DEFAULT (map (Z_to_bv 8) (seq_table_bytes LL_defaultDTable)).
Proof. intros m MI. apply img_bytes_at; [exact MI | vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate]. Qed.
Lemma pof_default_at : forall m, mem_inv usegs m -> bytes_at usegs m PZD_OF_DEFAULT (map (Z_to_bv 8) (seq_table_bytes OF_defaultDTable)).
Proof. intros m MI. apply img_bytes_at; [exact MI | vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate]. Qed.
Lemma pml_default_at : forall m, mem_inv usegs m -> bytes_at usegs m PZD_ML_DEFAULT (map (Z_to_bv 8) (seq_table_bytes ML_defaultDTable)).
Proof. intros m MI. apply img_bytes_at; [exact MI | vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate]. Qed.

(* [comment removed for export] *)
Definition ptbl_seq := zd_tbl_seq usegs PZD_LL_DEFAULT PZD_OF_DEFAULT PZD_ML_DEFAULT.
Definition ptbl (HUFINV : (word -> option byte) -> Z -> word -> word -> Prop) :=
  zd_tbl usegs PZD_LL_DEFAULT PZD_OF_DEFAULT PZD_ML_DEFAULT HUFINV.

Lemma ptbl_seq_frame : forall m m' W DCTX llt mlt oft fe,
  ptbl_seq m DCTX llt mlt oft fe -> munch W m m' -> mem_inv usegs m' ->
  (forall x, DCTX + 32 <= x < DCTX + 29888 -> outside W x) -> ptbl_seq m' DCTX llt mlt oft fe.
Proof. intros. eapply (zd_tbl_seq_frame usegs _ _ _ pll_default_at pof_default_at pml_default_at); eassumption. Qed.

Section Laws.
Variable HUFINV : (word -> option byte) -> Z -> word -> word -> Prop.
Hypothesis huf_init : forall m DCTX,
  bytes_at usegs m (DCTX + 10296) (le4 (Z_to_bv 64 201326604)) -> HUFINV m DCTX (Z_to_bv 64 (DCTX + 10296)) (Z_to_bv 64 0).
Hypothesis huf_frame : forall m m' W DCTX huf le,
  HUFINV m DCTX huf le -> munch W m m' -> mem_inv usegs m -> mem_inv usegs m' ->
  (forall x, DCTX + 32 <= x < DCTX + 29888 -> outside W x) -> HUFINV m' DCTX huf le.

Lemma ptbl_init : forall m DCTX llt mlt oft,
  bytes_at usegs m (DCTX + 10296) (le4 (Z_to_bv 64 201326604)) ->
  ptbl HUFINV m DCTX llt mlt oft (Z_to_bv 64 (DCTX + 10296)) (Z_to_bv 64 0) (Z_to_bv 64 0).
Proof. intros. apply (zd_tbl_init usegs _ _ _ HUFINV huf_init). assumption. Qed.

Lemma ptbl_frame : forall m m' W DCTX llt mlt oft huf le fe,
  ptbl HUFINV m DCTX llt mlt oft huf le fe -> munch W m m' -> mem_inv usegs m -> mem_inv usegs m' ->
  (forall x, DCTX + 32 <= x < DCTX + 29888 -> outside W x) -> ptbl HUFINV m' DCTX llt mlt oft huf le fe.
Proof. intros. eapply (zd_tbl_frame usegs _ _ _ HUFINV pll_default_at pof_default_at pml_default_at huf_frame); eassumption. Qed.
End Laws.
