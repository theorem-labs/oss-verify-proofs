(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdDCtx ZdSeqTable.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import ZdTbl DrvAgree.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface AFake_iface AZ_kit AZ_globals AZ_globalsR .
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.


Section CANSEC1. Context {rc : runConstT}.

Definition APZD_LL_DEFAULT : Z := 0x218a0.   (* [comment removed for export] *)
Definition APZD_OF_DEFAULT : Z := 0x21c20.   (* [comment removed for export] *)
Definition APZD_ML_DEFAULT : Z := 0x21ee0.   (* [comment removed for export] *)

Lemma img_bytes_at : forall (m : word -> option byte) A (bs : list byte),
  mem_inv bsegs m -> ro_bytes_b bsegs A bs = true -> 0 <= A -> A + Z.of_nat (length bs) <= 2^64 -> bytes_at bsegs m A bs.
Proof.
  intros m A bs MI RB H0 H1. pose proof (ro_cells_image bsegs m A bs MI RB H0 H1) as [_ H].
  cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H.
Qed.

Lemma all_default_at : forall m, mem_inv bsegs m -> bytes_at bsegs m APZD_LL_DEFAULT (map (Z_to_bv 8) (seq_table_bytes LL_defaultDTable)).
Proof. intros m MI. apply img_bytes_at; [exact MI | vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate]. Qed.
Lemma aof_default_at : forall m, mem_inv bsegs m -> bytes_at bsegs m APZD_OF_DEFAULT (map (Z_to_bv 8) (seq_table_bytes OF_defaultDTable)).
Proof. intros m MI. apply img_bytes_at; [exact MI | vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate]. Qed.
Lemma aml_default_at : forall m, mem_inv bsegs m -> bytes_at bsegs m APZD_ML_DEFAULT (map (Z_to_bv 8) (seq_table_bytes ML_defaultDTable)).
Proof. intros m MI. apply img_bytes_at; [exact MI | vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate]. Qed.

(* [comment removed for export] *)
Definition atbl_seq := zd_tbl_seq bsegs APZD_LL_DEFAULT APZD_OF_DEFAULT APZD_ML_DEFAULT.
Definition atbl (HUFINV : (word -> option byte) -> Z -> word -> word -> Prop) :=
  zd_tbl bsegs APZD_LL_DEFAULT APZD_OF_DEFAULT APZD_ML_DEFAULT HUFINV.

Lemma atbl_seq_frame : forall m m' W DCTX llt mlt oft fe,
  atbl_seq m DCTX llt mlt oft fe -> munch W m m' -> mem_inv bsegs m' ->
  (forall x, DCTX + 32 <= x < DCTX + 29888 -> outside W x) -> atbl_seq m' DCTX llt mlt oft fe.
Proof. intros. eapply (zd_tbl_seq_frame bsegs _ _ _ all_default_at aof_default_at aml_default_at); eassumption. Qed.

Section Laws.
Variable HUFINV : (word -> option byte) -> Z -> word -> word -> Prop.
Hypothesis huf_init : forall m DCTX,
  bytes_at bsegs m (DCTX + 10296) (le4 (Z_to_bv 64 201326604)) -> HUFINV m DCTX (Z_to_bv 64 (DCTX + 10296)) (Z_to_bv 64 0).
Hypothesis huf_frame : forall m m' W DCTX huf le,
  HUFINV m DCTX huf le -> munch W m m' -> mem_inv bsegs m -> mem_inv bsegs m' ->
  (forall x, DCTX + 32 <= x < DCTX + 29888 -> outside W x) -> HUFINV m' DCTX huf le.

Lemma atbl_init : forall m DCTX llt mlt oft,
  bytes_at bsegs m (DCTX + 10296) (le4 (Z_to_bv 64 201326604)) ->
  atbl HUFINV m DCTX llt mlt oft (Z_to_bv 64 (DCTX + 10296)) (Z_to_bv 64 0) (Z_to_bv 64 0).
Proof. intros. apply (zd_tbl_init bsegs _ _ _ HUFINV huf_init). assumption. Qed.

Lemma atbl_frame : forall m m' W DCTX llt mlt oft huf le fe,
  atbl HUFINV m DCTX llt mlt oft huf le fe -> munch W m m' -> mem_inv bsegs m -> mem_inv bsegs m' ->
  (forall x, DCTX + 32 <= x < DCTX + 29888 -> outside W x) -> atbl HUFINV m' DCTX llt mlt oft huf le fe.
Proof. intros. eapply (zd_tbl_frame bsegs _ _ _ HUFINV all_default_at aof_default_at aml_default_at huf_frame); eassumption. Qed.
End Laws.
End CANSEC1.
