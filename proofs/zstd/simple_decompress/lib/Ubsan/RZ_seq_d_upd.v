(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_d_base RZ_seq_d_lbase RZ_seq_d_lkit RZ_seq_d_lbase2 huf411_kit_rs seqS_kit_al seqD_kit_d_upd1 seqD_kit_d_upd2.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma land_mask_lt2 : forall x nb, 0 <= nb -> 0 <= Z.land x (2^nb - 1) < 2^nb.
Proof.
  intros x nb Hn. replace (2^nb - 1) with (Z.ones nb) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.
Lemma land_mask_lt3 : forall x nb, 0 <= nb <= 62 -> 0 <= Z.land x ((2^nb + -1) mod 2^64) < 2^nb.
Proof.
  intros x nb Hn. assert (P : 0 < 2^nb) by (apply Z.pow_pos_nonneg; lia).
  assert (Q : 2^nb <= 2^62) by (apply Z.pow_le_mono_r; lia).
  rewrite Z.mod_small by lia. replace (2^nb + -1) with (2^nb - 1) by lia. apply land_mask_lt2. lia.
Qed.
(* [comment removed for export] *)
Ltac sd_land :=
  repeat match goal with
  | |- context [Z.land ?x ((2 ^ ?b + -1) mod 2 ^ 64)] =>
      let H := fresh "LND" in pose proof (land_mask_lt3 x b ltac:(lia)) as H;
      let v := fresh "lv" in set (v := Z.land x ((2 ^ b + -1) mod 2 ^ 64)) in *; clearbody v
  end.
(* [comment removed for export] *)
Ltac sd_rbf2 :=
  repeat match goal with
  | |- context [bv_unsigned ?w / 2 ^ (((-1 * ?a) mod 2 ^ 64) mod 64)] =>
      let H := fresh "RBF" in pose proof (rbf_bound_w w a ltac:(lia)) as H;
      let v := fresh "rv" in set (v := bv_unsigned w / 2 ^ (((-1 * a) mod 2 ^ 64) mod 64)) in *; clearbody v
  end.

Lemma seqd_update : forall P OEND LEND K, seqd_static P OEND LEND -> 1 <= K <= q_nbSeq P ->
  at_b93c P OEND LEND K -> at_ba80 P OEND LEND K -> at_b898 P OEND LEND K.
Proof.
  intros P OEND LEND K ST HK CONT1 CONT2.
  destruct (Z.eq_dec K 1) as [E|E].
  - exact (seqd_update_k1 P OEND LEND K ST E HK CONT2).
  - exact (seqd_update_k2 P OEND LEND K ST ltac:(lia) CONT1).
Qed.
