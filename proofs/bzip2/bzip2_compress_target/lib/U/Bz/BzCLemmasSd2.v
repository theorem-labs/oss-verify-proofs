(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCLemmas1. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCNumZ BzCLemmasSd.
Import ListNotations.

Module BzCLemmasSd3.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmas1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCNumZ OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasSd.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma put_ones_ok : forall k b, bw_ok b -> bw_ok (sm_put_ones k b) /\ bw_live (sm_put_ones k b) <= Z.max (bw_live b) 8.
Proof.
  induction k as [|k IH]; intros b OK; cbn [sm_put_ones].
  - split; [exact OK| lia].
  - destruct (IH (bsW b 1 1) (bw_ok_bsW b 1 1 OK ltac:(lia) ltac:(lia))) as [OK' L'].
    split; [exact OK'|]. pose proof (bsW_live_le b 1 1 OK ltac:(lia) ltac:(lia)). lia.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
End BzCLemmasSd3.

Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition ROW16 (inUse : zarr) (i : Z) : Z := sm_in16_row 16 inUse i 0 0.

Lemma ROW16_01 : forall inUse i, ROW16 inUse i = 0 \/ ROW16 inUse i = 1.
Proof. intros. unfold ROW16. apply in16_row_01. left; reflexivity. Qed.

Lemma sm_in16_get : forall n in16 inUse i0 k,
  zget (sm_in16 n in16 inUse i0) k = if (i0 <=? k) && (k <? i0 + Z.of_nat n) then ROW16 inUse k else zget in16 k.
Proof.
  induction n as [|n IH]; intros in16 inUse i0 k.
  - cbn [sm_in16]. replace ((i0 <=? k) && (k <? i0 + Z.of_nat 0%nat)) with false; [reflexivity|].
    symmetry. apply andb_false_iff. destruct (Z.leb_spec i0 k); [right; apply Z.ltb_ge; lia| left; reflexivity].
  - rewrite in16_S. rewrite IH. unfold ROW16.
    destruct (Z.leb_spec (i0 + 1) k), (Z.ltb_spec k (i0 + 1 + Z.of_nat n)), (Z.leb_spec i0 k), (Z.ltb_spec k (i0 + Z.of_nat (S n))); cbn [andb]; try lia;
      first [ rewrite zget_zset_other by lia; reflexivity | replace k with i0 by lia; rewrite zget_zset_same; reflexivity ].
Qed.
Lemma smD_in16_row : forall in160 inUse k, 0 <= k < 16 -> zget (sm_in16 16 in160 inUse 0) k = ROW16 inUse k.
Proof.
  intros. rewrite sm_in16_get. replace ((0 <=? k) && (k <? 0 + Z.of_nat 16)) with true; [reflexivity|].
  symmetry. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
