(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import MState Mem Cells Step Frame Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Lemma wr_at_app : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
  wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
  intros segs m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply HB. lia.
Qed.

Lemma rw_cells_app : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_app by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
    rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

Lemma bytes_eq_of_unsigned : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|b1 l1 IH]; intros [|b2 l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

Lemma rw_cells_recell_mid : forall segs m A pre mid post mid',
  rw_cells segs m A (pre ++ mid ++ post) -> cells_wf mid' ->
  map bv_unsigned (cells_bytes mid') = map bv_unsigned (cells_bytes mid) ->
  rw_cells segs m A (pre ++ mid' ++ post).
Proof.
  intros segs m A pre mid post mid' RW WF E.
  apply bytes_eq_of_unsigned in E.
  destruct RW as [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W23]. apply cells_wf_app in W23. destruct W23 as [W2 W3].
  assert (SZ : cells_size mid' = cells_size mid).
  { rewrite <- (cells_bytes_length mid' WF), <- (cells_bytes_length mid W2), E. reflexivity. }
  split; [split|].
  - apply cells_wf_app. split; [exact W1|]. apply cells_wf_app. split; assumption.
  - rewrite !cells_bytes_app in *. rewrite E. exact Hb.
  - rewrite !cells_size_app in *. rewrite SZ. exact Hw.
Qed.

Lemma Z_to_le_bytes_add : forall a b z, Z_to_le_bytes (a + b) z = Z_to_le_bytes a z ++ Z_to_le_bytes b (Z.shiftr z (8 * Z.of_nat a)).
Proof.
  induction a as [|a IH]; intros b z; cbn [Z_to_le_bytes Nat.add app].
  - rewrite Z.shiftr_0_r. reflexivity.
  - f_equal. rewrite IH. f_equal. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

Lemma le8_small_split : forall v, (0 <= v < 2^32)%Z -> le8 (Z_to_bv 64 v) = le4 (Z_to_bv 64 v) ++ le4 (Z_to_bv 64 0).
Proof.
  intros v Hv. unfold le8, le4, word_to_le_bytes. rewrite !unsigned_lit by lia.
  change 8%nat with (4 + 4)%nat at 1. rewrite Z_to_le_bytes_add. f_equal.
  change (8 * Z.of_nat 4)%Z with 32%Z. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_C8_C4C4 : forall segs m A pre post v,
  rw_cells segs m A (pre ++ C8 (Z_to_bv 64 v) :: post) -> (0 <= v < 2^32)%Z ->
  rw_cells segs m A (pre ++ C4 (Z_to_bv 64 v) :: C4 (Z_to_bv 64 0) :: post).
Proof.
  intros segs m A pre post v H Hv.
  change (pre ++ C4 (Z_to_bv 64 v) :: C4 (Z_to_bv 64 0) :: post) with (pre ++ [C4 (Z_to_bv 64 v); C4 (Z_to_bv 64 0)] ++ post).
  eapply rw_cells_recell_mid with (mid := [C8 (Z_to_bv 64 v)]); [exact H | cbv; repeat split |].
  cbn [cells_bytes cbytes app]. rewrite app_nil_r. rewrite (le8_small_split v Hv). reflexivity.
Qed.
Lemma rw_cells_C4C4_C8 : forall segs m A pre post v,
  rw_cells segs m A (pre ++ C4 (Z_to_bv 64 v) :: C4 (Z_to_bv 64 0) :: post) -> (0 <= v < 2^32)%Z ->
  rw_cells segs m A (pre ++ C8 (Z_to_bv 64 v) :: post).
Proof.
  intros segs m A pre post v H Hv.
  change (pre ++ C8 (Z_to_bv 64 v) :: post) with (pre ++ [C8 (Z_to_bv 64 v)] ++ post).
  eapply rw_cells_recell_mid with (mid := [C4 (Z_to_bv 64 v); C4 (Z_to_bv 64 0)]); [exact H | cbv; repeat split |].
  cbn [cells_bytes cbytes app]. rewrite app_nil_r. rewrite (le8_small_split v Hv). reflexivity.
Qed.
End CANSEC1.
