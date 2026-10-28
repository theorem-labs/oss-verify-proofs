(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Arr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma bk_swrap32_small : forall z, -2147483648 <= z < 2147483648 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 `div` 2) with 2147483648.
  rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma sx32_small : forall z, 0 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit by lia. apply bk_swrap32_small. lia.
Qed.

Lemma signed_small : forall x, 0 <= x < 2^63 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros x Hx. rewrite ZBridge.zb_signed, unsigned_lit by lia.
  destruct (Z.ltb_spec0 x (2^63)); lia.
Qed.

Lemma zx32_small : forall z, 0 <= z < 2^32 -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold zx32. f_equal. rewrite unsigned_lit by lia. apply Z.mod_small. lia.
Qed.

Lemma b2z_range : forall b : bool, 0 <= Z.b2z b < 2. Proof. destruct b; cbn; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithSegs.
Variable segs : list Segment.

Lemma wr_at_app : forall m A n1 n2, 0 <= n1 -> 0 <= n2 ->
  (wr_at segs m A (n1 + n2) <-> wr_at segs m A n1 /\ wr_at segs m (A + n1) n2).
Proof.
  intros m A n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). split; [split; [lia| split; [lia|]]| split; [lia| split; [lia|]]].
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (A + n1 + i) with (A + (n1 + i)) by lia. apply H. lia.
  - intros ((Ha & Hb & Hx) & (Hc & Hd & Hy)). split; [lia| split; [lia|]]. intros i Hi.
    destruct (Z_lt_ge_dec i n1) as [L|G]; [apply Hx; lia|].
    replace (A + i) with (A + n1 + (i - n1)) by lia. apply Hy. lia.
Qed.

Lemma u8arr_app : forall m A b1 b2,
  u8arr segs m A (b1 ++ b2) <-> u8arr segs m A b1 /\ u8arr segs m (A + Z.of_nat (length b1)) b2.
Proof.
  intros m A b1 b2. unfold u8arr. rewrite bytes_at_app, length_app, Nat2Z.inj_add, wr_at_app by lia. tauto.
Qed.

Lemma u64arr_u8arr : forall m A ws, u64arr segs m A ws <-> u8arr segs m A (u64s ws).
Proof.
  intros m A ws. unfold u64arr, u8arr. rewrite u64s_length.
  replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. tauto.
Qed.

Lemma u64arr_app : forall m A w1 w2,
  u64arr segs m A (w1 ++ w2) <-> u64arr segs m A w1 /\ u64arr segs m (A + 8 * Z.of_nat (length w1)) w2.
Proof.
  intros m A w1 w2. rewrite !u64arr_u8arr, u64s_app, u8arr_app, u64s_length.
  replace (Z.of_nat (8 * length w1)) with (8 * Z.of_nat (length w1)) by lia. tauto.
Qed.

Lemma u64arr_CB : forall m A ws, u64arr segs m A ws -> rw_cells segs m A [CB (8 * length ws) (u64s ws)].
Proof. intros m A ws H. apply u64arr_u8arr in H. apply rw_cells_of_u8arr in H. rewrite u64s_length in H. exact H. Qed.

Lemma CB_u64arr : forall m A n ws, rw_cells segs m A [CB n (u64s ws)] -> u64arr segs m A ws.
Proof. intros m A n ws H. apply u8arr_of_rw_cells in H. apply u64arr_u8arr. exact H. Qed.

Lemma CB_u8arr_eq : forall m A n bs bs', rw_cells segs m A [CB n bs] -> bs = bs' -> u8arr segs m A bs'.
Proof. intros m A n bs bs' H <-. eapply u8arr_of_rw_cells. exact H. Qed.

End WithSegs.

Lemma u64s_repeat0 : forall k, u64s (repeat (Z_to_bv 64 0) k) = repeat (Z_to_bv 8 0) (8 * k).
Proof.
  induction k as [|k IH]; [reflexivity|]. cbn [repeat u64s]. rewrite IH.
  replace (8 * S k)%nat with (8 + 8 * k)%nat by lia. rewrite repeat_app. f_equal.
Qed.

Lemma firstn_u64s : forall k ws, firstn (8 * k) (u64s ws) = u64s (firstn k ws).
Proof.
  induction k as [|k IH]; intros ws; [reflexivity|]. destruct ws as [|w ws]; [rewrite firstn_nil; reflexivity|].
  cbn [u64s firstn]. replace (8 * S k)%nat with (8 + 8 * k)%nat by lia.
  rewrite firstn_app, length_le8. replace (8 + 8 * k - 8)%nat with (8 * k)%nat by lia.
  rewrite firstn_all2 by (rewrite length_le8; lia). rewrite IH. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma le4_bit : forall f, 0 <= f <= 1 -> le4 (Z_to_bv 64 f) = [Z_to_bv 8 f; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Proof. intros f Hf. assert (f = 0 \/ f = 1) as [-> | ->] by lia; vm_compute; reflexivity. Qed.

Lemma zxb_small : forall f, 0 <= f < 256 -> zxb (Z_to_bv 8 f) = Z_to_bv 64 f.
Proof.
  intros f Hf. unfold zxb. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma flag_cell_split : forall segs m a (d t x n : word) f, 0 <= f <= 1 ->
  rw_cells segs m a [C8 d; C4 t; C4 x; C4 n; C4 (Z_to_bv 64 f)] ->
  rw_cells segs m a [C8 d; C4 t; C4 x; C4 n; C1 (Z_to_bv 8 f); CB 3 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]].
Proof.
  intros segs m a d t x n f Hf [[Hwf Hb] Hw]. split; [split|].
  - cbn [cells_wf cell_wf]. repeat split.
  - cbn [cells_bytes cbytes] in *. rewrite (le4_bit f Hf) in Hb. exact Hb.
  - exact Hw.
Qed.

Lemma flag_cell_join : forall segs m a (d t x n : word) f, 0 <= f <= 1 ->
  rw_cells segs m a [C8 d; C4 t; C4 x; C4 n; C1 (Z_to_bv 8 f); CB 3 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]] ->
  rw_cells segs m a [C8 d; C4 t; C4 x; C4 n; C4 (Z_to_bv 64 f)].
Proof.
  intros segs m a d t x n f Hf [[Hwf Hb] Hw]. split; [split|].
  - cbn [cells_wf cell_wf]. repeat split.
  - cbn [cells_bytes cbytes] in *. rewrite (le4_bit f Hf). exact Hb.
  - exact Hw.
Qed.

(* [comment removed for export] *)
Lemma shl32_shr30 : forall x, 0 <= x < 2^32 -> Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl x 32))) 30 = 4 * x.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. rewrite unsigned_lit by lia.
  rewrite Z.shiftr_div_pow2 by lia. replace (x * 2^32) with (4 * x * 2^30) by lia. apply Z.div_mul. lia.
Qed.
