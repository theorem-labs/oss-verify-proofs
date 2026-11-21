(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Lemma upd4_pending_buf : forall s A P B V, ds_pending_buf (upd4 s A P B V) = A.
Proof. intros. reflexivity. Qed.
Lemma upd4_pending : forall s A P B V, ds_pending (upd4 s A P B V) = P.
Proof. intros. reflexivity. Qed.
Lemma upd4_bi_buf : forall s A P B V, ds_bi_buf (upd4 s A P B V) = B.
Proof. intros. reflexivity. Qed.
Lemma upd4_bi_valid : forall s A P B V, ds_bi_valid (upd4 s A P B V) = V.
Proof. intros. reflexivity. Qed.
Lemma upd4_upd4 : forall s A P B V A' P' B' V',
  upd4 (upd4 s A P B V) A' P' B' V' = upd4 s A' P' B' V'.
Proof. intros. destruct s; reflexivity. Qed.

Lemma sb_nb_0 : forall s, 0 <= ds_bi_buf s < 2 ^ 16 -> sb_nb s 0 = ds_bi_buf s.
Proof.
  intros s H. unfold sb_nb. change (wrap16 0) with 0. rewrite Z.shiftl_0_l, Z.lor_0_r.
  rewrite wrap16_mod'. apply Z.mod_small. exact H.
Qed.

Lemma shiftr_wrap16_0 : forall k, Z.shiftr (wrap16 0) k = 0.
Proof. intros k. change (wrap16 0) with 0. apply Z.shiftr_0_l. Qed.


Lemma static_ltree_fc_256 : arr_get static_ltree_fc END_BLOCK = 0.
Proof. vm_compute. reflexivity. Qed.
Lemma static_ltree_dl_256 : arr_get static_ltree_dl END_BLOCK = 7.
Proof. vm_compute. reflexivity. Qed.

Lemma tr_align_unfold : forall s, tr_align s = bi_flush (send_bits (send_bits s 2 3) 0 7).
Proof.
  intros s. unfold tr_align, send_code. rewrite static_ltree_fc_256, static_ltree_dl_256. reflexivity.
Qed.

Section Align.
Variable s : deflate_state.
Local Notation A := (ds_pending_buf s).
Local Notation pend := (ds_pending s).
Local Notation bb := (ds_bi_buf s).
Local Notation bv := (ds_bi_valid s).
Local Notation nb := (sb_nb s 2).
Hypothesis Hbb : 0 <= bb < 2 ^ 16.

Let Hnb : 0 <= nb < 2 ^ 16 := sb_nb_range s 2.

Lemma tr_align_eq1 : 0 <= bv < 6 ->
  tr_align s = upd4 s (arr_set A pend (wrap8 nb)) (pend + 1) (Z.shiftr nb 8) (bv + 2).
Proof.
  intros H. rewrite tr_align_unfold.
  rewrite (send_bits_keep_eq s 2 3) by (unfold Buf_size; lia).
  rewrite send_bits_keep_eq by (rewrite upd4_bi_valid; unfold Buf_size; lia).
  rewrite sb_nb_0 by (rewrite upd4_bi_buf; exact Hnb).
  rewrite upd4_pending_buf, upd4_pending, upd4_bi_buf, upd4_bi_valid, upd4_upd4.
  rewrite bi_flush_eq8 by (rewrite upd4_bi_valid; lia).
  rewrite upd4_pending_buf, upd4_pending, upd4_bi_buf, upd4_bi_valid, upd4_upd4.
  f_equal. lia.
Qed.

Lemma tr_align_eq2 : bv = 6 ->
  tr_align s = upd4 s (arr_set (arr_set A pend (wrap8 (Z.land nb 255))) (pend + 1) (wrap8 (Z.shiftr (wrap16 nb) 8)))
                      (pend + 1 + 1) 0 0.
Proof.
  intros H. rewrite tr_align_unfold.
  rewrite (send_bits_keep_eq s 2 3) by (unfold Buf_size; lia).
  rewrite send_bits_keep_eq by (rewrite upd4_bi_valid; unfold Buf_size; lia).
  rewrite sb_nb_0 by (rewrite upd4_bi_buf; exact Hnb).
  rewrite upd4_pending_buf, upd4_pending, upd4_bi_buf, upd4_bi_valid, upd4_upd4.
  rewrite bi_flush_eq16 by (rewrite upd4_bi_valid; lia).
  rewrite upd4_pending_buf, upd4_pending, upd4_bi_buf, upd4_upd4.
  reflexivity.
Qed.

Lemma tr_align_eq3 : 7 <= bv <= 13 ->
  tr_align s = upd4 s (arr_set (arr_set A pend (wrap8 (Z.land nb 255))) (pend + 1) (wrap8 (Z.shiftr (wrap16 nb) 8)))
                      (pend + 1 + 1) 0 (bv - 6).
Proof.
  intros H. rewrite tr_align_unfold.
  rewrite (send_bits_keep_eq s 2 3) by (unfold Buf_size; lia).
  rewrite send_bits_flush_eq by (rewrite upd4_bi_valid; unfold Buf_size; lia).
  rewrite sb_nb_0 by (rewrite upd4_bi_buf; exact Hnb).
  rewrite upd4_pending_buf, upd4_pending, upd4_bi_buf, upd4_bi_valid, upd4_upd4.
  rewrite (wrap16_mod' nb), (Z.mod_small nb) by exact Hnb.
  rewrite shiftr_wrap16_0.
  rewrite bi_flush_eq0 by (rewrite upd4_bi_valid; unfold Buf_size; lia).
  rewrite upd4_pending_buf, upd4_pending, upd4_bi_buf, upd4_bi_valid, upd4_upd4.
  f_equal. unfold Buf_size. lia.
Qed.

Lemma tr_align_eq4 : 14 <= bv <= 16 ->
  let b1 := Z.shiftr (wrap16 2) (Buf_size - bv) in
  tr_align s = upd4 s (arr_set (arr_set (arr_set A pend (wrap8 (Z.land nb 255))) (pend + 1) (wrap8 (Z.shiftr (wrap16 nb) 8)))
                               (pend + 1 + 1) (wrap8 b1))
                      (pend + 1 + 1 + 1) (Z.shiftr b1 8) (bv - 14).
Proof.
  intros H. cbv zeta. rewrite tr_align_unfold.
  pose proof (shiftr_wrap16_range 2 (Buf_size - bv) ltac:(unfold Buf_size; lia)) as Hb1.
  rewrite (send_bits_flush_eq s 2 3) by (unfold Buf_size; lia).
  rewrite send_bits_keep_eq by (rewrite upd4_bi_valid; unfold Buf_size; lia).
  rewrite sb_nb_0 by (rewrite upd4_bi_buf; exact Hb1).
  rewrite upd4_pending_buf, upd4_pending, upd4_bi_buf, upd4_bi_valid, upd4_upd4.
  rewrite bi_flush_eq8; rewrite ?upd4_bi_valid; [| unfold Buf_size; lia | unfold Buf_size; lia].
  rewrite upd4_pending_buf, upd4_pending, upd4_bi_buf, upd4_upd4.
  f_equal. unfold Buf_size. lia.
Qed.

End Align.


Definition tsb_hA (s : deflate_state) (last : Z) : arr :=
  let nb := sb_nb s last in
  if ds_bi_valid s <=? 5 then arr_set (ds_pending_buf s) (ds_pending s) (wrap8 nb)
  else if ds_bi_valid s <=? 13 then
    arr_set (arr_set (ds_pending_buf s) (ds_pending s) (wrap8 (Z.land nb 255)))
            (ds_pending s + 1) (wrap8 (Z.shiftr (wrap16 nb) 8))
  else
    arr_set (arr_set (arr_set (ds_pending_buf s) (ds_pending s) (wrap8 (Z.land nb 255)))
                     (ds_pending s + 1) (wrap8 (Z.shiftr (wrap16 nb) 8)))
            (ds_pending s + 1 + 1) (wrap8 (Z.shiftr (wrap16 last) (Buf_size - ds_bi_valid s))).

Definition tsb_hP (s : deflate_state) : Z :=
  if ds_bi_valid s <=? 5 then ds_pending s + 1
  else if ds_bi_valid s <=? 13 then ds_pending s + 1 + 1
  else ds_pending s + 1 + 1 + 1.

Lemma tsb_head_eq : forall s last, 0 <= ds_bi_valid s <= 16 -> 0 <= ds_bi_buf s < 2 ^ 16 ->
  bi_windup (send_bits s last 3) = upd4 s (tsb_hA s last) (tsb_hP s) 0 0.
Proof.
  intros s last Hbv Hbb. unfold tsb_hA, tsb_hP.
  pose proof (sb_nb_range s last) as Hnb.
  destruct (Z.leb_spec (ds_bi_valid s) 5) as [C1|C1].
  - rewrite send_bits_keep_eq by (unfold Buf_size; lia).
    rewrite bi_windup_eq1 by (rewrite upd4_bi_valid; lia).
    rewrite upd4_pending_buf, upd4_pending, upd4_bi_buf, upd4_upd4. reflexivity.
  - destruct (Z.leb_spec (ds_bi_valid s) 13) as [C2|C2].
    + rewrite send_bits_keep_eq by (unfold Buf_size; lia).
      rewrite bi_windup_eq2 by (rewrite upd4_bi_valid; lia).
      rewrite upd4_pending_buf, upd4_pending, upd4_bi_buf, upd4_upd4. reflexivity.
    + rewrite send_bits_flush_eq by (unfold Buf_size; lia).
      rewrite bi_windup_eq1 by (rewrite upd4_bi_valid; unfold Buf_size; lia).
      rewrite upd4_pending_buf, upd4_pending, upd4_bi_buf, upd4_upd4.
      pose proof (shiftr_wrap16_range last (Buf_size - ds_bi_valid s) ltac:(unfold Buf_size; lia)) as Hb1.
      reflexivity.
Qed.

Lemma tsb_hP_range : forall s, ds_pending s + 1 <= tsb_hP s <= ds_pending s + 3.
Proof. intros s. unfold tsb_hP. destruct (_ <=? 5); [lia|]. destruct (_ <=? 13); lia. Qed.

Lemma tsb_hA_len : forall s last, arr_len (tsb_hA s last) = arr_len (ds_pending_buf s).
Proof.
  intros s last. unfold tsb_hA. destruct (_ <=? 5); [|destruct (_ <=? 13)]; rewrite ?arr_len_set; reflexivity.
Qed.

Definition tsb_lenA (A1 : arr) (P1 len : Z) : arr :=
  arr_set (arr_set (arr_set (arr_set A1 P1 (wrap8 (Z.land (wrap16 len) 255)))
                            (P1 + 1) (wrap8 (Z.shiftr (wrap16 (wrap16 len)) 8)))
                   (P1 + 1 + 1) (wrap8 (Z.land (wrap16 (Z.lnot len)) 255)))
          (P1 + 1 + 1 + 1) (wrap8 (Z.shiftr (wrap16 (wrap16 (Z.lnot len))) 8)).

Definition tsb_tail (s : deflate_state) (A1 : arr) (P1 : Z) (buf : option Z) (len : Z) : deflate_state :=
  let A2 := tsb_lenA A1 P1 len in
  let A3 := if negb (len =? 0)
            then match buf with
                 | Some off => arr_blit A2 (P1 + 1 + 1 + 1 + 1) (ds_window s) off len
                 | None => A2
                 end
            else A2 in
  upd4 s A3 (P1 + 1 + 1 + 1 + 1 + len) 0 0.

Lemma tr_stored_block_eq : forall s buf len last, 0 <= ds_bi_valid s <= 16 -> 0 <= ds_bi_buf s < 2 ^ 16 ->
  tr_stored_block s buf len last = tsb_tail s (tsb_hA s last) (tsb_hP s) buf len.
Proof.
  intros s buf len last Hbv Hbb. unfold tr_stored_block.
  change (Z.shiftl STORED_BLOCK 1 + last) with (0 + last). rewrite Z.add_0_l.
  rewrite tsb_head_eq by assumption.
  unfold tsb_tail, tsb_lenA, put_short, put_byte, upd4. dsred.
  destruct (negb (len =? 0)); [destruct buf|]; reflexivity.
Qed.

Lemma tsb_tail_pending : forall s A1 P1 buf len, ds_pending (tsb_tail s A1 P1 buf len) = P1 + 1 + 1 + 1 + 1 + len.
Proof. intros. reflexivity. Qed.

Lemma tsb_b0 : forall len, wrap8 (len mod 2 ^ 8) = wrap8 (Z.land (wrap16 len) 255).
Proof.
  intros len. rewrite wrap8_land255. rewrite !wrap8_mod', wrap16_mod'.
  rewrite Z.mod_mod by lia. symmetry. apply mod_pow2_mod_pow2. lia.
Qed.

Lemma tsb_b1 : forall len, wrap8 (len mod 2 ^ 16 / 2 ^ 8) = wrap8 (Z.shiftr (wrap16 (wrap16 len)) 8).
Proof.
  intros len. rewrite !wrap16_mod'. rewrite Z.mod_mod by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma lnot_mod_mod : forall a n, 0 <= n -> (Z.lnot (a mod 2 ^ n)) mod 2 ^ n = (Z.lnot a) mod 2 ^ n.
Proof.
  intros a n Hn. rewrite !Z.lnot_eq_pred_opp.
  pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) Hn) as Hp.
  replace (- (a mod 2 ^ n) - 1) with (0 - (a mod 2 ^ n + 1)) by lia.
  replace (- a - 1) with (0 - (a + 1)) by lia.
  rewrite (Zminus_mod 0 (a mod 2 ^ n + 1)), (Zminus_mod 0 (a + 1)). f_equal. f_equal.
  rewrite <- (Z.add_mod_idemp_l a 1 (2 ^ n)) by lia. reflexivity.
Qed.

Lemma tsb_b2 : forall len, wrap8 (Z.lxor (len mod 2 ^ 8) (-1)) = wrap8 (Z.land (wrap16 (Z.lnot len)) 255).
Proof.
  intros len. rewrite Z.lxor_m1_r. rewrite wrap8_land255. rewrite !wrap8_mod', wrap16_mod'.
  rewrite lnot_mod_mod by lia. symmetry. apply mod_pow2_mod_pow2. lia.
Qed.

Lemma tsb_b3 : forall len,
  wrap8 ((Z.lxor (len mod 2 ^ 16) (-1)) mod 2 ^ 32 / 2 ^ 8) = wrap8 (Z.shiftr (wrap16 (wrap16 (Z.lnot len))) 8).
Proof.
  intros len. rewrite Z.lxor_m1_r. rewrite !wrap8_mod', !wrap16_mod'. rewrite Z.mod_mod by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite <- (lnot_mod_mod len 16) by lia.
  set (x := Z.lnot (len mod 2 ^ 16)).
  rewrite <- !Z.shiftr_div_pow2 by lia. rewrite <- !Z.land_ones by lia.
  apply Z.bits_inj'. intros n Hn.
  rewrite !Z.land_spec, !Z.shiftr_spec, !Z.land_spec by lia.
  rewrite !Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec n 8); cbn [andb]; [|rewrite !Bool.andb_false_r; reflexivity].
  rewrite !Bool.andb_true_r.
  destruct (Z.ltb_spec (n + 8) 32), (Z.ltb_spec (n + 8) 16); cbn [andb]; try lia; reflexivity.
Qed.
