(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec SeqExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import FillWinMem BitsModel BitsModel2.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import SendModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.
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






Section Align.
Variable s : deflate_state.
Local Notation A := (ds_pending_buf s).
Local Notation pend := (ds_pending s).
Local Notation bb := (ds_bi_buf s).
Local Notation bv := (ds_bi_valid s).
Local Notation nb := (sb_nb s 2).
Hypothesis Hbb : 0 <= bb < 2 ^ 16.

Let Hnb : 0 <= nb < 2 ^ 16 := sb_nb_range s 2.





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





End FXG.
