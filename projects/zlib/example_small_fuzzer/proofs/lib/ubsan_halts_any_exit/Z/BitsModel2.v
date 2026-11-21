(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition sb_nb (s : deflate_state) (v : Z) : Z :=
  wrap16 (Z.lor (ds_bi_buf s) (Z.shiftl (wrap16 v) (ds_bi_valid s))).

Lemma send_bits_flush_eq : forall s v l, Buf_size - l < ds_bi_valid s ->
  send_bits s v l =
    upd4 s (arr_set (arr_set (ds_pending_buf s) (ds_pending s) (wrap8 (Z.land (sb_nb s v) 255)))
                    (ds_pending s + 1) (wrap8 (Z.shiftr (wrap16 (sb_nb s v)) 8)))
         (ds_pending s + 1 + 1)
         (Z.shiftr (wrap16 v) (Buf_size - ds_bi_valid s))
         (ds_bi_valid s + l - Buf_size).
Proof.
  intros s v l H. unfold send_bits, put_short, put_byte, upd4, sb_nb. cbv zeta.
  rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity.
Qed.

Lemma send_bits_keep_eq : forall s v l, ~ (Buf_size - l < ds_bi_valid s) ->
  send_bits s v l = upd4 s (ds_pending_buf s) (ds_pending s) (sb_nb s v) (ds_bi_valid s + l).
Proof.
  intros s v l H. unfold send_bits, upd4, sb_nb. cbv zeta.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
Qed.

Lemma bi_windup_eq2 : forall s, 8 < ds_bi_valid s ->
  bi_windup s =
    upd4 s (arr_set (arr_set (ds_pending_buf s) (ds_pending s) (wrap8 (Z.land (ds_bi_buf s) 255)))
                    (ds_pending s + 1) (wrap8 (Z.shiftr (wrap16 (ds_bi_buf s)) 8)))
         (ds_pending s + 1 + 1) 0 0.
Proof.
  intros s H. unfold bi_windup, put_short, put_byte, upd4. cbv zeta.
  rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity.
Qed.

Lemma bi_windup_eq1 : forall s, 0 < ds_bi_valid s <= 8 ->
  bi_windup s =
    upd4 s (arr_set (ds_pending_buf s) (ds_pending s) (wrap8 (ds_bi_buf s))) (ds_pending s + 1) 0 0.
Proof.
  intros s H. unfold bi_windup, put_byte, upd4. cbv zeta.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma bi_windup_eq0 : forall s, ds_bi_valid s <= 0 ->
  bi_windup s = upd4 s (ds_pending_buf s) (ds_pending s) 0 0.
Proof.
  intros s H. unfold bi_windup, upd4. cbv zeta.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
Qed.

Lemma bi_flush_eq16 : forall s, ds_bi_valid s = 16 ->
  bi_flush s =
    upd4 s (arr_set (arr_set (ds_pending_buf s) (ds_pending s) (wrap8 (Z.land (ds_bi_buf s) 255)))
                    (ds_pending s + 1) (wrap8 (Z.shiftr (wrap16 (ds_bi_buf s)) 8)))
         (ds_pending s + 1 + 1) 0 0.
Proof.
  intros s H. unfold bi_flush, put_short, put_byte, upd4. rewrite H. reflexivity.
Qed.

Lemma bi_flush_eq8 : forall s, 8 <= ds_bi_valid s -> ds_bi_valid s <> 16 ->
  bi_flush s =
    upd4 s (arr_set (ds_pending_buf s) (ds_pending s) (wrap8 (ds_bi_buf s))) (ds_pending s + 1)
         (Z.shiftr (ds_bi_buf s) 8) (ds_bi_valid s - 8).
Proof.
  intros s H1 H2. unfold bi_flush, put_byte, upd4. cbv zeta.
  rewrite (proj2 (Z.eqb_neq _ _) H2). rewrite (proj2 (Z.leb_le _ _) H1). reflexivity.
Qed.

Lemma bi_flush_eq0 : forall s, ds_bi_valid s < 8 ->
  bi_flush s = upd4 s (ds_pending_buf s) (ds_pending s) (ds_bi_buf s) (ds_bi_valid s).
Proof.
  intros s H. unfold bi_flush, upd4. cbv zeta.
  replace (ds_bi_valid s =? 16) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite (proj2 (Z.leb_gt _ _)) by lia. destruct s; reflexivity.
Qed.

Lemma upd4_self : forall s, upd4 s (ds_pending_buf s) (ds_pending s) (ds_bi_buf s) (ds_bi_valid s) = s.
Proof. intros s. destruct s; reflexivity. Qed.


Lemma wrap16_eqm : forall a b, a mod 2 ^ 16 = b mod 2 ^ 16 -> wrap16 a = wrap16 b.
Proof. intros a b E. rewrite !wrap16_mod'. exact E. Qed.

Lemma byte0_eq : forall e nb, e mod 2 ^ 16 = nb -> wrap8 e = wrap8 (Z.land nb 255).
Proof.
  intros e nb E. rewrite wrap8_land255. rewrite !wrap8_mod'. rewrite <- E.
  symmetry. apply mod_pow2_mod_pow2. lia.
Qed.

Lemma byte1_eq : forall e nb, e mod 2 ^ 16 = nb -> wrap8 ((e mod 2 ^ 16) / 2 ^ 8) = wrap8 (Z.shiftr (wrap16 nb) 8).
Proof.
  intros e nb E. rewrite E. rewrite wrap16_mod'.
  pose proof (Z.mod_pos_bound e (2 ^ 16) ltac:(lia)) as B. rewrite E in B.
  rewrite (Z.mod_small nb) by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma byte1_eq' : forall e nb, 0 <= e < 2 ^ 16 -> e = nb -> wrap8 (e / 2 ^ 8) = wrap8 (Z.shiftr (wrap16 nb) 8).
Proof.
  intros e nb He ->. rewrite wrap16_mod', Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma sb_nb_range : forall s v, 0 <= sb_nb s v < 2 ^ 16.
Proof. intros. unfold sb_nb. apply wrap16_range'. Qed.

Lemma shiftr_wrap16_range : forall v k, 0 <= k -> 0 <= Z.shiftr (wrap16 v) k < 2 ^ 16.
Proof.
  intros v k Hk. pose proof (wrap16_range' v). rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk).
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

Lemma send_bits_eqm : forall s v v' l, v' mod 2 ^ 16 = v mod 2 ^ 16 -> send_bits s v' l = send_bits s v l.
Proof. intros s v v' l E. apply send_bits_wrap. apply wrap16_eqm. exact E. Qed.

Lemma szwrap32_mod16 : forall x, (szwrap 32 x) mod 2 ^ 16 = x mod 2 ^ 16.
Proof.
  intros x. rewrite <- (mod_pow2_mod_pow2 (szwrap 32 x) 32 16) by lia.
  rewrite szwrap_eqm by lia. apply mod_pow2_mod_pow2. lia.
Qed.
