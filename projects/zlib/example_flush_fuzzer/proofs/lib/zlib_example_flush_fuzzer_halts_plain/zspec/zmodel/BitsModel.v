(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZIface DeflateState Trees FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma lor_mod_pow2 : forall a b n, 0 <= n ->
  (Z.lor a b) mod 2 ^ n = Z.lor (a mod 2 ^ n) (b mod 2 ^ n).
Proof.
  intros a b n Hn. rewrite <- !Z.land_ones by lia. apply Z.land_lor_distr_l.
Qed.

Lemma mod_pow2_mod_pow2 : forall x m n, 0 <= n <= m -> (x mod 2 ^ m) mod 2 ^ n = x mod 2 ^ n.
Proof.
  intros x m n H. apply Z.mod_mod_divide.
  exists (2 ^ (m - n)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma wrap16_mod' : forall z, wrap16 z = z mod 2 ^ 16.
Proof. intros. rewrite wrap16_mod. reflexivity. Qed.
Lemma wrap8_mod' : forall z, wrap8 z = z mod 2 ^ 8.
Proof. intros. rewrite wrap8_mod. reflexivity. Qed.

Lemma wrap8_land255 : forall w, wrap8 (Z.land w 255) = wrap8 w.
Proof. intros w. unfold wrap8. rewrite <- Z.land_assoc. rewrite Z.land_diag. reflexivity. Qed.



Lemma pending_buf_set_pending : forall s n, ds_pending_buf (set_pending s n) = ds_pending_buf s.
Proof. intros. reflexivity. Qed.
Lemma pending_set_pending_buf : forall s a, ds_pending (set_pending_buf s a) = ds_pending s.
Proof. intros. reflexivity. Qed.
Lemma pending_buf_set_bi_buf : forall s v, ds_pending_buf (set_bi_buf s v) = ds_pending_buf s.
Proof. intros. reflexivity. Qed.
Lemma pending_set_bi_buf : forall s v, ds_pending (set_bi_buf s v) = ds_pending s.
Proof. intros. reflexivity. Qed.

Lemma put_byte_eq : forall s c,
  put_byte s c = set_pending_buf (set_pending s (ds_pending s + 1))
                                 (arr_set (ds_pending_buf s) (ds_pending s) (wrap8 c)).
Proof. intros. reflexivity. Qed.

