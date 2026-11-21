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
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees.
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

Lemma wrap8_hi_byte : forall nb, 0 <= nb < 2 ^ 16 -> wrap8 (Z.shiftr (wrap16 nb) 8) = wrap8 (nb / 2 ^ 8).
Proof.
  intros nb H. rewrite wrap16_mod'. rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma wrap8_eqm : forall a b, a mod 2 ^ 8 = b mod 2 ^ 8 -> wrap8 a = wrap8 b.
Proof. intros a b E. rewrite !wrap8_mod'. exact E. Qed.


Lemma set_pending_pending_buf : forall s a n,
  set_pending (set_pending_buf s a) n = set_pending_buf (set_pending s n) a.
Proof. intros. reflexivity. Qed.
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

Lemma put_short_eq : forall s w,
  put_short s w =
    let s1 := set_pending_buf (set_pending s (ds_pending s + 1))
                              (arr_set (ds_pending_buf s) (ds_pending s) (wrap8 (Z.land w 255))) in
    set_pending_buf (set_pending s1 (ds_pending s + 1 + 1))
                    (arr_set (ds_pending_buf s1) (ds_pending s + 1) (wrap8 (Z.shiftr (wrap16 w) 8))).
Proof. intros. reflexivity. Qed.
