(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate
  TreeModel FillWinModel SendModel BitsModel RefFlushPend1 RefDeflateEnd1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma land255_mod : forall x, Z.land x 255 = x mod 2 ^ 8.
Proof. intros x. change 255 with (Z.ones 8). apply Z.land_ones. lia. Qed.

Lemma land65535_mod : forall x, Z.land x 65535 = x mod 2 ^ 16.
Proof. intros x. change 65535 with (Z.ones 16). apply Z.land_ones. lia. Qed.

Lemma byte_hi_hi : forall a, 0 <= a < 2 ^ 32 -> Z.shiftr (wrap32 (Z.shiftr a 16)) 8 = a / 2 ^ 24.
Proof.
  intros a Ha. rewrite !Z.shiftr_div_pow2 by lia.
  assert (0 <= a / 2 ^ 16 < 2 ^ 32) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite wrap32_id by lia. rewrite Z.div_div by lia. reflexivity.
Qed.

Lemma byte_hi_lo : forall a, 0 <= a < 2 ^ 32 -> (Z.land (wrap32 (Z.shiftr a 16)) 255) mod 2 ^ 8 = (a / 2 ^ 16) mod 2 ^ 8.
Proof.
  intros a Ha. rewrite Z.shiftr_div_pow2 by lia.
  assert (0 <= a / 2 ^ 16 < 2 ^ 32) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite wrap32_id by lia. rewrite land255_mod. apply Z.mod_mod. lia.
Qed.

Lemma byte_lo_hi : forall a, 0 <= a -> (Z.shiftr (Z.land a 65535) 8) mod 2 ^ 8 = (a / 2 ^ 8) mod 2 ^ 8.
Proof. intros a Ha. rewrite Z.shiftr_div_pow2 by lia. rewrite land65535_mod. lia. Qed.

Lemma byte_lo_lo : forall a, 0 <= a -> (Z.land (Z.land a 65535) 255) mod 2 ^ 8 = a mod 2 ^ 8.
Proof. intros a Ha. rewrite land255_mod, land65535_mod. lia. Qed.

Lemma byte_shr : forall a k, 0 <= a -> 0 <= k -> (Z.land (Z.shiftr a k) 255) mod 2 ^ 8 = (a / 2 ^ k) mod 2 ^ 8.
Proof. intros a k Ha Hk. rewrite Z.shiftr_div_pow2 by lia. rewrite land255_mod. apply Z.mod_mod. lia. Qed.

Lemma byte_land : forall a, (Z.land a 255) mod 2 ^ 8 = a mod 2 ^ 8.
Proof. intros a. rewrite land255_mod. apply Z.mod_mod. lia. Qed.

Lemma mod64_nz : forall x, - 2 ^ 64 < x < 2 ^ 64 -> x <> 0 -> x mod 2 ^ 64 <> 0.
Proof.
  intros x Hx Hnz. destruct (Z_lt_le_dec x 0).
  - rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
  - rewrite Z.mod_small by lia. lia.
Qed.

Lemma mod64_z : forall x, x = 0 -> x mod 2 ^ 64 = 0.
Proof. intros x ->. reflexivity. Qed.

Lemma put_byte_congr : forall s c c', c mod 2 ^ 8 = c' mod 2 ^ 8 -> put_byte s c = put_byte s c'.
Proof. intros s c c' H. rewrite !put_byte_eq, !wrap8_mod, H. reflexivity. Qed.

Lemma pending_put_byte : forall s c, ds_pending (put_byte s c) = ds_pending s + 1.
Proof. intros s c. destruct s; reflexivity. Qed.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


