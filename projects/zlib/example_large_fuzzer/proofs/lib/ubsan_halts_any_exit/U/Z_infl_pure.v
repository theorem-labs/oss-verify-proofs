(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface ZChecksum AdlerModel DeflateLz InflateState InflateArms RefInflateArmLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma NEEDBITS_have1 : forall n s c r, 0 <= ir_have r <= 1 ->
  NEEDBITS n (mkW s c r)
  = if ir_bits r <? n then
      if ir_have r =? 0 then ALeave (mkW s c r)
      else if ir_bits (pullr c r) <? n then ALeave (mkW s c (pullr c r)) else ARun tt (mkW s c (pullr c r))
    else ARun tt (mkW s c r).
Proof.
  intros n s c r Hh. unfold NEEDBITS. rewrite NEEDBITS_k_S.
  destruct (ir_bits r <? n); [|reflexivity].
  destruct (Z.eqb_spec (ir_have r) 0) as [E|NE]; [reflexivity|].
  rewrite NEEDBITS_k_S. destruct (ir_bits (pullr c r) <? n); [|reflexivity].
  assert (H1 : ir_have r = 1) by lia.
  unfold pullr at 1. cbn [ir_have]. rewrite H1. reflexivity.
Qed.

Lemma pullr_hold : forall c r, 0 < ir_have r < 2^32 -> 0 <= ir_bits r <= 56 -> 0 <= ir_hold r < 2 ^ ir_bits r ->
  0 <= arr_get (ic_input c) (ir_next r) < 256 ->
  ir_hold (pullr c r) = ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r.
Proof. intros c r H1 H2 H3 H4. exact (proj1 (proj2 (proj2 (proj2 (proj2 (pullr_facts c r H1 H2 H3 H4)))))). Qed.
Lemma pullr_bits : forall c r, 0 <= ir_bits r <= 56 -> ir_bits (pullr c r) = ir_bits r + 8.
Proof. intros c r H. unfold pullr. cbn [ir_bits]. apply wrap32_id. lia. Qed.
Lemma pullr_have : forall c r, 0 < ir_have r < 2^32 -> ir_have (pullr c r) = ir_have r - 1.
Proof. intros c r H. unfold pullr. cbn [ir_have]. apply wrap32_id. lia. Qed.
Lemma pullr_next : forall c r, ir_next (pullr c r) = ir_next r + 1. Proof. reflexivity. Qed.
Lemma pullr_put : forall c r, ir_put (pullr c r) = ir_put r. Proof. reflexivity. Qed.
Lemma pullr_left : forall c r, ir_left (pullr c r) = ir_left r. Proof. reflexivity. Qed.
Lemma pullr_in : forall c r, ir_in (pullr c r) = ir_in r. Proof. reflexivity. Qed.
Lemma pullr_out : forall c r, ir_out (pullr c r) = ir_out r. Proof. reflexivity. Qed.
Lemma pullr_ret : forall c r, ir_ret (pullr c r) = ir_ret r. Proof. reflexivity. Qed.

Lemma lor8_small : forall b, 0 <= b < 8 -> Z.lor b 8 = b + 8.
Proof.
  intros b H. assert (C : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7) by lia.
  destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; reflexivity.
Qed.

Lemma land63_small : forall b, 0 <= b < 64 -> Z.land b 63 = b.
Proof. intros b H. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma pull_shift : forall b bits, 0 <= b < 256 -> 0 <= bits <= 56 ->
  Z.shiftl (bv_unsigned (Z_to_bv 8 b)) (Z.land bits 63) = b * 2 ^ bits.
Proof.
  intros b bits Hb Hbits. rewrite land63_small by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma pull_hold_range : forall b bits hold, 0 <= b < 256 -> 0 <= bits <= 56 -> 0 <= hold < 2 ^ bits ->
  0 <= hold + b * 2 ^ bits < 2 ^ (bits + 8).
Proof. intros b bits hold Hb Hbits Hh. rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256. nia. Qed.

Ltac pullr_rw c r :=
  rewrite ?(pullr_next c r), ?(pullr_put c r), ?(pullr_left c r), ?(pullr_in c r), ?(pullr_out c r), ?(pullr_ret c r);
  rewrite ?(pullr_have c r), ?(pullr_bits c r), ?(pullr_hold c r) by (first [assumption | lia]).

Lemma land1_mod : forall h, Z.land h 1 = h mod 2 ^ 1.
Proof. intros h. change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma type_bits : forall h, 0 <= h < 2^64 ->
  Z.shiftr (Z.land (Z.shiftl h 61) 18446744073709551615) 62 = (h / 2 ^ 1) mod 2 ^ 2.
Proof.
  intros h H. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2 ^ 61) with 2305843009213693952. change (2 ^ 64) with 18446744073709551616. change (2 ^ 62) with 4611686018427387904.
  change (2 ^ 1) with 2. change (2 ^ 2) with 4. Z.div_mod_to_equations. lia.
Qed.

Lemma land_m8_u64 : forall b, 0 <= b < 2^32 -> Z.land b 18446744073709551608 = b - Z.land b 7.
Proof.
  intros b H. change 18446744073709551608 with (Z.land (-8) (Z.ones 64)). rewrite Z.land_assoc, Z.land_ones by lia.
  rewrite land_m8 by lia. rewrite land7_mod. change (2 ^ 3) with 8. change (2 ^ 64) with 18446744073709551616. change (2 ^ 32) with 4294967296 in H.
  Z.div_mod_to_equations. lia.
Qed.
Lemma land7_le : forall b, 0 <= b -> 0 <= Z.land b 7 <= b /\ Z.land b 7 < 8.
Proof. intros b H. rewrite land7_mod. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia. Qed.



Lemma nb_enough : forall n s c r, n <= ir_bits r -> NEEDBITS n (mkW s c r) = ARun tt (mkW s c r).
Proof. intros n s c r H. unfold NEEDBITS. apply NEEDBITS_k_done. exact H. Qed.
Lemma nb_dry : forall n s c r, ir_bits r < n -> ir_have r = 0 -> NEEDBITS n (mkW s c r) = ALeave (mkW s c r).
Proof.
  intros n s c r Hb Hh. rewrite NEEDBITS_have1 by lia.
  replace (ir_bits r <? n) with true by (symmetry; apply Z.ltb_lt; lia). rewrite Hh. reflexivity.
Qed.
Lemma nb_pull_ok : forall n s c r, ir_have r = 1 -> 0 <= ir_bits r <= 56 -> ir_bits r < n <= ir_bits r + 8 ->
  NEEDBITS n (mkW s c r) = ARun tt (mkW s c (pullr c r)).
Proof.
  intros n s c r Hh Hb Hn. rewrite NEEDBITS_have1 by lia.
  replace (ir_bits r <? n) with true by (symmetry; apply Z.ltb_lt; lia). rewrite Hh. cbn [Z.eqb].
  rewrite pullr_bits by lia. replace (ir_bits r + 8 <? n) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
Lemma nb_pull_dry : forall n s c r, ir_have r = 1 -> 0 <= ir_bits r <= 56 -> ir_bits r + 8 < n ->
  NEEDBITS n (mkW s c r) = ALeave (mkW s c (pullr c r)).
Proof.
  intros n s c r Hh Hb Hn. rewrite NEEDBITS_have1 by lia.
  replace (ir_bits r <? n) with true by (symmetry; apply Z.ltb_lt; lia). rewrite Hh. cbn [Z.eqb].
  rewrite pullr_bits by lia. replace (ir_bits r + 8 <? n) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
