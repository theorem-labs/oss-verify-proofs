(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma land_bit63_small : forall y, 0 <= y < 9223372036854775808 -> Z.land y 9223372036854775808 = 0.
Proof.
  intros y Hy. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
  change 9223372036854775808 with (2 ^ 63). rewrite Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec 63 n) as [<-|NE]; [|apply andb_false_r].
  rewrite andb_true_r. destruct (Z.eq_dec y 0) as [->|NZ]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma lxor_bias_small : forall y, 0 <= y < 9223372036854775808 -> Z.lxor y 9223372036854775808 = y + 9223372036854775808.
Proof. intros y Hy. symmetry. apply Z.add_nocarry_lxor. apply land_bit63_small. exact Hy. Qed.

Lemma lxor_bias_signed : forall e, -9223372036854775808 <= e < 9223372036854775808 ->
  Z.lxor (e mod 18446744073709551616) 9223372036854775808 = e + 9223372036854775808.
Proof.
  intros e He. destruct (Z_lt_dec e 0) as [N|P].
  - replace (e mod 18446744073709551616) with (e + 9223372036854775808 + 9223372036854775808)
      by (rewrite <- (Z.mod_add e 1) by lia; symmetry; rewrite Z.mod_small by lia; lia).
    rewrite <- (lxor_bias_small (e + 9223372036854775808)) by lia.
    rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r. reflexivity.
  - rewrite Z.mod_small by lia. apply lxor_bias_small. lia.
Qed.

Ltac b_lia := lia.
Ltac g_bias :=
  repeat match goal with
  | |- context [Z.lxor (?e mod 18446744073709551616) 9223372036854775808] => rewrite (lxor_bias_signed e) by b_lia
  | |- context [Z.lxor ?y 9223372036854775808] =>
      lazymatch y with
      | Z.modulo _ _ => fail
      | _ => rewrite (lxor_bias_small y) by b_lia
      end
  end.

Lemma land255_any : forall x, Z.land x 255 = x mod 256.
Proof. intros x. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.
