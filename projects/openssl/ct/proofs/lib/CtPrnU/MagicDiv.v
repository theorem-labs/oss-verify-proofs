(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma magic_div : forall x m d K e, 0 < d -> 0 <= x -> 0 <= K -> m * d = 2^K + e -> 0 <= e -> x * e < 2^K -> (x * m) / 2^K = x / d.
Proof.
  intros x m d K e Hd Hx HK Hm He Hxe.
  set (P := 2^K) in *. assert (HP : 0 < P) by (subst P; apply Z.pow_pos_nonneg; lia).
  set (q := x / d). set (r := x mod d).
  assert (Hxqr : x = d * q + r) by (subst q r; apply Z.div_mod; lia).
  assert (Hr : 0 <= r < d) by (subst r; apply Z.mod_pos_bound; lia).
  assert (Hq : 0 <= q) by (subst q; apply Z.div_pos; lia).
  assert (Hm0 : 0 <= m) by nia.
  symmetry. apply Z.div_unique_pos with (r := x * m - q * P); [| lia].
  split.
  + (* [comment removed for export] *)
    assert (q * P * d <= x * m * d) by nia. nia.
  + (* [comment removed for export] *)
    assert (x * m * d < (q + 1) * P * d) by nia. nia.
Qed.

(* [comment removed for export] *)
Lemma div_div' : forall x a b, 0 < a -> 0 < b -> x / (a * b) = (x / a) / b.
Proof. intros. rewrite Z.div_div by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma day_magic : forall ts, 0 <= ts < 2^64 -> ((ts / 2^10) * 13992196986280431) / 2^70 = ts / 86400000.
Proof.
  intros ts Hts. rewrite (magic_div (ts / 2^10) 13992196986280431 84375 70 62201); try lia.
  - change 86400000 with (2^10 * 84375). rewrite div_div' by lia. reflexivity.
  - apply Z.div_pos; lia.
  - assert (ts / 2^10 < 2^54) by (apply Z.div_lt_upper_bound; [lia|]; change (2^10 * 2^54) with (2^64); lia). nia.
Qed.
Lemma ms_magic : forall ts, 0 <= ts < 2^64 -> ((ts / 2^3) * 2361183241434822607) / 2^68 = ts / 1000.
Proof.
  intros ts Hts. rewrite (magic_div (ts / 2^3) 2361183241434822607 125 68 19); try lia.
  - change 1000 with (2^3 * 125). rewrite div_div' by lia. reflexivity.
  - apply Z.div_pos; lia.
  - assert (ts / 2^3 < 2^61) by (apply Z.div_lt_upper_bound; [lia|]; change (2^3 * 2^61) with (2^64); lia). nia.
Qed.
Lemma sec_magic : forall r, 0 <= r < 86400000 -> (r * 274877907) / 2^38 = r / 1000.
Proof.
  intros r Hr. apply (magic_div r 274877907 1000 38 56); lia.
Qed.
