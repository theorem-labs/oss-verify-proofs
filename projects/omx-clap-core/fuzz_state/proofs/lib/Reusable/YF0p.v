(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition DH_M : Z := 14313749767032793493.
Definition DH_M8 : Z := 3829533694005038248.
Definition DH_SEED : Z := 10900877739976798860.
Definition dh_mul (x : Z) : Z := (x * DH_M) mod 2 ^ 64.
Definition dh_step (h w : Z) : Z :=
let k := dh_mul w in let k := Z.lxor (Z.shiftr k 47) k in let k := dh_mul k in dh_mul (Z.lxor k h).
Definition tfib_dhash (tr : list Z) : Z :=
let h0 := Z.lxor ((Z.of_nat (length tr) * DH_M8) mod 2 ^ 64) DH_SEED in
let h := fold_left dh_step tr h0 in
let h := dh_step h 0 in
let h := Z.lxor (Z.shiftr h 47) h in
let h := dh_mul h in
Z.lxor (Z.shiftr h 47) h.
Lemma lxor_u64 : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= Z.lxor a b < 2 ^ 64.
Proof.
intros a b Ha Hb. assert (H0 : 0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia). split; [exact H0|].
destruct (Z.eq_dec (Z.lxor a b) 0) as [->|Hne]; [lia|].
pose proof (Z.log2_lxor a b ltac:(lia) ltac:(lia)) as L.
assert (La : Z.log2 a < 64) by (destruct (Z.eq_dec a 0) as [->|]; [cbn; lia | apply Z.log2_lt_pow2; lia]).
assert (Lb : Z.log2 b < 64) by (destruct (Z.eq_dec b 0) as [->|]; [cbn; lia | apply Z.log2_lt_pow2; lia]).
apply Z.log2_lt_cancel. rewrite Z.log2_pow2 by lia. lia.
Qed.
Lemma shiftr_u64 : forall a n, 0 <= a < 2 ^ 64 -> 0 <= n -> 0 <= Z.shiftr a n < 2 ^ 64.
Proof.
intros a n Ha Hn. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]|].
apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|]. assert (1 <= 2 ^ n) by (apply Z.pow_le_mono_r with (a := 2) (b := 0) (c := n) in Hn; lia). nia.
Qed.
Lemma dh_mul_u64 : forall x, 0 <= dh_mul x < 2 ^ 64.
Proof. intros x. unfold dh_mul. apply Z.mod_pos_bound. lia. Qed.
Lemma dh_step_u64 : forall h w, 0 <= dh_step h w < 2 ^ 64.
Proof. intros h w. unfold dh_step. apply dh_mul_u64. Qed.
Lemma dh_step_zev : forall h w M_ : Z, 0 <= h < 2 ^ 64 -> 0 <= w < 2 ^ 64 -> M_ = DH_M ->
(Z.lxor ((Z.lxor ((Z.shiftr ((w * M_) mod 2 ^ 64) (Z.land 47 63)) mod 2 ^ 64) ((w * M_) mod 2 ^ 64) mod 2 ^ 64 * M_) mod 2 ^ 64) h) mod 2 ^ 64 * M_ mod 2 ^ 64
= dh_step h w.
Proof.
intros h w M_ Hh Hw ->. unfold dh_step, dh_mul. change (Z.land 47 63) with 47.
set (k := (w * DH_M) mod 2 ^ 64). assert (Hk : 0 <= k < 2 ^ 64) by (subst k; apply Z.mod_pos_bound; lia).
pose proof (shiftr_u64 k 47 Hk ltac:(lia)) as Hs. rewrite (Z.mod_small (Z.shiftr k 47)) by exact Hs.
pose proof (lxor_u64 (Z.shiftr k 47) k Hs Hk) as Hx. rewrite (Z.mod_small (Z.lxor (Z.shiftr k 47) k)) by exact Hx.
set (k2 := (Z.lxor (Z.shiftr k 47) k * DH_M) mod 2 ^ 64). assert (Hk2 : 0 <= k2 < 2 ^ 64) by (subst k2; apply Z.mod_pos_bound; lia).
rewrite (Z.mod_small (Z.lxor k2 h)) by (apply lxor_u64; assumption). reflexivity.
Qed.
