(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith Lia.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition AHM_MAGIC : Z := 0x8713f185cccd38dd.
Lemma mulhu_magic_31051 : forall x, 0 <= x < 2^64 -> x * AHM_MAGIC / 2^78 = x / 31051.
Proof.
intros x Hx. unfold AHM_MAGIC. set (C := 0x8713f185cccd38dd).
assert (HC : C * 31051 = 2^78 + 7615) by reflexivity.
pose proof (Z.div_mod x 31051 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound x 31051 ltac:(lia)) as Hm.
set (q := x / 31051) in *. set (r := x mod 31051) in *.
assert (E : 31051 * (x * C) = 31051 * (2^78 * q) + (r * 2^78 + 7615 * x)) by nia.
assert (Hm0 : (r * 2 ^ 78 + 7615 * x) mod 31051 = 0).
{ replace (r * 2 ^ 78 + 7615 * x) with (31051 * (x * C - 2 ^ 78 * q)) by lia. rewrite Z.mul_comm. apply Z_mod_mult. }
pose proof (Z.div_mod (r * 2 ^ 78 + 7615 * x) 31051 ltac:(lia)) as Hd2.
set (t := (r * 2 ^ 78 + 7615 * x) / 31051) in *.
symmetry. apply Z.div_unique_pos with (r := t); [| lia].
split; subst t; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
Definition ahm_mix (f : Z) : Z := let t := (f * 1025) mod 2 ^ 64 in Z.lxor t (Z.shiftr t 6).
Definition ahm_idx (f : Z) : Z := ahm_mix f mod 31051.
Lemma lxor_range64 : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= Z.lxor a b < 2 ^ 64.
Proof.
intros a b Ha Hb. split; [apply Z.lxor_nonneg; lia|].
destruct (Z.eq_dec (Z.lxor a b) 0) as [-> | Hnz]; [lia|].
apply (proj2 (Z.log2_lt_pow2 (Z.lxor a b) 64 ltac:(pose proof (Z.lxor_nonneg a b); lia))).
eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|].
apply Z.max_lub_lt.
- destruct (Z.eq_dec a 0) as [E|NE]; [rewrite E; cbn; lia | apply (proj1 (Z.log2_lt_pow2 a 64 ltac:(lia))); lia].
- destruct (Z.eq_dec b 0) as [E|NE]; [rewrite E; cbn; lia | apply (proj1 (Z.log2_lt_pow2 b 64 ltac:(lia))); lia].
Qed.
Lemma ahm_mix_range : forall f, 0 <= ahm_mix f < 2 ^ 64.
Proof.
intros f. unfold ahm_mix. cbv zeta.
pose proof (Z.mod_pos_bound (f * 1025) (2 ^ 64) ltac:(lia)) as Ht. set (t := (f * 1025) mod 2 ^ 64) in *.
apply lxor_range64; [lia|]. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
Lemma ahm_idx_range : forall f, 0 <= ahm_idx f < 31051.
Proof. intros f. unfold ahm_idx. apply Z.mod_pos_bound. lia. Qed.
Lemma ahm_offset_eval : forall f, 0 <= f < 2 ^ 64 ->
let t := ((f * 2 ^ 10) mod 2 ^ 64 + f) mod 2 ^ 64 in
let h := Z.lxor t ((t / 2 ^ 6) mod 2 ^ 64) mod 2 ^ 64 in
let q := ((h * AHM_MAGIC / 2 ^ 64) mod 2 ^ 64 / 2 ^ 14) mod 2 ^ 64 in
let i := (h - (q * 31051) mod 2 ^ 64) mod 2 ^ 64 in
((i * 2 ^ 7) mod 2 ^ 64 - (i * 2 ^ 3) mod 2 ^ 64) mod 2 ^ 64 = 120 * ahm_idx f.
Proof.
intros f Hf. cbv zeta.
assert (Ht : ((f * 2 ^ 10) mod 2 ^ 64 + f) mod 2 ^ 64 = (f * 1025) mod 2 ^ 64).
{ rewrite Z.add_mod_idemp_l by lia. f_equal. lia. }
rewrite !Ht. pose proof (Z.mod_pos_bound (f * 1025) (2 ^ 64) ltac:(lia)) as Tr. set (t := (f * 1025) mod 2 ^ 64) in *.
assert (Hh : Z.lxor t ((t / 2 ^ 6) mod 2 ^ 64) mod 2 ^ 64 = ahm_mix f).
{ unfold ahm_mix. cbv zeta. fold t. rewrite Z.shiftr_div_pow2 by lia.
rewrite (Z.mod_small (t / 2 ^ 6)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
apply Z.mod_small. apply lxor_range64; [lia|]. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
rewrite !Hh. pose proof (ahm_mix_range f) as Hr. set (h := ahm_mix f) in *.
assert (Hq : ((h * AHM_MAGIC / 2 ^ 64) mod 2 ^ 64 / 2 ^ 14) mod 2 ^ 64 = h / 31051).
{ assert (M0 : 0 <= h * AHM_MAGIC) by (unfold AHM_MAGIC; lia).
rewrite (Z.mod_small (h * AHM_MAGIC / 2 ^ 64)).
2:{ split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia|]]. unfold AHM_MAGIC. nia. }
rewrite Z.div_div by lia. change (2 ^ 64 * 2 ^ 14) with (2 ^ 78). rewrite mulhu_magic_31051 by lia.
apply Z.mod_small. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
rewrite !Hq.
pose proof (Z.div_mod h 31051 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound h 31051 ltac:(lia)) as Hm.
assert (Hi : (h - (h / 31051 * 31051) mod 2 ^ 64) mod 2 ^ 64 = ahm_idx f).
{ unfold ahm_idx. fold h. rewrite (Z.mod_small (h / 31051 * 31051)) by nia. rewrite Z.mod_small by nia. lia. }
rewrite !Hi. pose proof (ahm_idx_range f) as Hx. set (i := ahm_idx f) in *.
rewrite (Z.mod_small (i * 2 ^ 7)) by lia. rewrite (Z.mod_small (i * 2 ^ 3)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
