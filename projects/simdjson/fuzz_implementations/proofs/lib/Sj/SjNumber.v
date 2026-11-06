(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition swrap32 (x : Z) : Z := (x + 2147483648) mod 4294967296 - 2147483648.

Lemma swrap32_range : forall x, -2147483648 <= swrap32 x < 2147483648.
Proof. intros x. unfold swrap32. pose proof (Z.mod_pos_bound (x + 2147483648) 4294967296 ltac:(lia)). lia. Qed.

Lemma swrap32_small : forall x, -2147483648 <= x < 2147483648 -> swrap32 x = x.
Proof. intros x H. unfold swrap32. rewrite Z.mod_small by lia. lia. Qed.

Lemma swrap32_mod : forall x, swrap32 x mod 4294967296 = x mod 4294967296.
Proof.
  intros x. unfold swrap32.
  pose proof (Z.div_mod (x + 2147483648) 4294967296 ltac:(lia)) as D.
  replace ((x + 2147483648) mod 4294967296 - 2147483648) with (x + (- ((x + 2147483648) / 4294967296)) * 4294967296) by lia.
  apply Z.mod_add. lia.
Qed.

Lemma pow5_large_step : forall e, -2147483648 <= e < 2147483648 -> (e < 0 \/ 135 <= e) ->
  swrap32 (e - 135) mod 4294967296 = e mod 4294967296 - 135 /\ 135 <= e mod 4294967296.
Proof.
  intros e He Hout. rewrite swrap32_mod.
  assert (E : e mod 4294967296 = if e <? 0 then e + 4294967296 else e).
  { destruct (Z.ltb_spec e 0).
    - replace e with (e + 4294967296 + (-1) * 4294967296) at 1 by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
    - apply Z.mod_small. lia. }
  assert (G : 135 <= e mod 4294967296) by (rewrite E; destruct (Z.ltb_spec e 0); lia).
  split; [|exact G].
  replace (e - 135) with (e mod 4294967296 - 135 + (e / 4294967296) * 4294967296).
  2:{ pose proof (Z.div_mod e 4294967296 ltac:(lia)). lia. }
  rewrite Z.mod_add by lia. apply Z.mod_small.
  pose proof (Z.mod_pos_bound e 4294967296 ltac:(lia)). lia.
Qed.

Lemma s32_mod64 : forall e, -2147483648 <= e < 2147483648 ->
  e mod 18446744073709551616 = if e <? 0 then e + 18446744073709551616 else e.
Proof.
  intros e H. destruct (Z.ltb_spec e 0).
  - replace e with (e + 18446744073709551616 + (-1) * 18446744073709551616) at 1 by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - apply Z.mod_small. lia.
Qed.

Lemma s32_gtu : forall e c, -2147483648 <= e < 2147483648 -> 0 <= c < 2147483648 ->
  (c < e mod 18446744073709551616 <-> (e < 0 \/ c < e)).
Proof. intros e c He Hc. rewrite (s32_mod64 e He). destruct (Z.ltb_spec e 0); lia. Qed.

Lemma s32_leu : forall e c, -2147483648 <= e < 2147483648 -> 0 <= c < 2147483648 ->
  (e mod 18446744073709551616 <= c <-> 0 <= e <= c).
Proof. intros e c He Hc. rewrite (s32_mod64 e He). destruct (Z.ltb_spec e 0); lia. Qed.

Lemma swrap32_mod64 : forall x k, swrap32 (x mod 18446744073709551616 + k) = swrap32 (x + k).
Proof.
  intros x k. unfold swrap32. f_equal.
  pose proof (Z.div_mod x 18446744073709551616 ltac:(lia)) as D.
  replace (x mod 18446744073709551616 + k + 2147483648)
    with (x + k + 2147483648 + (- (x / 18446744073709551616) * 4294967296) * 4294967296) by lia.
  apply Z.mod_add. lia.
Qed.

Definition numchar (c : Z) : bool :=
  ((48 <=? c) && (c <=? 57)) || (c =? 43) || (c =? 45) || (c =? 46) || (c =? 69) || (c =? 101).

Definition NUMMASK : Z := 288230376218820621.

Lemma numchar_mask : forall c, 0 <= c < 256 -> ~ (48 <= c <= 57) -> 43 <= c <= 101 ->
  Z.land (Z.shiftr NUMMASK (c - 43)) 1 = if numchar c then 1 else 0.
Proof.
  intros c Hc Hd Hr. unfold numchar.
  assert (D : (48 <=? c) && (c <=? 57) = false) by (destruct (Z.leb_spec 48 c); destruct (Z.leb_spec c 57); cbn; try reflexivity; lia).
  rewrite D. cbn [orb].
  assert (E : exists k, c = 43 + Z.of_nat k /\ (k <= 58)%nat) by (exists (Z.to_nat (c - 43)); lia).
  destruct E as (k & -> & Hk).
  replace (43 + Z.of_nat k - 43) with (Z.of_nat k) by lia.
  do 59 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma numend_exists : forall (nc : Z -> bool) (off stop : Z), off <= stop -> nc stop = false ->
  exists e, off <= e <= stop /\ nc e = false /\ forall i, off <= i < e -> nc i = true.
Proof.
  intros nc off stop Hle Hs.
  assert (G : forall (n : nat) o, stop - o <= Z.of_nat n -> o <= stop ->
              exists e, o <= e <= stop /\ nc e = false /\ forall i, o <= i < e -> nc i = true).
  { induction n as [|n IH]; intros o Hn Ho.
    - exists stop. split; [lia|]. split; [exact Hs|]. intros i Hi. lia.
    - destruct (nc o) eqn:E.
      + destruct (Z.eq_dec o stop) as [->|NE]; [congruence|].
        destruct (IH (o + 1) ltac:(lia) ltac:(lia)) as (e & He & Hf & Ht).
        exists e. split; [lia|]. split; [exact Hf|]. intros i Hi.
        destruct (Z.eq_dec i o) as [->|]; [exact E| apply Ht; lia].
      + exists o. split; [lia|]. split; [exact E|]. intros i Hi. lia. }
  apply (G (Z.to_nat (stop - off))); lia.
Qed.

Lemma shl48_small : forall k, 0 <= k < 65536 -> (Z.shiftl k 48) mod 18446744073709551616 = k * 281474976710656.
Proof. intros k H. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 48) with 281474976710656. apply Z.mod_small. lia. Qed.

Lemma shl48_shr48 : forall k, 0 <= k < 65536 -> Z.shiftr ((Z.shiftl k 48) mod 18446744073709551616) 48 = k.
Proof.
  intros k H. rewrite shl48_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 48) with 281474976710656.
  apply Z.div_mul. lia.
Qed.

Lemma shl48_shr45 : forall k, 0 <= k < 65536 -> Z.shiftr ((Z.shiftl k 48) mod 18446744073709551616) 45 = 8 * k.
Proof.
  intros k H. rewrite shl48_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 45) with 35184372088832.
  replace (k * 281474976710656) with ((8 * k) * 35184372088832) by lia. apply Z.div_mul. lia.
Qed.

Lemma shl51_shr48 : forall k, 0 <= k < 8192 -> Z.shiftr ((Z.shiftl k 51) mod 18446744073709551616) 48 = 8 * k.
Proof.
  intros k H. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 51) with 2251799813685248.
  rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 48) with 281474976710656.
  replace (k * 2251799813685248) with ((8 * k) * 281474976710656) by lia. apply Z.div_mul. lia.
Qed.

Lemma shl48_zero : forall k, 0 <= k < 65536 -> ((Z.shiftl k 48) mod 18446744073709551616 = 0 <-> k = 0).
Proof. intros k H. rewrite shl48_small by lia. lia. Qed.

Lemma neg_mod64_zero : forall r, 0 <= r < 18446744073709551616 -> ((- r) mod 18446744073709551616 = 0 <-> r = 0).
Proof.
  intros r H. split; [|intros ->; reflexivity].
  intros E. destruct (Z.eq_dec r 0) as [|NE]; [assumption|exfalso].
  replace (- r) with (18446744073709551616 - r + (-1) * 18446744073709551616) in E by lia.
  rewrite Z.mod_add in E by lia. rewrite Z.mod_small in E by lia. lia.
Qed.

Lemma memmove_overlap_test : forall s d n, 0 <= s < d -> d + n <= 18446744073709551616 -> 0 <= n < 4611686018427387904 ->
  (s - (n + d)) mod 18446744073709551616 <= (- (2 * n)) mod 18446744073709551616 -> s + n <= d.
Proof.
  intros s d n Hs Hd Hn K. destruct (Z.eq_dec n 0) as [->|NZ]; [lia|].
  assert (E2 : (- (2 * n)) mod 18446744073709551616 = 18446744073709551616 - 2 * n).
  { replace (- (2 * n)) with (18446744073709551616 - 2 * n + (-1) * 18446744073709551616) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  rewrite E2 in K.
  destruct (Z.eq_dec (s - (n + d)) (-18446744073709551616)) as [E|NE]; [lia|].
  assert (E1 : (s - (n + d)) mod 18446744073709551616 = s - (n + d) + 18446744073709551616).
  { replace (s - (n + d)) with (s - (n + d) + 18446744073709551616 + (-1) * 18446744073709551616) at 1 by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  lia.
Qed.

Lemma xor_low3_zero : forall s d, 0 <= s -> 0 <= d -> (d - s) mod 8 = 0 -> Z.land (Z.lxor s d) 7 = 0.
Proof.
  intros s d Hs Hd H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia.
  assert (E : s mod 2 ^ 3 = d mod 2 ^ 3).
  { change (2 ^ 3) with 8. pose proof (Z.div_mod (d - s) 8 ltac:(lia)) as DM. rewrite H in DM.
    replace d with (s + ((d - s) / 8) * 8) by lia. rewrite Z.mod_add by lia. reflexivity. }
  apply Z.bits_inj'. intros i Hi. rewrite Z.bits_0.
  destruct (Z.lt_ge_cases i 3) as [L|G].
  - rewrite Z.mod_pow2_bits_low by lia. rewrite Z.lxor_spec.
    rewrite <- (Z.mod_pow2_bits_low s 3 i) by lia. rewrite <- (Z.mod_pow2_bits_low d 3 i) by lia. rewrite E. apply xorb_nilpotent.
  - apply Z.mod_pow2_bits_high. lia.
Qed.

Lemma memmove_overlap_test_w : forall s d n, 0 <= s < d -> d + n <= 18446744073709551616 -> 0 <= n < 4611686018427387904 ->
  (s - (n + d) mod 18446744073709551616) mod 18446744073709551616 <= (0 - (2 * n) mod 18446744073709551616) mod 18446744073709551616 ->
  s + n <= d.
Proof.
  intros s d n Hs Hd Hn K. destruct (Z.eq_dec n 0) as [->|NZ]; [lia|].
  rewrite (Z.mod_small (2 * n)) in K by lia.
  destruct (Z.eq_dec (n + d) 18446744073709551616) as [E|NE].
  - rewrite E, Z.mod_same in K by lia. rewrite Z.sub_0_r in K. rewrite (Z.mod_small s) in K by lia.
    replace (0 - 2 * n) with (18446744073709551616 - 2 * n + (-1) * 18446744073709551616) in K by lia.
    rewrite Z.mod_add in K by lia. rewrite Z.mod_small in K by lia. lia.
  - rewrite (Z.mod_small (n + d)) in K by lia.
    apply memmove_overlap_test; [lia | lia | lia |]. replace (- (2 * n)) with (0 - 2 * n) by lia. exact K.
Qed.

Lemma srliw6_range : forall x, 0 <= Z.shiftr (x mod 4294967296) 6 < 67108864.
Proof.
  intros x. pose proof (Z.mod_pos_bound x 4294967296 ltac:(lia)) as B.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 6) with 64.
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.

Lemma shr6_range : forall z, 0 <= z < 18446744073709551616 -> 0 <= Z.shiftr z 6 < 288230376151711744.
Proof.
  intros z H. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 6) with 64.
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.
