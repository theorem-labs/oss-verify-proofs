(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Znumtheory.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BgWords.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma recp_estimate : forall m N n i, 1 <= n -> 2 ^ (n - 1) <= N < 2 ^ n -> 0 <= m < 2 ^ i -> 2 * n <= i ->
  let Nr := 2 ^ i / N in
  let a := m / 2 ^ n in
  let d := (a * Nr) / 2 ^ (i - n) in
  0 <= d /\ d * N <= m < (d + 4) * N.
Proof.
  intros m N n i Hn HN Hm Hi. cbv zeta.
  assert (Hp1 : 0 < 2 ^ (n - 1)) by (apply Z.pow_pos_nonneg; lia).
  assert (HNpos : 0 < N) by lia.
  assert (Hpn : 0 < 2 ^ n) by (apply Z.pow_pos_nonneg; lia).
  assert (Hpin : 0 < 2 ^ (i - n)) by (apply Z.pow_pos_nonneg; lia).
  assert (Epow : 2 ^ i = 2 ^ n * 2 ^ (i - n)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (E2n : 2 ^ n = 2 * 2 ^ (n - 1)) by (replace n with (Z.succ (n - 1)) at 1 by lia; apply Z.pow_succ_r; lia).
  set (Nr := 2 ^ i / N). set (a := m / 2 ^ n). set (d := (a * Nr) / 2 ^ (i - n)).

  pose proof (Z.div_mod (2 ^ i) N ltac:(lia)) as HNr. fold Nr in HNr. set (e := 2 ^ i mod N) in *.
  pose proof (Z.mod_pos_bound (2 ^ i) N HNpos) as He. fold e in He.

  pose proof (Z.div_mod m (2 ^ n) ltac:(lia)) as Ha. fold a in Ha. set (m0 := m mod 2 ^ n) in *.
  pose proof (Z.mod_pos_bound m (2 ^ n) Hpn) as Hm0. fold m0 in Hm0.

  pose proof (Z.div_mod (a * Nr) (2 ^ (i - n)) ltac:(lia)) as Hd. fold d in Hd. set (f := (a * Nr) mod 2 ^ (i - n)) in *.
  pose proof (Z.mod_pos_bound (a * Nr) (2 ^ (i - n)) Hpin) as Hf. fold f in Hf.
  assert (Ha0 : 0 <= a) by (apply Z.div_pos; lia).
  assert (HNr0 : 0 <= Nr) by (apply Z.div_pos; lia).
  assert (Hd0 : 0 <= d) by (apply Z.div_pos; [apply Z.mul_nonneg_nonneg; lia|lia]).
  assert (Halt : a < 2 ^ (i - n)) by (apply Z.div_lt_upper_bound; [lia|rewrite <- Epow; lia]).
  split; [exact Hd0|]. split.
  -
    assert (H1 : d * 2 ^ (i - n) <= a * Nr) by lia.
    assert (H2 : a * Nr * N <= a * 2 ^ i) by nia.
    assert (H3 : d * N * 2 ^ (i - n) <= m * 2 ^ (i - n)) by nia.
    nia.
  -
    assert (H1 : a * Nr < (d + 1) * 2 ^ (i - n)) by lia.
    assert (H2 : a * e <= a * N) by nia.
    assert (H3 : a * N <= (2 ^ (i - n) - 1) * N) by nia.
    assert (H4 : m0 < 2 * N) by lia.

    assert (H5 : m * 2 ^ (i - n) < (d + 4) * N * 2 ^ (i - n)).
    { assert (Ea : a * 2 ^ i = a * Nr * N + a * e) by nia.
      assert (Em : m * 2 ^ (i - n) = a * 2 ^ i + m0 * 2 ^ (i - n)) by nia.
      assert (H6 : a * Nr * N < (d + 1) * 2 ^ (i - n) * N) by nia.
      assert (H7 : m0 * 2 ^ (i - n) < 2 * N * 2 ^ (i - n)) by nia.
      nia. }
    nia.
Qed.

Lemma mod_eq_divide : forall a b N, 0 < N -> a mod N = b mod N -> (N | a - b).
Proof. intros a b N HN H. apply Z.mod_divide; [lia|]. rewrite Zminus_mod, H, Z.sub_diag. apply Z.mod_0_l. lia. Qed.

Lemma divide_mod_eq : forall a b N, 0 < N -> (N | a - b) -> a mod N = b mod N.
Proof.
  intros a b N HN [k Hk]. replace a with (b + k * N) by lia. apply Z.mod_add. lia.
Qed.

Lemma mont_cancel : forall R N z t, 0 < N -> Z.gcd R N = 1 -> (z * R) mod N = (t * R) mod N -> z mod N = t mod N.
Proof.
  intros R N z t HN Hg H. apply divide_mod_eq; [exact HN|]. apply mod_eq_divide in H; [|exact HN].
  replace (z * R - t * R) with (R * (z - t)) in H by ring.
  apply (Z.gauss N R (z - t)); [exact H|]. rewrite Z.gcd_comm. exact Hg.
Qed.

Lemma gcd_pow2_odd : forall k N, 0 <= k -> Z.odd N = true -> Z.gcd (2 ^ k) N = 1.
Proof.
  intros k N Hk Hodd. apply Zgcd_1_rel_prime. apply rel_prime_sym.
  assert (H2 : rel_prime N 2).
  { apply rel_prime_sym. apply prime_rel_prime; [exact prime_2|]. intros [q Hq]. rewrite Hq, Z.mul_comm, Z.odd_mul in Hodd.
    cbn in Hodd. discriminate. }
  pattern k. apply natlike_ind; [|intros x Hx IH|exact Hk].
  - cbn. apply rel_prime_sym, rel_prime_1.
  - rewrite Z.pow_succ_r by exact Hx. apply rel_prime_mult; assumption.
Qed.

Definition bits_val (p lo len : Z) : Z := (p / 2 ^ lo) mod 2 ^ len.

Lemma bits_val_testbit : forall p lo len k, 0 <= lo -> 0 <= len -> 0 <= k ->
  Z.testbit (bits_val p lo len) k = if k <? len then Z.testbit p (lo + k) else false.
Proof.
  intros p lo len k Hlo Hlen Hk. unfold bits_val. destruct (Z.ltb_spec k len) as [Hlt|Hge].
  - rewrite Z.mod_pow2_bits_low by lia. rewrite Z.div_pow2_bits by lia. f_equal. lia.
  - apply Z.mod_pow2_bits_high. lia.
Qed.

Lemma window_extend : forall p s e i, 0 <= p -> 0 <= e -> e < i -> i <= s ->
  (forall j, e < j < i -> Z.testbit p (s - j) = false) -> Z.testbit p (s - i) = true ->
  Z.lor (Z.shiftl (bits_val p (s - e) (e + 1)) (i - e)) 1 = bits_val p (s - i) (i + 1).
Proof.
  intros p s e i Hp He Hei His Hzero Hbit. apply Z.bits_inj'. intros k Hk.
  rewrite Z.lor_spec, Z.shiftl_spec by lia. rewrite (bits_val_testbit p (s - i) (i + 1) k) by lia.
  destruct (Z.ltb_spec k (i + 1)) as [Hlt|Hge].
  - destruct (Z.eq_dec k 0) as [->|Hk0].
    + rewrite Z.add_0_r, Hbit. cbn [Z.testbit]. apply orb_true_r.
    + assert (E1 : Z.testbit 1 k = false) by (destruct k; try lia; reflexivity). rewrite E1, orb_false_r.
      destruct (Z.lt_ge_cases k (i - e)) as [Hlow|Hhigh].
      * rewrite Z.testbit_neg_r by lia. symmetry. replace (s - i + k) with (s - (i - k)) by lia. apply Hzero. lia.
      * rewrite bits_val_testbit by lia. destruct (Z.ltb_spec (k - (i - e)) (e + 1)); [|lia]. f_equal. lia.
  - assert (E1 : Z.testbit 1 k = false) by (destruct k; try lia; reflexivity). rewrite E1, orb_false_r.
    rewrite bits_val_testbit by lia. destruct (Z.ltb_spec (k - (i - e)) (e + 1)); [lia|reflexivity].
Qed.

Lemma window_scan_inv : forall p wstart cnt i wvalue wend, 0 <= p -> 0 <= wend -> wend < i -> wend <= wstart ->
  wvalue = bits_val p (wstart - wend) (wend + 1) -> Z.testbit p (wstart - wend) = true ->
  (forall j, wend < j < i -> Z.testbit p (wstart - j) = false) ->
  let '(wv, we) := window_scan (Z.testbit p) wstart cnt i wvalue wend in
  0 <= we < i + Z.of_nat cnt /\ we <= wstart /\ wv = bits_val p (wstart - we) (we + 1) /\ Z.testbit p (wstart - we) = true.
Proof.
  intros p wstart cnt. induction cnt as [|c IH]; intros i wvalue wend Hp He Hei Hes Hv Hb Hz; cbn [window_scan].
  - repeat split; try lia; assumption.
  - destruct (Z.ltb_spec (wstart - i) 0) as [Hneg|Hpos].
    + repeat split; try lia; assumption.
    + destruct (Z.testbit p (wstart - i)) eqn:Ebit.
      * specialize (IH (i + 1) (Z.lor (Z.shiftl wvalue (i - wend)) 1) i Hp ltac:(lia) ltac:(lia) ltac:(lia)).
        rewrite Hv, window_extend in IH by (try assumption; lia). specialize (IH eq_refl Ebit ltac:(intros j Hj; lia)).
        rewrite Hv, window_extend by (try assumption; lia).
        destruct (window_scan (Z.testbit p) wstart c (i + 1) (bits_val p (wstart - i) (i + 1)) i) as [wv we].
        destruct IH as (I1 & I2 & I3 & I4). repeat split; try assumption; lia.
      * specialize (IH (i + 1) wvalue wend Hp He ltac:(lia) Hes Hv Hb).
        assert (Hz' : forall j, wend < j < i + 1 -> Z.testbit p (wstart - j) = false).
        { intros j Hj. destruct (Z.eq_dec j i) as [->|Hne]; [exact Ebit|apply Hz; lia]. }
        specialize (IH Hz'). destruct (window_scan (Z.testbit p) wstart c (i + 1) wvalue wend) as [wv we].
        destruct IH as (I1 & I2 & I3 & I4). repeat split; try assumption; lia.
Qed.

Lemma window_scan_spec : forall p wstart window, 0 <= p -> 0 <= wstart -> 1 <= window -> Z.testbit p wstart = true ->
  let '(wv, we) := window_scan (Z.testbit p) wstart (Z.to_nat (window - 1)) 1 1 0 in
  0 <= we < window /\ we <= wstart /\ wv = bits_val p (wstart - we) (we + 1) /\ Z.odd wv = true /\ 1 <= wv < 2 ^ window.
Proof.
  intros p wstart window Hp Hs Hw Hbit.
  pose proof (window_scan_inv p wstart (Z.to_nat (window - 1)) 1 1 0 Hp ltac:(lia) ltac:(lia) Hs) as H.
  assert (E0 : 1 = bits_val p (wstart - 0) (0 + 1)).
  { unfold bits_val. rewrite Z.sub_0_r. cbn [Z.add Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]. change (2 ^ 1) with 2.
    rewrite <- Z.bit0_mod, Z.div_pow2_bits, Z.add_0_l by lia. rewrite Hbit. reflexivity. }
  specialize (H E0 ltac:(rewrite Z.sub_0_r; exact Hbit) ltac:(intros j Hj; lia)).
  destruct (window_scan (Z.testbit p) wstart (Z.to_nat (window - 1)) 1 1 0) as [wv we].
  destruct H as (I1 & I2 & I3 & I4). rewrite Z2Nat.id in I1 by lia.
  split; [lia|]. split; [exact I2|]. split; [exact I3|].
  assert (Hodd : Z.odd wv = true).
  { rewrite I3. rewrite <- Z.bit0_odd, bits_val_testbit by lia. destruct (Z.ltb_spec 0 (we + 1)); [|lia]. rewrite Z.add_0_r. exact I4. }
  split; [exact Hodd|].
  pose proof (Z.mod_pos_bound (p / 2 ^ (wstart - we)) (2 ^ (we + 1)) ltac:(apply Z.pow_pos_nonneg; lia)) as Hb.
  assert (2 ^ (we + 1) <= 2 ^ window) by (apply Z.pow_le_mono_r; lia).
  fold (bits_val p (wstart - we) (we + 1)) in Hb. rewrite <- I3 in Hb.
  destruct (Z.eq_dec wv 0) as [E|E]; [rewrite E in Hodd; discriminate|]. lia.
Qed.

Lemma exp_window_step : forall p s we, 0 <= p -> 0 <= we <= s ->
  p / 2 ^ (s - we) = (p / 2 ^ (s + 1)) * 2 ^ (we + 1) + bits_val p (s - we) (we + 1).
Proof.
  intros p s we Hp Hwe. unfold bits_val.
  assert (H1 : 0 < 2 ^ (we + 1)) by (apply Z.pow_pos_nonneg; lia).
  assert (H2 : 0 < 2 ^ (s - we)) by (apply Z.pow_pos_nonneg; lia).
  rewrite (Z.div_mod (p / 2 ^ (s - we)) (2 ^ (we + 1))) at 1 by lia.
  rewrite Z.div_div by lia. rewrite <- Z.pow_add_r by lia. replace (s - we + (we + 1)) with (s + 1) by lia. ring.
Qed.

Lemma exp_zero_bit : forall p s, 0 <= p -> 0 <= s -> Z.testbit p s = false -> p / 2 ^ s = 2 * (p / 2 ^ (s + 1)).
Proof.
  intros p s Hp Hs Hbit. pose proof (exp_window_step p s 0 Hp ltac:(lia)) as H. rewrite Z.sub_0_r in H.
  assert (E : bits_val p s (0 + 1) = 0).
  { unfold bits_val. change (2 ^ (0 + 1)) with 2. rewrite <- Z.bit0_mod, Z.div_pow2_bits, Z.add_0_l by lia. rewrite Hbit. reflexivity. }
  rewrite E in H. change (2 ^ (0 + 1)) with 2 in H. lia.
Qed.

Lemma exp_top : forall p bits, 0 <= p < 2 ^ bits -> p / 2 ^ bits = 0.
Proof. intros p bits H. apply Z.div_small. exact H. Qed.
