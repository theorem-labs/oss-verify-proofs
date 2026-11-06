(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Znumtheory.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnKara BnModel BnTree BnWordsCorrect BnDivWords
  BnKaraCorrect BnInv BnSpecs BnSpecs2 BnAddSpec BnDivSpec BnMulSpec.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BgState BgWords BgLib BgArith BgMont BgInv BgSpecs BgFrame BgLibSpec BgShiftSpec BgAddSpec
  BgWordSpec BgDivSpec BgMulSpec BgSqrCorrect BgSqrSpec BgModSpec BgMontCorrect BgNumTheory BgMontSpec BgRecpSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition half_mod (n x : Z) : Z := (if Z.odd x then x + n else x) / 2.

Lemma half_mod_eq : forall n x, Z.odd n = true -> 0 <= x -> 2 * half_mod n x = x + (if Z.odd x then n else 0).
Proof.
  intros n x Hn Hx. unfold half_mod.
  destruct (Z.odd x) eqn:Ox.
  - assert (E : Z.even (x + n) = true).
    { rewrite Z.even_add. rewrite <- Z.negb_odd, Ox, <- Z.negb_odd, Hn. reflexivity. }
    apply Z.even_spec in E. destruct E as [k Hk]. rewrite Hk. rewrite (Z.mul_comm 2 k), Z.div_mul by lia. lia.
  - assert (E : Z.even x = true) by (rewrite <- Z.negb_odd, Ox; reflexivity).
    apply Z.even_spec in E. destruct E as [k Hk]. rewrite Hk at 1. rewrite (Z.mul_comm 2 k), Z.div_mul by lia. lia.
Qed.

Lemma half_mod_nonneg : forall n x, 0 <= n -> 0 <= x -> 0 <= half_mod n x.
Proof. intros n x Hn Hx. unfold half_mod. destruct (Z.odd x); apply Z.div_pos; lia. Qed.

Lemma half_mod_le : forall n x, Z.odd n = true -> 0 <= n -> 0 <= x -> 2 * half_mod n x <= x + n.
Proof. intros n x Hn Hn0 Hx. rewrite (half_mod_eq n x Hn Hx). destruct (Z.odd x); lia. Qed.

Lemma testbit_false_mod : forall b s, 0 <= s -> 0 <= b -> b mod 2 ^ s = 0 -> Z.testbit b s = false -> b mod 2 ^ (s + 1) = 0.
Proof.
  intros b s Hs Hb Hm Ht.
  rewrite Z.testbit_false in Ht by lia.
  apply Z.mod_divide in Hm; [|apply Z.pow_nonzero; lia]. destruct Hm as [q Hq].
  rewrite Hq in Ht. rewrite Z.div_mul in Ht by (apply Z.pow_nonzero; lia).
  apply Z.mod_divide; [apply Z.pow_nonzero; lia|].
  apply Zmod_divides in Ht; [|lia]. destruct Ht as [c Hc]. exists c. rewrite Hq, Hc, Z.pow_add_r by lia. change (2 ^ 1) with 2. lia.
Qed.

Lemma pos_mod_pow2_lt : forall b s, 0 <= s -> 0 < b -> b mod 2 ^ s = 0 -> 2 ^ s <= b.
Proof.
  intros b s Hs Hb Hm. apply Z.mod_divide in Hm; [|apply Z.pow_nonzero; lia]. destruct Hm as [q Hq].
  assert (P : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia). assert (0 < q) by nia. nia.
Qed.

Lemma inv_final : forall N Y a r, 1 < N -> (Y * a + 1) mod N = 0 -> r mod N = (N - Y) mod N -> (r * a) mod N = 1.
Proof.
  intros N Y a r HN H1 H2.
  apply Z.mod_divide in H1; [|lia]. destruct H1 as [q Hq].
  apply mod_eq_divide in H2; [|lia]. destruct H2 as [k Hk].
  rewrite <- (Z.mod_small 1 N) by lia. apply divide_mod_eq; [lia|].
  exists (k * a + a - q). assert (E : r = N - Y + k * N) by lia. rewrite E. nia.
Qed.

Definition ibl_inv (a N A B X Y : Z) : Prop :=
  0 <= B <= N /\ 0 < A <= N /\ 0 <= X /\ 0 <= Y /\ X * A + Y * B <= N * N /\
  (X * a) mod N = B mod N /\ (Y * a + A) mod N = 0 /\ Z.gcd A B = 1.

Definition inv_mu (A B : Z) : Z := if Z.even (A * B) then A * B else 2 * (A * B).

Lemma pow2_split_le : forall s t, 0 <= s -> 0 <= t -> 2 ^ s + 2 ^ t - 1 <= 2 ^ (s + t).
Proof.
  intros s t Hs Ht. rewrite Z.pow_add_r by lia.
  assert (P1 : 1 <= 2 ^ s) by (change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia).
  assert (P2 : 1 <= 2 ^ t) by (change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia).
  nia.
Qed.

Lemma div_pow2_exact : forall B s, 0 <= s -> B mod 2 ^ s = 0 -> 2 ^ s * (B / 2 ^ s) = B.
Proof.
  intros B s Hs Hm. pose proof (Z.div_mod B (2 ^ s) ltac:(apply Z.pow_nonzero; lia)). lia.
Qed.

Lemma odd_testbit_div : forall B s, 0 <= s -> Z.testbit B s = true -> Z.odd (B / 2 ^ s) = true.
Proof. intros B s Hs Ht. rewrite Z.testbit_true in Ht by lia. rewrite Zmod_odd in Ht. destruct (Z.odd (B / 2 ^ s)); [reflexivity|discriminate]. Qed.

Lemma gcd_factors : forall A B A1 B1 cA cB, A = cA * A1 -> B = cB * B1 -> Z.gcd A B = 1 -> Z.gcd A1 B1 = 1.
Proof.
  intros A B A1 B1 cA cB EA EB HG. apply Z.bezout_1_gcd.
  destruct (Z.gcd_bezout A B 1 HG) as [u [v Huv]]. exists (u * cA), (v * cB). lia.
Qed.

Lemma even_sub_odd : forall x y, Z.odd x = true -> Z.odd y = true -> Z.even (x - y) = true.
Proof. intros x y Hx Hy. rewrite Z.even_sub. rewrite <- (Z.negb_odd x), <- (Z.negb_odd y), Hx, Hy. reflexivity. Qed.

Lemma ibl_round : forall a N A B X Y sh1 sh2 X1 Y1,
  Z.odd N = true -> 0 < N ->
  ibl_inv a N A B X Y -> 0 < B ->
  0 <= sh1 -> B mod 2 ^ sh1 = 0 -> Z.testbit B sh1 = true -> 0 <= X1 ->
  (2 ^ sh1 * X1) mod N = X mod N -> 2 ^ sh1 * X1 <= X + N * (2 ^ sh1 - 1) ->
  0 <= sh2 -> A mod 2 ^ sh2 = 0 -> Z.testbit A sh2 = true -> 0 <= Y1 ->
  (2 ^ sh2 * Y1) mod N = Y mod N -> 2 ^ sh2 * Y1 <= Y + N * (2 ^ sh2 - 1) ->
  let B1 := B / 2 ^ sh1 in let A1 := A / 2 ^ sh2 in
  0 < B1 <= N /\ 0 < A1 <= N /\ X1 <= N * N /\ Y1 <= N * N /\ 2 <= inv_mu A B /\
  (A1 <= B1 -> ibl_inv a N A1 (B1 - A1) (X1 + Y1) Y1 /\ 2 * inv_mu A1 (B1 - A1) < inv_mu A B /\ X1 + Y1 <= N * N) /\
  (B1 < A1 -> ibl_inv a N (A1 - B1) B1 X1 (Y1 + X1) /\ 2 * inv_mu (A1 - B1) B1 < inv_mu A B /\ Y1 + X1 <= N * N).
Proof.
  intros a N A B X Y sh1 sh2 X1 Y1 ON NP (HB & HA & HX & HY & HQ & C1 & C2 & HG) BP Hs1 Bm Bt X10 CX1 BX1 Hs2 Am At Y10 CY1 BY1 B1 A1.
  pose proof (div_pow2_exact B sh1 Hs1 Bm) as EB. pose proof (div_pow2_exact A sh2 Hs2 Am) as EA. fold B1 in EB. fold A1 in EA.
  assert (P1 : 0 < 2 ^ sh1) by (apply Z.pow_pos_nonneg; lia). assert (P2 : 0 < 2 ^ sh2) by (apply Z.pow_pos_nonneg; lia).
  assert (OB1 : Z.odd B1 = true) by (apply odd_testbit_div; assumption).
  assert (OA1 : Z.odd A1 = true) by (apply odd_testbit_div; assumption).
  assert (HB1 : 0 < B1 <= N).
  { split; [|nia]. destruct (Z.le_gt_cases B1 0); [|lia]. exfalso. assert (2 ^ sh1 * B1 <= 0) by (apply Z.mul_nonneg_nonpos; lia). lia. }
  assert (HA1 : 0 < A1 <= N).
  { split; [|nia]. destruct (Z.le_gt_cases A1 0); [|lia]. exfalso. assert (2 ^ sh2 * A1 <= 0) by (apply Z.mul_nonneg_nonpos; lia). lia. }

  assert (G1 : Z.gcd (2 ^ sh1) N = 1) by (apply gcd_pow2_odd; assumption).
  assert (G2 : Z.gcd (2 ^ sh2) N = 1) by (apply gcd_pow2_odd; assumption).
  assert (CX : (X1 * a) mod N = B1 mod N).
  { apply (mont_cancel (2 ^ sh1) N); [exact NP | exact G1 |].
    replace (X1 * a * 2 ^ sh1) with (2 ^ sh1 * X1 * a) by lia. replace (B1 * 2 ^ sh1) with B by lia.
    rewrite <- C1. rewrite <- Zmult_mod_idemp_l, CX1, Zmult_mod_idemp_l. reflexivity. }
  assert (CY : (Y1 * a + A1) mod N = 0).
  { assert (E : ((Y1 * a + A1) * 2 ^ sh2) mod N = (0 * 2 ^ sh2) mod N).
    { rewrite Z.mul_0_l, Zmod_0_l. replace ((Y1 * a + A1) * 2 ^ sh2) with (2 ^ sh2 * Y1 * a + A) by lia.
      rewrite <- C2. rewrite <- Zplus_mod_idemp_l, <- Zmult_mod_idemp_l, CY1, Zmult_mod_idemp_l, Zplus_mod_idemp_l. reflexivity. }
    pose proof (mont_cancel (2 ^ sh2) N _ _ NP G2 E) as E'. rewrite Zmod_0_l in E'. exact E'. }

  assert (HQ1 : X1 * A1 + Y1 * B1 <= N * N).
  { assert (E : 2 ^ (sh1 + sh2) * (X1 * A1 + Y1 * B1) = (2 ^ sh1 * X1) * A + (2 ^ sh2 * Y1) * B) by (rewrite Z.pow_add_r by lia; nia).
    pose proof (pow2_split_le sh1 sh2 Hs1 Hs2) as PS.
    assert (P12 : 0 < 2 ^ (sh1 + sh2)) by (apply Z.pow_pos_nonneg; lia).
    assert (U1 : (2 ^ sh1 * X1) * A <= (X + N * (2 ^ sh1 - 1)) * A) by (apply Z.mul_le_mono_nonneg_r; lia).
    assert (U2 : (2 ^ sh2 * Y1) * B <= (Y + N * (2 ^ sh2 - 1)) * B) by (apply Z.mul_le_mono_nonneg_r; lia).
    assert (U3 : N * (2 ^ sh1 - 1) * A <= N * (2 ^ sh1 - 1) * N) by (apply Z.mul_le_mono_nonneg_l; [apply Z.mul_nonneg_nonneg; lia|lia]).
    assert (U4 : N * (2 ^ sh2 - 1) * B <= N * (2 ^ sh2 - 1) * N) by (apply Z.mul_le_mono_nonneg_l; [apply Z.mul_nonneg_nonneg; lia|lia]).
    assert (D1 : (X + N * (2 ^ sh1 - 1)) * A = X * A + N * (2 ^ sh1 - 1) * A) by ring.
    assert (D2 : (Y + N * (2 ^ sh2 - 1)) * B = Y * B + N * (2 ^ sh2 - 1) * B) by ring.
    assert (D3 : N * N * (2 ^ sh1 + 2 ^ sh2 - 1) = N * N + N * (2 ^ sh1 - 1) * N + N * (2 ^ sh2 - 1) * N) by ring.
    assert (U : (2 ^ sh1 * X1) * A + (2 ^ sh2 * Y1) * B <= N * N * (2 ^ sh1 + 2 ^ sh2 - 1)) by lia.
    assert (NN0 : 0 <= N * N) by (apply Z.mul_nonneg_nonneg; lia).
    assert (U5 : N * N * (2 ^ sh1 + 2 ^ sh2 - 1) <= N * N * 2 ^ (sh1 + sh2)) by (apply Z.mul_le_mono_nonneg_l; [exact NN0|exact PS]).
    rewrite <- E in U. assert (U6 : 2 ^ (sh1 + sh2) * (X1 * A1 + Y1 * B1) <= 2 ^ (sh1 + sh2) * (N * N)) by lia.
    apply Z.mul_le_mono_pos_l in U6; [exact U6 | exact P12]. }
  assert (HX1 : X1 <= N * N).
  { assert (X1 * 1 <= X1 * A1) by (apply Z.mul_le_mono_nonneg_l; lia). assert (0 <= Y1 * B1) by (apply Z.mul_nonneg_nonneg; lia). lia. }
  assert (HY1 : Y1 <= N * N).
  { assert (Y1 * 1 <= Y1 * B1) by (apply Z.mul_le_mono_nonneg_l; lia). assert (0 <= X1 * A1) by (apply Z.mul_nonneg_nonneg; lia). lia. }
  assert (HG1 : Z.gcd A1 B1 = 1) by (apply (gcd_factors A B A1 B1 (2 ^ sh2) (2 ^ sh1)); [lia | lia | exact HG]).

  assert (AB0 : 0 <= A1 * B1) by nia.
  assert (LA1 : A1 <= A) by nia. assert (LB1 : B1 <= B) by nia.
  assert (E12 : A * B = 2 ^ (sh1 + sh2) * (A1 * B1)) by (rewrite Z.pow_add_r by lia; rewrite <- EA, <- EB; ring).
  assert (MU : 2 * (A1 * B1) <= inv_mu A B).
  { unfold inv_mu. destruct (Z.even (A * B)) eqn:EV.
    -
      destruct (Z.eq_dec (sh1 + sh2) 0) as [E0|NE0].
      + exfalso. rewrite E0, Z.pow_0_r, Z.mul_1_l in E12.
        assert (OO : Z.odd (A * B) = true) by (rewrite E12, Z.odd_mul, OA1, OB1; reflexivity).
        rewrite <- Z.negb_odd, OO in EV. discriminate.
      + assert (P : 2 <= 2 ^ (sh1 + sh2)) by (change 2 with (2 ^ 1); apply Z.pow_le_mono_r; lia).
        rewrite E12. apply Z.mul_le_mono_nonneg_r; [exact AB0 | exact P].
    - assert (A1 * B1 <= A * B) by (apply Z.mul_le_mono_nonneg; lia). lia. }
  split; [exact HB1|]. split; [exact HA1|]. split; [exact HX1|]. split; [exact HY1|]. split; [lia|]. split; intros Hc.
  -
    assert (XY : X1 + Y1 <= N * N).
    { assert ((X1 + Y1) * 1 <= (X1 + Y1) * A1) by (apply Z.mul_le_mono_nonneg_l; lia).
      assert (Y1 * A1 <= Y1 * B1) by (apply Z.mul_le_mono_nonneg_l; lia).
      assert ((X1 + Y1) * A1 = X1 * A1 + Y1 * A1) by ring. lia. }
    split; [|split; [|exact XY]].
    + unfold ibl_inv. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [replace ((X1 + Y1) * A1 + Y1 * (B1 - A1)) with (X1 * A1 + Y1 * B1) by ring; exact HQ1|].
      split. { rewrite Z.mul_add_distr_r, <- Zplus_mod_idemp_l, CX, Zplus_mod_idemp_l.
               replace (B1 + Y1 * a) with ((B1 - A1) + (Y1 * a + A1)) by lia. rewrite <- Zplus_mod_idemp_r, CY, Z.add_0_r. reflexivity. }
      split; [exact CY|]. rewrite Z.gcd_sub_diag_r. exact HG1.
    + unfold inv_mu at 1.
      assert (EV2 : Z.even (A1 * (B1 - A1)) = true) by (rewrite Z.even_mul, (even_sub_odd B1 A1 OB1 OA1); apply Bool.orb_true_r).
      rewrite EV2. assert (A1 * (B1 - A1) <= A1 * B1 - 1) by nia. lia.
  -
    assert (XY : Y1 + X1 <= N * N).
    { assert ((Y1 + X1) * 1 <= (Y1 + X1) * B1) by (apply Z.mul_le_mono_nonneg_l; lia).
      assert (X1 * B1 <= X1 * A1) by (apply Z.mul_le_mono_nonneg_l; lia).
      assert ((Y1 + X1) * B1 = Y1 * B1 + X1 * B1) by ring. lia. }
    split; [|split; [|exact XY]].
    + unfold ibl_inv. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [replace (X1 * (A1 - B1) + (Y1 + X1) * B1) with (X1 * A1 + Y1 * B1) by ring; exact HQ1|].
      split; [exact CX|].
      split. { replace ((Y1 + X1) * a + (A1 - B1)) with ((Y1 * a + A1) + (X1 * a - B1)) by lia.
               rewrite <- Zplus_mod_idemp_l, CY, Z.add_0_l. rewrite Zminus_mod, CX, <- Zminus_mod, Z.sub_diag. apply Zmod_0_l. }
      rewrite Z.gcd_comm, Z.gcd_sub_diag_r, Z.gcd_comm. exact HG1.
    + unfold inv_mu at 1.
      assert (EV2 : Z.even ((A1 - B1) * B1) = true) by (rewrite Z.even_mul, (even_sub_odd A1 B1 OA1 OB1); reflexivity).
      rewrite EV2. assert ((A1 - B1) * B1 <= A1 * B1 - 1) by nia. lia.
Qed.

Section InvSpec.
Context {ptr : Type}.
Local Notation ST := (bstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).

Lemma inv_shift_loop_spec : forall fuel rB rX rn sh XB K F s,
  (rB < length (st_bns s))%nat -> (rX < length (st_bns s))%nat -> (rn < length (st_bns s))%nat ->
  rX <> ROne -> ndiff rX rB -> ndiff rX rn ->
  0 <= sh -> 0 < bn_mag (getbn rB s) -> bn_mag (getbn rB s) mod 2 ^ sh = 0 -> bn_mag (getbn rB s) < 2 ^ (sh + Z.of_nat fuel) ->
  bn_norm (getbn rX s) -> bn_neg (getbn rX s) = false -> bn_mag (getbn rX s) <= XB ->
  bn_norm (getbn rn s) -> Z.odd (bn_mag (getbn rn s)) = true -> bn_mag (getbn rn s) <= XB -> XB + bn_mag (getbn rn s) < Bp K ->
  Z.of_nat K + 1 <= BG_DMAX ->
  hoare F s (inv_shift_loop ops fuel rB rX rn sh) (fun sh' s' =>
    exists x', s' = setbn rX x' s /\ sh <= sh' /\
      bn_mag (getbn rB s) mod 2 ^ sh' = 0 /\ Z.testbit (bn_mag (getbn rB s)) sh' = true /\
      bn_norm x' /\ bn_neg x' = false /\ bn_mag x' <= XB /\ (bn_top x' <= K)%nat /\
      (2 ^ (sh' - sh) * bn_mag x') mod bn_mag (getbn rn s) = bn_mag (getbn rX s) mod bn_mag (getbn rn s) /\
      2 ^ (sh' - sh) * bn_mag x' <= bn_mag (getbn rX s) + bn_mag (getbn rn s) * (2 ^ (sh' - sh) - 1)).
Proof.
  induction fuel as [|f IH]; intros rB rX rn sh XB K F s VB VX Vn NX1 NXB NXn Hsh HB0 HBm HBf NX SX MX Nn On Mn HK HKD.
  { exfalso. rewrite Nat2Z.inj_0, Z.add_0_r in HBf. pose proof (pos_mod_pow2_lt _ _ Hsh HB0 HBm). lia. }
  apply hoare_wf. intros Hs. cbn [inv_shift_loop].
  pose proof (st_wf_okv rB s Hs VB) as OB. pose proof (st_wf_okv rX s Hs VX) as OX. pose proof (st_wf_okv rn s Hs Vn) as On'.
  pose proof (okv_mag_nonneg _ OX) as X0. pose proof (okv_mag_nonneg _ On') as N0.
  assert (Npos : 0 < bn_mag (getbn rn s)).
  { destruct (Z.eq_dec (bn_mag (getbn rn s)) 0) as [E|]; [|lia]. rewrite E in On. cbn in On. discriminate. }
  assert (TX : (bn_top (getbn rX s) <= K)%nat) by (apply norm_top_lt; [exact OX | exact NX | lia]).
  assert (Tn : (bn_top (getbn rn s) <= K)%nat) by (apply norm_top_lt; [exact On' | exact Nn | lia]).
  apply hoare_bind_get. rewrite (is_bit_set_pure_spec _ _ OB Hsh).
  destruct (Z.testbit (bn_mag (getbn rB s)) sh) eqn:TB.
  { apply hoare_ret. exists (getbn rX s). rewrite setbn_getbn_id. rewrite Z.sub_diag, Z.pow_0_r.
    split; [reflexivity|]. split; [lia|]. split; [exact HBm|]. split; [exact TB|]. split; [exact NX|]. split; [exact SX|].
    split; [exact MX|]. split; [exact TX|]. split; [rewrite Z.mul_1_l; reflexivity | lia]. }
  pose proof (testbit_false_mod _ _ Hsh (okv_mag_nonneg _ OB) HBm TB) as HBm1.
  apply hoare_bind_get.

  eapply hoare_bind with (R := fun _ s1 => exists x1, s1 = setbn rX x1 s /\ bn_norm x1 /\ bn_neg x1 = false /\
                            bn_mag x1 = bn_mag (getbn rX s) + (if Z.odd (bn_mag (getbn rX s)) then bn_mag (getbn rn s) else 0) /\
                            (bn_top x1 <= K + 1)%nat).
  { rewrite (is_odd_pure_spec _ OX). destruct (Z.odd (bn_mag (getbn rX s))) eqn:OX1.
    + eapply hoare_mono; [apply BN_uadd_spec; try assumption; lia|].
      intros [] s1 _ (x1 & -> & (P1 & P2 & P3 & P4)). exists x1. split; [reflexivity|]. split; [exact P1|]. split; [exact P3|].
      split; [exact P2 | lia].
    + apply hoare_ret. exists (getbn rX s). rewrite setbn_getbn_id. repeat split; try assumption; lia. }
  intros [] s1 Hs1 (x1 & -> & P1 & P3 & P2 & P4).
  assert (VX1 : (rX < length (st_bns (setbn rX x1 s)))%nat) by (rewrite length_setbn; exact VX).
  eapply hoare_bind with (R := fun _ s2 => exists x2, s2 = setbn rX x2 s /\ bn_norm x2 /\ bn_neg x2 = false /\
                            bn_mag x2 = half_mod (bn_mag (getbn rn s)) (bn_mag (getbn rX s)) /\ (bn_top x2 <= K + 1)%nat).
  { eapply hoare_mono; [apply BN_rshift1_spec; [exact VX1 | exact NX1 | rewrite getbn_setbn_same by exact VX; exact P1]|].
    intros [] s2 _ (x2 & -> & (Q1 & Q2 & Q3 & Q4)). rewrite getbn_setbn_same in Q1, Q3, Q4 by exact VX.
    exists x2. rewrite setbn_setbn_same. split; [reflexivity|]. split; [exact Q2|]. split; [exact (Q3 P3)|].
    split; [|lia]. rewrite Q1, P2. unfold half_mod. destruct (Z.odd (bn_mag (getbn rX s))); [reflexivity | rewrite Z.add_0_r; reflexivity]. }
  intros [] s2 Hs2 (x2 & -> & N2 & S2 & M2 & T2).
  pose proof (half_mod_nonneg (bn_mag (getbn rn s)) (bn_mag (getbn rX s)) N0 X0) as X20.
  pose proof (half_mod_le (bn_mag (getbn rn s)) (bn_mag (getbn rX s)) On N0 X0) as X2L.
  assert (MX2 : bn_mag x2 <= XB) by (rewrite M2; lia).
  assert (EB : getbn rB (setbn rX x2 s) = getbn rB s) by (apply getbn_setbn_other; exact NXB).
  assert (En : getbn rn (setbn rX x2 s) = getbn rn s) by (apply getbn_setbn_other; exact NXn).
  assert (EX : getbn rX (setbn rX x2 s) = x2) by (apply getbn_setbn_same; exact VX).
  pose proof (length_setbn rX x2 s) as EL.
  eapply hoare_mono.
  { apply (IH rB rX rn (sh + 1) XB K); rewrite ?EL, ?EB, ?En, ?EX; try assumption; try lia.
    replace (sh + 1 + Z.of_nat f) with (sh + Z.of_nat (S f)) by lia. exact HBf. }
  intros sh' s3 _ (x3 & -> & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
  rewrite EB in H2, H3. rewrite En, EX in H8, H9.
  exists x3. rewrite setbn_setbn_same. split; [reflexivity|]. split; [lia|]. split; [exact H2|]. split; [exact H3|].
  split; [exact H4|]. split; [exact H5|]. split; [exact H6|]. split; [exact H7|].
  pose proof (okv_mag_nonneg _ (st_wf_okv rX _ Hs2 ltac:(rewrite length_setbn; exact VX))) as X30'.
  assert (E : sh' - sh = (sh' - (sh + 1)) + 1) by lia.
  split.
  - rewrite E. rewrite M2 in H8.
    replace (2 ^ (sh' - (sh + 1) + 1) * bn_mag x3) with (2 ^ (sh' - (sh + 1)) * (2 ^ 1 * bn_mag x3)) by (rewrite Z.pow_add_r by lia; lia).

    apply mod_eq_divide in H8; [|lia]. destruct H8 as [q Hq].
    pose proof (half_mod_eq (bn_mag (getbn rn s)) (bn_mag (getbn rX s)) On X0) as HE.
    apply divide_mod_eq; [lia|]. change (2 ^ 1) with 2.
    destruct (Z.odd (bn_mag (getbn rX s))).
    + exists (2 * q + 1). nia.
    + exists (2 * q). nia.
  - rewrite E. rewrite M2 in H9. rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2.
    assert (P : 0 < 2 ^ (sh' - (sh + 1))) by (apply Z.pow_pos_nonneg; lia). nia.
Qed.

Definition ibl_rep (rA rB rX rY : bnref) (A B X Y : Z) (s : ST) : Prop :=
  let xa := getbn rA s in let xb := getbn rB s in let xx := getbn rX s in let xy := getbn rY s in
  (bn_norm xa /\ bn_neg xa = false /\ bn_mag xa = A) /\ (bn_norm xb /\ bn_neg xb = false /\ bn_mag xb = B) /\
  (bn_norm xx /\ bn_neg xx = false /\ bn_mag xx = X) /\ (bn_norm xy /\ bn_neg xy = false /\ bn_mag xy = Y).

Lemma keeps_setbn_in : forall u outs r b (s0 s : ST), keeps u outs s0 s -> In r outs -> keeps u outs s0 (setbn r b s).
Proof.
  intros u outs r b s0 s K Hin. eapply keeps_weaken; [apply Nat.le_refl | | eapply keeps_trans; [exact K | apply keeps_setbn]].
  intros z Hz _. apply in_app_or in Hz. destruct Hz as [Hz|[Hz|[]]]; [exact Hz | subst z; exact Hin].
Qed.

Lemma cond_rshift_spec : forall r sh F s,
  (r < length (st_bns s))%nat -> r <> ROne -> 0 <= sh -> bn_norm (getbn r s) -> bn_neg (getbn r s) = false ->
  hoare F s (if 0 <? sh then BN_rshift ops r r sh else bret ops tt) (fun _ s' =>
    exists b', s' = setbn r b' s /\ bn_norm b' /\ bn_neg b' = false /\ bn_mag b' = bn_mag (getbn r s) / 2 ^ sh /\
      (bn_top b' <= bn_top (getbn r s))%nat).
Proof.
  intros r sh F s Vr Nr1 Hsh Hn Hs0. destruct (Z.ltb_spec 0 sh).
  - eapply hoare_mono; [apply BN_rshift_spec; assumption|].
    intros [] s' _ (b' & -> & ([C1 _] & C2 & C3 & C4)). exists b'. split; [reflexivity|]. split; [exact C1|]. split; [exact (C3 Hs0)|].
    split; [exact C2 | exact C4].
  - apply hoare_ret. exists (getbn r s). rewrite setbn_getbn_id. replace sh with 0 by lia. rewrite Z.pow_0_r, Z.div_1_r.
    split; [reflexivity|]. split; [exact Hn|]. split; [exact Hs0|]. split; [reflexivity | lia].
Qed.

Lemma inv_binary_loop_spec : forall fuel rA rB rX rY rn a A B X Y K F s,
  (rA < length (st_bns s))%nat -> (rB < length (st_bns s))%nat -> (rX < length (st_bns s))%nat -> (rY < length (st_bns s))%nat ->
  (rn < length (st_bns s))%nat ->
  rA <> ROne -> rB <> ROne -> rX <> ROne -> rY <> ROne ->
  ndiff rA rB -> ndiff rA rX -> ndiff rA rY -> ndiff rA rn -> ndiff rB rX -> ndiff rB rY -> ndiff rB rn -> ndiff rX rY -> ndiff rX rn -> ndiff rY rn ->
  bn_norm (getbn rn s) -> Z.odd (bn_mag (getbn rn s)) = true ->
  bn_mag (getbn rn s) * bn_mag (getbn rn s) + bn_mag (getbn rn s) < Bp K -> Z.of_nat K + 1 <= BG_DMAX ->
  ibl_rep rA rB rX rY A B X Y s -> ibl_inv a (bn_mag (getbn rn s)) A B X Y ->
  X <= bn_mag (getbn rn s) * bn_mag (getbn rn s) -> Y <= bn_mag (getbn rn s) * bn_mag (getbn rn s) ->
  (1 <= fuel)%nat -> (B = 0 \/ inv_mu A B < 2 ^ (Z.of_nat fuel - 1)) ->
  hoare F s (inv_binary_loop ops fuel rA rB rX rY rn) (fun _ s' =>
    keeps (gx_used (st_ctx s)) [rX; rB; rY; rA] s s' /\ getbn rn s' = getbn rn s /\
    exists A' X' Y', ibl_rep rA rB rX rY A' 0 X' Y' s' /\ ibl_inv a (bn_mag (getbn rn s)) A' 0 X' Y' /\
      X' <= bn_mag (getbn rn s) * bn_mag (getbn rn s) /\ Y' <= bn_mag (getbn rn s) * bn_mag (getbn rn s)).
Proof.
  induction fuel as [|f IH]; intros rA rB rX rY rn a A B X Y K F s VA VB VX VY Vn NA1 NB1 NX1 NY1
    DAB DAX DAY DAn DBX DBY DBn DXY DXn DYn Nn On HK HKD REP INV HXB HYB Hf HF; [lia|].
  apply hoare_wf. intros Hs. cbn [inv_binary_loop].
  assert (DXB : ndiff rX rB) by (exact (ndiff_sym _ _ DBX)). assert (DYA : ndiff rY rA) by (exact (ndiff_sym _ _ DAY)).
  set (N := bn_mag (getbn rn s)) in *.
  pose proof (st_wf_okv rA s Hs VA) as OA. pose proof (st_wf_okv rB s Hs VB) as OB.
  pose proof (st_wf_okv rX s Hs VX) as OX. pose proof (st_wf_okv rY s Hs VY) as OY. pose proof (st_wf_okv rn s Hs Vn) as ON'.
  destruct REP as ((NA & SA & MA) & (NB & SB & MB) & (NX & SX & MX) & (NY & SY & MY)). cbv zeta in NA, SA, MA, NB, SB, MB, NX, SX, MX, NY, SY, MY.
  pose proof INV as (IB & IA & IX & IY & IQ & IC1 & IC2 & IG).
  assert (Npos : 0 < N).
  { pose proof (okv_mag_nonneg _ ON') as N0. fold N in N0. destruct (Z.eq_dec N 0) as [E|]; [|lia]. rewrite E in On. cbn in On. discriminate. }
  assert (N1 : N <= N * N) by nia.
  apply hoare_bind_get. unfold is_zero_pure.
  destruct (Nat.eqb_spec (bn_top (getbn rB s)) 0) as [TB0|TB0].
  {
    assert (B0 : B = 0) by (rewrite <- MB; apply (proj1 (norm_zero_iff _ OB NB)); exact TB0).
    apply hoare_ret. split; [apply keeps_refl|]. split; [reflexivity|]. exists A, X, Y. rewrite B0 in INV, MB.
    split; [|split; [exact INV | split; assumption]].
    unfold ibl_rep. cbv zeta. repeat split; assumption. }
  assert (Bpos : 0 < B).
  { rewrite <- MB. pose proof (okv_mag_nonneg _ OB). destruct (Z.eq_dec (bn_mag (getbn rB s)) 0) as [E|]; [|lia].
    exfalso. apply TB0. apply (proj2 (norm_zero_iff _ OB NB)). exact E. }
  destruct HF as [HF|HF]; [lia|].

  pose proof (num_bits_pure_spec _ OB NB) as (NB0 & _ & NB2 & _). rewrite MB in NB2. specialize (NB2 Bpos).
  eapply hoare_bind.
  { apply (inv_shift_loop_spec _ rB rX rn 0 (N * N) K F s VB VX Vn NX1 DXB DXn (Z.le_refl 0)); try assumption; try lia.
    - rewrite Z.pow_0_r. apply Z.mod_1_r.
    - rewrite MB, Z.add_0_l, Nat2Z.inj_add, Z2Nat.id by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.to_nat].
      apply (Z.lt_trans _ _ _ (proj2 NB2)). apply Z.pow_lt_mono_r; lia. }
  intros sh1 s1 Hs1 (x1 & -> & Hsh1 & Bm1 & Bt1 & NX1' & SX1' & MX1 & TX1 & CX1 & BX1).
  rewrite Z.sub_0_r in CX1, BX1. rewrite MB in Bm1, Bt1. rewrite MX in CX1, BX1. fold N in CX1, BX1.
  assert (L1 := length_setbn rX x1 s).
  assert (EB1 : getbn rB (setbn rX x1 s) = getbn rB s) by (apply getbn_setbn_other; apply ndiff_sym; exact DBX).
  assert (EA1 : getbn rA (setbn rX x1 s) = getbn rA s) by (apply getbn_setbn_other; apply ndiff_sym; exact DAX).
  assert (EY1 : getbn rY (setbn rX x1 s) = getbn rY s) by (apply getbn_setbn_other; exact DXY).
  assert (En1 : getbn rn (setbn rX x1 s) = getbn rn s) by (apply getbn_setbn_other; exact DXn).
  assert (EX1 : getbn rX (setbn rX x1 s) = x1) by (apply getbn_setbn_same; exact VX).

  eapply hoare_bind.
  { apply (cond_rshift_spec rB sh1); rewrite ?L1, ?EB1; try assumption. }
  intros [] s2 Hs2 (b2 & -> & NB2' & SB2 & MB2' & TB2). rewrite EB1 in MB2', TB2. rewrite MB in MB2'.
  set (s1 := setbn rX x1 s) in *.
  assert (L2 : length (st_bns (setbn rB b2 s1)) = length (st_bns s)) by (rewrite length_setbn; exact L1).
  assert (EB2 : getbn rB (setbn rB b2 s1) = b2) by (apply getbn_setbn_same; rewrite L1; exact VB).
  assert (EA2 : getbn rA (setbn rB b2 s1) = getbn rA s) by (rewrite getbn_setbn_other by (apply ndiff_sym; exact DAB); exact EA1).
  assert (EY2 : getbn rY (setbn rB b2 s1) = getbn rY s) by (rewrite getbn_setbn_other by exact DBY; exact EY1).
  assert (En2 : getbn rn (setbn rB b2 s1) = getbn rn s) by (rewrite getbn_setbn_other by exact DBn; exact En1).
  assert (EX2 : getbn rX (setbn rB b2 s1) = x1) by (rewrite getbn_setbn_other by exact DBX; exact EX1).

  apply hoare_bind_get. rewrite EA2.
  pose proof (num_bits_pure_spec _ OA NA) as (NA0 & _ & NA2 & _). rewrite MA in NA2. specialize (NA2 ltac:(lia)).
  eapply hoare_bind.
  { apply (inv_shift_loop_spec _ rA rY rn 0 (N * N) K); rewrite ?L2, ?EA2, ?EY2, ?En2; try assumption; try lia.
    - rewrite Z.pow_0_r. apply Z.mod_1_r.
    - rewrite MA, Z.add_0_l, Nat2Z.inj_add, Z2Nat.id by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.to_nat].
      apply (Z.lt_trans _ _ _ (proj2 NA2)). apply Z.pow_lt_mono_r; lia. }
  intros sh2 s3 Hs3 (y3 & -> & Hsh2 & Am3 & At3 & NY3 & SY3 & MY3 & TY3 & CY3 & BY3).
  rewrite Z.sub_0_r in CY3, BY3. rewrite EA2, MA in Am3, At3. rewrite EY2, MY, En2 in CY3, BY3. fold N in CY3, BY3.
  set (s2 := setbn rB b2 s1) in *.
  assert (L3 : length (st_bns (setbn rY y3 s2)) = length (st_bns s)) by (rewrite length_setbn; exact L2).
  assert (EB3 : getbn rB (setbn rY y3 s2) = b2) by (rewrite getbn_setbn_other by (apply ndiff_sym; exact DBY); exact EB2).
  assert (EA3 : getbn rA (setbn rY y3 s2) = getbn rA s) by (rewrite getbn_setbn_other by (apply ndiff_sym; exact DAY); exact EA2).
  assert (EY3 : getbn rY (setbn rY y3 s2) = y3) by (apply getbn_setbn_same; rewrite L2; exact VY).
  assert (En3 : getbn rn (setbn rY y3 s2) = getbn rn s) by (rewrite getbn_setbn_other by exact DYn; exact En2).
  assert (EX3 : getbn rX (setbn rY y3 s2) = x1) by (rewrite getbn_setbn_other by (apply ndiff_sym; exact DXY); exact EX2).

  eapply hoare_bind.
  { apply (cond_rshift_spec rA sh2); rewrite ?L3, ?EA3; try assumption. }
  intros [] s4 Hs4 (a4 & -> & NA4 & SA4 & MA4 & TA4'). rewrite EA3 in MA4, TA4'. rewrite MA in MA4.
  set (s3 := setbn rY y3 s2) in *.
  assert (L4 : length (st_bns (setbn rA a4 s3)) = length (st_bns s)) by (rewrite length_setbn; exact L3).
  assert (EB4 : getbn rB (setbn rA a4 s3) = b2) by (rewrite getbn_setbn_other by exact DAB; exact EB3).
  assert (EA4 : getbn rA (setbn rA a4 s3) = a4) by (apply getbn_setbn_same; rewrite L3; exact VA).
  assert (EY4 : getbn rY (setbn rA a4 s3) = y3) by (rewrite getbn_setbn_other by exact DAY; exact EY3).
  assert (En4 : getbn rn (setbn rA a4 s3) = getbn rn s) by (rewrite getbn_setbn_other by exact DAn; exact En3).
  assert (EX4 : getbn rX (setbn rA a4 s3) = x1) by (rewrite getbn_setbn_other by exact DAX; exact EX3).
  set (s4 := setbn rA a4 s3) in *.

  pose proof (okv_mag_nonneg _ (st_wf_okv rX s1 Hs1 ltac:(rewrite L1; exact VX))) as X10. rewrite EX1 in X10.
  pose proof (okv_mag_nonneg _ (st_wf_okv rY s3 Hs3 ltac:(rewrite L3; exact VY))) as Y30. rewrite EY3 in Y30.
  pose proof (ibl_round a N A B X Y sh1 sh2 (bn_mag x1) (bn_mag y3) On Npos INV Bpos Hsh1 Bm1 Bt1 X10 CX1 BX1 Hsh2 Am3 At3 Y30 CY3 BY3)
    as (HB1 & HA1 & HX1 & HY1 & MU2 & CASE1 & CASE2). cbv zeta in HB1, HA1, CASE1, CASE2.
  rewrite <- MB2' in HB1, CASE1, CASE2. rewrite <- MA4 in HA1, CASE1, CASE2.
  pose proof (st_wf_okv rB s4 Hs4 ltac:(rewrite L4; exact VB)) as OB4. rewrite EB4 in OB4.
  pose proof (st_wf_okv rA s4 Hs4 ltac:(rewrite L4; exact VA)) as OA4. rewrite EA4 in OA4.
  pose proof (st_wf_okv rX s4 Hs4 ltac:(rewrite L4; exact VX)) as OX4. rewrite EX4 in OX4.
  pose proof (st_wf_okv rY s4 Hs4 ltac:(rewrite L4; exact VY)) as OY4. rewrite EY4 in OY4.
  assert (TX4 : (bn_top x1 <= K)%nat) by (apply norm_top_lt; [exact OX4 | exact NX1' | lia]).
  assert (TY4 : (bn_top y3 <= K)%nat) by (apply norm_top_lt; [exact OY4 | exact NY3 | lia]).
  assert (TB4 : (bn_top b2 <= K)%nat) by (apply norm_top_lt; [exact OB4 | exact NB2' | lia]).
  assert (TA4 : (bn_top a4 <= K)%nat) by (apply norm_top_lt; [exact OA4 | exact NA4 | lia]).

  assert (K4 : keeps (gx_used (st_ctx s)) [rX; rB; rY; rA] s s4).
  { unfold s4, s3, s2, s1. repeat (apply keeps_setbn_in; [|cbn; tauto]). apply keeps_refl. }
  assert (HFf : forall A2 B2, 2 * inv_mu A2 B2 < inv_mu A B -> (1 <= f)%nat /\ (B2 = 0 \/ inv_mu A2 B2 < 2 ^ (Z.of_nat f - 1))).
  { intros A2 B2 HM. rewrite Nat2Z.inj_succ in HF. replace (Z.succ (Z.of_nat f) - 1) with (Z.of_nat f) in HF by lia.
    assert (Hf1 : (1 <= f)%nat).
    { destruct f; [|lia]. exfalso. cbn in HF. lia. }
    split; [exact Hf1|]. right.
    assert (E : 2 ^ Z.of_nat f = 2 * 2 ^ (Z.of_nat f - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia). lia. }
  eapply hoare_bind; [apply BN_ucmp_spec; rewrite L4; assumption|]. intros c s5 _ [-> ->]. rewrite EB4, EA4.
  destruct (ucmp_okv_spec b2 a4 OB4 OA4 NB2' NA4) as (U1 & U2 & U3).
  eapply hoare_bind with (R := fun _ s6 => keeps (gx_used (st_ctx s)) [rX; rB; rY; rA] s s6 /\ getbn rn s6 = getbn rn s /\
      length (st_bns s6) = length (st_bns s) /\
      exists A2 B2 X2 Y2, ibl_rep rA rB rX rY A2 B2 X2 Y2 s6 /\ ibl_inv a N A2 B2 X2 Y2 /\ X2 <= N * N /\ Y2 <= N * N /\
        2 * inv_mu A2 B2 < inv_mu A B).
  { destruct (Z.leb_spec 0 (ucmp_pure b2 a4)) as [Hc|Hc].
    -
      assert (HLE : bn_mag a4 <= bn_mag b2).
      { destruct (Z.eq_dec (ucmp_pure b2 a4) 0) as [E|E]; [rewrite (U3 E); lia|]. assert (H0 : 0 < ucmp_pure b2 a4) by lia. pose proof (U1 H0). lia. }
      destruct (CASE1 HLE) as (INV2 & MU2' & XY2).
      eapply hoare_bind.
      { eapply BN_uadd_spec; rewrite ?L4, ?EX4, ?EY4; try assumption. lia. }
      intros [] s6 Hs6 (x6 & -> & (P1 & P2 & P3 & P4)). rewrite EX4, EY4 in P2.
      assert (EA6 : getbn rA (setbn rX x6 s4) = a4) by (rewrite getbn_setbn_other by (apply ndiff_sym; exact DAX); exact EA4).
      assert (EB6 : getbn rB (setbn rX x6 s4) = b2) by (rewrite getbn_setbn_other by (apply ndiff_sym; exact DBX); exact EB4).
      eapply hoare_mono.
      { eapply BN_usub_spec; rewrite ?length_setbn, ?L4, ?EA6, ?EB6; try assumption. }
      intros [] s7 _ (b7 & -> & (Q1 & Q2 & Q3 & Q4)). rewrite EA6, EB6 in Q2. rewrite EB6 in Q4.
      split. { apply keeps_setbn_in; [|cbn; tauto]. apply keeps_setbn_in; [|cbn; tauto]. exact K4. }
      split. { rewrite !getbn_setbn_other by (first [exact DBn | exact DXn]). exact En4. }
      split. { rewrite !length_setbn. exact L4. }
      exists (bn_mag a4), (bn_mag b2 - bn_mag a4), (bn_mag x1 + bn_mag y3), (bn_mag y3).
      split; [|split; [exact INV2 | split; [exact XY2 | split; [exact HY1 | exact MU2']]]].
      assert (FA : getbn rA (setbn rB b7 (setbn rX x6 s4)) = a4) by (rewrite getbn_setbn_other by (apply ndiff_sym; exact DAB); exact EA6).
      assert (FB : getbn rB (setbn rB b7 (setbn rX x6 s4)) = b7) by (apply getbn_setbn_same; rewrite length_setbn, L4; exact VB).
      assert (FX : getbn rX (setbn rB b7 (setbn rX x6 s4)) = x6) by (rewrite getbn_setbn_other by exact DBX; apply getbn_setbn_same; rewrite L4; exact VX).
      assert (FY : getbn rY (setbn rB b7 (setbn rX x6 s4)) = y3) by (rewrite getbn_setbn_other by exact DBY; rewrite getbn_setbn_other by exact DXY; exact EY4).
      unfold ibl_rep. cbv zeta. rewrite FA, FB, FX, FY. repeat split; try assumption; reflexivity.
    -
      pose proof (U2 Hc) as HLT.
      destruct (CASE2 HLT) as (INV2 & MU2' & XY2).
      eapply hoare_bind.
      { eapply BN_uadd_spec; rewrite ?L4, ?EX4, ?EY4; try assumption. lia. }
      intros [] s6 Hs6 (y6 & -> & (P1 & P2 & P3 & P4)). rewrite EY4, EX4 in P2.
      assert (EA6 : getbn rA (setbn rY y6 s4) = a4) by (rewrite getbn_setbn_other by exact DYA; exact EA4).
      assert (EB6 : getbn rB (setbn rY y6 s4) = b2) by (rewrite getbn_setbn_other by (apply ndiff_sym; exact DBY); exact EB4).
      eapply hoare_mono.
      { eapply BN_usub_spec; rewrite ?length_setbn, ?L4, ?EA6, ?EB6; try assumption. lia. }
      intros [] s7 _ (a7 & -> & (Q1 & Q2 & Q3 & Q4)). rewrite EA6, EB6 in Q2. rewrite EA6 in Q4.
      split. { apply keeps_setbn_in; [|cbn; tauto]. apply keeps_setbn_in; [|cbn; tauto]. exact K4. }
      split. { rewrite !getbn_setbn_other by (first [exact DAn | exact DYn]). exact En4. }
      split. { rewrite !length_setbn. exact L4. }
      exists (bn_mag a4 - bn_mag b2), (bn_mag b2), (bn_mag x1), (bn_mag y3 + bn_mag x1).
      split; [|split; [exact INV2 | split; [exact HX1 | split; [exact XY2 | exact MU2']]]].
      assert (FA : getbn rA (setbn rA a7 (setbn rY y6 s4)) = a7) by (apply getbn_setbn_same; rewrite length_setbn, L4; exact VA).
      assert (FB : getbn rB (setbn rA a7 (setbn rY y6 s4)) = b2) by (rewrite getbn_setbn_other by exact DAB; exact EB6).
      assert (FX : getbn rX (setbn rA a7 (setbn rY y6 s4)) = x1) by (rewrite getbn_setbn_other by exact DAX; rewrite getbn_setbn_other by (apply ndiff_sym; exact DXY); exact EX4).
      assert (FY : getbn rY (setbn rA a7 (setbn rY y6 s4)) = y6) by (rewrite getbn_setbn_other by exact DAY; apply getbn_setbn_same; rewrite L4; exact VY).
      unfold ibl_rep. cbv zeta. rewrite FA, FB, FX, FY. repeat split; try assumption; reflexivity. }

  intros [] s6 Hs6 (K6 & En6 & L6 & A2 & B2 & X2 & Y2 & REP6 & INV6 & HX6 & HY6 & MU6).
  destruct (HFf _ _ MU6) as (Hf1 & HF6).
  eapply hoare_mono.
  { apply (IH rA rB rX rY rn a A2 B2 X2 Y2 K); rewrite ?L6, ?En6; try assumption. }
  intros [] s7 _ (K7 & En7 & POST7). rewrite (keeps_used _ _ _ _ K6) in K7. rewrite En6 in En7, POST7.
  split; [|split; [exact En7 | exact POST7]].
  eapply keeps_weaken; [apply Nat.le_refl | | eapply keeps_trans; [exact K6 | exact K7]].
  intros z Hz _. apply in_app_or in Hz. destruct Hz as [Hz|Hz]; exact Hz.
Qed.

Lemma norm_mag_one : forall b : BN, bg_okv b -> bn_norm b -> bn_mag b = 1 -> bn_top b = 1%nat /\ nth 0 (bn_buf b) 0 = 1.
Proof.
  intros b Hb Hn Hm.
  assert (T1 : (bn_top b <= 1)%nat) by (apply norm_top_lt; [exact Hb | exact Hn | rewrite Hm; unfold Bp, BW; cbn; lia]).
  destruct (Nat.eq_dec (bn_top b) 0) as [E|E]; [exfalso; rewrite (proj1 (norm_zero_iff _ Hb Hn) E) in Hm; lia|].
  assert (T : bn_top b = 1%nat) by lia. split; [exact T|].
  unfold bn_mag in Hm. rewrite T in Hm. destruct (bn_buf b) as [|x l]; [cbn in Hm; lia|]. cbn [firstn nth] in *.
  cbn [lval] in Hm. lia.
Qed.

Definition modinv_pre (rR ra rn : bnref) (s : ST) : Prop :=
  live rR s /\ live ra s /\ live rn s /\ ndiff rR ROne /\ ndiff rR rn /\
  (length (gx_frames (st_ctx s)) + 2 <= BG_DEPTH)%nat /\ (gx_used (st_ctx s) + 11 <= BG_POOL)%nat /\
  (let n := getbn rn s in bn_norm n /\ bn_neg n = false /\ bn_top n = 1%nat /\ Z.odd (bn_mag n) = true /\ 1 < bn_mag n) /\
  (let x := getbn ra s in bn_norm x /\ bn_neg x = false /\ (bn_top x <= 2)%nat /\ Z.gcd (bn_mag x) (bn_mag (getbn rn s)) = 1).

Lemma BN_mod_inverse_spec : forall rR ra rn F s,
  modinv_pre rR ra rn s ->
  hoare F s (BN_mod_inverse ops rR ra rn) (fun _ s' =>
    keeps (gx_used (st_ctx s)) [rR] s s' /\
    let r := getbn rR s' in bn_canon r /\ bn_neg r = false /\ 0 <= bn_mag r < bn_mag (getbn rn s) /\ (bn_top r <= 1)%nat /\
      (bn_mag r * bn_mag (getbn ra s)) mod bn_mag (getbn rn s) = 1).
Proof.
  intros rR ra rn F s (LR & La & Ln & NR1 & NRn & Hdepth & Hpool & (Nn & Sn & Tn & On & N1) & (Na & Sa & Ta & Ga)).
  apply hoare_wf. intros Hs. unfold BN_mod_inverse. set (u := gx_used (st_ctx s)) in *.
  pose proof (live_valid _ _ Hs LR) as VR. pose proof (live_valid _ _ Hs La) as Va. pose proof (live_valid _ _ Hs Ln) as Vn.
  unfold live in LR, La, Ln. fold u in LR, La, Ln.
  set (n := getbn rn s) in *. set (x := getbn ra s) in *. set (N := bn_mag n) in *.
  pose proof (st_wf_okv rn s Hs Vn) as On'. fold n in On'. pose proof (st_wf_okv ra s Hs Va) as Oa. fold x in Oa.
  pose proof (okv_mag_nonneg _ Oa) as X0.
  assert (NB : N < Bp 1) by (pose proof (okv_mag_lt _ On') as HH; fold N in HH; rewrite Tn in HH; exact HH).
  apply hoare_bind_get. apply hoare_bind_get. fold n x.

  replace (abs_is_word_pure n 1 || is_zero_pure n) with false.
  2:{ unfold abs_is_word_pure, is_zero_pure. rewrite Tn. cbn [Nat.eqb andb orb].
      destruct (Z.eqb_spec (nth 0 (bn_buf n) 0) 1) as [E|]; [|reflexivity]. exfalso.
      unfold N, bn_mag in N1. rewrite Tn in N1. destruct (bn_buf n) as [|y l]; cbn in E, N1; [lia|]. cbn [lval] in N1. lia. }
  rewrite (st_wf_no_flag ra s _ Hs Va) by (left; reflexivity). rewrite (st_wf_no_flag rn s _ Hs Vn) by (left; reflexivity). cbn [orb].

  eapply hoare_bind; [apply BN_CTX_start_spec; unfold BG_DEPTH in *; lia|].
  intros [] s0 Hs0 (Eb0 & Sc0 & Eu0 & Ef0). fold u in Eu0, Ef0.
  pose proof (inner_bns_eq u s s0 Eb0 Sc0) as I0.
  eapply hoare_bind; [apply BN_CTX_get_spec; rewrite Eu0; unfold BG_POOL in *; lia|].
  intros rA g1 Hg1 (ErA & Eu1 & Ef1 & Sc1 & Len1 & Oth1 & _). rewrite Eu0 in ErA, Eu1.
  pose proof (inner_get u rA s0 g1 Len1 Sc1 Oth1 ltac:(rewrite ErA; unfold RPool; lia)) as I1.
  eapply hoare_bind; [apply BN_CTX_get_spec; rewrite Eu1; unfold BG_POOL in *; lia|].
  intros rB g2 Hg2 (ErB & Eu2 & Ef2 & Sc2 & Len2 & Oth2 & _). rewrite Eu1 in ErB, Eu2.
  pose proof (inner_get u rB g1 g2 Len2 Sc2 Oth2 ltac:(rewrite ErB; unfold RPool; lia)) as I2.
  eapply hoare_bind; [apply BN_CTX_get_spec; rewrite Eu2; unfold BG_POOL in *; lia|].
  intros rX g3 Hg3 (ErX & Eu3 & Ef3 & Sc3 & Len3 & Oth3 & _). rewrite Eu2 in ErX, Eu3.
  pose proof (inner_get u rX g2 g3 Len3 Sc3 Oth3 ltac:(rewrite ErX; unfold RPool; lia)) as I3.
  eapply hoare_bind; [apply BN_CTX_get_spec; rewrite Eu3; unfold BG_POOL in *; lia|].
  intros rD g4 Hg4 (ErD & Eu4 & Ef4 & Sc4 & Len4 & Oth4 & _). rewrite Eu3 in ErD, Eu4.
  pose proof (inner_get u rD g3 g4 Len4 Sc4 Oth4 ltac:(rewrite ErD; unfold RPool; lia)) as I4.
  eapply hoare_bind; [apply BN_CTX_get_spec; rewrite Eu4; unfold BG_POOL in *; lia|].
  intros rM g5 Hg5 (ErM & Eu5 & Ef5 & Sc5 & Len5 & Oth5 & _). rewrite Eu4 in ErM, Eu5.
  pose proof (inner_get u rM g4 g5 Len5 Sc5 Oth5 ltac:(rewrite ErM; unfold RPool; lia)) as I5.
  eapply hoare_bind; [apply BN_CTX_get_spec; rewrite Eu5; unfold BG_POOL in *; lia|].
  intros rY g6 Hg6 (ErY & Eu6 & Ef6 & Sc6 & Len6 & Oth6 & _). rewrite Eu5 in ErY, Eu6.
  pose proof (inner_get u rY g5 g6 Len6 Sc6 Oth6 ltac:(rewrite ErY; unfold RPool; lia)) as I6.
  eapply hoare_bind; [apply BN_CTX_get_spec; rewrite Eu6; unfold BG_POOL in *; lia|].
  intros rT g7 Hg7 (ErT & Eu7 & Ef7 & Sc7 & Len7 & Oth7 & _). rewrite Eu6 in ErT, Eu7.
  pose proof (inner_get u rT g6 g7 Len7 Sc7 Oth7 ltac:(rewrite ErT; unfold RPool; lia)) as I7.
  pose proof (inner_trans _ _ _ _ _ _ (inner_trans _ _ _ _ _ _ (inner_trans _ _ _ _ _ _ (inner_trans _ _ _ _ _ _
              (inner_trans _ _ _ _ _ _ (inner_trans _ _ _ _ _ _ (inner_trans _ _ _ _ _ _ I0 I1) I2) I3) I4) I5) I6) I7) as I07. cbn [app] in I07.
  replace (S (S (S (S (S (S (S u))))))) with (u + 7)%nat in Eu7 by lia.
  assert (G7 : forall z, (z < NFIX + u)%nat -> getbn z g7 = getbn z s) by (intros z Hz; apply (inner_get_slot _ _ _ _ z I07 Hz); intros []).
  assert (Ef7' : gx_frames (st_ctx g7) = gx_frames (st_ctx s) ++ [u]) by (rewrite Ef7, Ef6, Ef5, Ef4, Ef3, Ef2, Ef1; exact Ef0).
  assert (V7 : forall z, (z < NFIX + (u + 7))%nat -> (z < length (st_bns g7))%nat).
  { intros z Hz. apply live_valid; [exact Hg7|]. unfold live. rewrite Eu7. lia. }

  assert (DD : ndiff rA rB /\ ndiff rA rX /\ ndiff rA rY /\ ndiff rA rn /\ ndiff rB rX /\ ndiff rB rY /\ ndiff rB rn /\ ndiff rX rY /\ ndiff rX rn /\
               ndiff rY rn /\ ndiff rA ra /\ ndiff rB ra /\ ndiff rX ra /\ ndiff rY ra /\ ndiff rA rR /\ ndiff rB rR /\ ndiff rX rR /\ ndiff rY rR /\
               rA <> ROne /\ rB <> ROne /\ rX <> ROne /\ rY <> ROne).
  { rewrite ErA, ErB, ErX, ErY. unfold ndiff, RPool, ROne, NFIX in *. repeat split; lia. }
  destruct DD as (DAB & DAX & DAY & DAn & DBX & DBY & DBn & DXY & DXn & DYn & DAa & DBa & DXa & DYa & DAR & DBR & DXR & DYR & NA1 & NB1 & NX1 & NY1).
  assert (DYA' : ndiff rY rA) by (exact (ndiff_sym _ _ DAY)).
  assert (VA : (rA < length (st_bns g7))%nat) by (apply V7; rewrite ErA; unfold RPool; lia).
  assert (VB : (rB < length (st_bns g7))%nat) by (apply V7; rewrite ErB; unfold RPool; lia).
  assert (VX : (rX < length (st_bns g7))%nat) by (apply V7; rewrite ErX; unfold RPool; lia).
  assert (VY : (rY < length (st_bns g7))%nat) by (apply V7; rewrite ErY; unfold RPool; lia).
  assert (Va7 : (ra < length (st_bns g7))%nat) by (apply V7; lia).
  assert (Vn7 : (rn < length (st_bns g7))%nat) by (apply V7; lia).
  assert (VR7 : (rR < length (st_bns g7))%nat) by (apply V7; lia).

  eapply hoare_bind; [apply BN_one_spec; [exact VX | exact NX1]|].
  intros [] s8 Hs8 (x8 & -> & (MX8 & [NX8 _] & SX8 & TX8)).

  eapply hoare_bind; [apply BN_zero_spec; [rewrite length_setbn; exact VY | exact NY1]|].
  intros [] s9 Hs9 (y9 & -> & (TY9 & SY9)).

  eapply hoare_bind; [apply BN_copy_spec; rewrite ?length_setbn; [exact VB | exact NB1 | exact Va7]|].
  intros [] s10 Hs10 (b10 & -> & (TB10 & SB10 & FB10)).
  rewrite !getbn_setbn_other in TB10, SB10, FB10 by (first [exact DYa | exact DXa]). rewrite (G7 ra La) in TB10, SB10, FB10. fold x in TB10, SB10, FB10.
  pose proof (mag_of_firstn_eq b10 x TB10 FB10) as MB10. pose proof (norm_of_firstn_eq b10 x TB10 FB10 Na) as NB10.

  eapply hoare_bind; [apply BN_copy_spec; rewrite ?length_setbn; [exact VA | exact NA1 | exact Vn7]|].
  intros [] s11 Hs11 (a11 & -> & (TA11 & SA11 & FA11)).
  rewrite !getbn_setbn_other in TA11, SA11, FA11 by (first [exact DBn | exact DYn | exact DXn]). rewrite (G7 rn Ln) in TA11, SA11, FA11. fold n in TA11, SA11, FA11.
  pose proof (mag_of_firstn_eq a11 n TA11 FA11) as MA11. pose proof (norm_of_firstn_eq a11 n TA11 FA11 Nn) as NA11.
  set (s11 := setbn rA a11 (setbn rB b10 (setbn rY y9 (setbn rX x8 g7)))) in *.
  assert (L11 : length (st_bns s11) = length (st_bns g7)) by (unfold s11; rewrite !length_setbn; reflexivity).
  eapply hoare_bind.
  { apply (set_neg_spec rA false F s11 (fun b => bn_norm b /\ bn_neg b = false /\ bn_mag b = N /\ bn_top b = 1%nat));
      [rewrite L11; exact VA | exact NA1 |].
    unfold s11. rewrite getbn_setbn_same by (rewrite !length_setbn; exact VA).
    split; [exact NA11|]. split; [reflexivity|]. split; [exact MA11 | change (bn_top a11 = 1%nat); rewrite TA11; exact Tn]. }
  intros [] s12 Hs12 (a12 & -> & (NA12 & SA12 & MA12 & TA12)).
  set (s12 := setbn rA a12 s11) in *.
  assert (L12 : length (st_bns s12) = length (st_bns g7)) by (unfold s12; rewrite length_setbn; exact L11).
  assert (EA12 : getbn rA s12 = a12) by (unfold s12; apply getbn_setbn_same; rewrite L11; exact VA).
  assert (EB12 : getbn rB s12 = b10).
  { unfold s12, s11. rewrite !getbn_setbn_other by (first [exact DAB]). apply getbn_setbn_same. rewrite !length_setbn. exact VB. }
  assert (EX12 : getbn rX s12 = x8).
  { unfold s12, s11. rewrite !getbn_setbn_other by (first [exact DAX | exact DBX | apply ndiff_sym; exact DXY]). apply getbn_setbn_same. exact VX. }
  assert (EY12 : getbn rY s12 = y9).
  { unfold s12, s11. rewrite !getbn_setbn_other by (first [exact DAY | exact DBY]). apply getbn_setbn_same. rewrite length_setbn. exact VY. }
  assert (G12 : forall z, (z < NFIX + u)%nat -> getbn z s12 = getbn z s).
  { intros z Hz. unfold s12, s11. rewrite !getbn_setbn_other by (rewrite ?ErA, ?ErB, ?ErX, ?ErY; unfold RPool; lia). apply G7. exact Hz. }
  assert (K12 : keeps (u + 7) [rX; rY; rB; rA] g7 s12).
  { unfold s12, s11. repeat (apply keeps_setbn_in; [|cbn; tauto]). apply keeps_refl. }
  pose proof (st_wf_okv rB s12 Hs12 ltac:(rewrite L12; exact VB)) as OB12. rewrite EB12 in OB12.
  pose proof (st_wf_okv rA s12 Hs12 ltac:(rewrite L12; exact VA)) as OA12. rewrite EA12 in OA12.
  assert (Npos : 0 < N) by lia.

  apply hoare_bind_get. rewrite EB12, SB10, Sa. cbn [orb].
  eapply hoare_bind; [apply BN_ucmp_spec; rewrite L12; assumption|]. intros c s12' _ [-> ->]. rewrite EB12, EA12.
  destruct (ucmp_okv_spec b10 a12 OB12 OA12 NB10 NA12) as (U1 & U2 & U3). rewrite MB10, MA12 in U1, U2, U3.
  eapply hoare_bind with (R := fun _ s13 => keeps (u + 7) [rB] s12 s13 /\
      let b := getbn rB s13 in bn_norm b /\ bn_neg b = false /\ bn_mag b = bn_mag x mod N /\ (bn_top b <= 2)%nat).
  { destruct (Z.leb_spec 0 (ucmp_pure b10 a12)) as [Hc|Hc].
    - eapply hoare_mono.
      + apply BN_nnmod_spec. unfold nnmod_pre, live. rewrite (keeps_used _ _ _ _ K12), (keeps_frames _ _ _ _ K12), Eu7, Ef7', length_app, EB12, EA12.
        cbn [length].
        split; [rewrite ErB; unfold RPool; lia|]. split; [rewrite ErB; unfold RPool; lia|]. split; [rewrite ErA; unfold RPool; lia|].
        split; [exact NB1|]. split; [exact (ndiff_sym _ _ DAB)|].
        split; [unfold BG_DEPTH in *; lia|]. split; [unfold BG_POOL in *; lia|]. split; [exact NA12|]. split; [rewrite TA12; lia|].
        rewrite TB10, TA12. pose proof Ta. unfold BG_DMAX. lia.
      + intros [] s13 _ (K13 & (C13 & S13 & M13 & T13)). rewrite EB12, EA12, MA12 in M13. rewrite EA12, TA12 in T13. rewrite (keeps_used _ _ _ _ K12), Eu7 in K13.
        split; [exact K13|]. cbv zeta. destruct C13 as [N13 _]. split; [exact N13|]. split; [exact S13|].
        split; [rewrite M13; unfold bn_val; rewrite SB10, MB10; fold x; rewrite Sa; reflexivity | lia].
    - apply hoare_ret. split; [apply keeps_refl|]. cbv zeta. rewrite EB12. split; [exact NB10|]. split; [rewrite SB10; exact Sa|].
      split; [rewrite MB10; symmetry; apply Z.mod_small; pose proof (U2 Hc); fold x in X0; lia | lia]. }
  intros [] s13 Hs13 (K13 & NB13 & SB13 & MB13 & TB13). cbv zeta in NB13, SB13, MB13, TB13.
  assert (S13 : forall z, (z < NFIX + (u + 7))%nat -> z <> rB -> getbn z s13 = getbn z s12).
  { intros z Hl Hz. destruct K13 as [[_ Sl] _]. apply Sl; [exact Hl | intros [E|[]]; exact (Hz (eq_sym E))]. }
  pose proof (keeps_used _ _ _ _ K13) as Eu13. rewrite (keeps_used _ _ _ _ K12), Eu7 in Eu13.
  pose proof (keeps_frames _ _ _ _ K13) as Ef13. rewrite (keeps_frames _ _ _ _ K12), Ef7' in Ef13.
  assert (V13 : forall z, (z < NFIX + (u + 7))%nat -> (z < length (st_bns s13))%nat).
  { intros z Hz. apply live_valid; [exact Hs13|]. unfold live. rewrite Eu13. lia. }
  assert (PA : (rA < NFIX + (u + 7))%nat) by (rewrite ErA; unfold RPool; lia).
  assert (PB : (rB < NFIX + (u + 7))%nat) by (rewrite ErB; unfold RPool; lia).
  assert (PX : (rX < NFIX + (u + 7))%nat) by (rewrite ErX; unfold RPool; lia).
  assert (PY : (rY < NFIX + (u + 7))%nat) by (rewrite ErY; unfold RPool; lia).
  assert (EA13 : getbn rA s13 = a12) by (rewrite (S13 rA PA DAB); exact EA12).
  assert (EX13 : getbn rX s13 = x8) by (rewrite (S13 rX PX (ndiff_sym _ _ DBX)); exact EX12).
  assert (EY13 : getbn rY s13 = y9) by (rewrite (S13 rY PY (ndiff_sym _ _ DBY)); exact EY12).
  assert (En13 : getbn rn s13 = n) by (rewrite (S13 rn ltac:(lia) (ndiff_sym _ _ DBn)); rewrite (G12 rn Ln); reflexivity).
  assert (Ea13 : getbn ra s13 = x) by (rewrite (S13 ra ltac:(lia) (ndiff_sym _ _ DBa)); rewrite (G12 ra La); reflexivity).
  assert (ER13 : getbn rR s13 = getbn rR s) by (rewrite (S13 rR ltac:(lia) (ndiff_sym _ _ DBR)); apply (G12 rR LR)).

  eapply hoare_bind; [apply BN_num_bits_spec; apply V13; lia|]. intros nb s13' _ [-> ->]. rewrite En13.
  apply hoare_bind_get. rewrite En13.
  pose proof (num_bits_pure_spec _ On' Nn) as (Hnb0 & _ & Hnb2 & Hnb3). fold N in Hnb2. specialize (Hnb2 Npos). rewrite Tn in Hnb3.
  rewrite (is_odd_pure_spec _ On'). fold N. rewrite On.
  replace (num_bits_pure n <=? 2048) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
  assert (NN : N * N + N < Bp 2).
  { change (Bp 2) with (Bp 1 * Bp 1). assert (N * N + N = N * (N + 1)) by ring.
    assert (N * (N + 1) <= (Bp 1 - 1) * Bp 1) by (apply Z.mul_le_mono_nonneg; lia). assert (0 < Bp 1) by (unfold Bp, BW; cbn; lia).
    replace ((Bp 1 - 1) * Bp 1) with (Bp 1 * Bp 1 - Bp 1) in * by ring. lia. }
  eapply hoare_bind.
  { apply (inv_binary_loop_spec _ rA rB rX rY rn (bn_mag x) N (bn_mag x mod N) 1 0 2 F s13);
      rewrite ?En13, ?EA13, ?EX13, ?EY13; try (apply V13; lia); try assumption; fold N.
    - unfold BG_DMAX. lia.
    - unfold ibl_rep. cbv zeta. rewrite EA13, EX13, EY13.
      split; [split; [exact NA12 | split; [exact SA12 | exact MA12]]|].
      split; [split; [exact NB13 | split; [exact SB13 | exact MB13]]|].
      split; [split; [exact NX8 | split; [exact SX8 | exact MX8]]|].
      split; [left; exact TY9 | split; [exact SY9 | unfold bn_mag; rewrite TY9; reflexivity]].
    - unfold ibl_inv. pose proof (Z.mod_pos_bound (bn_mag x) N Npos) as MB.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [rewrite Z.mul_1_l, Z.mul_0_l, Z.add_0_r; replace N with (N * 1) at 1 by lia; apply Z.mul_le_mono_nonneg_l; lia|].
      split; [rewrite Z.mul_1_l, Z.mod_mod by lia; reflexivity|].
      split; [rewrite Z.mul_0_l, Z.add_0_l; apply Z.mod_same; lia|].
      rewrite Z.gcd_comm, Z.gcd_mod_l. exact Ga.
    - assert (1 * 1 <= N * N) by (apply Z.mul_le_mono_nonneg; lia). lia.
    - apply Z.mul_nonneg_nonneg; lia.
    - lia.
    - right. pose proof (Z.mod_pos_bound (bn_mag x) N Npos) as MB.
      rewrite Nat2Z.inj_add, Z2Nat.id by lia. replace (2 * num_bits_pure n + Z.of_nat 2 - 1) with (2 * num_bits_pure n + 1) by lia.
      assert (P2 : N * N < 2 ^ (2 * num_bits_pure n)).
      { replace (2 * num_bits_pure n) with (num_bits_pure n + num_bits_pure n) by lia. rewrite Z.pow_add_r by lia.
        apply Z.mul_lt_mono_nonneg; lia. }
      rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2.
      assert (NB0 : 0 <= N * (bn_mag x mod N)) by (apply Z.mul_nonneg_nonneg; lia).
      assert (MU : inv_mu N (bn_mag x mod N) <= 2 * (N * (bn_mag x mod N))) by (unfold inv_mu; destruct (Z.even _); lia).
      assert (NB1' : N * (bn_mag x mod N) <= N * (N - 1)) by (apply Z.mul_le_mono_nonneg_l; lia).
      replace (N * (N - 1)) with (N * N - N) in NB1' by ring. lia. }
  intros [] s14 Hs14 (K14 & En14 & A' & X' & Y' & REP14 & INV14 & HX14 & HY14). rewrite Eu13 in K14. rewrite En13 in En14, INV14, HX14, HY14. fold N in INV14, HX14, HY14.
  pose proof (keeps_used _ _ _ _ K14) as Eu14. rewrite Eu13 in Eu14. pose proof (keeps_frames _ _ _ _ K14) as Ef14. rewrite Ef13 in Ef14.
  assert (V14 : forall z, (z < NFIX + (u + 7))%nat -> (z < length (st_bns s14))%nat).
  { intros z Hz. apply live_valid; [exact Hs14|]. unfold live. rewrite Eu14. lia. }
  assert (S14 : forall z, (z < NFIX + u)%nat -> getbn z s14 = getbn z s13).
  { intros z Hz. destruct K14 as [[_ Sl] _]. apply Sl; [lia|]. intros Hin. cbn [In] in Hin. rewrite ErX, ErB, ErY, ErA in Hin. unfold RPool in Hin. lia. }
  destruct REP14 as ((NA14 & SA14 & MA14) & _ & _ & (NY14 & SY14 & MY14)). cbv zeta in NA14, SA14, MA14, NY14, SY14, MY14.
  pose proof INV14 as (_ & IA' & _ & IY' & _ & _ & IC2 & IG'). rewrite (Z.gcd_0_r_nonneg A') in IG' by lia.
  pose proof (st_wf_okv rY s14 Hs14 (V14 rY PY)) as OY14. pose proof (st_wf_okv rA s14 Hs14 (V14 rA PA)) as OA14.
  assert (TY14 : (bn_top (getbn rY s14) <= 2)%nat) by (apply norm_top_lt; [exact OY14 | exact NY14 | rewrite MY14; lia]).

  eapply hoare_bind.
  { apply BN_sub_spec; try (apply V14; lia); [exact NY1 | rewrite En14; split; [exact Nn | rewrite Tn; discriminate] | split; [exact NY14 | intros _; exact SY14] |].
    rewrite En14, Tn. unfold BG_DMAX. lia. }
  intros [] s15 Hs15 (y15 & -> & (CY15 & VY15 & TY15)). rewrite En14, Tn in TY15. rewrite En14 in VY15.
  unfold bn_val in VY15 at 2 3. rewrite SY14, MY14 in VY15.
  rewrite Sn in VY15. fold N in VY15.
  assert (L15 := length_setbn rY y15 s14).
  assert (EA15 : getbn rA (setbn rY y15 s14) = getbn rA s14) by (apply getbn_setbn_other; exact DYA').
  pose proof (norm_mag_one _ OA14 NA14 ltac:(rewrite MA14; exact IG')) as [TA1 BA1].

  apply hoare_bind_get. rewrite EA15. unfold is_one_pure, abs_is_word_pure. rewrite TA1, BA1, SA14. cbn [Nat.eqb Z.eqb andb orb negb].
  assert (V15 : forall z, (z < NFIX + (u + 7))%nat -> (z < length (st_bns (setbn rY y15 s14)))%nat) by (intros z Hz; rewrite L15; apply V14; exact Hz).
  assert (EY15 : getbn rY (setbn rY y15 s14) = y15) by (apply getbn_setbn_same; apply V14; exact PY).
  assert (En15 : getbn rn (setbn rY y15 s14) = n) by (rewrite getbn_setbn_other by exact DYn; exact En14).
  pose proof (st_wf_okv rY _ Hs15 (V15 rY PY)) as OY15. rewrite EY15 in OY15.
  destruct CY15 as [NY15 ZY15].
  eapply hoare_bind with (R := fun _ s16 => keeps (u + 7) [rR] (setbn rY y15 s14) s16 /\
      let r := getbn rR s16 in bn_canon r /\ bn_neg r = false /\ 0 <= bn_mag r < N /\ (bn_top r <= 1)%nat /\ bn_mag r mod N = (N - Y') mod N).
  { apply hoare_bind_get. rewrite EY15.
    eapply hoare_bind; [apply BN_ucmp_spec; apply V15; lia|]. intros c s15' _ [-> ->]. rewrite EY15, En15.
    destruct (ucmp_okv_spec y15 n OY15 On' NY15 Nn) as (U1' & U2' & U3'). fold N in U1', U2', U3'.
    destruct (bn_neg y15) eqn:SY15; cbn [negb andb].
    -
      eapply hoare_mono.
      + apply BN_nnmod_spec. unfold nnmod_pre, live. rewrite (keeps_used _ _ _ _ (keeps_setbn (u + 7) rY y15 s14)), Eu14.
        rewrite (keeps_frames _ _ _ _ (keeps_setbn (u + 7) rY y15 s14)), Ef14, length_app, EY15, En15, Tn. cbn [length].
        split; [lia|]. split; [rewrite ErY; unfold RPool; lia|]. split; [lia|]. split; [exact NR1|]. split; [exact NRn|].
        split; [unfold BG_DEPTH in *; lia|]. split; [unfold BG_POOL in *; lia|]. split; [exact Nn|]. split; [lia|]. unfold BG_DMAX. lia.
      + intros [] s16 _ (K16 & (C16 & S16 & M16 & T16)). rewrite EY15, En15 in M16. rewrite En15, Tn in T16. fold N in M16.
        rewrite (keeps_used _ _ _ _ (keeps_setbn (u + 7) rY y15 s14)), Eu14 in K16.
        split; [exact K16|]. cbv zeta. pose proof (Z.mod_pos_bound (bn_val y15) N Npos).
        split; [exact C16|]. split; [exact S16|]. split; [rewrite M16; lia|]. split; [exact T16|]. rewrite M16, VY15, Z.mod_mod by lia. reflexivity.
    - destruct (Z.ltb_spec (ucmp_pure y15 n) 0) as [Hc|Hc].
      +
        pose proof (U2' Hc) as HLT. assert (MYv : bn_mag y15 = N - Y') by (unfold bn_val in VY15; rewrite SY15 in VY15; exact VY15).
        eapply hoare_mono; [apply BN_copy_spec; [apply V15; lia | exact NR1 | apply V15; exact PY]|].
        intros [] s16 _ (r16 & -> & (TR & SR & FR)). rewrite EY15 in TR, SR, FR.
        pose proof (mag_of_firstn_eq r16 y15 TR FR) as MR. pose proof (norm_of_firstn_eq r16 y15 TR FR NY15) as NRm.
        split; [apply keeps_setbn|]. cbv zeta. rewrite getbn_setbn_same by (apply V15; lia).
        assert (TY1 : (bn_top y15 <= 1)%nat) by (apply norm_top_lt; [exact OY15 | exact NY15 | lia]).
        split; [split; [exact NRm | intros _; rewrite SR; exact SY15]|]. split; [rewrite SR; exact SY15|].
        split; [rewrite MR, MYv; pose proof (okv_mag_nonneg _ OY15); lia|]. split; [rewrite TR; exact TY1|]. rewrite MR, MYv. reflexivity.
      +
        eapply hoare_mono.
        * apply BN_nnmod_spec. unfold nnmod_pre, live. rewrite (keeps_used _ _ _ _ (keeps_setbn (u + 7) rY y15 s14)), Eu14.
          rewrite (keeps_frames _ _ _ _ (keeps_setbn (u + 7) rY y15 s14)), Ef14, length_app, EY15, En15, Tn. cbn [length].
          split; [lia|]. split; [rewrite ErY; unfold RPool; lia|]. split; [lia|]. split; [exact NR1|]. split; [exact NRn|].
          split; [unfold BG_DEPTH in *; lia|]. split; [unfold BG_POOL in *; lia|]. split; [exact Nn|]. split; [lia|]. unfold BG_DMAX. lia.
        * intros [] s16 _ (K16 & (C16 & S16 & M16 & T16)). rewrite EY15, En15 in M16. rewrite En15, Tn in T16. fold N in M16.
          rewrite (keeps_used _ _ _ _ (keeps_setbn (u + 7) rY y15 s14)), Eu14 in K16.
          split; [exact K16|]. cbv zeta. pose proof (Z.mod_pos_bound (bn_val y15) N Npos).
          split; [exact C16|]. split; [exact S16|]. split; [rewrite M16; lia|]. split; [exact T16|]. rewrite M16, VY15, Z.mod_mod by lia. reflexivity. }
  intros [] s16 Hs16 (K16 & CR & SR & MR & TR & QR). cbv zeta in CR, SR, MR, TR, QR.
  pose proof (keeps_used _ _ _ _ K16) as Eu16. rewrite (keeps_used _ _ _ _ (keeps_setbn (u + 7) rY y15 s14)), Eu14 in Eu16.
  pose proof (keeps_frames _ _ _ _ K16) as Ef16. rewrite (keeps_frames _ _ _ _ (keeps_setbn (u + 7) rY y15 s14)), Ef14 in Ef16.

  eapply hoare_mono; [apply (BN_CTX_end_spec F s16 (gx_frames (st_ctx s)) u); exact Ef16|].
  intros [] s17 _ (Eb17 & Sc17 & Eu17 & Ef17).
  assert (G17 : forall z, getbn z s17 = getbn z s16) by (intros z; unfold getbn; rewrite Eb17; reflexivity).
  split.
  -
    assert (SL : slots_same u [rR] s s17).
    { intros z Hz Hnin. assert (HzR : z <> rR) by (intros E; apply Hnin; left; symmetry; exact E).
      rewrite G17. destruct K16 as [[_ Sl16] _]. rewrite Sl16; [|lia|intros [E|[]]; exact (HzR (eq_sym E))].
      rewrite getbn_setbn_other by (rewrite ErY; unfold RPool; lia). rewrite (S14 z Hz). rewrite (S13 z ltac:(lia) ltac:(rewrite ErB; unfold RPool; lia)).
      apply G12. exact Hz. }
    assert (SC : scal_same s s17).
    { destruct I07 as (_ & Sc07 & _). destruct K12 as [_ Sc12]. destruct K13 as [_ Sc13']. destruct K14 as [_ Sc14]. destruct K16 as [_ Sc16].
      pose proof (proj2 (keeps_setbn (u + 7) rY y15 s14)) as Sc15.
      exact (scal_same_trans _ _ _ Sc07 (scal_same_trans _ _ _ Sc12 (scal_same_trans _ _ _ Sc13' (scal_same_trans _ _ _ Sc14
               (scal_same_trans _ _ _ Sc15 (scal_same_trans _ _ _ Sc16 Sc17)))))). }
    split; [split; [|exact SL]|exact SC]. unfold ctx_keep. rewrite Eb17, Eu17, Ef17. split; [|split; reflexivity].
    destruct K16 as [[(L16 & _) _] _]. rewrite length_setbn in L16.
    destruct K14 as [[(L14 & _) _] _]. destruct K13 as [[(L13 & _) _] _]. rewrite L12 in L13. destruct I07 as (L07 & _). lia.
  - cbv zeta. rewrite G17. split; [exact CR|]. split; [exact SR|]. split; [exact MR|]. split; [exact TR|].
    rewrite IG' in IC2. apply (inv_final N Y' (bn_mag x) (bn_mag (getbn rR s16)) N1 IC2 QR).
Qed.

End InvSpec.
