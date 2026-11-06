(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool.
From Stdlib Require Import Uint63.
From stdpp.bitvector Require Import bitvector.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Open Scope Z_scope.

#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Record w64 : Set := W { wh : bool; wl : int }.

Definition two63 : Z := 9223372036854775808.
Definition two64 : Z := 18446744073709551616.

Lemma wB_eq : wB = two63.
Proof. reflexivity. Qed.

Lemma two64_eq : two64 = 2 * two63.
Proof. reflexivity. Qed.

Lemma bv_modulus_64 : bv_modulus 64 = two64.
Proof. reflexivity. Qed.

Lemma phi_range (x : int) : 0 <= to_Z x < two63.
Proof. rewrite <- wB_eq. apply to_Z_bounded. Qed.

Definition wZ (w : w64) : Z := (if wh w then two63 else 0) + to_Z (wl w).

Lemma wZ_range (w : w64) : 0 <= wZ w < two64.
Proof.
  unfold wZ, two64, two63. pose proof (phi_range (wl w)) as H. unfold two63 in H.
  destruct (wh w); lia.
Qed.

Lemma wZ_inj (a b : w64) : wZ a = wZ b -> a = b.
Proof.
  destruct a as [ha la], b as [hb lb]. unfold wZ; cbn [wh wl].
  pose proof (phi_range la) as Ha. pose proof (phi_range lb) as Hb.
  intros E. destruct ha, hb; cbn [wh wl] in E.
  - f_equal. apply to_Z_inj. lia.
  - exfalso. unfold two63 in *. lia.
  - exfalso. unfold two63 in *. lia.
  - f_equal. apply to_Z_inj. lia.
Qed.

(* [comment removed for export] *)
Definition wofZ (z : Z) : w64 :=
  let z' := z mod two64 in W (two63 <=? z') (of_Z z').

Lemma wZ_wofZ (z : Z) : wZ (wofZ z) = z mod two64.
Proof.
  unfold wofZ, wZ; cbn [wh wl]. rewrite of_Z_spec, wB_eq.
  pose proof (Z.mod_pos_bound z two64 ltac:(reflexivity)) as H.
  destruct (two63 <=? z mod two64) eqn:E.
  - apply Z.leb_le in E. rewrite (Z.mod_eq (z mod two64) two63) by (unfold two63; lia).
    assert (Hq : (z mod two64) / two63 = 1).
    { symmetry; apply Z.div_unique with (r := z mod two64 - two63); unfold two63, two64 in *; lia. }
    rewrite Hq. lia.
  - apply Z.leb_gt in E. rewrite Z.mod_small by (split; lia). lia.
Qed.

Lemma wofZ_wZ (w : w64) : wofZ (wZ w) = w.
Proof.
  apply wZ_inj. rewrite wZ_wofZ. apply Z.mod_small. apply wZ_range.
Qed.

(* [comment removed for export] *)
Definition wbv (w : w64) : bv 64 := Z_to_bv 64 (wZ w).

Lemma wbv_unsigned (w : w64) : bv_unsigned (wbv w) = wZ w.
Proof.
  unfold wbv. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite bv_modulus_64.
  apply Z.mod_small. apply wZ_range.
Qed.

Definition w_of_bv (b : bv 64) : w64 := wofZ (bv_unsigned b).

Lemma wbv_w_of_bv (b : bv 64) : wbv (w_of_bv b) = b.
Proof.
  apply bv_eq. rewrite wbv_unsigned. unfold w_of_bv. rewrite wZ_wofZ.
  apply Z.mod_small. pose proof (bv_unsigned_in_range 64 b) as H. rewrite bv_modulus_64 in H. exact H.
Qed.

Lemma wZ_w_of_bv (b : bv 64) : wZ (w_of_bv b) = bv_unsigned b.
Proof. rewrite <- wbv_unsigned. rewrite wbv_w_of_bv. reflexivity. Qed.

Lemma wbv_inj (a b : w64) : wbv a = wbv b -> a = b.
Proof. intros H. apply wZ_inj. rewrite <- !wbv_unsigned. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma wZ_W_mod (h : bool) (l : int) (k : Z) :
  Z.b2z h = k mod 2 -> wZ (W h l) = (two63 * k + to_Z l) mod two64.
Proof.
  intros Hk. unfold wZ; cbn [wh wl]. pose proof (phi_range l) as Hl.
  rewrite (Z.div_mod k 2) at 1 by lia. rewrite <- Hk.
  replace (two63 * (2 * (k / 2) + Z.b2z h) + to_Z l) with (Z.b2z h * two63 + to_Z l + (k / 2) * two64)
    by (rewrite two64_eq; ring).
  rewrite Z.mod_add by (unfold two64; lia).
  rewrite Z.mod_small by (destruct h; cbn; unfold two64, two63 in *; lia).
  destruct h; cbn; lia.
Qed.

Lemma b2z_xorb (a b : bool) : Z.b2z (xorb a b) = (Z.b2z a + Z.b2z b) mod 2.
Proof. destruct a, b; reflexivity. Qed.

Lemma mod2_add_mod (x y : Z) : (x mod 2 + y) mod 2 = (x + y) mod 2.
Proof. rewrite Z.add_mod_idemp_l by lia. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition w_zero : w64 := W false 0%uint63.
Definition w_one : w64 := W false 1%uint63.
Definition w_ones : w64 := W true max_int.

Lemma wZ_zero : wZ w_zero = 0.
Proof. reflexivity. Qed.
Lemma wZ_one : wZ w_one = 1.
Proof. reflexivity. Qed.
Lemma wZ_ones : wZ w_ones = two64 - 1.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition w_of_int (i : int) : w64 := W false i.
Lemma wZ_of_int (i : int) : wZ (w_of_int i) = to_Z i.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition w_add (a b : w64) : w64 :=
  let l := (wl a + wl b)%uint63 in
  W (xorb (xorb (wh a) (wh b)) (l <? wl a)%uint63) l.

Lemma add_carry (x y : int) :
  to_Z x + to_Z y = to_Z (x + y)%uint63 + (if (x + y <? x)%uint63 then two63 else 0).
Proof.
  rewrite add_spec, wB_eq. pose proof (phi_range x). pose proof (phi_range y).
  destruct (Z_lt_le_dec (to_Z x + to_Z y) two63) as [Hs|Hs].
  - rewrite Z.mod_small by lia.
    destruct (ltbP (x + y) x) as [Hb|Hb]; rewrite ?add_spec, ?wB_eq, ?Z.mod_small in Hb by lia; lia.
  - assert (E : (to_Z x + to_Z y) mod two63 = to_Z x + to_Z y - two63).
    { rewrite (Z.mod_eq _ two63) by (unfold two63; lia).
      assert ((to_Z x + to_Z y) / two63 = 1) as -> by (symmetry; apply Z.div_unique with (r := to_Z x + to_Z y - two63); unfold two63 in *; lia). lia. }
    rewrite E.
    destruct (ltbP (x + y) x) as [Hb|Hb]; rewrite ?add_spec, ?wB_eq, ?E in Hb; lia.
Qed.

Lemma wZ_add (a b : w64) : wZ (w_add a b) = (wZ a + wZ b) mod two64.
Proof.
  destruct a as [ha la], b as [hb lb]. unfold w_add; cbn [wh wl].
  rewrite (wZ_W_mod _ _ (Z.b2z ha + Z.b2z hb + Z.b2z (la + lb <? la)%uint63)).
  2:{ destruct ha, hb, (la + lb <? la)%uint63; reflexivity. }
  f_equal. unfold wZ; cbn [wh wl]. pose proof (add_carry la lb) as H.
  destruct ha, hb, (la + lb <? la)%uint63; cbn in *; lia.
Qed.

Definition w_sub (a b : w64) : w64 :=
  let l := (wl a - wl b)%uint63 in
  W (xorb (xorb (wh a) (wh b)) (wl a <? wl b)%uint63) l.

Lemma sub_borrow (x y : int) :
  to_Z x - to_Z y = to_Z (x - y)%uint63 - (if (x <? y)%uint63 then two63 else 0).
Proof.
  rewrite sub_spec, wB_eq. pose proof (phi_range x). pose proof (phi_range y).
  destruct (ltbP x y) as [Hb|Hb].
  - assert (E : (to_Z x - to_Z y) mod two63 = to_Z x - to_Z y + two63).
    { rewrite (Z.mod_eq _ two63) by (unfold two63; lia).
      assert ((to_Z x - to_Z y) / two63 = -1) as -> by (symmetry; apply Z.div_unique with (r := to_Z x - to_Z y + two63); unfold two63 in *; lia). lia. }
    rewrite E. lia.
  - rewrite Z.mod_small by lia. lia.
Qed.

Lemma wZ_sub (a b : w64) : wZ (w_sub a b) = (wZ a - wZ b) mod two64.
Proof.
  destruct a as [ha la], b as [hb lb]. unfold w_sub; cbn [wh wl].
  rewrite (wZ_W_mod _ _ (Z.b2z ha - Z.b2z hb - Z.b2z (la <? lb)%uint63)).
  2:{ destruct ha, hb, (la <? lb)%uint63; reflexivity. }
  f_equal. unfold wZ; cbn [wh wl]. pose proof (sub_borrow la lb) as H.
  destruct ha, hb, (la <? lb)%uint63; cbn in *; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wZ_split (w : w64) : wZ w = Z.b2z (wh w) * two63 + to_Z (wl w).
Proof. unfold wZ. destruct (wh w); cbn; lia. Qed.

Lemma two63_pow : two63 = 2 ^ 63.
Proof. reflexivity. Qed.

Lemma wZ_mod63 (w : w64) : wZ w mod two63 = to_Z (wl w).
Proof.
  rewrite wZ_split. rewrite Z.add_comm, Z.mod_add by (unfold two63; lia).
  apply Z.mod_small. apply phi_range.
Qed.

Lemma wZ_div63 (w : w64) : wZ w / two63 = Z.b2z (wh w).
Proof.
  rewrite wZ_split. rewrite Z.add_comm, Z.div_add by (unfold two63; lia).
  rewrite Z.div_small by apply phi_range. lia.
Qed.

Lemma testbit_wZ (w : w64) (n : Z) :
  0 <= n -> Z.testbit (wZ w) n = if n <? 63 then Z.testbit (to_Z (wl w)) n else Z.testbit (Z.b2z (wh w)) (n - 63).
Proof.
  intros Hn. destruct (Z.ltb_spec n 63) as [Hlt|Hge].
  - rewrite <- (wZ_mod63 w), two63_pow. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite <- (wZ_div63 w), two63_pow. rewrite Z.div_pow2_bits by lia. f_equal. lia.
Qed.

Lemma testbit_b2z (b : bool) (k : Z) : Z.testbit (Z.b2z b) k = b && (k =? 0).
Proof.
  destruct b; cbn [Z.b2z andb].
  - destruct (Z.eqb_spec k 0) as [->|H]; [reflexivity|].
    destruct (Z_lt_le_dec k 0) as [Hk|Hk].
    + apply Z.testbit_neg_r. lia.
    + apply Z.bits_above_log2; cbn; lia.
  - apply Z.bits_0.
Qed.

Definition w_and (a b : w64) : w64 := W (wh a && wh b) (wl a land wl b)%uint63.
Definition w_or (a b : w64) : w64 := W (wh a || wh b) (wl a lor wl b)%uint63.
Definition w_xor (a b : w64) : w64 := W (xorb (wh a) (wh b)) (wl a lxor wl b)%uint63.

Lemma wZ_and (a b : w64) : wZ (w_and a b) = Z.land (wZ a) (wZ b).
Proof.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, !testbit_wZ by lia. unfold w_and; cbn [wh wl].
  destruct (n <? 63).
  - rewrite land_spec', Z.land_spec. reflexivity.
  - rewrite !testbit_b2z. destruct (wh a), (wh b), (n - 63 =? 0); reflexivity.
Qed.

Lemma wZ_or (a b : w64) : wZ (w_or a b) = Z.lor (wZ a) (wZ b).
Proof.
  apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec, !testbit_wZ by lia. unfold w_or; cbn [wh wl].
  destruct (n <? 63).
  - rewrite lor_spec', Z.lor_spec. reflexivity.
  - rewrite !testbit_b2z. destruct (wh a), (wh b), (n - 63 =? 0); reflexivity.
Qed.

Lemma wZ_xor (a b : w64) : wZ (w_xor a b) = Z.lxor (wZ a) (wZ b).
Proof.
  apply Z.bits_inj'. intros n Hn. rewrite Z.lxor_spec, !testbit_wZ by lia. unfold w_xor; cbn [wh wl].
  destruct (n <? 63).
  - rewrite lxor_spec', Z.lxor_spec. reflexivity.
  - rewrite !testbit_b2z. destruct (wh a), (wh b), (n - 63 =? 0); reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition w_eqb (a b : w64) : bool := Bool.eqb (wh a) (wh b) && (wl a =? wl b)%uint63.
Definition w_ltu (a b : w64) : bool :=
  if Bool.eqb (wh a) (wh b) then (wl a <? wl b)%uint63 else wh b.
Definition w_lts (a b : w64) : bool :=
  if Bool.eqb (wh a) (wh b) then (wl a <? wl b)%uint63 else wh a.

Lemma w_eqb_spec (a b : w64) : w_eqb a b = (wZ a =? wZ b).
Proof.
  destruct (Z.eqb_spec (wZ a) (wZ b)) as [E|NE].
  - apply wZ_inj in E. subst b. unfold w_eqb. rewrite Bool.eqb_reflx. cbn [andb].
    destruct (eqbP (wl a) (wl a)) as [_|C]; [reflexivity|congruence].
  - unfold w_eqb. destruct (Bool.eqb (wh a) (wh b)) eqn:Eh; cbn; [|reflexivity].
    apply Bool.eqb_prop in Eh. destruct (eqbP (wl a) (wl b)) as [El|El]; [|reflexivity].
    exfalso. apply NE. unfold wZ. rewrite Eh, El. reflexivity.
Qed.

Lemma w_ltu_spec (a b : w64) : w_ltu a b = (wZ a <? wZ b).
Proof.
  destruct a as [ha la], b as [hb lb]. unfold w_ltu, wZ; cbn.
  pose proof (phi_range la). pose proof (phi_range lb).
  destruct ha, hb; cbn; unfold two63 in *;
    try (destruct (ltbP la lb); symmetry; first [apply Z.ltb_lt | apply Z.ltb_ge]; lia);
    symmetry; first [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

(* [comment removed for export] *)
Definition wS (w : w64) : Z := if wh w then wZ w - two64 else wZ w.

Lemma w_lts_spec (a b : w64) : w_lts a b = (wS a <? wS b).
Proof.
  destruct a as [ha la], b as [hb lb]. unfold w_lts, wS, wZ; cbn.
  pose proof (phi_range la). pose proof (phi_range lb).
  destruct ha, hb; cbn; unfold two63, two64 in *;
    try (destruct (ltbP la lb); symmetry; first [apply Z.ltb_lt | apply Z.ltb_ge]; lia);
    symmetry; first [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition is_odd (x : int) : bool := (x land 1 =? 1)%uint63.

Lemma phi_land1 (x : int) : to_Z (x land 1)%uint63 = to_Z x mod 2.
Proof.
  rewrite land_spec'. change (to_Z 1%uint63) with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma is_odd_spec (x : int) : Z.b2z (is_odd x) = to_Z x mod 2.
Proof.
  unfold is_odd. pose proof (Z.mod_pos_bound (to_Z x) 2 ltac:(lia)).
  destruct (eqbP (x land 1) 1) as [E|E]; rewrite phi_land1 in E; change (to_Z 1%uint63) with 1 in E;
    cbn [Z.b2z]; lia.
Qed.

Lemma phi_sub_le (x y : int) : to_Z y <= to_Z x -> to_Z (x - y)%uint63 = to_Z x - to_Z y.
Proof.
  intros H. rewrite sub_spec. pose proof (phi_range x). pose proof (phi_range y). rewrite wB_eq.
  apply Z.mod_small. lia.
Qed.

Lemma phi_63 : to_Z 63%uint63 = 63.
Proof. reflexivity. Qed.

Lemma pow2_split (j : Z) : 0 <= j <= 63 -> two63 = 2 ^ (63 - j) * 2 ^ j.
Proof. intros H. rewrite <- Z.pow_add_r by lia. replace (63 - j + j) with 63 by lia. reflexivity. Qed.

Definition w_sll (a : w64) (k : int) : w64 :=
  if (k =? 0)%uint63 then a
  else W (is_odd (wl a >> (63 - k))%uint63) (wl a << k)%uint63.

Lemma wZ_sll (a : w64) (k : int) :
  to_Z k < 64 -> wZ (w_sll a k) = (wZ a * 2 ^ to_Z k) mod two64.
Proof.
  intros Hk. unfold w_sll. pose proof (phi_range (wl a)) as Hla. pose proof (phi_range k) as Hkr.
  destruct (eqbP k 0) as [E|E].
  - change (to_Z 0%uint63) with 0 in E. rewrite E. rewrite Z.mul_1_r. symmetry. apply Z.mod_small. apply wZ_range.
  - change (to_Z 0%uint63) with 0 in E. set (j := to_Z k) in *.
    assert (Hj : 1 <= j <= 63) by lia.
    set (q := to_Z (wl a) / 2 ^ (63 - j)). set (r := to_Z (wl a) mod 2 ^ (63 - j)).
    assert (Hdiv : to_Z (wl a) = 2 ^ (63 - j) * q + r) by (apply Z.div_mod; lia).
    assert (Hr : 0 <= r < 2 ^ (63 - j)) by (apply Z.mod_pos_bound; lia).
    assert (Hp : 2 ^ (63 - j) * 2 ^ j = two63) by (symmetry; apply pow2_split; lia).
    rewrite (wZ_W_mod _ _ q).
    2:{ rewrite is_odd_spec, lsr_spec, phi_sub_le by (rewrite phi_63; lia). rewrite phi_63. reflexivity. }
    rewrite lsl_spec, wB_eq. fold j.
    assert (E1 : (to_Z (wl a) * 2 ^ j) mod two63 = r * 2 ^ j).
    { rewrite Hdiv. replace ((2 ^ (63 - j) * q + r) * 2 ^ j) with (r * 2 ^ j + q * two63) by (rewrite <- Hp; ring).
      rewrite Z.mod_add by (unfold two63; lia). apply Z.mod_small. split; [nia|].
      rewrite <- Hp. apply Z.mul_lt_mono_pos_r; [apply Z.pow_pos_nonneg; lia | lia]. }
    rewrite E1. rewrite wZ_split.
    replace ((Z.b2z (wh a) * two63 + to_Z (wl a)) * 2 ^ j)
      with (two63 * q + r * 2 ^ j + (Z.b2z (wh a) * 2 ^ (j - 1)) * two64).
    2:{ rewrite Hdiv. rewrite two64_eq. rewrite <- Hp.
        assert (HQ : 2 ^ j = 2 * 2 ^ (j - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
        rewrite HQ. ring. }
    rewrite Z.mod_add by (unfold two64; lia). reflexivity.
Qed.

Definition w_srl (a : w64) (k : int) : w64 :=
  if (k =? 0)%uint63 then a
  else W false ((wl a >> k) + (if wh a then 1 << (63 - k) else 0))%uint63.

Lemma wZ_srl (a : w64) (k : int) :
  to_Z k < 64 -> wZ (w_srl a k) = wZ a / 2 ^ to_Z k.
Proof.
  intros Hk. unfold w_srl. pose proof (phi_range (wl a)) as Hla. pose proof (phi_range k) as Hkr.
  destruct (eqbP k 0) as [E|E].
  - change (to_Z 0%uint63) with 0 in E. rewrite E. rewrite Z.pow_0_r, Z.div_1_r. reflexivity.
  - change (to_Z 0%uint63) with 0 in E. set (j := to_Z k) in *.
    assert (Hj : 1 <= j <= 63) by lia.
    assert (Hp : 2 ^ (63 - j) * 2 ^ j = two63) by (symmetry; apply pow2_split; lia).
    assert (Hq : to_Z (wl a) / 2 ^ j < 2 ^ (63 - j)).
    { apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|]. rewrite Z.mul_comm, Hp. lia. }
    assert (Hq0 : 0 <= to_Z (wl a) / 2 ^ j) by (apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]).
    assert (H63 : 2 ^ (63 - j) <= 2 ^ 62) by (apply Z.pow_le_mono_r; lia).
    change (2 ^ 62) with 4611686018427387904 in H63.
    assert (Ht : two63 = 9223372036854775808) by reflexivity.
    unfold wZ at 1. cbn [wh wl]. rewrite Z.add_0_l.
    rewrite add_spec, lsr_spec, wB_eq. fold j.
    rewrite wZ_split.
    replace (Z.b2z (wh a) * two63 + to_Z (wl a)) with (to_Z (wl a) + (Z.b2z (wh a) * 2 ^ (63 - j)) * 2 ^ j)
      by (rewrite <- Hp; ring).
    rewrite Z.div_add by (apply Z.pow_nonzero; lia).
    destruct (wh a); cbn [Z.b2z].
    + rewrite lsl_spec, phi_sub_le by (rewrite phi_63; lia). rewrite phi_63, wB_eq.
      change (to_Z 1%uint63) with 1. rewrite Z.mul_1_l.
      rewrite (Z.mod_small (2 ^ (63 - j))) by lia.
      rewrite Z.mod_small by lia. lia.
    + change (to_Z 0%uint63) with 0. rewrite Z.add_0_r, Z.mod_small by lia. lia.
Qed.

Definition w_sra (a : w64) (k : int) : w64 :=
  if wh a then W true ((wl a >> k) + (0 - (1 << (63 - k))))%uint63
  else W false (wl a >> k)%uint63.

Lemma wZ_sra (a : w64) (k : int) :
  to_Z k < 64 -> wZ (w_sra a k) = (wS a / 2 ^ to_Z k) mod two64.
Proof.
  intros Hk. unfold w_sra, wS. pose proof (phi_range (wl a)) as Hla. pose proof (phi_range k) as Hkr.
  set (j := to_Z k) in *.
  assert (Hj : 0 <= j <= 63) by lia.
  assert (Hp : 2 ^ (63 - j) * 2 ^ j = two63) by (symmetry; apply pow2_split; lia).
  assert (Hq : to_Z (wl a) / 2 ^ j < 2 ^ (63 - j)).
  { apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|]. rewrite Z.mul_comm, Hp. lia. }
  assert (Hq0 : 0 <= to_Z (wl a) / 2 ^ j) by (apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]).
  assert (H63 : 1 <= 2 ^ (63 - j) <= two63).
  { split; [pose proof (Z.pow_pos_nonneg 2 (63 - j) ltac:(lia) ltac:(lia)); lia | change two63 with (2^63); apply Z.pow_le_mono_r; lia]. }
  destruct (wh a) eqn:Eh.
  - unfold wZ at 1; cbn [wh wl]. rewrite wZ_split, Eh. cbn [Z.b2z].
    rewrite add_spec, lsr_spec, sub_spec, lsl_spec, phi_sub_le by (rewrite phi_63; lia). rewrite phi_63, wB_eq. fold j.
    change (to_Z 0%uint63) with 0. change (to_Z 1%uint63) with 1. rewrite Z.mul_1_l.
    assert (Ehi : (0 - (2 ^ (63 - j)) mod two63) mod two63 = two63 - 2 ^ (63 - j)).
    { destruct (Z.eq_dec j 0) as [->|Hj0].
      - change (63 - 0) with 63. change (2 ^ 63) with two63. rewrite Z.mod_same by (unfold two63; lia). cbn. rewrite Z.sub_diag. reflexivity.
      - rewrite (Z.mod_small (2 ^ (63 - j))).
        2:{ split; [lia|]. change two63 with (2^63). apply Z.pow_lt_mono_r; lia. }
        replace (0 - 2 ^ (63 - j)) with (two63 - 2 ^ (63 - j) + (-1) * two63) by ring.
        rewrite Z.mod_add by (unfold two63; lia). apply Z.mod_small. lia. }
    rewrite Ehi.
    rewrite Z.mod_small by lia.
    replace (1 * two63 + to_Z (wl a) - two64) with (to_Z (wl a) + (- 2 ^ (63 - j)) * 2 ^ j) by (rewrite two64_eq, <- Hp; ring).
    rewrite Z.div_add by (apply Z.pow_nonzero; lia).
    replace (to_Z (wl a) / 2 ^ j + - 2 ^ (63 - j)) with (two63 + (two63 - 2 ^ (63 - j) + to_Z (wl a) / 2 ^ j) + (-1) * two64)
      by (rewrite two64_eq; ring).
    rewrite Z.mod_add by (unfold two64; lia). rewrite Z.mod_small by (rewrite two64_eq; lia). lia.
  - unfold wZ at 1; cbn [wh wl]. rewrite Z.add_0_l, lsr_spec. fold j.
    rewrite wZ_split, Eh. cbn [Z.b2z]. rewrite Z.mul_0_l, Z.add_0_l.
    rewrite Z.mod_small by (split; [lia | unfold two64, two63 in *; lia]). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mod2_sum3 (x y z : Z) : (x mod 2 + y mod 2 + z mod 2) mod 2 = (x + y + z) mod 2.
Proof.
  pose proof (Z.div_mod x 2 ltac:(lia)). pose proof (Z.div_mod y 2 ltac:(lia)). pose proof (Z.div_mod z 2 ltac:(lia)).
  replace (x + y + z) with (x mod 2 + y mod 2 + z mod 2 + (x / 2 + y / 2 + z / 2) * 2) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma b2z_andb_odd (h : bool) (x : int) : Z.b2z (h && is_odd x) = (Z.b2z h * to_Z x) mod 2.
Proof.
  destruct h; cbn [andb Z.b2z].
  - rewrite is_odd_spec. rewrite Z.mul_1_l. reflexivity.
  - reflexivity.
Qed.

Definition w_mul (a b : w64) : w64 :=
  let p := mulc (wl a) (wl b) in
  W (xorb (xorb (is_odd (fst p)) (wh a && is_odd (wl b))) (wh b && is_odd (wl a))) (snd p).

Lemma wZ_mul (a b : w64) : wZ (w_mul a b) = (wZ a * wZ b) mod two64.
Proof.
  unfold w_mul. pose proof (mulc_spec (wl a) (wl b)) as Hm. rewrite wB_eq in Hm.
  destruct (mulc (wl a) (wl b)) as [hi lo]. cbn [fst snd] in *.
  rewrite (wZ_W_mod _ _ (to_Z hi + Z.b2z (wh a) * to_Z (wl b) + Z.b2z (wh b) * to_Z (wl a)
                          + (Z.b2z (wh a) * Z.b2z (wh b) * 4611686018427387904) * 2)).
  2:{ rewrite Z.mod_add by lia. rewrite !b2z_xorb, !b2z_andb_odd, !is_odd_spec.
      rewrite Z.add_mod_idemp_l by lia. apply mod2_sum3. }
  f_equal. rewrite !wZ_split.
  replace ((Z.b2z (wh a) * two63 + to_Z (wl a)) * (Z.b2z (wh b) * two63 + to_Z (wl b)))
    with (Z.b2z (wh a) * Z.b2z (wh b) * two63 * two63 + two63 * (Z.b2z (wh a) * to_Z (wl b) + Z.b2z (wh b) * to_Z (wl a))
          + to_Z (wl a) * to_Z (wl b)) by ring.
  rewrite Hm. unfold two63. ring.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wbv_eq_iff (a : w64) (b : bv 64) : wbv a = b <-> wZ a = bv_unsigned b.
Proof.
  split; intros H.
  - subst b. rewrite wbv_unsigned. reflexivity.
  - apply bv_eq. rewrite wbv_unsigned. exact H.
Qed.

Lemma wbv_add (a b : w64) : wbv (w_add a b) = bv_add (wbv a) (wbv b).
Proof. apply wbv_eq_iff. rewrite bv_add_unsigned, !wbv_unsigned, wZ_add. reflexivity. Qed.

Lemma wbv_sub (a b : w64) : wbv (w_sub a b) = bv_sub (wbv a) (wbv b).
Proof. apply wbv_eq_iff. rewrite bv_sub_unsigned, !wbv_unsigned, wZ_sub. reflexivity. Qed.

Lemma wbv_and (a b : w64) : wbv (w_and a b) = bv_and (wbv a) (wbv b).
Proof. apply wbv_eq_iff. rewrite bv_and_unsigned, !wbv_unsigned, wZ_and. reflexivity. Qed.

Lemma wbv_or (a b : w64) : wbv (w_or a b) = bv_or (wbv a) (wbv b).
Proof. apply wbv_eq_iff. rewrite bv_or_unsigned, !wbv_unsigned, wZ_or. reflexivity. Qed.

Lemma wbv_xor (a b : w64) : wbv (w_xor a b) = bv_xor (wbv a) (wbv b).
Proof. apply wbv_eq_iff. rewrite bv_xor_unsigned, !wbv_unsigned, wZ_xor. reflexivity. Qed.

Lemma wbv_mul (a b : w64) : wbv (w_mul a b) = bv_mul (wbv a) (wbv b).
Proof. apply wbv_eq_iff. rewrite bv_mul_unsigned, !wbv_unsigned, wZ_mul. reflexivity. Qed.

Lemma wbv_signed (a : w64) : bv_signed (wbv a) = wS a.
Proof.
  unfold bv_signed, bv_swrap. rewrite wbv_unsigned. unfold wS.
  pose proof (wZ_range a) as Hr. rewrite wZ_split in *.
  pose proof (phi_range (wl a)) as Hl.
  change (bv_half_modulus 64) with two63. unfold bv_wrap. rewrite bv_modulus_64.
  destruct (wh a); cbn [Z.b2z] in *.
  - replace (1 * two63 + to_Z (wl a) + two63) with (to_Z (wl a) + 1 * two64) by (rewrite two64_eq; ring).
    rewrite Z.mod_add by (unfold two64; lia). rewrite Z.mod_small by (unfold two64, two63 in *; lia).
    rewrite two64_eq. ring.
  - rewrite Z.mod_small by (unfold two64, two63 in *; lia). ring.
Qed.

(* [comment removed for export] *)
Definition w_shamt6 (b : w64) : int := (wl b land 63)%uint63.

Lemma phi_shamt6 (b : w64) : to_Z (w_shamt6 b) = Z.land (wZ b) 63.
Proof.
  unfold w_shamt6. rewrite land_spec'. change (to_Z 63%uint63) with (Z.ones 6).
  change (Z.land (wZ b) 63) with (Z.land (wZ b) (Z.ones 6)).
  rewrite !Z.land_ones by lia. rewrite wZ_split.
  replace (Z.b2z (wh b) * two63 + to_Z (wl b)) with (to_Z (wl b) + (Z.b2z (wh b) * 144115188075855872) * 2 ^ 6)
    by (unfold two63; ring).
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma phi_shamt6_range (b : w64) : 0 <= to_Z (w_shamt6 b) < 64.
Proof.
  rewrite phi_shamt6. change 63 with (Z.ones 6). rewrite Z.land_ones by lia.
  apply Z.mod_pos_bound. lia.
Qed.

Lemma wbv_sll (a b : w64) :
  wbv (w_sll a (w_shamt6 b)) = bv_shiftl (wbv a) (bv_and (wbv b) (Z_to_bv 64 63)).
Proof.
  apply wbv_eq_iff. rewrite bv_shiftl_unsigned, bv_and_unsigned, !wbv_unsigned.
  rewrite Z_to_bv_unsigned. change (bv_wrap 64 63) with 63.
  rewrite wZ_sll by (pose proof (phi_shamt6_range b); lia). rewrite phi_shamt6.
  unfold bv_wrap. rewrite bv_modulus_64. rewrite Z.shiftl_mul_pow2 by (apply Z.land_nonneg; right; lia).
  reflexivity.
Qed.

Lemma wbv_srl (a b : w64) :
  wbv (w_srl a (w_shamt6 b)) = bv_shiftr (wbv a) (bv_and (wbv b) (Z_to_bv 64 63)).
Proof.
  apply wbv_eq_iff. rewrite bv_shiftr_unsigned, bv_and_unsigned, !wbv_unsigned.
  rewrite Z_to_bv_unsigned. change (bv_wrap 64 63) with 63.
  rewrite wZ_srl by (pose proof (phi_shamt6_range b); lia). rewrite phi_shamt6.
  rewrite Z.shiftr_div_pow2 by (apply Z.land_nonneg; right; lia). reflexivity.
Qed.

Lemma wbv_sra (a b : w64) :
  wbv (w_sra a (w_shamt6 b)) = bv_ashiftr (wbv a) (bv_and (wbv b) (Z_to_bv 64 63)).
Proof.
  apply wbv_eq_iff. rewrite bv_ashiftr_unsigned, bv_and_unsigned, wbv_signed, !wbv_unsigned.
  rewrite Z_to_bv_unsigned. change (bv_wrap 64 63) with 63.
  rewrite wZ_sra by (pose proof (phi_shamt6_range b); lia). rewrite phi_shamt6.
  unfold bv_wrap. rewrite bv_modulus_64. rewrite Z.shiftr_div_pow2 by (apply Z.land_nonneg; right; lia).
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition m32 : int := 4294967295%uint63.
Definition two32 : Z := 4294967296.

Definition w_low32 (a : w64) : int := (wl a land m32)%uint63.

Lemma phi_m32_land (x : int) : to_Z (x land m32)%uint63 = to_Z x mod two32.
Proof.
  rewrite land_spec'. change (to_Z m32) with (Z.ones 32). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma phi_low32 (a : w64) : to_Z (w_low32 a) = wZ a mod two32.
Proof.
  unfold w_low32. rewrite phi_m32_land. rewrite wZ_split.
  replace (Z.b2z (wh a) * two63 + to_Z (wl a)) with (to_Z (wl a) + (Z.b2z (wh a) * 2147483648) * two32)
    by (unfold two63, two32; ring).
  rewrite Z.mod_add by (unfold two32; lia). reflexivity.
Qed.

Lemma phi_low32_range (a : w64) : 0 <= to_Z (w_low32 a) < two32.
Proof. rewrite phi_low32. apply Z.mod_pos_bound. unfold two32; lia. Qed.

(* [comment removed for export] *)
Definition w_sext32 (x : int) : w64 :=
  if (x land 2147483648 =? 0)%uint63 then W false x else W true (x + 9223372032559808512)%uint63.

Lemma wZ_sext32 (x : int) : to_Z x < two32 ->
  wZ (w_sext32 x) = if to_Z x <? 2147483648 then to_Z x else to_Z x + two64 - two32.
Proof.
  intros Hx. unfold w_sext32. pose proof (phi_range x) as Hr.
  assert (Hb : to_Z (x land 2147483648)%uint63 = 0 <-> to_Z x < 2147483648).
  { rewrite land_spec'. change (to_Z 2147483648%uint63) with (2 ^ 31).
    split; intros H.
    - destruct (Z_lt_le_dec (to_Z x) 2147483648) as [?|Hge]; [assumption|exfalso].
      assert (Z.testbit (to_Z x) 31 = true).
      { rewrite Z.testbit_eqb by lia. apply Z.eqb_eq.
        assert (to_Z x / 2 ^ 31 = 1) as -> by (symmetry; apply Z.div_unique with (r := to_Z x - 2 ^ 31); unfold two32 in *; lia).
        reflexivity. }
      assert (Z.testbit (Z.land (to_Z x) (2 ^ 31)) 31 = true) by (rewrite Z.land_spec, Z.pow2_bits_true by lia; rewrite H0; reflexivity).
      rewrite H in H1. rewrite Z.bits_0 in H1. discriminate.
    - apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
      destruct (Z.eq_dec n 31) as [->|Hne].
      + rewrite Z.bits_above_log2; [reflexivity | lia |].
        destruct (Z.eq_dec (to_Z x) 0) as [->|Hnz]; [cbn; lia|].
        apply Z.log2_lt_pow2; lia.
      + rewrite Z.pow2_bits_false by lia. apply andb_false_r. }
  destruct (eqbP (x land 2147483648) 0) as [E|E]; change (to_Z 0%uint63) with 0 in E.
  - apply Hb in E. unfold wZ; cbn [wh wl]. destruct (Z.ltb_spec (to_Z x) 2147483648); lia.
  - assert (Hge : 2147483648 <= to_Z x) by (destruct (Z_lt_le_dec (to_Z x) 2147483648); [exfalso; apply E; apply Hb; assumption | lia]).
    unfold wZ; cbn [wh wl]. rewrite add_spec, wB_eq. change (to_Z 9223372032559808512%uint63) with 9223372032559808512.
    rewrite Z.mod_small by (unfold two32, two63 in *; lia).
    destruct (Z.ltb_spec (to_Z x) 2147483648); [lia|]. unfold two63, two64, two32. lia.
Qed.
