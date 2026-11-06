(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Bool Lia.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Spec Require Import SoftFloat.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Spec Require Import SoftFloatProps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac dlia := Z.div_mod_to_equations; lia.
Local Ltac dnia := Z.div_mod_to_equations; nia.

Lemma clz128_mirror_val : forall hi lo L, 0 <= hi < 2^64 -> 0 <= lo < 2^64 -> 0 <= L <= 127 ->
  2^L <= hi * 2^64 + lo < 2^(L+1) -> clz128_mirror hi lo = 127 - L.
Proof.
  intros hi lo L Hhi Hlo HL HV. unfold clz128_mirror.
  destruct (Z.eqb_spec hi 0) as [->|NZ].
  - cbn [b2z]. change (Z.shiftl 1 6) with (1 * 2^6).
    assert (L <= 63). { destruct (Z.le_gt_cases L 63); [lia|]. assert (2^64 <= 2^L) by (apply Z.pow_le_mono_r; lia). lia. }
    rewrite (clz64_mirror_val lo L) by lia. rewrite lor_low_high; lia.
  - cbn [b2z]. change (Z.shiftl 0 6) with 0. rewrite Z.lor_0_r.
    assert (64 <= L). { destruct (Z.le_gt_cases 64 L); [lia|]. assert (2^(L+1) <= 2^64) by (apply Z.pow_le_mono_r; lia). lia. }
    rewrite (clz64_mirror_val hi (L - 64)); [lia|lia|].
    assert (P : 2^L = 2^(L-64) * 2^64) by (rewrite <- pow2_split by lia; f_equal; lia).
    assert (P1 : 2^(L+1) = 2^(L-64+1) * 2^64) by (rewrite <- pow2_split by lia; f_equal; lia).
    rewrite P, P1 in HV. nia.
Qed.

Lemma shl128_mirror_val : forall hi lo s, 0 <= hi < 2^64 -> 0 <= lo < 2^64 -> 1 <= s <= 127 ->
  (hi * 2^64 + lo) * 2^s < 2^128 ->
  let '(nhi, nlo) := shl128_mirror hi lo s in
  0 <= nhi < 2^64 /\ 0 <= nlo < 2^64 /\ nhi * 2^64 + nlo = (hi * 2^64 + lo) * 2^s.
Proof.
  intros hi lo s Hhi Hlo Hs HV. unfold shl128_mirror.
  rewrite zext32_val, (Z.mod_small s) by lia.
  assert (Ps : 0 < 2^s) by (apply Z.pow_pos_nonneg; lia).
  destruct (Z.lt_ge_cases s 64) as [SM|BG].
  - rewrite (sub64_neg s 64) by lia. rewrite is_neg64_val by lia.
    replace (2 ^ 63 <=? s - 64 + 2 ^ 64) with true by (symmetry; apply Z.leb_le; lia). cbv iota.
    rewrite smask64_val by lia.
    replace (2 ^ 63 <=? s - 64 + 2 ^ 64) with true by (symmetry; apply Z.leb_le; lia).
    rewrite land63, (Z.mod_small s 64) by lia.
    rewrite not64_val by lia. rewrite land63.
    replace ((2 ^ 64 - 1 - s) mod 64) with (63 - s) by (apply Z.mod_unique with (q := 2^58 - 1); lia).
    rewrite !shiftr_div by lia. rewrite Z.div_div by lia. change (2^1) with 2.
    assert (P64 : 2^64 = 2^s * 2^(64 - s)) by (rewrite <- pow2_split by lia; f_equal; lia).
    assert (P63 : 2 * 2^(63 - s) = 2^(64 - s)) by (change 2 with (2^1) at 1; rewrite <- pow2_split by lia; f_equal; lia).
    rewrite P63.
    assert (Pt : 0 < 2^(64 - s)) by (apply Z.pow_pos_nonneg; lia).
    pose proof (Z.div_mod lo (2^(64-s)) ltac:(lia)) as DM. pose proof (Z.mod_pos_bound lo (2^(64-s)) ltac:(lia)) as MB.
    set (q := lo / 2^(64-s)) in *. set (r := lo mod 2^(64-s)) in *.
    assert (Hq : 0 <= q < 2^s) by (subst q; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; [lia|]; rewrite Z.mul_comm, <- P64; lia]).
    clearbody q r.
    assert (Hhs : hi * 2^s + q < 2^64) by nia.
    rewrite (shl64_small hi s) by nia.
    rewrite lor_high_low by lia.
    rewrite ones64_eq, Z.land_comm, land_ones_mod by lia.
    rewrite shl64_val by lia. rewrite Z.mod_mod by lia.
    replace ((lo * 2^s) mod 2^64) with (r * 2^s).
    2:{ apply Z.mod_unique with (q := q); [nia|]. rewrite DM. rewrite P64. nia. }
    nia.
  - rewrite (sub64_small s 64) by lia. rewrite is_neg64_val by lia.
    replace (2 ^ 63 <=? s - 64) with false by (symmetry; apply Z.leb_gt; lia). cbv iota.
    rewrite smask64_val by lia.
    replace (2 ^ 63 <=? s - 64) with false by (symmetry; apply Z.leb_gt; lia). rewrite Z.land_0_l.
    rewrite land63. replace (s mod 64) with (s - 64) by (apply Z.mod_unique with (q := 1); lia).
    assert (P : 2^s = 2^(s-64) * 2^64) by (rewrite <- pow2_split by lia; f_equal; lia).
    assert (Pt : 0 < 2^(s - 64)) by (apply Z.pow_pos_nonneg; lia).
    assert (hi = 0) by nia. subst hi.
    assert (lo * 2^(s-64) < 2^64) by nia.
    rewrite (shl64_small lo (s - 64)) by lia. nia.
Qed.

Lemma addsub_sub_exact : forall AHi ALo BHi BLo E D L,
  0 <= AHi < 2^64 -> 0 <= ALo < 2^64 -> 0 <= BHi < 2^64 -> 0 <= BLo < 2^64 ->
  (AHi * 2^64 + ALo) - (BHi * 2^64 + BLo) = 8 * D ->
  0 <= L <= 111 -> 2^L <= D < 2^(L+1) -> 113 <= E < 2^63 ->
  exists SHi SLo, addsub_mirror 1 AHi ALo BHi BLo E = Some (SHi, SLo, E - (112 - L)) /\
    0 <= SHi < 2^64 /\ 0 <= SLo < 2^64 /\ SHi * 2^64 + SLo = 8 * D * 2^(112 - L).
Proof.
  intros AHi ALo BHi BLo E D L HAH HAL HBH HBL HD HL HDL HE.
  assert (D112 : D < 2^112). { eapply Z.lt_le_trans; [apply (proj2 HDL)|]. apply Z.pow_le_mono_r; lia. }
  assert (Dpos : 0 < D). { pose proof (pow2_ge1 L ltac:(lia)). lia. }
  unfold addsub_mirror. change (negb (1 =? 0)) with true. cbv iota.
  rewrite lor_eqb0 by (apply Z.lxor_nonneg; lia). rewrite !lxor_eqb0.
  replace ((ALo =? BLo) && (AHi =? BHi)) with false.
  2:{ symmetry. destruct (Z.eqb_spec ALo BLo); destruct (Z.eqb_spec AHi BHi); cbn; try reflexivity. exfalso. nia. }
  rewrite b2z_val.
  set (borrow := if ALo <? BLo then 1 else 0).
  assert (Hb : (ALo < BLo /\ borrow = 1) \/ (BLo <= ALo /\ borrow = 0)).
  { subst borrow. destruct (Z.ltb_spec ALo BLo); lia. }
  clearbody borrow.
  assert (SH : sub64 (sub64 AHi BHi) borrow = AHi - BHi - borrow /\ 0 <= AHi - BHi - borrow < 2^51).
  { assert (0 <= AHi - BHi - borrow < 2^51) by nia.
    rewrite (sub64_small AHi BHi) by lia. rewrite sub64_small by lia. lia. }
  destruct SH as [SH1 SH2]. rewrite SH1.
  set (SHi := AHi - BHi - borrow) in *.
  assert (SL : sub64 ALo BLo = ALo - BLo + 2^64 * borrow /\ 0 <= ALo - BLo + 2^64 * borrow < 2^64).
  { destruct Hb as [[H1 ->]|[H1 ->]]. - rewrite sub64_neg by lia. lia. - rewrite sub64_small by lia. lia. }
  destruct SL as [SL1 SL2]. rewrite SL1. set (SLo := ALo - BLo + 2^64 * borrow) in *.
  assert (SV : SHi * 2^64 + SLo = 8 * D) by (subst SHi SLo; lia).
  clearbody SHi SLo.
  rewrite shiftr_div by lia. rewrite (Z.div_small SHi (2^51)) by lia. change (0 =? 0) with true. cbv iota.
  assert (P8 : 8 * 2^L = 2^(L+3)) by (change 8 with (2^3); rewrite <- pow2_split by lia; f_equal; lia).
  assert (P8' : 8 * 2^(L+1) = 2^(L+3+1)) by (change 8 with (2^3); rewrite <- pow2_split by lia; f_equal; lia).
  rewrite (clz128_mirror_val SHi SLo (L + 3)); [|lia|lia|lia|nia].
  replace (127 - (L + 3)) with (124 - L) by lia.
  rewrite (sub64_small (124 - L) 12) by lia. replace (124 - L - 12) with (112 - L) by lia.
  assert (PS : 2^(112 - L) * 2^(L + 1) = 2^113) by (rewrite <- pow2_split by lia; f_equal; lia).
  assert (Pp : 0 < 2^(112 - L)) by (apply Z.pow_pos_nonneg; lia).
  pose proof (shl128_mirror_val SHi SLo (112 - L)) as SHL.
  destruct (shl128_mirror SHi SLo (112 - L)) as [nhi nlo].
  destruct SHL as (R1 & R2 & EQ); [lia|lia|lia|nia|].
  rewrite (sub64_small E (112 - L)) by lia.
  exists nhi, nlo. split; [reflexivity|]. split; [lia|]. split; [lia|]. rewrite EQ, SV. reflexivity.
Qed.

Lemma round_mirror_exact : forall SHi SLo e M,
  0 <= SHi < 2^64 -> 0 <= SLo < 2^64 -> SHi * 2^64 + SLo = 8 * M -> 2^112 <= M < 2^113 -> 1 <= e <= 32766 ->
  round_mirror SHi SLo e 0 = f128_pack 0 e (M - 2^112).
Proof.
  intros SHi SLo e M HSH HSL HS HM He.
  pose proof (Z.div_mod M (2^64) ltac:(lia)) as DM. pose proof (Z.mod_pos_bound M (2^64) ltac:(lia)) as MB.
  assert (Hq : 2^48 <= M / 2^64 < 2^49) by dlia.
  set (q := M / 2^64) in *. set (r := M mod 2^64) in *. clearbody q r.
  assert (F1 : SLo mod 8 = 0) by dnia.
  assert (F2 : SLo / 8 + (SHi mod 8) * 2^61 = r) by dnia.
  assert (F3 : SHi / 8 = q) by dnia.
  unfold round_mirror.
  change 7 with (2^3 - 1). rewrite land_ones_mod by lia. change (2^3) with 8. rewrite F1.
  rewrite !shiftr_div by lia. change (2^3) with 8.
  rewrite (shl64_val SHi 61) by lia.
  replace ((SHi * 2^61) mod 2^64) with ((SHi mod 8) * 2^61) by dnia.
  rewrite lor_low_high by dlia.
  rewrite (shl64_small e 48) by lia. rewrite Z.lor_0_r.
  rewrite land_mask48, F3. replace (q mod 2^48) with (q - 2^48) by (apply Z.mod_unique with (q := 1); lia).
  rewrite lor_high_low by lia.
  change MASKLO with (2^64 - 1). rewrite land_ones_mod by lia.
  rewrite (Z.mod_small (SHi mod 8 * 2 ^ 61 + SLo / 8)) by dlia.
  change (negb (0 =? 4)) with true. change (b2z (negb (0 <? 5))) with 0. cbv iota.
  rewrite (add64_small (SHi mod 8 * 2^61 + SLo / 8) 0) by dlia. rewrite Z.add_0_r. rewrite Z.ltb_irrefl. change (b2z false) with 0.
  rewrite add64_small by lia.
  rewrite mk128_val by dlia. unfold f128_pack. lia.
Qed.

Theorem f128_sub_exact : forall E T Tz L,
  packed 0 E T -> 0 <= Tz < T -> 113 <= E <= 32766 ->
  0 <= L <= 111 -> 2^L <= T - Tz < 2^(L+1) ->
  f128_sub (f128_pack 0 E T) (f128_pack 0 E Tz) = f128_pack 0 (E - (112 - L)) ((T - Tz) * 2^(112 - L) - 2^112).
Proof.
  intros E T Tz L PK HTz HE HL HD. destruct PK as [_ HE' HT].
  pose proof (T_split T HT) as (Htha & Htla & ETa). pose proof (T_split Tz ltac:(lia)) as (Hthz & Htlz & ETz).
  unfold f128_sub.
  rewrite !f128_pack_hi, !f128_pack_lo by (constructor; lia).
  rewrite sign64_eq. rewrite lxor_bit_clear; [|lia|lia|rewrite Z.div_small by lia; reflexivity].
  rewrite mk128_val by lia.
  replace ((0 * 2 ^ 63 + E * 2 ^ 48 + Tz / 2 ^ 64 + 2 ^ 63) * 2 ^ 64 + Tz mod 2 ^ 64) with (f128_pack 1 E Tz).
  2:{ unfold f128_pack. lia. }
  unfold f128_add.
  rewrite !f128_pack_hi, !f128_pack_lo by (constructor; lia).
  rewrite !hiword_abs by lia.
  replace (E * 2 ^ 48 + T / 2 ^ 64 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  change SPEC_K with (2^63 + 2^48).
  rewrite !add64_small by lia.
  replace (E * 2 ^ 48 + T / 2 ^ 64 + (2 ^ 63 + 2 ^ 48) <? 2 ^ 63 + 2 ^ 48) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (E * 2 ^ 48 + Tz / 2 ^ 64 + (2 ^ 63 + 2 ^ 48) =? 2 ^ 63 + 2 ^ 48) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (2 ^ 63 + 2 ^ 48 <? E * 2 ^ 48 + Tz / 2 ^ 64 + (2 ^ 63 + 2 ^ 48)) with true by (symmetry; apply Z.ltb_lt; lia).
  cbn [negb orb].
  unfold add_main.
  set (tha := T / 2^64) in *. set (tla := T mod 2^64) in *.
  set (thz := Tz / 2^64) in *. set (tlz := Tz mod 2^64) in *. clearbody tha tla thz tlz.
  replace (if E * 2 ^ 48 + thz =? E * 2 ^ 48 + tha then tla <? tlz else E * 2 ^ 48 + tha <? E * 2 ^ 48 + thz) with false.
  2:{ symmetry. destruct (Z.eqb_spec (E * 2^48 + thz) (E * 2^48 + tha)). - apply Z.ltb_ge. nia. - apply Z.ltb_ge. nia. }
  cbv iota beta.
  rewrite !hiword_exp by lia.
  replace (E =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota beta.
  rewrite !hiword_frac by lia.
  unfold align_mirror. rewrite Z.eqb_refl.
  rewrite Z.shiftr_lxor, !hiword_sign by lia. change (Z.lxor 1 0) with 1.
  rewrite !shiftr_div by lia.
  rewrite (shl64_small tha 3), (shl64_small thz 3) by lia. rewrite impl3_hi_eq.
  assert (Hd1 : 0 <= tla / 2^61 < 2^3) by dlia. assert (Hd2 : 0 <= tlz / 2^61 < 2^3) by dlia.
  rewrite (lor_high_low tha (tla / 2^61) 3) by lia.
  replace (2^51) with (1 * 2^51) by lia.
  rewrite (lor_low_high 1 (tlz / 2^61) 51) by lia.
  replace (Z.lor (thz * 2 ^ 3) (1 * 2 ^ 51 + tlz / 2 ^ 61)) with (1 * 2^51 + (thz * 2^3 + tlz / 2^61)).
  2:{ replace (1 * 2 ^ 51 + tlz / 2 ^ 61) with (Z.lor (tlz / 2^61) (1 * 2^51)) by (apply lor_low_high; lia).
      rewrite Z.lor_assoc. rewrite (lor_high_low thz (tlz / 2^61) 3) by lia. symmetry. apply lor_low_high; lia. }
  rewrite (lor_low_high 1 (tha * 2^3 + tla / 2^61) 51) by lia.
  rewrite !shl64_val by lia.
  change ((0 * 2^63) mod 2^64) with 0.
  destruct (addsub_sub_exact (1 * 2 ^ 51 + (tha * 2 ^ 3 + tla / 2 ^ 61)) ((tla * 2 ^ 3) mod 2 ^ 64)
              (1 * 2 ^ 51 + (thz * 2 ^ 3 + tlz / 2 ^ 61)) ((tlz * 2 ^ 3) mod 2 ^ 64) E (T - Tz) L)
    as [SHi [SLo (EQ & R1 & R2 & SV)]]; try lia.
  { dlia. } { dlia. } { dnia. }
  rewrite EQ.
  rewrite !lt_s64_val by lia.
  replace (2 ^ 63 <=? E - (112 - L)) with false by (symmetry; apply Z.leb_gt; lia).
  change (2^63 <=? 32767) with false. change (2^63 <=? 0) with false. cbv iota.
  replace (E - (112 - L) <? 32767) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (0 <? E - (112 - L)) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].
  apply round_mirror_exact; try lia.
  - assert (PS : 2^(112 - L) * 2^(L + 1) = 2^113) by (rewrite <- pow2_split by lia; f_equal; lia).
    assert (PS' : 2^(112 - L) * 2^L = 2^112) by (rewrite <- pow2_split by lia; f_equal; lia).
    assert (Pp : 0 < 2^(112 - L)) by (apply Z.pow_pos_nonneg; lia). nia.
Qed.

Theorem f128_sub_same : forall E T, packed 0 E T -> 1 <= E <= 32766 ->
  f128_sub (f128_pack 0 E T) (f128_pack 0 E T) = f128_pack 0 0 0.
Proof.
  intros E T PK HE. destruct PK as [_ HE' HT].
  pose proof (T_split T HT) as (Htha & Htla & ETa).
  unfold f128_sub.
  rewrite !f128_pack_hi, !f128_pack_lo by (constructor; lia).
  rewrite sign64_eq. rewrite lxor_bit_clear; [|lia|lia|rewrite Z.div_small by lia; reflexivity].
  rewrite mk128_val by lia.
  replace ((0 * 2 ^ 63 + E * 2 ^ 48 + T / 2 ^ 64 + 2 ^ 63) * 2 ^ 64 + T mod 2 ^ 64) with (f128_pack 1 E T).
  2:{ unfold f128_pack. lia. }
  unfold f128_add.
  rewrite !f128_pack_hi, !f128_pack_lo by (constructor; lia).
  rewrite !hiword_abs by lia.
  replace (E * 2 ^ 48 + T / 2 ^ 64 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  change SPEC_K with (2^63 + 2^48).
  rewrite !add64_small by lia.
  replace (E * 2 ^ 48 + T / 2 ^ 64 + (2 ^ 63 + 2 ^ 48) <? 2 ^ 63 + 2 ^ 48) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (E * 2 ^ 48 + T / 2 ^ 64 + (2 ^ 63 + 2 ^ 48) =? 2 ^ 63 + 2 ^ 48) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (2 ^ 63 + 2 ^ 48 <? E * 2 ^ 48 + T / 2 ^ 64 + (2 ^ 63 + 2 ^ 48)) with true by (symmetry; apply Z.ltb_lt; lia).
  cbn [negb orb].
  unfold add_main.
  set (tha := T / 2^64) in *. set (tla := T mod 2^64) in *. clearbody tha tla.
  rewrite Z.eqb_refl, Z.ltb_irrefl. cbv iota beta.
  rewrite !hiword_exp by lia.
  replace (E =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota beta.
  rewrite !hiword_frac by lia.
  unfold align_mirror. rewrite Z.eqb_refl.
  rewrite Z.shiftr_lxor, !hiword_sign by lia. change (Z.lxor 1 0) with 1.
  rewrite !shiftr_div by lia.
  rewrite (shl64_small tha 3) by lia. rewrite impl3_hi_eq.
  assert (Hd1 : 0 <= tla / 2^61 < 2^3) by dlia.
  rewrite (lor_high_low tha (tla / 2^61) 3) by lia.
  replace (2^51) with (1 * 2^51) by lia.
  rewrite (lor_low_high 1 (tla / 2^61) 51) by lia.
  replace (Z.lor (tha * 2 ^ 3) (1 * 2 ^ 51 + tla / 2 ^ 61)) with (1 * 2^51 + (tha * 2^3 + tla / 2^61)).
  2:{ replace (1 * 2 ^ 51 + tla / 2 ^ 61) with (Z.lor (tla / 2^61) (1 * 2^51)) by (apply lor_low_high; lia).
      rewrite Z.lor_assoc. rewrite (lor_high_low tha (tla / 2^61) 3) by lia. symmetry. apply lor_low_high; lia. }
  rewrite (lor_low_high 1 (tha * 2^3 + tla / 2^61) 51) by lia.
  unfold addsub_mirror. change (negb (1 =? 0)) with true. cbv iota.
  rewrite !Z.lxor_nilpotent. change (Z.lor 0 0 =? 0) with true. reflexivity.
Qed.

Theorem f128_sub_zero_r : forall E T, packed 0 E T -> E <= 32766 ->
  f128_sub (f128_pack 0 E T) (f128_pack 0 0 0) = f128_pack 0 E T.
Proof.
  intros E T PK HE. destruct PK as [_ HE' HT].
  pose proof (T_split T HT) as (Htha & Htla & ETa).
  unfold f128_sub. change (hi64 (f128_pack 0 0 0)) with 0. change (lo64 (f128_pack 0 0 0)) with 0.
  change (mk128 (Z.lxor 0 SIGN64) 0) with (f128_pack 1 0 0).
  unfold f128_add.
  rewrite !f128_pack_hi, !f128_pack_lo by (constructor; lia).
  change (0 / 2^64) with 0. change (0 mod 2^64) with 0.
  rewrite !hiword_abs by lia.
  change (0 * 2^48 + 0) with 0.
  change (add64 0 SPEC_K =? SPEC_K) with true. change (0 =? 0) with true. rewrite Bool.orb_true_r.
  rewrite inf_hi_eq.
  replace (E * 2 ^ 48 + T / 2 ^ 64 =? 32767 * 2 ^ 48) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (E * 2 ^ 48 + T / 2 ^ 64 <? 32767 * 2 ^ 48) with true by (symmetry; apply Z.ltb_lt; lia).
  change (0 =? 32767 * 2^48) with false. change (0 <? 32767 * 2 ^ 48) with true. cbn [negb].
  rewrite lor_eqb0 by (try apply Z.lxor_nonneg; lia). rewrite lxor_eqb0.
  replace (E * 2 ^ 48 + T / 2 ^ 64 =? 32767 * 2 ^ 48) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite Bool.andb_false_r.
  change (Z.lor 0 (Z.lxor 0 (32767 * 2 ^ 48)) =? 0) with false.
  change (negb (Z.lor 0 0 =? 0)) with false. cbv iota.
  rewrite lor_eqb0 by lia.
  destruct ((T mod 2 ^ 64 =? 0) && (E * 2 ^ 48 + T / 2 ^ 64 =? 0)) eqn:C.
  - apply andb_prop in C. destruct C as [C1 C2]. apply Z.eqb_eq in C1. apply Z.eqb_eq in C2.
    rewrite C1. replace (0 * 2 ^ 63 + E * 2 ^ 48 + T / 2 ^ 64) with 0 by lia. rewrite !Z.land_0_r.
    change (mk128 0 0) with 0. unfold f128_pack. lia.
  - rewrite mk128_val by lia. unfold f128_pack. lia.
Qed.
