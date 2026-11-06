From Stdlib Require Import ZArith Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.Spec Require Import SoftFloat SoftFloatProps.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.G Require Import C_extendsftf2 C_floatditf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(** Value facts about three binary128 mirrors: the binary32 -> binary128 extension f128_of_f32 (V1), the signed
    64-bit integer -> binary128 conversion f128_of_i64 (V2), and the comparisons f128_le / f128_ge on non-NaN
    operands (V4). Each result is stated on the packed fields s, E, T of SoftFloatProps.f128_pack. *)

(* ------------------------------------------------------------------------------------------------------------ *)
(* Shared bit-field facts. *)

(** The high word s*2^63 + A*2^48 + m that every f128_of_f32 branch builds with two ORs. *)
Local Lemma lor3 : forall s A m, 0 <= s <= 1 -> 0 <= A < 2^15 -> 0 <= m < 2^48 ->
  Z.lor (Z.lor (A * 2^48) (s * 2^63)) m = s * 2^63 + A * 2^48 + m.
Proof.
  intros s A m Hs HA Hm.
  rewrite (Z.lor_comm (A * 2^48)), (lor_high_low s (A * 2^48) 63) by lia.
  replace (s * 2^63 + A * 2^48) with ((s * 2^15 + A) * 2^48) by lia.
  rewrite lor_high_low by lia. lia.
Qed.

(** A value with its leading one at bit L, shifted so that the leading one sits at bit 48 (or 112). Proved here, in
    a small context, so that nia sees only these facts. *)
Local Lemma scale48 : forall x L, 0 <= L <= 48 -> 2^L <= x < 2^(L+1) -> 2^48 <= x * 2^(48 - L) < 2^49.
Proof.
  intros x L HL Hx.
  assert (Q1 : 2^(48 - L) * 2^(L + 1) = 2^49) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (Q0 : 2^(48 - L) * 2^L = 2^48) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (Qpos : 0 < 2^(48 - L)) by (apply Z.pow_pos_nonneg; lia).
  nia.
Qed.

Local Lemma scale112 : forall x L, 0 <= L <= 112 -> 2^L <= x < 2^(L+1) -> 2^112 <= x * 2^(112 - L) < 2^113.
Proof.
  intros x L HL Hx.
  assert (Q1 : 2^(112 - L) * 2^(L + 1) = 2^113) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (Q0 : 2^(112 - L) * 2^L = 2^112) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (Qpos : 0 < 2^(112 - L)) by (apply Z.pow_pos_nonneg; lia).
  nia.
Qed.

Local Lemma mul_bound : forall r P Q, 0 <= r < P -> 0 < Q -> 0 <= r * Q < P * Q.
Proof. intros r P Q Hr HQ. split; nia. Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* V1: binary32 -> binary128. *)

(** The count of leading zeros of f128_of_f32's subnormal branch (the or-cascade and the 32-bit popcount), as a
    function of the fraction. The proofs below unfold f128_of_f32, rewrite its three field reads (exponent byte,
    23-bit fraction, sign bit) and, in the subnormal case, this count, which occurs inline in the mirror. *)
Local Definition clz_f32 (aSig : Z) : Z :=
  let x1 := Z.lor aSig (shr64 aSig 1) in
  let x2 := Z.lor x1 (shr64 x1 2) in
  let x3 := Z.lor x2 (shr64 x2 4) in
  let t := shl64 x3 41 in
  let x4 := Z.lor x3 (shr64 t 49) in
  let x5 := Z.lor x4 (shr64 t 57) in
  pop32 (not64 x5).

Local Lemma sx32_mod : forall x, sext32 (x mod 2^32) = sext32 x.
Proof. intro x. unfold sext32. rewrite !land_m32, Z.mod_mod by lia. reflexivity. Qed.

Local Lemma sext32_sr : forall s r, 0 <= s <= 1 -> 0 <= r < 2^31 -> sext32 (s * 2^31 + r) = s * (2^64 - 2^31) + r.
Proof.
  intros s r Hs Hr. assert (S : s = 0 \/ s = 1) by lia. destruct S as [-> | ->].
  - rewrite sext32_small; lia.
  - rewrite sext32_big; lia.
Qed.

(** The three field reads of the sign-extended pattern s*2^31 + ex*2^23 + mf. *)
Local Lemma f32_fields : forall s ex mf, 0 <= s <= 1 -> 0 <= ex <= 255 -> 0 <= mf < 2^23 ->
  Z.land (srliw (sext32 (s * 2^31 + ex * 2^23 + mf)) 23) 255 = ex /\
  Z.shiftr (shl64 (sext32 (s * 2^31 + ex * 2^23 + mf)) 41) 41 = mf /\
  shl64 (Z.shiftr (sext32 (s * 2^31 + ex * 2^23 + mf)) 31) 63 = s * 2^63.
Proof.
  intros s ex mf Hs Hex Hmf.
  replace (s * 2^31 + ex * 2^23 + mf) with (s * 2^31 + (ex * 2^23 + mf)) by lia.
  rewrite sext32_sr by lia.
  split; [|split].
  - unfold srliw. rewrite land_m32.
    replace (s * (2^64 - 2^31) + (ex * 2^23 + mf)) with ((s * 2^31 + ex * 2^23 + mf) + s * (2^32 - 1) * 2^32) by lia.
    rewrite Z_mod_plus_full, Z.mod_small by lia.
    rewrite shiftr_div by lia.
    replace ((s * 2^31 + ex * 2^23 + mf) / 2^23) with (ex + s * 2^8) by (apply Z.div_unique with (r := mf); lia).
    rewrite sext32_small by lia.
    change 255 with (2^8 - 1). rewrite land_ones_mod by lia.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia.
  - rewrite shl64_val, shiftr_div by lia.
    replace ((s * (2^64 - 2^31) + (ex * 2^23 + mf)) * 2^41) with (mf * 2^41 + (s * (2^41 - 2^8) + ex) * 2^64) by lia.
    rewrite Z_mod_plus_full, Z.mod_small by lia.
    apply Z.div_mul. lia.
  - rewrite shiftr_div by lia.
    replace ((s * (2^64 - 2^31) + (ex * 2^23 + mf)) / 2^31) with (s * (2^33 - 1))
      by (apply Z.div_unique with (r := ex * 2^23 + mf); lia).
    rewrite shl64_val by lia.
    replace (s * (2^33 - 1) * 2^63) with (s * 2^63 + s * (2^32 - 1) * 2^64) by lia.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

(** The count of leading zeros of the subnormal branch: x3 holds at most 23 bits, so t >> 49 and t >> 57 are
    x3 >> 8 and x3 >> 16, and x4 >> 16 = x3 >> 16; the cascade is smear32. *)
Local Lemma shr41 : forall x m k, 0 <= x -> 0 <= k -> m = 41 + k -> Z.shiftr (x * 2^41) m = Z.shiftr x k.
Proof.
  intros x m k Hx Hk ->. rewrite !shiftr_div by lia. rewrite Z.pow_add_r by lia.
  rewrite <- Z.div_div by (try apply Z.pow_pos_nonneg; lia). rewrite Z.div_mul by lia. reflexivity.
Qed.

Local Lemma clz_f32_smear : forall a, 0 <= a < 2^23 -> clz_f32 a = pop32 (not64 (smear32 a)).
Proof.
  intros a Ha. unfold clz_f32, smear32.
  assert (B1 : 0 <= Z.lor a (Z.shiftr a 1) < 2^23) by (apply lor_bound; [lia|lia|apply shiftr_bound; lia]).
  set (x1 := Z.lor a (Z.shiftr a 1)) in *.
  assert (B2 : 0 <= Z.lor x1 (Z.shiftr x1 2) < 2^23) by (apply lor_bound; [lia|lia|apply shiftr_bound; lia]).
  set (x2 := Z.lor x1 (Z.shiftr x1 2)) in *.
  assert (B3 : 0 <= Z.lor x2 (Z.shiftr x2 4) < 2^23) by (apply lor_bound; [lia|lia|apply shiftr_bound; lia]).
  set (x3 := Z.lor x2 (Z.shiftr x2 4)) in *.
  clearbody x1 x2 x3.
  rewrite (shl64_small x3 41) by lia.
  rewrite (shr41 x3 49 8), (shr41 x3 57 16) by lia.
  replace (Z.shiftr (Z.lor x3 (Z.shiftr x3 8)) 16) with (Z.shiftr x3 16); [reflexivity|].
  rewrite Z.shiftr_lor.
  replace (Z.shiftr (Z.shiftr x3 8) 16) with 0.
  2:{ rewrite !shiftr_div by lia. rewrite Z.div_div by lia. symmetry. apply Z.div_small. lia. }
  rewrite Z.lor_0_r. reflexivity.
Qed.

Local Lemma clz_f32_val : forall a L, 0 <= L <= 22 -> 2^L <= a < 2^(L+1) -> clz_f32 a = 31 - L.
Proof.
  intros a L HL Ha.
  assert (A23 : 2^(L+1) <= 2^23) by (apply Z.pow_le_mono_r; lia).
  assert (A0 : 1 <= 2^L) by (apply pow2_ge1; lia).
  rewrite clz_f32_smear by lia. rewrite (smear32_val a L) by lia.
  rewrite not64_val by lia.
  replace (2^64 - 1 - (2^(L+1) - 1)) with (2^64 - 2^(Z.of_nat (Z.to_nat L) + 1)) by (rewrite Z2Nat.id; lia).
  rewrite pop32_cases by lia. lia.
Qed.

(* V1: binary32 -> binary128, by class of the 32-bit pattern s*2^31 + ex*2^23 + mf *)
Lemma f128_of_f32_low : forall x, f128_of_f32 x = f128_of_f32 (x mod 2^32).
Proof. intro x. unfold f128_of_f32. rewrite sx32_mod. reflexivity. Qed.

Lemma f128_of_f32_normal : forall s ex mf, 0 <= s <= 1 -> 1 <= ex <= 254 -> 0 <= mf < 2^23 ->
  f128_of_f32 (s * 2^31 + ex * 2^23 + mf) = f128_pack s (ex + 16256) (mf * 2^89).
Proof.
  intros s ex mf Hs Hex Hmf.
  destruct (f32_fields s ex mf ltac:(lia) ltac:(lia) ltac:(lia)) as (F1 & F2 & F3).
  unfold f128_of_f32. rewrite F1, F2, F3.
  replace (ex =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (ex =? 255) with false by (symmetry; apply Z.eqb_neq; lia).
  cbn [negb].
  rewrite (add64_small ex 0x3f80) by lia.
  rewrite (shl64_small (ex + 0x3f80) 48), (shl64_small mf 25) by lia.
  rewrite lor3 by lia. rewrite mk128_val by lia. unfold f128_pack. lia.
Qed.

(** Exponent 255: infinity (mf = 0) or NaN; the fraction is kept. *)
Local Lemma f128_of_f32_infnan : forall s mf, 0 <= s <= 1 -> 0 <= mf < 2^23 ->
  f128_of_f32 (s * 2^31 + 255 * 2^23 + mf) = f128_pack s 32767 (mf * 2^89).
Proof.
  intros s mf Hs Hmf.
  destruct (f32_fields s 255 mf ltac:(lia) ltac:(lia) ltac:(lia)) as (F1 & F2 & F3).
  unfold f128_of_f32. rewrite F1, F2, F3. cbn [negb Z.eqb Pos.eqb].
  rewrite inf_hi_eq, (shl64_small mf 25) by lia.
  rewrite lor3 by lia. rewrite mk128_val by lia. unfold f128_pack. lia.
Qed.

Lemma f128_of_f32_subnormal : forall s mf L, 0 <= s <= 1 -> 0 <= L <= 22 -> 2^L <= mf < 2^(L+1) ->
  f128_of_f32 (s * 2^31 + mf) = f128_pack s (16234 + L) (mf * 2^(112 - L) - 2^112).
Proof.
  intros s mf L Hs HL Hm.
  assert (M23 : 2^(L+1) <= 2^23) by (apply Z.pow_le_mono_r; lia).
  assert (M0 : 1 <= 2^L) by (apply pow2_ge1; lia).
  replace (s * 2^31 + mf) with (s * 2^31 + 0 * 2^23 + mf) by lia.
  destruct (f32_fields s 0 mf ltac:(lia) ltac:(lia) ltac:(lia)) as (F1 & F2 & F3).
  unfold f128_of_f32. rewrite F1, F2, F3.
  replace (mf =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  pose proof (clz_f32_val mf L ltac:(lia) Hm) as C. unfold clz_f32, pop32 in C. rewrite C. clear C.
  cbn [negb Z.eqb].
  rewrite (add64_small (31 - L) 17) by lia.
  rewrite is_neg64_val by lia.
  replace (2^63 <=? 31 - L + 17) with false by (symmetry; apply Z.leb_gt; lia).
  change (b2z false) with 0.
  rewrite (sub64_neg 0 1) by lia.
  rewrite land63, (Z.mod_small (31 - L + 17) 64) by lia.
  replace (31 - L + 17) with (48 - L) by lia.
  pose proof (scale48 mf L ltac:(lia) Hm) as HB.
  rewrite (shl64_small mf (48 - L)) by lia.
  replace (0 - 1 + 2^64) with (2^64 - 1) by lia.
  rewrite Z.land_comm, land_ones_mod, Z.mod_small by lia.
  rewrite implicit_hi_eq. rewrite lxor_bit_set; [|lia|lia|].
  2:{ replace (mf * 2^(48 - L) / 2^48) with 1; [reflexivity|].
      apply Z.div_unique with (r := mf * 2^(48 - L) - 2^48); lia. }
  rewrite (sub64_small 0x3f80 (31 - L)) by lia. rewrite (add64_small (0x3f80 - (31 - L)) 9) by lia.
  replace (0x3f80 - (31 - L) + 9) with (16234 + L) by lia.
  rewrite (shl64_small (16234 + L) 48) by lia.
  rewrite lor3 by lia. rewrite mk128_val by lia. unfold f128_pack.
  assert (P2 : 2^(112 - L) = 2^(48 - L) * 2^64) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite P2. ring.
Qed.

Lemma f128_of_f32_zero : forall s, 0 <= s <= 1 -> f128_of_f32 (s * 2^31) = f128_pack s 0 0.
Proof.
  intros s Hs.
  replace (s * 2^31) with (s * 2^31 + 0 * 2^23 + 0) by lia.
  destruct (f32_fields s 0 0 ltac:(lia) ltac:(lia) ltac:(lia)) as (F1 & F2 & F3).
  unfold f128_of_f32. rewrite F1, F2, F3. cbn [negb Z.eqb].
  change (shl64 0 48) with 0. rewrite Z.lor_0_l, Z.lor_0_r.
  rewrite mk128_val by lia. unfold f128_pack. lia.
Qed.

Lemma f128_of_f32_inf : forall s, 0 <= s <= 1 -> f128_of_f32 (s * 2^31 + 255 * 2^23) = f128_pack s 32767 0.
Proof.
  intros s Hs.
  replace (s * 2^31 + 255 * 2^23) with (s * 2^31 + 255 * 2^23 + 0) by lia.
  rewrite f128_of_f32_infnan by lia. reflexivity.
Qed.

Local Lemma f32_split : forall v, 0 <= v < 2^32 -> exists s ex mf,
  0 <= s <= 1 /\ 0 <= ex <= 255 /\ 0 <= mf < 2^23 /\ v = s * 2^31 + ex * 2^23 + mf.
Proof.
  intros v Hv.
  pose proof (Z.div_mod v (2^31) ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound v (2^31) ltac:(lia)) as B1.
  assert (Q1 : 0 <= v / 2^31 <= 1).
  { split; [apply Z.div_pos; lia | apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia]. }
  set (m := v mod 2^31) in *. set (q := v / 2^31) in *. clearbody m q.
  pose proof (Z.div_mod m (2^23) ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound m (2^23) ltac:(lia)) as B2.
  assert (Q2 : 0 <= m / 2^23 <= 255).
  { split; [apply Z.div_pos; lia | apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia]. }
  set (e := m / 2^23) in *. set (f := m mod 2^23) in *. clearbody e f.
  exists q, e, f. lia.
Qed.

Lemma f128_of_f32_range : forall x, 0 <= f128_of_f32 x < 2^128.
Proof.
  intro x. rewrite f128_of_f32_low.
  assert (Hv : 0 <= x mod 2^32 < 2^32) by (apply Z.mod_pos_bound; lia).
  destruct (f32_split (x mod 2^32) Hv) as (s & ex & mf & Hs & Hex & Hmf & E).
  rewrite E. clear E Hv.
  destruct (Z.eq_dec ex 255) as [->|N255].
  { rewrite f128_of_f32_infnan by lia. apply f128_pack_range. constructor; lia. }
  destruct (Z.eq_dec ex 0) as [->|N0].
  - destruct (Z.eq_dec mf 0) as [->|NM].
    + replace (s * 2^31 + 0 * 2^23 + 0) with (s * 2^31) by lia.
      rewrite f128_of_f32_zero by lia. apply f128_pack_range. constructor; lia.
    + pose proof (Z.log2_spec mf ltac:(lia)) as [LL LU]. rewrite <- Z.add_1_r in LU.
      assert (L22 : Z.log2 mf < 23) by (apply Z.log2_lt_pow2; lia).
      pose proof (Z.log2_nonneg mf) as L0.
      set (L := Z.log2 mf) in *. clearbody L.
      replace (s * 2^31 + 0 * 2^23 + mf) with (s * 2^31 + mf) by lia.
      rewrite (f128_of_f32_subnormal s mf L) by lia.
      apply f128_pack_range.
      pose proof (scale112 mf L ltac:(lia) (conj LL LU)) as HS.
      constructor; lia.
  - rewrite f128_of_f32_normal by lia. apply f128_pack_range. constructor; lia.
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* V2: signed 64-bit integer -> binary128. *)

Local Lemma lxor_63 : forall c, 0 <= c <= 63 -> Z.lxor c 63 = 63 - c.
Proof.
  intros c Hc. rewrite <- (Z2Nat.id c) by lia.
  assert (L : (Z.to_nat c < 64)%nat) by lia. revert L. generalize (Z.to_nat c) as n. intros n L.
  do 64 (destruct n as [|n]; [reflexivity|]). lia.
Qed.

(** For a nonzero t inside the signed 64-bit range: |t| as the code forms it, the sign bit, and the zero test. *)
Local Lemma i64_parts : forall t, -(2^63) < t < 2^63 -> t <> 0 ->
  sub64 (Z.lxor (wrap64 t) (sra63 (wrap64 t))) (sra63 (wrap64 t)) = Z.abs t /\
  shl64 (Z.shiftr (wrap64 t) 63) 63 = (if t <? 0 then 1 else 0) * 2^63 /\
  (wrap64 t =? 0) = false.
Proof.
  intros t Ht NZ. destruct (Z.ltb_spec t 0) as [N|P].
  - assert (W : wrap64 t = t + 2^64).
    { rewrite wrap64_mod. replace t with ((t + 2^64) + (-1) * 2^64) at 1 by lia.
      rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
    rewrite W. rewrite smask64_val by lia.
    replace (2^63 <=? t + 2^64) with true by (symmetry; apply Z.leb_le; lia).
    cbv iota.
    split; [|split].
    + change (Z.lxor (t + 2^64) ONES64) with (not64 (t + 2^64)). rewrite not64_val by lia.
      rewrite ones64_eq. rewrite sub64_neg by lia. lia.
    + rewrite shiftr_div by lia.
      replace ((t + 2^64) / 2^63) with 1 by (apply Z.div_unique with (r := t + 2^63); lia).
      apply shl64_small; lia.
    + apply Z.eqb_neq. lia.
  - assert (W : wrap64 t = t) by (apply wrap64_id; lia).
    rewrite W. rewrite smask64_val by lia.
    replace (2^63 <=? t) with false by (symmetry; apply Z.leb_gt; lia).
    cbv iota.
    split; [|split].
    + rewrite Z.lxor_0_r. rewrite sub64_small by lia. lia.
    + rewrite shiftr_div by lia. rewrite Z.div_small by lia. reflexivity.
    + apply Z.eqb_neq. lia.
Qed.

(* V2: signed 64-bit integer -> binary128 *)
Lemma f128_of_i64_zero : f128_of_i64 0 = f128_pack 0 0 0.
Proof. reflexivity. Qed.

Lemma f128_of_i64_val : forall t L, 0 <= L <= 62 -> 2^L <= Z.abs t < 2^(L+1) ->
  f128_of_i64 t = f128_pack (if t <? 0 then 1 else 0) (16383 + L) (Z.abs t * 2^(112 - L) - 2^112).
Proof.
  intros t L HL Ht.
  assert (P63 : 2^(L+1) <= 2^63) by (apply Z.pow_le_mono_r; lia).
  assert (P0 : 1 <= 2^L) by (apply pow2_ge1; lia).
  destruct (i64_parts t ltac:(lia) ltac:(lia)) as (A1 & A2 & A3).
  unfold f128_of_i64. rewrite A3. cbv iota. rewrite A1, A2. clear A1 A2 A3.
  set (sg := if t <? 0 then 1 else 0) in *.
  assert (Hsg : 0 <= sg <= 1) by (unfold sg; destruct (t <? 0); lia).
  clearbody sg.
  set (a := Z.abs t) in *. clearbody a.
  rewrite (clz64_mirror_val a L) by lia.
  rewrite lxor_63 by lia. replace (63 - (63 - L)) with L by lia.
  rewrite (sub64_small 112 L) by lia. rewrite (sext32_small (112 - L)) by lia.
  rewrite zext32_val, (Z.mod_small (112 - L)) by lia.
  rewrite (sub64_small 0x403e (63 - L)) by lia. rewrite (sext32_small (0x403e - (63 - L))) by lia.
  replace (0x403e - (63 - L)) with (16383 + L) by lia.
  rewrite (shl64_small (16383 + L) 48) by lia.
  rewrite implicit_hi_eq.
  destruct (Z.le_gt_cases L 48) as [LA|LB].
  - (* the significand fits the high word: the low word is 0 *)
    rewrite (sub64_small (112 - L) 64) by lia.
    rewrite is_neg64_val by lia. rewrite smask64_val by lia.
    replace (2^63 <=? 112 - L - 64) with false by (symmetry; apply Z.leb_gt; lia).
    cbn [negb].
    rewrite Z.land_0_l.
    rewrite land63. replace ((112 - L) mod 64) with (48 - L) by (apply Z.mod_unique with (q := 1); lia).
    pose proof (scale48 a L ltac:(lia) Ht) as HB.
    rewrite (shl64_small a (48 - L)) by lia.
    rewrite lxor_bit_set; [|lia|lia|].
    2:{ replace (a * 2^(48 - L) / 2^48) with 1; [reflexivity|].
        apply Z.div_unique with (r := a * 2^(48 - L) - 2^48); lia. }
    rewrite add64_small by lia.
    rewrite lor_low_high by lia.
    rewrite mk128_val by lia. unfold f128_pack.
    assert (P2 : 2^(112 - L) = 2^(48 - L) * 2^64) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    rewrite P2. ring.
  - (* the significand spans both words: high word |t| / 2^(L-48), low word the rest shifted up *)
    rewrite (sub64_neg (112 - L) 64) by lia.
    rewrite is_neg64_val by lia. rewrite smask64_val by lia.
    replace (2^63 <=? 112 - L - 64 + 2^64) with true by (symmetry; apply Z.leb_le; lia).
    cbn [negb].
    rewrite !land63.
    rewrite (Z.mod_small (112 - L) 64) by lia.
    rewrite not64_val by lia.
    replace ((2^64 - 1 - (112 - L)) mod 64) with (L - 49) by (apply Z.mod_unique with (q := 2^58 - 1); lia).
    rewrite ones64_eq, Z.land_comm, land_ones_mod by lia.
    rewrite shl64_val, Z.mod_mod by lia.
    rewrite !shiftr_div by lia.
    rewrite Z.div_div by (try apply Z.pow_pos_nonneg; lia).
    replace (2^1 * 2^(L - 49)) with (2^(L - 48)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (P12 : 2^(L - 48) * 2^(112 - L) = 2^64) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (PL : 2^L = 2^(L - 48) * 2^48) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (PL1 : 2^(L + 1) = 2^(L - 48) * 2^49) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (P1pos : 0 < 2^(L - 48)) by (apply Z.pow_pos_nonneg; lia).
    assert (P2pos : 0 < 2^(112 - L)) by (apply Z.pow_pos_nonneg; lia).
    set (P1 := 2^(L - 48)) in *. set (P2 := 2^(112 - L)) in *. clearbody P1 P2.
    assert (Hq : 2^48 <= a / P1 < 2^49).
    { split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia. }
    pose proof (Z.div_mod a P1 ltac:(lia)) as DM.
    pose proof (Z.mod_pos_bound a P1 P1pos) as MB.
    set (q := a / P1) in *. set (r := a mod P1) in *. clearbody q r.
    pose proof (mul_bound r P1 P2 MB P2pos) as RB. rewrite P12 in RB.
    assert (LO : (a * P2) mod 2^64 = r * P2).
    { symmetry. apply Z.mod_unique with (q := q); [lia|].
      rewrite DM. replace ((P1 * q + r) * P2) with (q * (P1 * P2) + r * P2) by ring. rewrite P12. ring. }
    rewrite LO.
    rewrite lxor_bit_set; [|lia|lia|].
    2:{ replace (q / 2^48) with 1; [reflexivity|]. apply Z.div_unique with (r := q - 2^48); lia. }
    rewrite add64_small by lia.
    rewrite lor_low_high by lia.
    rewrite mk128_val by lia. unfold f128_pack.
    rewrite DM. replace ((P1 * q + r) * P2) with (q * (P1 * P2) + r * P2) by ring. rewrite P12. ring.
Qed.

Local Lemma f128_of_i64_wrap : forall t u, wrap64 t = wrap64 u -> f128_of_i64 t = f128_of_i64 u.
Proof. intros t u H. unfold f128_of_i64. rewrite H. reflexivity. Qed.

Local Lemma i64_range_core : forall u, -(2^63) <= u < 2^63 -> 0 <= f128_of_i64 u < 2^128.
Proof.
  intros u Hu.
  destruct (Z.eq_dec u 0) as [->|NZ].
  { rewrite f128_of_i64_zero. apply f128_pack_range. constructor; lia. }
  destruct (Z.eq_dec u (-(2^63))) as [->|NM].
  { split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity. }
  assert (HA : 0 < Z.abs u) by lia.
  pose proof (Z.log2_spec (Z.abs u) HA) as [LL LU]. rewrite <- Z.add_1_r in LU.
  assert (L62 : Z.log2 (Z.abs u) < 63) by (apply Z.log2_lt_pow2; lia).
  pose proof (Z.log2_nonneg (Z.abs u)) as L0.
  set (L := Z.log2 (Z.abs u)) in *. clearbody L.
  rewrite (f128_of_i64_val u L) by lia.
  apply f128_pack_range.
  pose proof (scale112 (Z.abs u) L ltac:(lia) (conj LL LU)) as HS.
  constructor; [destruct (u <? 0); lia | lia | lia].
Qed.

Lemma f128_of_i64_range : forall t, 0 <= f128_of_i64 t < 2^128.
Proof.
  intro t. pose proof (wrap64_range t) as Hw.
  destruct (Z.ltb_spec (wrap64 t) (2^63)) as [LT|GE].
  - rewrite (f128_of_i64_wrap t (wrap64 t)).
    2:{ rewrite (wrap64_id (wrap64 t)) by lia. reflexivity. }
    apply i64_range_core; lia.
  - rewrite (f128_of_i64_wrap t (wrap64 t - 2^64)).
    2:{ rewrite (wrap64_mod (wrap64 t - 2^64)).
        replace (wrap64 t - 2^64) with (wrap64 t + (-1) * 2^64) by lia.
        rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. reflexivity. }
    apply i64_range_core; lia.
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* V4: comparison of non-NaN packed values is the order of the signed key *)
Definition f128_okey (s E T : Z) : Z := if s =? 0 then E * 2^112 + T else - (E * 2^112 + T).
Definition cmp_res (c : comparison) : Z := match c with Lt => -1 | Eq => 0 | Gt => 1 end.

(** The NaN test of one operand, and the part after the two NaN tests, which f128_le and f128_ge share (they differ
    only in the value returned for a NaN). *)
Local Definition nan128 (a : Z) : bool :=
  if Z.land (hi64 a) ABS_HI =? INF_HI then negb (lo64 a =? 0) else INF_HI <? Z.land (hi64 a) ABS_HI.

Local Definition is_less (a_hi a_lo b_hi b_lo : Z) : bool :=
  if negb (is_neg64 (Z.land b_hi a_hi)) then
    (if a_hi =? b_hi then a_lo <? b_lo else lt_s64 a_hi b_hi)
  else
    (if a_hi =? b_hi then b_lo <? a_lo else lt_s64 b_hi a_hi).

Local Definition cmp_core (a_hi a_lo b_hi b_lo : Z) : Z :=
  if Z.lor (Z.lor b_lo a_lo) (Z.lor (Z.land b_hi ABS_HI) (Z.land a_hi ABS_HI)) =? 0 then 0
  else if is_less a_hi a_lo b_hi b_lo then (-1)
  else nez64 (Z.lor (Z.lxor a_lo b_lo) (Z.lxor a_hi b_hi)).

Local Lemma f128_le_split : forall a b,
  f128_le a b = if nan128 a then 1 else if nan128 b then 1 else cmp_core (hi64 a) (lo64 a) (hi64 b) (lo64 b).
Proof. intros a b. unfold f128_le, nan128, cmp_core, is_less. reflexivity. Qed.

Local Lemma f128_ge_split : forall a b,
  f128_ge a b = if nan128 a then -1 else if nan128 b then -1 else cmp_core (hi64 a) (lo64 a) (hi64 b) (lo64 b).
Proof. intros a b. unfold f128_ge, nan128, cmp_core, is_less. reflexivity. Qed.

Local Lemma nan128_pack : forall s E T, packed s E T -> (E <= 32766 \/ T = 0) -> nan128 (f128_pack s E T) = false.
Proof.
  intros s E T PK HN. pose proof PK as [Hs HE HT].
  pose proof (T_split T HT) as (Hth & Htl & ET).
  unfold nan128. rewrite f128_pack_hi, f128_pack_lo by exact PK.
  rewrite hiword_abs by lia. rewrite inf_hi_eq.
  set (th := T / 2^64) in *. set (tl := T mod 2^64) in *. clearbody th tl.
  destruct (Z.eqb_spec (E * 2^48 + th) (32767 * 2^48)) as [EQ|NE].
  - assert (TL : tl = 0) by lia. rewrite TL. reflexivity.
  - destruct (Z.ltb_spec (32767 * 2^48) (E * 2^48 + th)); [exfalso; lia | reflexivity].
Qed.

(** Word facts for a high word s*2^63 + h with h < 2^63. *)
Local Lemma hiw_abs : forall s h, 0 <= s -> 0 <= h < 2^63 -> Z.land (s * 2^63 + h) ABS_HI = h.
Proof. intros s h Hs Hh. rewrite land_abs. rewrite Z.add_comm, Z_mod_plus_full. apply Z.mod_small. lia. Qed.

Local Lemma hiw_sign : forall s h, 0 <= s -> 0 <= h < 2^63 -> Z.shiftr (s * 2^63 + h) 63 = s.
Proof. intros s h Hs Hh. rewrite shiftr_div by lia. symmetry. apply Z.div_unique with (r := h); lia. Qed.

Local Lemma isneg_land : forall s1 h1 s2 h2, 0 <= s1 <= 1 -> 0 <= h1 < 2^63 -> 0 <= s2 <= 1 -> 0 <= h2 < 2^63 ->
  is_neg64 (Z.land (s2 * 2^63 + h2) (s1 * 2^63 + h1)) = (s1 =? 1) && (s2 =? 1).
Proof.
  intros s1 h1 s2 h2 Hs1 Hh1 Hs2 Hh2. unfold is_neg64. rewrite Z.shiftr_land, !hiw_sign by lia.
  assert (S1 : s1 = 0 \/ s1 = 1) by lia. assert (S2 : s2 = 0 \/ s2 = 1) by lia.
  destruct S1 as [-> | ->]; destruct S2 as [-> | ->]; reflexivity.
Qed.

Local Lemma lts_val : forall s1 h1 s2 h2, 0 <= s1 <= 1 -> 0 <= h1 < 2^63 -> 0 <= s2 <= 1 -> 0 <= h2 < 2^63 ->
  lt_s64 (s1 * 2^63 + h1) (s2 * 2^63 + h2) = (h1 - s1 * 2^63 <? h2 - s2 * 2^63).
Proof.
  intros s1 h1 s2 h2 Hs1 Hh1 Hs2 Hh2. rewrite lt_s64_val by lia.
  assert (S1 : s1 = 0 \/ s1 = 1) by lia. assert (S2 : s2 = 0 \/ s2 = 1) by lia. clear Hs1 Hs2.
  destruct S1 as [-> | ->]; destruct S2 as [-> | ->];
    repeat match goal with |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b) end; cbn [negb];
    apply Bool.eq_true_iff_eq; rewrite !Z.ltb_lt; lia.
Qed.

(** x*2^64 + l with l < 2^64 determines x and l (by the uniqueness of division), without asking lia to search. *)
Local Lemma pair_eq : forall x1 l1 x2 l2, 0 <= l1 < 2^64 -> 0 <= l2 < 2^64 ->
  x1 * 2^64 + l1 = x2 * 2^64 + l2 -> x1 = x2 /\ l1 = l2.
Proof.
  intros x1 l1 x2 l2 Hl1 Hl2 H.
  assert (Q1 : x1 = (x1 * 2^64 + l1) / 2^64) by (apply Z.div_unique with (r := l1); lia).
  assert (Q2 : x2 = (x2 * 2^64 + l2) / 2^64) by (apply Z.div_unique with (r := l2); lia).
  assert (R1 : l1 = (x1 * 2^64 + l1) mod 2^64) by (apply Z.mod_unique with (q := x1); lia).
  assert (R2 : l2 = (x2 * 2^64 + l2) mod 2^64) by (apply Z.mod_unique with (q := x2); lia).
  rewrite H in Q1, R1. split; congruence.
Qed.

Local Lemma nez_val : forall a b c d, 0 <= a -> 0 <= b -> 0 <= c -> 0 <= d ->
  nez64 (Z.lor (Z.lxor a b) (Z.lxor c d)) = if (a =? b) && (c =? d) then 0 else 1.
Proof.
  intros a b c d Ha Hb Hc Hd. unfold nez64.
  rewrite lor_eqb0 by (apply Z.lxor_nonneg; split; intros; lia).
  rewrite !lxor_eqb0. destruct ((a =? b) && (c =? d)); reflexivity.
Qed.

Local Lemma zero4 : forall h1 l1 h2 l2, 0 <= h1 -> 0 <= l1 < 2^64 -> 0 <= h2 -> 0 <= l2 < 2^64 ->
  (Z.lor (Z.lor l2 l1) (Z.lor h2 h1) =? 0) = ((h1 * 2^64 + l1 =? 0) && (h2 * 2^64 + l2 =? 0)).
Proof.
  intros h1 l1 h2 l2 Hh1 Hl1 Hh2 Hl2.
  rewrite lor_eqb0 by (apply Z.lor_nonneg; lia). rewrite !lor_eqb0 by lia.
  apply Bool.eq_true_iff_eq. rewrite !Bool.andb_true_iff, !Z.eqb_eq. split; intros; lia.
Qed.

(** The unsigned high-word equality is the equality of the signed high words h - s*2^63. *)
Local Lemma hi_eqb : forall s1 h1 s2 h2, 0 <= s1 <= 1 -> 0 <= h1 < 2^63 -> 0 <= s2 <= 1 -> 0 <= h2 < 2^63 ->
  (s1 * 2^63 + h1 =? s2 * 2^63 + h2) = (h1 - s1 * 2^63 =? h2 - s2 * 2^63).
Proof.
  intros s1 h1 s2 h2 Hs1 Hh1 Hs2 Hh2.
  assert (S1 : s1 = 0 \/ s1 = 1) by lia. assert (S2 : s2 = 0 \/ s2 = 1) by lia. clear Hs1 Hs2.
  destruct S1 as [-> | ->]; destruct S2 as [-> | ->]; apply Bool.eq_true_iff_eq; rewrite !Z.eqb_eq; lia.
Qed.

(** isLess compares the signed 128-bit values A - s*2^127 (A = h*2^64 + l the magnitude): in that order unless
    both operands are negative, in reverse order when both are. *)
Local Lemma is_less_val : forall s1 h1 l1 s2 h2 l2,
  0 <= s1 <= 1 -> 0 <= h1 < 2^63 -> 0 <= l1 < 2^64 -> 0 <= s2 <= 1 -> 0 <= h2 < 2^63 -> 0 <= l2 < 2^64 ->
  is_less (s1 * 2^63 + h1) l1 (s2 * 2^63 + h2) l2 =
  if (s1 =? 1) && (s2 =? 1) then (h2 * 2^64 + l2 - s2 * 2^127 <? h1 * 2^64 + l1 - s1 * 2^127)
  else (h1 * 2^64 + l1 - s1 * 2^127 <? h2 * 2^64 + l2 - s2 * 2^127).
Proof.
  intros s1 h1 l1 s2 h2 l2 Hs1 Hh1 Hl1 Hs2 Hh2 Hl2. unfold is_less.
  rewrite isneg_land, hi_eqb, !lts_val by lia.
  assert (S1 : s1 = 0 \/ s1 = 1) by lia. assert (S2 : s2 = 0 \/ s2 = 1) by lia. clear Hs1 Hs2.
  destruct S1 as [-> | ->]; destruct S2 as [-> | ->]; cbn [Z.eqb Pos.eqb andb negb];
    match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b) end; cbn [negb];
    apply Bool.eq_true_iff_eq; rewrite !Z.ltb_lt; lia.
Qed.

Local Lemma nez_hi : forall s1 h1 l1 s2 h2 l2,
  0 <= s1 <= 1 -> 0 <= h1 < 2^63 -> 0 <= l1 < 2^64 -> 0 <= s2 <= 1 -> 0 <= h2 < 2^63 -> 0 <= l2 < 2^64 ->
  nez64 (Z.lor (Z.lxor l1 l2) (Z.lxor (s1 * 2^63 + h1) (s2 * 2^63 + h2))) =
  if h1 * 2^64 + l1 - s1 * 2^127 =? h2 * 2^64 + l2 - s2 * 2^127 then 0 else 1.
Proof.
  intros s1 h1 l1 s2 h2 l2 Hs1 Hh1 Hl1 Hs2 Hh2 Hl2. rewrite nez_val by lia. rewrite hi_eqb by lia.
  replace ((l1 =? l2) && (h1 - s1 * 2^63 =? h2 - s2 * 2^63))
    with (h1 * 2^64 + l1 - s1 * 2^127 =? h2 * 2^64 + l2 - s2 * 2^127); [reflexivity|].
  apply Bool.eq_true_iff_eq. rewrite Bool.andb_true_iff, !Z.eqb_eq. split.
  - intro HV.
    replace (h1 * 2^64 + l1 - s1 * 2^127) with ((h1 - s1 * 2^63) * 2^64 + l1) in HV by lia.
    replace (h2 * 2^64 + l2 - s2 * 2^127) with ((h2 - s2 * 2^63) * 2^64 + l2) in HV by lia.
    destruct (pair_eq _ _ _ _ Hl1 Hl2 HV) as [EX EL]. split; [exact EL | exact EX].
  - intros [EL EX]. lia.
Qed.

Local Ltac zfinish :=
  repeat (match goal with
          | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
          | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b)
          end; cbn [andb negb]);
  match goal with |- context [Z.compare ?x ?y] => destruct (Z.compare_spec x y) end;
  cbn [cmp_res]; lia.

(** The result after the NaN tests, on magnitudes A1, A2 and signs s1, s2 only. *)
Local Lemma final_cmp : forall s1 A1 s2 A2, 0 <= s1 <= 1 -> 0 <= A1 < 2^127 -> 0 <= s2 <= 1 -> 0 <= A2 < 2^127 ->
  (if (A1 =? 0) && (A2 =? 0) then 0
   else if (if (s1 =? 1) && (s2 =? 1) then A2 - s2 * 2^127 <? A1 - s1 * 2^127 else A1 - s1 * 2^127 <? A2 - s2 * 2^127)
   then -1
   else if A1 - s1 * 2^127 =? A2 - s2 * 2^127 then 0 else 1)
  = cmp_res (Z.compare (if s1 =? 0 then A1 else - A1) (if s2 =? 0 then A2 else - A2)).
Proof.
  intros s1 A1 s2 A2 Hs1 HA1 Hs2 HA2.
  assert (S1 : s1 = 0 \/ s1 = 1) by lia. assert (S2 : s2 = 0 \/ s2 = 1) by lia. clear Hs1 Hs2.
  destruct S1 as [-> | ->]; destruct S2 as [-> | ->]; cbn [Z.eqb Pos.eqb andb]; zfinish.
Qed.

(** The shared part on two non-NaN operands with high words s*2^63 + h and low words l is the order of the signed
    keys; h*2^64 + l is the magnitude. *)
Local Lemma cmp_core_val : forall s1 h1 l1 s2 h2 l2,
  0 <= s1 <= 1 -> 0 <= h1 < 2^63 -> 0 <= l1 < 2^64 ->
  0 <= s2 <= 1 -> 0 <= h2 < 2^63 -> 0 <= l2 < 2^64 ->
  cmp_core (s1 * 2^63 + h1) l1 (s2 * 2^63 + h2) l2 =
  cmp_res (Z.compare (if s1 =? 0 then h1 * 2^64 + l1 else - (h1 * 2^64 + l1))
                     (if s2 =? 0 then h2 * 2^64 + l2 else - (h2 * 2^64 + l2))).
Proof.
  intros s1 h1 l1 s2 h2 l2 Hs1 Hh1 Hl1 Hs2 Hh2 Hl2. unfold cmp_core.
  rewrite !hiw_abs by lia. rewrite zero4 by lia. rewrite is_less_val by lia. rewrite nez_hi by lia.
  apply final_cmp; lia.
Qed.

Local Lemma cmp_pack : forall s1 E1 T1 s2 E2 T2, packed s1 E1 T1 -> packed s2 E2 T2 ->
  cmp_core (hi64 (f128_pack s1 E1 T1)) (lo64 (f128_pack s1 E1 T1)) (hi64 (f128_pack s2 E2 T2)) (lo64 (f128_pack s2 E2 T2))
  = cmp_res (Z.compare (f128_okey s1 E1 T1) (f128_okey s2 E2 T2)).
Proof.
  intros s1 E1 T1 s2 E2 T2 P1 P2.
  rewrite !f128_pack_hi, !f128_pack_lo by assumption.
  destruct P1 as [Hs1 HE1 HT1], P2 as [Hs2 HE2 HT2].
  pose proof (T_split T1 HT1) as (Hth1 & Htl1 & ET1).
  pose proof (T_split T2 HT2) as (Hth2 & Htl2 & ET2).
  set (th1 := T1 / 2^64) in *. set (tl1 := T1 mod 2^64) in *.
  set (th2 := T2 / 2^64) in *. set (tl2 := T2 mod 2^64) in *.
  clearbody th1 tl1 th2 tl2. subst T1 T2.
  replace (s1 * 2^63 + E1 * 2^48 + th1) with (s1 * 2^63 + (E1 * 2^48 + th1)) by lia.
  replace (s2 * 2^63 + E2 * 2^48 + th2) with (s2 * 2^63 + (E2 * 2^48 + th2)) by lia.
  rewrite cmp_core_val by lia.
  unfold f128_okey.
  replace (E1 * 2^112 + (th1 * 2^64 + tl1)) with ((E1 * 2^48 + th1) * 2^64 + tl1) by lia.
  replace (E2 * 2^112 + (th2 * 2^64 + tl2)) with ((E2 * 2^48 + th2) * 2^64 + tl2) by lia.
  reflexivity.
Qed.

Lemma f128_le_key : forall s1 E1 T1 s2 E2 T2, packed s1 E1 T1 -> packed s2 E2 T2 ->
  (E1 <= 32766 \/ T1 = 0) -> (E2 <= 32766 \/ T2 = 0) ->
  f128_le (f128_pack s1 E1 T1) (f128_pack s2 E2 T2) = cmp_res (Z.compare (f128_okey s1 E1 T1) (f128_okey s2 E2 T2)).
Proof.
  intros s1 E1 T1 s2 E2 T2 P1 P2 N1 N2.
  rewrite f128_le_split, (nan128_pack s1 E1 T1 P1 N1), (nan128_pack s2 E2 T2 P2 N2). cbv iota.
  apply cmp_pack; assumption.
Qed.

Lemma f128_ge_key : forall s1 E1 T1 s2 E2 T2, packed s1 E1 T1 -> packed s2 E2 T2 ->
  (E1 <= 32766 \/ T1 = 0) -> (E2 <= 32766 \/ T2 = 0) ->
  f128_ge (f128_pack s1 E1 T1) (f128_pack s2 E2 T2) = cmp_res (Z.compare (f128_okey s1 E1 T1) (f128_okey s2 E2 T2)).
Proof.
  intros s1 E1 T1 s2 E2 T2 P1 P2 N1 N2.
  rewrite f128_ge_split, (nan128_pack s1 E1 T1 P1 N1), (nan128_pack s2 E2 T2 P2 N2). cbv iota.
  apply cmp_pack; assumption.
Qed.
