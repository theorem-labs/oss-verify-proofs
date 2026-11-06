(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/FP.v; 949 of its 1006 lines of code are new or changed and 334 lines of the source are left out. *)
(** The binary64 steps of reac_float_nearest (src/reac_float_near.h:24-34), inlined in the readers of the pod
    (fuzz_headamp: reac_headamp_prop_parse_result; text from fuzz_role's reac_role_prop_parse), read against
    Pod/Nearest.v's [nearest]. No function of a binary is proved here: these are model lemmas the parse walk uses.

    The C code is [d = (double)f + 0.5] (fcvt.d.s, then fadd.d, both round to nearest-even), the range test
    [lo <= d < hi + 1] (fle.d, flt.d against two double constants), [t = (long long)d] (fcvt.l.d, round toward
    zero) and [r = t - (d < (double)t)] (fcvt.d.l, flt.d, sub). The rounded sum d has the floor of f + 1/2 for
    every finite float f ([pf_floor_key]): either f + 1/2 is a binary64 number, or f is tiny and d lies in
    [1/4, 3/4], or |f| >= 2^52 and f is an even integer, so the half is rounded off. Then t - [d < t] is
    floor d, and the comparisons are exact real comparisons. *)
From Stdlib Require Import ZArith Lia Bool Reals Lra Psatz SpecFloat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Fpu Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Nearest.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(** * The definitions the walk consumes *)

(** The value of a binary64 pattern as N / D, D a power of 2 (f32_ratio's binary64 twin); None for NaN, inf. *)
Definition f64_ratio (x : Z) : option (Z * Z) :=
  match fp_decode fmt_double x with
  | S754_zero _ => Some (0, 1)
  | S754_finite s m e =>
      let v := if s then - Zpos m else Zpos m in
      Some (if 0 <=? e then (v * 2^e, 1) else (v, 2^(-e)))
  | _ => None
  end.

(** reac_float_nearest(f, lo, hi) in binary64 with frm = RNE: d = f + 0.5 rounded; none unless lo <= d < hi + 1;
    else floor d. *)
Definition rfn_f64 (b lo hi : Z) : option Z :=
  let d := fst (fp_add fmt_double RNE (fst (fp_convert fmt_single fmt_double RNE b)) 0x3FE0000000000000) in
  match f64_ratio d with
  | Some (N, D) => if (lo * D <=? N) && (N <? (hi + 1) * D) then Some (N / D) else None
  | None => None
  end.

(** The words the instructions compute. *)
Definition f64_is_int (x : word) (k : Z) : bool :=
  match f64_ratio (bv_unsigned x) with Some (N, D) => N =? k * D | None => false end.
Definition rfn_d (b : Z) : word := fadd_d RNE (fcvt_d_s RNE (nan_box (Z_to_bv 32 b))) (Z_to_bv 64 0x3FE0000000000000).
Definition rfn_in (b : Z) (lod hid : word) : bool := fle_d lod (rfn_d b) && flt_d (rfn_d b) hid.
Definition rfn_t (b : Z) : word := fcvt_l_d RTZ (rfn_d b).
Definition rfn_r (b : Z) : Z := bv_signed (rfn_t b) - (if flt_d (rfn_d b) (fcvt_d_l RNE (rfn_t b)) then 1 else 0).

(** * Binary64 patterns, their values and Flocq's rounding *)

#[local] Instance pf_prec53 : Prec_gt_0 53. Proof. unfold Prec_gt_0; lia. Qed.
#[local] Instance pf_max53 : Prec_lt_emax 53 1024. Proof. unfold Prec_lt_emax; lia. Qed.

Lemma pf_round_exact_binary_round md s m e :
  fst (round_exact fmt_double md s m e) = binary_round 53 1024 (flocq_mode md) s m e.
Proof.
  unfold round_exact, binary_round, shl_align_fexp. cbn [fp_prec fp_emax fmt_double].
  destruct (SpecFloat.shl_align m e _) as [mz ez]. apply round_aux_value.
Qed.

Lemma pf_round_scaled_normalize md sz m e :
  fst (round_scaled fmt_double md sz (m, e)) =
  B2SF (binary_normalize 53 1024 pf_prec53 pf_max53 (flocq_mode md) m e sz).
Proof.
  unfold round_scaled, binary_normalize. destruct m as [|p|p]; cbn [fst].
  - reflexivity.
  - rewrite pf_round_exact_binary_round. rewrite B2SF_SF2B. reflexivity.
  - rewrite pf_round_exact_binary_round. rewrite B2SF_SF2B. reflexivity.
Qed.

Lemma pf_D_mw : fp_mw fmt_double = 52. Proof. reflexivity. Qed.
Lemma pf_D_ew : fp_ew fmt_double = 11. Proof. reflexivity. Qed.
Lemma pf_D_emin : fp_emin fmt_double = -1074. Proof. reflexivity. Qed.

Definition pf_pack (s : bool) (E M : Z) : Z := (if s then 2^63 else 0) + E * 2^52 + M.

Lemma pf_pack_fields s E M :
  0 <= E < 2048 -> 0 <= M < 2^52 ->
  fp_sign_bit fmt_double (pf_pack s E M) = s /\ fp_exp_field fmt_double (pf_pack s E M) = E /\
  fp_man_field fmt_double (pf_pack s E M) = M.
Proof.
  intros HE HM. unfold fp_sign_bit, fp_exp_field, fp_man_field. rewrite pf_D_mw, pf_D_ew. unfold pf_pack.
  set (sb := if s then 2^63 else 0).
  assert (Hsb : sb = (if s then 1 else 0) * 2^11 * 2^52) by (destruct s; reflexivity).
  repeat split.
  - change (52 + 11) with 63.
    assert (Hq : (sb + E * 2^52 + M) / 2^63 = (if s then 1 else 0)).
    { rewrite Hsb. replace ((if s then 1 else 0) * 2 ^ 11 * 2 ^ 52 + E * 2 ^ 52 + M)
        with ((E * 2^52 + M) + (if s then 1 else 0) * 2^63) by ring.
      rewrite Z.div_add by lia. rewrite (Z.div_small (E * 2^52 + M)) by lia. ring. }
    destruct s.
    + apply Z.testbit_true; [lia|]. rewrite Hq. reflexivity.
    + apply Z.testbit_false; [lia|]. rewrite Hq. reflexivity.
  - rewrite Z.shiftr_div_pow2 by lia. rewrite Z.land_ones by lia.
    replace ((sb + E * 2^52 + M) / 2^52) with ((if s then 1 else 0) * 2^11 + E).
    2:{ rewrite Hsb. replace ((if s then 1 else 0) * 2 ^ 11 * 2 ^ 52 + E * 2 ^ 52 + M)
          with (M + ((if s then 1 else 0) * 2^11 + E) * 2^52) by ring.
        rewrite Z.div_add by lia. rewrite Z.div_small by lia. ring. }
    rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.land_ones by lia. rewrite Hsb.
    replace ((if s then 1 else 0) * 2 ^ 11 * 2 ^ 52 + E * 2 ^ 52 + M)
      with (M + ((if s then 1 else 0) * 2^11 + E) * 2^52) by ring.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma pf_decode_pack s E M :
  0 <= E < 2048 -> 0 <= M < 2^52 ->
  fp_decode fmt_double (pf_pack s E M) =
    if E =? 0 then match M with Zpos p => S754_finite s p (-1074) | _ => S754_zero s end
    else if E =? 2047 then (if M =? 0 then S754_infinity s else S754_nan)
    else match 2^52 + M with Zpos p => S754_finite s p (E - 1075) | _ => S754_nan end.
Proof.
  intros HE HM. unfold fp_decode.
  destruct (pf_pack_fields s E M HE HM) as (H1 & H2 & H3). rewrite H1, H2, H3, pf_D_ew, pf_D_mw, pf_D_emin.
  change (Z.ones 11) with 2047. change (Z.shiftl 1 52) with (2^52).
  destruct (E =? 0); [reflexivity|]. destruct (E =? 2047); [reflexivity|].
  destruct (2^52 + M) eqn:EQ; try reflexivity; try lia. f_equal. lia.
Qed.

Lemma pf_digits2_pos_size m : SpecFloat.digits2_pos m = Pos.size m.
Proof. induction m; cbn; congruence. Qed.

Lemma pf_Zpos_size_bounds m : 2 ^ (Z.pos (Pos.size m) - 1) <= Z.pos m < 2 ^ Z.pos (Pos.size m).
Proof.
  split.
  - pose proof (Pos.size_le m) as H.
    assert (H1 : Z.pos (2 ^ Pos.size m) <= Z.pos (m~0)) by (apply Pos2Z.pos_le_pos; exact H).
    rewrite Pos2Z.inj_pow in H1. change (Z.pos m~0) with (2 * Z.pos m) in H1.
    replace (Z.pos (Pos.size m)) with (Z.pos (Pos.size m) - 1 + 1) in H1 by lia.
    rewrite Z.pow_add_r in H1 by lia. change (2^1) with 2 in H1. lia.
  - pose proof (Pos.size_gt m) as H.
    assert (H1 : Z.pos m < Z.pos (2 ^ Pos.size m)) by (apply Pos2Z.pos_lt_pos; exact H).
    rewrite Pos2Z.inj_pow in H1. exact H1.
Qed.

Lemma pf_encode_zero s : fp_encode fmt_double (S754_zero s) = pf_pack s 0 0.
Proof. unfold fp_encode, pf_pack. rewrite pf_D_mw, pf_D_ew. destruct s; reflexivity. Qed.
Lemma pf_encode_inf s : fp_encode fmt_double (S754_infinity s) = pf_pack s 2047 0.
Proof. unfold fp_encode, pf_pack. rewrite pf_D_mw, pf_D_ew. destruct s; reflexivity. Qed.
Lemma pf_encode_nan : fp_encode fmt_double S754_nan = pf_pack false 2047 (2^51).
Proof. reflexivity. Qed.

Lemma pf_valid_finite_cases s m e :
  valid_binary 53 1024 (S754_finite s m e) = true ->
  (Z.pos (Pos.size m) < 53 /\ e = -1074 /\ Z.pos m < 2^52)
  \/ (Z.pos (Pos.size m) = 53 /\ -1074 <= e <= 971 /\ 2^52 <= Z.pos m < 2^53).
Proof.
  unfold valid_binary, SpecFloat.bounded, SpecFloat.canonical_mantissa, SpecFloat.fexp, SpecFloat.emin.
  rewrite pf_digits2_pos_size. intros H.
  apply andb_prop in H. destruct H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.leb_le in H2.
  pose proof (pf_Zpos_size_bounds m) as [B1 B2].
  destruct (Z_lt_le_dec (Z.pos (Pos.size m)) 53) as [L|L].
  - left. repeat split; try lia.
    assert (2 ^ Z.pos (Pos.size m) <= 2^52) by (apply Z.pow_le_mono_r; lia). lia.
  - right. assert (Z.pos (Pos.size m) = 53) by lia. repeat split; try lia.
    + rewrite H in B1. change (2^(53-1)) with (2^52) in B1. lia.
    + rewrite H in B2. lia.
Qed.

Lemma pf_encode_finite_sub s m e :
  Z.pos (Pos.size m) < 53 -> fp_encode fmt_double (S754_finite s m e) = pf_pack s 0 (Z.pos m).
Proof.
  intros H. unfold fp_encode, pf_pack. cbn [fp_prec fmt_double]. rewrite pf_D_mw, pf_D_ew.
  replace (Z.pos (Pos.size m) <? 53) with true by (symmetry; apply Z.ltb_lt; lia).
  change (Z.shiftl 1 (52 + 11)) with (2^63). destruct s; lia.
Qed.

Lemma pf_encode_finite_norm s m e :
  Z.pos (Pos.size m) = 53 -> fp_encode fmt_double (S754_finite s m e) = pf_pack s (e + 1075) (Z.pos m - 2^52).
Proof.
  intros H. unfold fp_encode, pf_pack. cbn [fp_prec fmt_double]. rewrite pf_D_mw, pf_D_ew, pf_D_emin.
  replace (Z.pos (Pos.size m) <? 53) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite (Z.shiftl_mul_pow2 (e - -1074 + 1)) by lia. change (Z.shiftl 1 52) with (2^52).
  change (Z.shiftl 1 (52 + 11)) with (2^63).
  replace (e - -1074 + 1) with (e + 1075) by lia. destruct s; lia.
Qed.

Theorem pf_decode_encode sf :
  valid_binary 53 1024 sf = true -> fp_decode fmt_double (fp_encode fmt_double sf) = sf.
Proof.
  intros V. destruct sf as [s|s| |s m e].
  - rewrite pf_encode_zero, pf_decode_pack by lia. reflexivity.
  - rewrite pf_encode_inf, pf_decode_pack by lia. reflexivity.
  - rewrite pf_encode_nan, pf_decode_pack by lia. reflexivity.
  - destruct (pf_valid_finite_cases s m e V) as [(A & B & C)|(A & B & C)].
    + rewrite (pf_encode_finite_sub s m e A), pf_decode_pack by lia. cbn. subst e. reflexivity.
    + rewrite (pf_encode_finite_norm s m e A), pf_decode_pack by lia.
      replace (e + 1075 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (e + 1075 =? 2047) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (2 ^ 52 + (Z.pos m - 2 ^ 52)) with (Z.pos m) by lia. f_equal. lia.
Qed.

Lemma pf_encode_range sf : valid_binary 53 1024 sf = true -> 0 <= fp_encode fmt_double sf < 2^64.
Proof.
  intros V. destruct sf as [s|s| |s m e].
  - rewrite pf_encode_zero. unfold pf_pack; destruct s; lia.
  - rewrite pf_encode_inf. unfold pf_pack; destruct s; lia.
  - rewrite pf_encode_nan. unfold pf_pack; lia.
  - destruct (pf_valid_finite_cases s m e V) as [(A & B & C)|(A & B & C)].
    + rewrite (pf_encode_finite_sub s m e A). unfold pf_pack; destruct s; lia.
    + rewrite (pf_encode_finite_norm s m e A). unfold pf_pack; destruct s; lia.
Qed.

Definition pf_Dval (a : Z) : R := SF2R radix2 (fp_decode fmt_double a).
Definition pf_Dfin (a : Z) : Prop := is_finite_SF (fp_decode fmt_double a) = true.
Definition pf_rnd (x : R) : R := Generic_fmt.round radix2 (FLT_exp (-1074) 53) ZnearestE x.
Abbreviation pf_fmt := (generic_format radix2 (FLT_exp (-1074) 53)).

Lemma pf_fexp_D : SpecFloat.fexp 53 1024 = FLT_exp (-1074) 53.
Proof. reflexivity. Qed.

Lemma pf_Dfin_not_nan a : pf_Dfin a -> fp_is_nan fmt_double a = false.
Proof.
  unfold pf_Dfin, fp_is_nan, fp_decode. cbv zeta. rewrite pf_D_ew.
  destruct (fp_exp_field fmt_double a =? 0) eqn:E0.
  - intros _. apply Z.eqb_eq in E0. rewrite E0. reflexivity.
  - destruct (fp_exp_field fmt_double a =? Z.ones 11) eqn:E1; [|reflexivity].
    destruct (fp_man_field fmt_double a =? 0) eqn:M0; [reflexivity|]. cbn. intros H. discriminate H.
Qed.

Lemma pf_nan_pass2_none a b : pf_Dfin a -> pf_Dfin b -> nan_pass2 fmt_double a b = None.
Proof.
  intros Ha Hb. unfold nan_pass2. rewrite (pf_Dfin_not_nan a Ha), (pf_Dfin_not_nan b Hb). reflexivity.
Qed.

Lemma pf_Dfin_encode_valid z : valid_binary 53 1024 z = true -> is_finite_SF z = true ->
  pf_Dfin (fp_encode fmt_double z) /\ pf_Dval (fp_encode fmt_double z) = SF2R radix2 z /\
  0 <= fp_encode fmt_double z < 2^64.
Proof.
  intros V F. unfold pf_Dfin, pf_Dval. rewrite (pf_decode_encode z V).
  split; [exact F|]. split; [reflexivity|]. exact (pf_encode_range z V).
Qed.

Definition pf_ZZval (p : Z * Z) : R := F2R (Float radix2 (fst p) (snd p)).

Lemma pf_F2R_IZR_bpow m e : F2R (Float radix2 m e) = (IZR m * bpow radix2 e)%R.
Proof. reflexivity. Qed.

Lemma pf_sf_scaled_val x : is_finite_SF x = true -> pf_ZZval (sf_scaled x) = SF2R radix2 x.
Proof.
  destruct x as [s|s| |s m e]; cbn [is_finite_SF sf_scaled fst snd SF2R]; intros H; try discriminate H.
  - unfold pf_ZZval; cbn [fst snd]. rewrite pf_F2R_IZR_bpow. lra.
  - unfold pf_ZZval; cbn [fst snd]. destruct s; reflexivity.
Qed.

Lemma pf_scaled_add_val p q : pf_ZZval (scaled_add p q) = (pf_ZZval p + pf_ZZval q)%R.
Proof.
  destruct p as [ma ea], q as [mb eb]. unfold scaled_add, pf_ZZval; cbn [fst snd].
  set (e := Z.min ea eb).
  rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite !pf_F2R_IZR_bpow. rewrite plus_IZR, !mult_IZR.
  replace (IZR (2 ^ (ea - e))) with (bpow radix2 (ea - e)) by (rewrite <- IZR_Zpower by lia; reflexivity).
  replace (IZR (2 ^ (eb - e))) with (bpow radix2 (eb - e)) by (rewrite <- IZR_Zpower by lia; reflexivity).
  replace ea with ((ea - e) + e) at 2 by lia. replace eb with ((eb - e) + e) at 2 by lia.
  rewrite !bpow_plus. ring.
Qed.

Theorem pf_round_scaled_correct sz p :
  (Rabs (pf_rnd (pf_ZZval p)) < bpow radix2 1024)%R ->
  pf_Dfin (fp_encode fmt_double (fst (round_scaled fmt_double RNE sz p))) /\
  pf_Dval (fp_encode fmt_double (fst (round_scaled fmt_double RNE sz p))) = pf_rnd (pf_ZZval p) /\
  0 <= fp_encode fmt_double (fst (round_scaled fmt_double RNE sz p)) < 2^64.
Proof.
  intros Hov. destruct p as [m e].
  rewrite pf_round_scaled_normalize. cbn [flocq_mode].
  pose proof (binary_normalize_correct 53 1024 pf_prec53 pf_max53 mode_NE m e sz) as BN. cbv zeta in BN.
  rewrite pf_fexp_D in BN. cbn [round_mode] in BN. unfold pf_ZZval in Hov; cbn [fst snd] in Hov.
  unfold pf_rnd in Hov.
  rewrite (Rlt_bool_true _ _ Hov) in BN. destruct BN as (R1 & R2 & R3).
  set (z := binary_normalize 53 1024 pf_prec53 pf_max53 mode_NE m e sz) in *.
  destruct (pf_Dfin_encode_valid (B2SF z) (valid_binary_B2SF _ _ z)) as (A & B & C).
  { rewrite is_finite_SF_B2SF. exact R2. }
  split; [exact A|]. split; [|exact C].
  rewrite B, SF2R_B2SF, R1. unfold pf_rnd, pf_ZZval. reflexivity.
Qed.

Theorem pf_dadd_correct a b :
  pf_Dfin a -> pf_Dfin b ->
  (Rabs (pf_rnd (pf_Dval a + pf_Dval b)) < bpow radix2 1024)%R ->
  pf_Dfin (fst (fp_add fmt_double RNE a b)) /\
  pf_Dval (fst (fp_add fmt_double RNE a b)) = pf_rnd (pf_Dval a + pf_Dval b) /\
  0 <= fst (fp_add fmt_double RNE a b) < 2^64.
Proof.
  intros Ha Hb Hov. unfold fp_add. rewrite (pf_nan_pass2_none a b Ha Hb).
  unfold pf_Dfin, pf_Dval in *.
  assert (E : forall x y : spec_float, is_finite_SF x = true -> is_finite_SF y = true ->
    match x, y with
    | S754_infinity sa, S754_infinity sb =>
        if Bool.eqb sa sb then (fp_encode fmt_double (S754_infinity sa), no_flags)
        else (fp_canonical_nan fmt_double, nv_flag)
    | S754_infinity sa, _ => (fp_encode fmt_double (S754_infinity sa), no_flags)
    | _, S754_infinity sb => (fp_encode fmt_double (S754_infinity sb), no_flags)
    | _, _ => enc fmt_double (round_scaled fmt_double RNE (zero_sign RNE (sf_sign x) (sf_sign y))
                                (scaled_add (sf_scaled x) (sf_scaled y)))
    end = enc fmt_double (round_scaled fmt_double RNE (zero_sign RNE (sf_sign x) (sf_sign y))
                            (scaled_add (sf_scaled x) (sf_scaled y)))).
  { intros x y Hx Hy. destruct x; try discriminate; destruct y; try discriminate; reflexivity. }
  first [ rewrite (E _ _ Ha Hb) | cbv beta iota zeta; rewrite (E _ _ Ha Hb) ]. unfold enc. cbn [fst].
  pose proof (pf_round_scaled_correct (zero_sign RNE (sf_sign (fp_decode fmt_double a)) (sf_sign (fp_decode fmt_double b)))
                (scaled_add (sf_scaled (fp_decode fmt_double a)) (sf_scaled (fp_decode fmt_double b)))) as RS.
  rewrite pf_scaled_add_val, !pf_sf_scaled_val in RS by assumption.
  exact (RS Hov).
Qed.

Lemma pf_size_lt_of_lt p k : 0 < k -> Z.pos p < 2^k -> Z.pos (Pos.size p) <= k.
Proof.
  intros Hk H. pose proof (pf_Zpos_size_bounds p) as [B1 B2].
  destruct (Z_lt_le_dec k (Z.pos (Pos.size p))); [|lia].
  assert (2^k <= 2^(Z.pos (Pos.size p) - 1)) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma pf_size_eq_of_bounds p k : 0 < k -> 2^(k-1) <= Z.pos p < 2^k -> Z.pos (Pos.size p) = k.
Proof.
  intros Hk [H1 H2]. pose proof (pf_size_lt_of_lt p k Hk H2).
  pose proof (pf_Zpos_size_bounds p) as [B1 B2].
  destruct (Z_lt_le_dec (Z.pos (Pos.size p)) k); [|lia].
  assert (2^(Z.pos (Pos.size p)) <= 2^(k-1)) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma pf_exp_field_range a : 0 <= fp_exp_field fmt_double a < 2048.
Proof. unfold fp_exp_field. rewrite pf_D_ew, Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.
Lemma pf_man_field_range a : 0 <= fp_man_field fmt_double a < 2^52.
Proof. unfold fp_man_field. rewrite pf_D_mw, Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.

Theorem pf_decode_valid a : valid_binary 53 1024 (fp_decode fmt_double a) = true.
Proof.
  pose proof (pf_exp_field_range a) as HE. pose proof (pf_man_field_range a) as HM.
  unfold fp_decode. cbv zeta. rewrite pf_D_ew, pf_D_mw, pf_D_emin.
  change (Z.ones 11) with 2047. change (Z.shiftl 1 52) with (2^52).
  set (E := fp_exp_field fmt_double a) in *. set (M := fp_man_field fmt_double a) in *.
  destruct (E =? 0) eqn:E0.
  - destruct M as [|p|p] eqn:EM; try reflexivity.
    unfold valid_binary, SpecFloat.bounded, SpecFloat.canonical_mantissa, SpecFloat.fexp, SpecFloat.emin.
    rewrite pf_digits2_pos_size. pose proof (pf_size_lt_of_lt p 52 ltac:(lia) ltac:(lia)).
    apply andb_true_intro; split; [apply Z.eqb_eq; lia| apply Z.leb_le; lia].
  - destruct (E =? 2047) eqn:E1. { destruct (M =? 0); reflexivity. }
    apply Z.eqb_neq in E0. apply Z.eqb_neq in E1.
    destruct (2^52 + M) as [|p|p] eqn:EP; try lia.
    unfold valid_binary, SpecFloat.bounded, SpecFloat.canonical_mantissa, SpecFloat.fexp, SpecFloat.emin.
    rewrite pf_digits2_pos_size. rewrite (pf_size_eq_of_bounds p 53) by (simpl; lia).
    apply andb_true_intro; split; [apply Z.eqb_eq; lia| apply Z.leb_le; lia].
Qed.

Definition pf_DB (a : Z) : binary_float 53 1024 := SF2B (fp_decode fmt_double a) (pf_decode_valid a).

Lemma pf_DB_B2R a : B2R (pf_DB a) = pf_Dval a.
Proof. unfold pf_DB, pf_Dval. apply B2R_SF2B. Qed.
Lemma pf_DB_finite a : pf_Dfin a -> is_finite (pf_DB a) = true.
Proof. unfold pf_DB, pf_Dfin. rewrite is_finite_SF2B. auto. Qed.

Lemma pf_fp_compare_correct a b : pf_Dfin a -> pf_Dfin b ->
  fp_compare fmt_double a b = Some (Rcompare (pf_Dval a) (pf_Dval b)).
Proof.
  intros Ha Hb. unfold fp_compare.
  rewrite <- (B2SF_SF2B _ _ _ (pf_decode_valid a)). rewrite <- (B2SF_SF2B _ _ _ (pf_decode_valid b)).
  change (SFcompare (B2SF ?x) (B2SF ?y)) with (Bcompare x y).
  rewrite Bcompare_correct by (apply pf_DB_finite; assumption).
  rewrite <- !pf_DB_B2R. reflexivity.
Qed.

Theorem pf_dlt_correct a b : pf_Dfin a -> pf_Dfin b ->
  fst (fp_lt fmt_double a b) = Rlt_bool (pf_Dval a) (pf_Dval b).
Proof. intros Ha Hb. unfold fp_lt. cbn [fst]. rewrite pf_fp_compare_correct by assumption. reflexivity. Qed.

Theorem pf_dle_correct a b : pf_Dfin a -> pf_Dfin b ->
  fst (fp_le fmt_double a b) = Rle_bool (pf_Dval a) (pf_Dval b).
Proof.
  intros Ha Hb. unfold fp_le. cbn [fst]. rewrite pf_fp_compare_correct by assumption.
  unfold Rle_bool. destruct (Rcompare _ _); reflexivity.
Qed.

Lemma pf_rnd_generic x : pf_fmt x -> pf_rnd x = x.
Proof. intros H. unfold pf_rnd. apply round_generic; auto with typeclass_instances. Qed.

Lemma pf_rnd_le x y : (x <= y)%R -> (pf_rnd x <= pf_rnd y)%R.
Proof.
  intros H. unfold pf_rnd.
  apply round_le; [apply FLT_exp_valid; unfold Prec_gt_0; lia | auto with typeclass_instances | exact H].
Qed.

Lemma pf_fmt_bpow e : -1074 <= e -> pf_fmt (bpow radix2 e).
Proof. intros H. apply generic_format_bpow. unfold FLT_exp. lia. Qed.

Lemma pf_fmt_opp x : pf_fmt x -> pf_fmt (- x)%R.
Proof. apply generic_format_opp. Qed.

Lemma pf_fmt_IZR n : Z.abs n < 2^53 -> pf_fmt (IZR n).
Proof.
  intros H. apply generic_format_FLT. exists (Float radix2 n 0).
  - unfold F2R, Fnum, Fexp. cbn [bpow]. ring.
  - cbn [Fnum]. change (radix_val radix2) with 2. exact H.
  - cbn [Fexp]. lia.
Qed.

Lemma pf_fmt_IZR_bpow n e : Z.abs n < 2^53 -> -1074 <= e -> pf_fmt (IZR n * bpow radix2 e)%R.
Proof.
  intros H He. apply generic_format_FLT. exists (Float radix2 n e).
  - reflexivity.
  - cbn [Fnum]. change (radix_val radix2) with 2. exact H.
  - cbn [Fexp]. lia.
Qed.

Lemma pf_rnd_abs_le x B : pf_fmt B -> (Rabs x <= B)%R -> (Rabs (pf_rnd x) <= B)%R.
Proof.
  intros FB H. apply Rabs_le_inv in H. destruct H as [H1 H2].
  apply Rabs_le. split.
  - rewrite <- (pf_rnd_generic (-B)) by (apply pf_fmt_opp; auto). apply pf_rnd_le. exact H1.
  - rewrite <- (pf_rnd_generic B) by auto. apply pf_rnd_le. exact H2.
Qed.

Lemma pf_rnd_ge_fmt x B : pf_fmt B -> (B <= x)%R -> (B <= pf_rnd x)%R.
Proof. intros FB H. rewrite <- (pf_rnd_generic B) by auto. apply pf_rnd_le. exact H. Qed.
Lemma pf_rnd_le_fmt x B : pf_fmt B -> (x <= B)%R -> (pf_rnd x <= B)%R.
Proof. intros FB H. rewrite <- (pf_rnd_generic B) by auto. apply pf_rnd_le. exact H. Qed.

(** * Small real and integer facts *)

Lemma pf_IZR_pow k : 0 <= k -> IZR (2^k) = bpow radix2 k.
Proof. intros H. rewrite <- (IZR_Zpower radix2 k H). reflexivity. Qed.

Lemma pf_IZR_mul_pow v e : 0 <= e -> IZR (v * 2^e) = (IZR v * bpow radix2 e)%R.
Proof. intros H. rewrite mult_IZR, pf_IZR_pow by exact H. reflexivity. Qed.

Lemma pf_abs_cond_Zopp s m : Z.abs (cond_Zopp s (Z.pos m)) = Z.pos m.
Proof. destruct s; reflexivity. Qed.

Lemma pf_abs_val_lt v e k : Z.abs v < 2^k -> 0 <= k ->
  (Rabs (IZR v * bpow radix2 e) < bpow radix2 (k + e))%R.
Proof.
  intros Hv Hk. rewrite Rabs_mult, Rabs_Zabs, (Rabs_pos_eq (bpow radix2 e)) by (apply bpow_ge_0).
  rewrite bpow_plus. apply Rmult_lt_compat_r; [apply bpow_gt_0|].
  rewrite <- pf_IZR_pow by exact Hk. apply IZR_lt. exact Hv.
Qed.

Lemma pf_floor_eq n y : (IZR n <= y < IZR n + 1)%R -> Zfloor y = n.
Proof. intros H. apply Zfloor_imp. rewrite plus_IZR. exact H. Qed.

Lemma pf_floor_bounds lo hi y : lo <= Zfloor y <= hi -> (IZR lo <= y < IZR (hi + 1))%R.
Proof.
  intros [H1 H2]. pose proof (Zfloor_lb y). pose proof (Zfloor_ub y).
  apply IZR_le in H1. apply IZR_le in H2. rewrite plus_IZR. split; lra.
Qed.

Lemma pf_Rle_floor n y : Rle_bool (IZR n) y = (n <=? Zfloor y).
Proof.
  destruct (Rle_bool_spec (IZR n) y) as [H|H].
  - symmetry. apply Z.leb_le. apply Zfloor_lub. exact H.
  - symmetry. apply Z.leb_gt. pose proof (Zfloor_lb y).
    destruct (Z_lt_le_dec (Zfloor y) n) as [L|L]; [exact L|]. apply IZR_le in L. lra.
Qed.

Lemma pf_Rlt_floor y n : Rlt_bool y (IZR (n + 1)) = (Zfloor y <=? n).
Proof.
  destruct (Rlt_bool_spec y (IZR (n + 1))) as [H|H].
  - symmetry. apply Z.leb_le. pose proof (Zfloor_lb y).
    assert (L : Zfloor y < n + 1) by (apply lt_IZR; lra). lia.
  - symmetry. apply Z.leb_gt. assert (L : n + 1 <= Zfloor y) by (apply Zfloor_lub; exact H). lia.
Qed.

(** t - [d < t] with t = trunc d is floor d. *)
Lemma pf_trunc_floor y : Ztrunc y - (if Rlt_bool y (IZR (Ztrunc y)) then 1 else 0) = Zfloor y.
Proof.
  pose proof (Zfloor_lb y) as L. pose proof (Zfloor_ub y) as U.
  destruct (Rlt_or_le y 0) as [Hn|Hp].
  - rewrite (Ztrunc_ceil y) by lra.
    destruct (Req_dec (IZR (Zfloor y)) y) as [E|E].
    + assert (C : Zceil y = Zfloor y). { rewrite <- E at 1. apply Zceil_IZR. }
      rewrite C, Rlt_bool_false by lra. lia.
    + rewrite (Zceil_floor_neq y E). rewrite Rlt_bool_true; [lia|]. rewrite plus_IZR. lra.
  - rewrite (Ztrunc_floor y) by lra. rewrite Rlt_bool_false by lra. lia.
Qed.

Lemma pf_leb_div lo N D : 0 < D -> (lo * D <=? N) = (lo <=? N / D).
Proof.
  intros HD. pose proof (Z.div_mod N D ltac:(lia)) as DM. pose proof (Z.mod_pos_bound N D HD) as MB.
  destruct (Z.leb_spec lo (N / D)) as [H|H].
  - apply Z.leb_le. nia.
  - apply Z.leb_gt. nia.
Qed.

Lemma pf_ltb_div N hi D : 0 < D -> (N <? (hi + 1) * D) = (N / D <=? hi).
Proof.
  intros HD. pose proof (Z.div_mod N D ltac:(lia)) as DM. pose proof (Z.mod_pos_bound N D HD) as MB.
  destruct (Z.leb_spec (N / D) hi) as [H|H].
  - apply Z.ltb_lt. nia.
  - apply Z.ltb_ge. nia.
Qed.

(** * The rounding fact: RNE64(f + 1/2) has the floor of f + 1/2 *)

Lemma pf_Znearest_even W t : Z.even W = true -> (0 <= t <= /2)%R -> ZnearestE (IZR W + t) = W.
Proof.
  intros HW Ht. unfold Znearest.
  rewrite (pf_floor_eq W (IZR W + t)) by lra.
  replace (IZR W + t - IZR W)%R with t by ring.
  destruct (Rle_lt_or_eq_dec t (/2) (proj2 Ht)) as [Hlt|Heq].
  - rewrite Rcompare_Lt by exact Hlt. reflexivity.
  - rewrite Rcompare_Eq by exact Heq. cbv beta. rewrite HW. reflexivity.
Qed.

(** |f| >= 2^52 (here f = v 2^e, an integer): RNE64(f + 1/2) = f. *)
Lemma pf_rnd_big v e : 0 <= e -> Z.abs v < 2^24 -> 2^53 <= Z.abs (2 * (v * 2^e) + 1) ->
  pf_rnd (IZR (v * 2^e) + /2) = IZR (v * 2^e).
Proof.
  intros He Hv Hb.
  assert (HVa : Z.abs (v * 2^e) < 2^(24 + e)).
  { rewrite Z.abs_mul, Z.pow_add_r by lia. rewrite (Z.abs_eq (2^e)) by (apply Z.pow_nonneg; lia).
    assert (P : 0 < 2^e) by (apply Z.pow_pos_nonneg; lia). nia. }
  remember (v * 2^e) as V eqn:EV.
  assert (HV : 2^52 <= V \/ V <= -2^52 - 1) by lia.
  assert (P52 : (0 < IZR (2^52))%R) by (apply IZR_lt; lia).
  assert (HxB : (bpow radix2 52 <= Rabs (IZR V + /2))%R).
  { rewrite <- pf_IZR_pow by lia. destruct HV as [HV|HV].
    - apply IZR_le in HV. rewrite Rabs_pos_eq; lra.
    - apply IZR_le in HV. rewrite minus_IZR, opp_IZR in HV. rewrite Rabs_left; lra. }
  assert (Hx0 : (IZR V + /2 <> 0)%R).
  { intros H0. rewrite H0, Rabs_R0 in HxB. pose proof (bpow_gt_0 radix2 52). lra. }
  assert (HxV : (Rabs (IZR V + /2) <= IZR (Z.abs V) + /2)%R).
  { rewrite <- Rabs_Zabs. eapply Rle_trans; [apply Rabs_triang|]. rewrite (Rabs_pos_eq (/2)) by lra. lra. }
  pose proof (mag_ge_bpow radix2 (IZR V + /2) 53 HxB) as Hk1.
  pose proof (bpow_mag_le radix2 (IZR V + /2) Hx0) as Hk3.
  unfold pf_rnd, Generic_fmt.round, scaled_mantissa, cexp.
  set (k := mag_val radix2 (IZR V + /2) (mag radix2 (IZR V + /2))) in *.
  unfold FLT_exp. rewrite Z.max_l by lia.
  assert (Hek : k - 24 <= e).
  { assert (H2 : 2^(k-1) <= Z.abs V).
    { assert (H1 : (IZR (2^(k-1)) <= IZR (Z.abs V) + /2)%R) by (rewrite pf_IZR_pow by lia; lra).
      assert (H3 : (IZR (2^(k-1) - Z.abs V) < IZR 1)%R) by (rewrite minus_IZR; lra).
      apply lt_IZR in H3. lia. }
    destruct (Z_lt_le_dec e (k - 24)) as [L|L]; [|exact L].
    assert (H4 : 2^(24 + e) <= 2^(k-1)) by (apply Z.pow_le_mono_r; lia).
    lia. }
  remember (k - 53) as c eqn:Ec.
  assert (SM : ((IZR V + /2) * bpow radix2 (- c) = IZR (v * 2^(e - c)) + bpow radix2 (-1 - c))%R).
  { rewrite EV, Rmult_plus_distr_r. rewrite (pf_IZR_mul_pow v e) by lia. rewrite (pf_IZR_mul_pow v (e - c)) by lia.
    rewrite Rmult_assoc, <- bpow_plus. replace (e + - c) with (e - c) by lia.
    change (/2)%R with (bpow radix2 (-1)). rewrite <- bpow_plus. replace (-1 + - c) with (-1 - c) by lia.
    reflexivity. }
  rewrite SM.
  assert (Hev : Z.even (v * 2^(e - c)) = true).
  { assert (E2 : 2^(e - c) = 2 * 2^(e - c - 1)).
    { rewrite <- Z.pow_succ_r by lia. f_equal. lia. }
    rewrite E2, !Z.even_mul. destruct (Z.even v); reflexivity. }
  rewrite (pf_Znearest_even _ _ Hev).
  - rewrite pf_F2R_IZR_bpow, (pf_IZR_mul_pow v (e - c)) by lia. rewrite Rmult_assoc, <- bpow_plus.
    replace (e - c + c) with e by lia. rewrite EV, (pf_IZR_mul_pow v e) by lia. reflexivity.
  - split; [apply bpow_ge_0|]. change (/2)%R with (bpow radix2 (-1)). apply bpow_le. lia.
Qed.

(** The core, for f = v 2^e with |v| < 2^24 (a finite binary32 value). *)
Lemma pf_floor_core v e : Z.abs v < 2^24 -> -149 <= e ->
  Zfloor (pf_rnd (IZR v * bpow radix2 e + /2)) = Zfloor (IZR v * bpow radix2 e + /2).
Proof.
  intros Hv He0.
  destruct (Z_lt_le_dec e (-53)) as [ET|EE].
  - (* |f| < 2^-30: f + 1/2 and its rounding lie in [1/4, 3/4]. *)
    assert (A : (Rabs (IZR v * bpow radix2 e) < /4)%R).
    { eapply Rlt_le_trans; [apply (pf_abs_val_lt v e 24 Hv); lia|].
      change (/4)%R with (bpow radix2 (-2)). apply bpow_le. lia. }
    destruct (Rabs_def2 _ _ A) as [A1 A2].
    assert (F14 : pf_fmt (/4)%R) by (change (/4)%R with (bpow radix2 (-2)); apply pf_fmt_bpow; lia).
    assert (F34 : pf_fmt (3/4)%R).
    { replace (3/4)%R with (IZR 3 * bpow radix2 (-2))%R by (change (bpow radix2 (-2)) with (/4)%R; lra).
      apply pf_fmt_IZR_bpow; lia. }
    assert (R1 : (/4 <= pf_rnd (IZR v * bpow radix2 e + /2))%R) by (apply pf_rnd_ge_fmt; [exact F14 | lra]).
    assert (R2 : (pf_rnd (IZR v * bpow radix2 e + /2) <= 3/4)%R) by (apply pf_rnd_le_fmt; [exact F34 | lra]).
    rewrite (pf_floor_eq 0 (pf_rnd (IZR v * bpow radix2 e + /2))) by lra.
    rewrite (pf_floor_eq 0 (IZR v * bpow radix2 e + /2)) by lra. reflexivity.
  - destruct (Z_lt_le_dec e 0) as [EN|EP].
    + (* -53 <= e < 0: f + 1/2 = (v + 2^(-1-e)) 2^e is a binary64 number. *)
      assert (EX : (IZR v * bpow radix2 e + /2 = IZR (v + 2^(-1-e)) * bpow radix2 e)%R).
      { rewrite plus_IZR, Rmult_plus_distr_r, (pf_IZR_pow (-1-e)) by lia. rewrite <- bpow_plus.
        replace (-1 - e + e) with (-1) by lia. change (bpow radix2 (-1)) with (/2)%R. reflexivity. }
      rewrite EX, pf_rnd_generic; [reflexivity|].
      apply pf_fmt_IZR_bpow; [|lia].
      assert (P : 2^(-1-e) <= 2^52) by (apply Z.pow_le_mono_r; lia).
      assert (P0 : 0 < 2^(-1-e)) by (apply Z.pow_pos_nonneg; lia).
      lia.
    + (* e >= 0: f is an integer. *)
      rewrite <- (pf_IZR_mul_pow v e EP).
      destruct (Z_lt_le_dec (Z.abs (2 * (v * 2^e) + 1)) (2^53)) as [Small|Big].
      * assert (EX : (IZR (v * 2^e) + /2 = IZR (2 * (v * 2^e) + 1) * bpow radix2 (-1))%R).
        { change (bpow radix2 (-1)) with (/2)%R. rewrite plus_IZR, (mult_IZR 2 (v * 2^e)). field. }
        rewrite EX, pf_rnd_generic; [reflexivity|]. apply pf_fmt_IZR_bpow; lia.
      * rewrite (pf_rnd_big v e EP Hv Big). rewrite Zfloor_IZR. symmetry. apply pf_floor_eq. lra.
Qed.

(** * Binary32 patterns *)

Definition pf_Sval (b : Z) : R := SF2R radix2 (fp_decode fmt_single b).
Definition pf_Sfin (b : Z) : Prop := is_finite_SF (fp_decode fmt_single b) = true.

Lemma pf_S_exp_range b : 0 <= fp_exp_field fmt_single b < 2^8.
Proof.
  unfold fp_exp_field. change (fp_ew fmt_single) with 8. rewrite Z.land_ones by lia.
  apply Z.mod_pos_bound. lia.
Qed.

Lemma pf_S_man_range b : 0 <= fp_man_field fmt_single b < 2^23.
Proof.
  unfold fp_man_field. change (fp_mw fmt_single) with 23. rewrite Z.land_ones by lia.
  apply Z.mod_pos_bound. lia.
Qed.

Lemma pf_S_fin_bounds b s m e : fp_decode fmt_single b = S754_finite s m e -> Z.pos m < 2^24 /\ -149 <= e <= 104.
Proof.
  pose proof (pf_S_exp_range b) as HE. pose proof (pf_S_man_range b) as HM.
  unfold fp_decode. cbv zeta.
  change (Z.ones (fp_ew fmt_single)) with 255. change (Z.shiftl 1 (fp_mw fmt_single)) with 8388608.
  change (fp_emin fmt_single) with (-149).
  destruct (Z.eqb_spec (fp_exp_field fmt_single b) 0) as [E0|E0]; cbv iota.
  - destruct (fp_man_field fmt_single b) as [|p|p] eqn:EM; cbv iota; intros H; try discriminate H.
    injection H as Hs Hp He. subst m e. split; lia.
  - destruct (Z.eqb_spec (fp_exp_field fmt_single b) 255) as [E1|E1]; cbv iota.
    + destruct (fp_man_field fmt_single b =? 0); cbv iota; intros H; discriminate H.
    + destruct (8388608 + fp_man_field fmt_single b) as [|p|p] eqn:EP; cbv iota; intros H; try discriminate H.
      injection H as Hs Hp He. subst m e. split; lia.
Qed.

Lemma pf_S_is_nan b : fp_is_nan fmt_single b = match fp_decode fmt_single b with S754_nan => true | _ => false end.
Proof.
  pose proof (pf_S_man_range b) as HM.
  unfold fp_decode, fp_is_nan. cbv zeta.
  change (Z.ones (fp_ew fmt_single)) with 255. change (Z.shiftl 1 (fp_mw fmt_single)) with 8388608.
  destruct (Z.eqb_spec (fp_exp_field fmt_single b) 0) as [E0|E0]; cbv iota.
  - rewrite E0. destruct (fp_man_field fmt_single b); reflexivity.
  - destruct (Z.eqb_spec (fp_exp_field fmt_single b) 255) as [E1|E1]; cbv iota.
    + destruct (fp_man_field fmt_single b =? 0); reflexivity.
    + destruct (8388608 + fp_man_field fmt_single b) as [|p|p] eqn:EP.
      * exfalso. lia.
      * reflexivity.
      * exfalso. pose proof (Pos2Z.neg_is_neg p). lia.
Qed.

Lemma pf_S_fin_not_nan b : pf_Sfin b -> fp_is_nan fmt_single b = false.
Proof.
  unfold pf_Sfin. rewrite pf_S_is_nan.
  destruct (fp_decode fmt_single b); intros H; cbn in H |- *; first [reflexivity | discriminate H].
Qed.

Lemma pf_S_inf_not_nan b s : fp_decode fmt_single b = S754_infinity s -> fp_is_nan fmt_single b = false.
Proof. intros H. rewrite pf_S_is_nan, H. reflexivity. Qed.

Lemma pf_S_nan_is_nan b : fp_decode fmt_single b = S754_nan -> fp_is_nan fmt_single b = true.
Proof. intros H. rewrite pf_S_is_nan, H. reflexivity. Qed.

Lemma pf_Sval_bound b : (Rabs (pf_Sval b) <= bpow radix2 128)%R.
Proof.
  unfold pf_Sval. destruct (fp_decode fmt_single b) as [s|s| |s m e] eqn:Eb; cbn [SF2R];
    try (rewrite Rabs_R0; apply bpow_ge_0).
  destruct (pf_S_fin_bounds b s m e Eb) as [Hm He].
  rewrite pf_F2R_IZR_bpow. apply Rlt_le. eapply Rlt_le_trans.
  - apply (pf_abs_val_lt _ e 24); [rewrite pf_abs_cond_Zopp; exact Hm | lia].
  - apply bpow_le. lia.
Qed.

(** The floor fact for every finite binary32 pattern. *)
Lemma pf_floor_key b : pf_Sfin b -> Zfloor (pf_rnd (pf_Sval b + /2)) = Zfloor (pf_Sval b + /2).
Proof.
  unfold pf_Sfin, pf_Sval.
  destruct (fp_decode fmt_single b) as [s|s| |s m e] eqn:Eb; intros F; cbn [is_finite_SF] in F;
    try discriminate F.
  - cbn [SF2R]. rewrite Rplus_0_l, pf_rnd_generic; [reflexivity|].
    change (/2)%R with (bpow radix2 (-1)). apply pf_fmt_bpow. lia.
  - cbn [SF2R]. rewrite pf_F2R_IZR_bpow. destruct (pf_S_fin_bounds b s m e Eb) as [Hm He].
    apply pf_floor_core; [rewrite pf_abs_cond_Zopp; exact Hm | lia].
Qed.

(** * fcvt.d.s, then fadd.d of 0.5 *)

Ltac pf_crange := split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity.

Lemma pf_cvt_fin b : pf_Sfin b ->
  pf_Dfin (fst (fp_convert fmt_single fmt_double RNE b)) /\
  pf_Dval (fst (fp_convert fmt_single fmt_double RNE b)) = pf_Sval b /\
  0 <= fst (fp_convert fmt_single fmt_double RNE b) < 2^64.
Proof.
  intros F. unfold fp_convert. rewrite (pf_S_fin_not_nan b F). unfold pf_Sval. revert F. unfold pf_Sfin.
  destruct (fp_decode fmt_single b) as [s|s| |s m e] eqn:Eb; intros F; cbn [is_finite_SF] in F;
    try discriminate F.
  - cbn [fst]. exact (pf_Dfin_encode_valid (S754_zero s) eq_refl eq_refl).
  - unfold enc. cbn [fst]. rewrite pf_round_exact_binary_round. cbn [flocq_mode].
    destruct (pf_S_fin_bounds b s m e Eb) as [Hm He].
    pose proof (binary_round_correct 53 1024 pf_prec53 pf_max53 mode_NE s m e) as BR. cbv zeta in BR.
    destruct BR as [V BR].
    assert (FM : pf_fmt (F2R (Float radix2 (cond_Zopp s (Z.pos m)) e))).
    { rewrite pf_F2R_IZR_bpow. apply pf_fmt_IZR_bpow; [rewrite pf_abs_cond_Zopp; lia | lia]. }
    rewrite pf_fexp_D in BR. cbn [round_mode] in BR. rewrite (round_generic _ _ _ _ FM) in BR.
    rewrite Rlt_bool_true in BR.
    + destruct BR as (R1 & R2 & R3). destruct (pf_Dfin_encode_valid _ V R2) as (X & Y & W).
      split; [exact X|]. split; [rewrite Y, R1; reflexivity | exact W].
    + rewrite pf_F2R_IZR_bpow. eapply Rlt_le_trans.
      * apply (pf_abs_val_lt _ e 24); [rewrite pf_abs_cond_Zopp; exact Hm | lia].
      * apply bpow_le. lia.
Qed.

Lemma pf_cvt_range b : 0 <= fst (fp_convert fmt_single fmt_double RNE b) < 2^64.
Proof.
  destruct (is_finite_SF (fp_decode fmt_single b)) eqn:F.
  { destruct (pf_cvt_fin b F) as (_ & _ & R). exact R. }
  unfold fp_convert. revert F.
  destruct (fp_decode fmt_single b) as [s|s| |s m e] eqn:Eb; intros F; cbn [is_finite_SF] in F;
    try discriminate F.
  - rewrite (pf_S_inf_not_nan b s Eb). destruct s; pf_crange.
  - rewrite (pf_S_nan_is_nan b Eb). pf_crange.
Qed.

Lemma pf_half_fin : pf_Dfin 0x3FE0000000000000.
Proof. unfold pf_Dfin. vm_compute. reflexivity. Qed.

Lemma pf_half_val : pf_Dval 0x3FE0000000000000 = (/2)%R.
Proof.
  unfold pf_Dval.
  replace (fp_decode fmt_double 0x3FE0000000000000) with (S754_finite false 4503599627370496 (-53))
    by (vm_compute; reflexivity).
  cbn [SF2R cond_Zopp]. rewrite pf_F2R_IZR_bpow.
  change (IZR (Z.pos 4503599627370496)) with (bpow radix2 52). rewrite <- bpow_plus. reflexivity.
Qed.

Lemma pf_ovf_half b : (Rabs (pf_rnd (pf_Sval b + /2)) < bpow radix2 1024)%R.
Proof.
  apply Rle_lt_trans with (bpow radix2 129).
  - apply pf_rnd_abs_le; [apply pf_fmt_bpow; lia|].
    eapply Rle_trans; [apply Rabs_triang|]. rewrite (Rabs_pos_eq (/2)) by lra.
    pose proof (pf_Sval_bound b) as SB.
    assert (B1 : (1 <= bpow radix2 128)%R) by (change 1%R with (bpow radix2 0); apply bpow_le; lia).
    assert (B2 : bpow radix2 129 = (2 * bpow radix2 128)%R).
    { change 129 with (1 + 128). rewrite bpow_plus. reflexivity. }
    lra.
  - apply bpow_lt. lia.
Qed.

(** The integer the walk sees in the d register (before boxing into a word). *)
Definition pf_dz (b : Z) : Z :=
  fst (fp_add fmt_double RNE (fst (fp_convert fmt_single fmt_double RNE b)) 0x3FE0000000000000).

Lemma pf_dz_fin b : pf_Sfin b ->
  pf_Dfin (pf_dz b) /\ pf_Dval (pf_dz b) = pf_rnd (pf_Sval b + /2) /\ 0 <= pf_dz b < 2^64.
Proof.
  intros F. destruct (pf_cvt_fin b F) as (Fc & Vc & Rc).
  unfold pf_dz.
  destruct (pf_dadd_correct _ 0x3FE0000000000000 Fc pf_half_fin) as (Fd & Vd & Rd).
  { rewrite Vc, pf_half_val. apply pf_ovf_half. }
  rewrite Vc, pf_half_val in Vd.
  split; [exact Fd|]. split; [exact Vd | exact Rd].
Qed.

(** * Ratios: f32_ratio and f64_ratio read a decoded datum the same way *)

Definition pf_ratio (x : spec_float) : option (Z * Z) :=
  match x with
  | S754_zero _ => Some (0, 1)
  | S754_finite s m e =>
      let v := if s then - Zpos m else Zpos m in
      Some (if 0 <=? e then (v * 2^e, 1) else (v, 2^(-e)))
  | _ => None
  end.

Lemma pf_f64_ratio x : f64_ratio x = pf_ratio (fp_decode fmt_double x).
Proof. reflexivity. Qed.
Lemma pf_f32_ratio x : f32_ratio x = pf_ratio (fp_decode fmt_single x).
Proof. reflexivity. Qed.

Lemma pf_ratio_val x N D : pf_ratio x = Some (N, D) ->
  0 < D /\ is_finite_SF x = true /\ SF2R radix2 x = (IZR N / IZR D)%R.
Proof.
  destruct x as [s|s| |s m e]; cbn [pf_ratio]; intros H; try discriminate H.
  - injection H as <- <-. split; [lia|]. split; [reflexivity|]. cbn [SF2R].
    unfold Rdiv. rewrite Rinv_1, Rmult_1_r. reflexivity.
  - cbn [SF2R]. rewrite pf_F2R_IZR_bpow.
    replace (cond_Zopp s (Z.pos m)) with (if s then - Z.pos m else Z.pos m) by (destruct s; reflexivity).
    revert H. destruct (Z.leb_spec 0 e) as [He|He]; intros H; cbv iota in H; injection H as <- <-.
    + split; [lia|]. split; [reflexivity|]. rewrite pf_IZR_mul_pow by exact He.
      unfold Rdiv. rewrite Rinv_1, Rmult_1_r. reflexivity.
    + split; [apply Z.pow_pos_nonneg; lia|]. split; [reflexivity|].
      unfold Rdiv. rewrite pf_IZR_pow by lia. rewrite <- bpow_opp, Z.opp_involutive. reflexivity.
Qed.

Lemma pf_ratio_some x : is_finite_SF x = true -> exists N D, pf_ratio x = Some (N, D).
Proof.
  destruct x as [s|s| |s m e]; cbn [pf_ratio is_finite_SF]; intros H; try discriminate H.
  - exists 0, 1. reflexivity.
  - destruct (0 <=? e); eexists; eexists; reflexivity.
Qed.

Lemma pf_near_fin b : pf_Sfin b -> near_f32 b = Some (Zfloor (pf_Sval b + /2)).
Proof.
  intros F. unfold pf_Sfin in F. destruct (near_f32_ratio b) as [E _]. rewrite E, pf_f32_ratio.
  destruct (pf_ratio_some _ F) as (N & D & ER). rewrite ER. cbn [option_map fst snd]. f_equal.
  destruct (pf_ratio_val _ _ _ ER) as (HD & _ & HV).
  assert (ND : IZR D <> 0%R) by (apply not_0_IZR; lia).
  unfold pf_Sval. rewrite HV.
  rewrite <- (Zfloor_div (2 * N + D) (2 * D)) by lia.
  f_equal. rewrite plus_IZR, !mult_IZR. field; repeat split; assumption.
Qed.

Lemma pf_near_nonfin b : is_finite_SF (fp_decode fmt_single b) = false -> near_f32 b = None.
Proof.
  destruct (near_f32_ratio b) as [E _]. rewrite E, pf_f32_ratio.
  destruct (fp_decode fmt_single b); intros F; cbn in F |- *; first [reflexivity | discriminate F].
Qed.

(** The three shapes of d: finite with value RNE64(f + 1/2), the canonical NaN, or an infinity. *)
Lemma pf_dz_cases b :
  (pf_Sfin b /\ pf_Dfin (pf_dz b) /\ pf_Dval (pf_dz b) = pf_rnd (pf_Sval b + /2) /\ 0 <= pf_dz b < 2^64)
  \/ (pf_dz b = fp_canonical_nan fmt_double /\ near_f32 b = None)
  \/ (exists s, pf_dz b = fp_encode fmt_double (S754_infinity s) /\ near_f32 b = None).
Proof.
  destruct (is_finite_SF (fp_decode fmt_single b)) eqn:F.
  { left. split; [exact F|]. apply pf_dz_fin. exact F. }
  right. rewrite (pf_near_nonfin b F). unfold pf_dz, fp_convert. revert F.
  destruct (fp_decode fmt_single b) as [s|s| |s m e] eqn:Eb; intros F; cbn [is_finite_SF] in F;
    try discriminate F.
  - right. exists s. split; [|reflexivity]. rewrite (pf_S_inf_not_nan b s Eb).
    destruct s; vm_compute; reflexivity.
  - left. split; [|reflexivity]. rewrite (pf_S_nan_is_nan b Eb). vm_compute; reflexivity.
Qed.

Lemma pf_dz_range b : 0 <= pf_dz b < 2^64.
Proof.
  destruct (pf_dz_cases b) as [(_ & _ & _ & R) | [(Ed & _) | (s & Ed & _)]].
  - exact R.
  - rewrite Ed. pf_crange.
  - rewrite Ed. destruct s; pf_crange.
Qed.

(** * The words *)

Lemma pf_bv64 z : 0 <= z < 2^64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros H. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2^64). exact H. Qed.
Lemma pf_bv32 z : 0 <= z < 2^32 -> bv_unsigned (Z_to_bv 32 z) = z.
Proof. intros H. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 32) with (2^32). exact H. Qed.

Lemma pf_unbox_nan_box : forall v : bv 32, unbox_s (nan_box v) = v.
Proof.
  intros v. unfold unbox_s, nan_box, low32.
  pose proof (bv_unsigned_in_range 32 v) as Hv. unfold bv_modulus in Hv.
  assert (E : bv_unsigned (bv_concat 64 (Z_to_bv 32 (-1)) v) = (Z.lor (Z.shiftl (2^32 - 1) 32) (bv_unsigned v))%Z).
  { rewrite bv_concat_unsigned by reflexivity. reflexivity. }
  assert (Hhi : bv_unsigned (bv_extract 32 32 (bv_concat 64 (Z_to_bv 32 (-1)) v)) = Z.ones 32).
  { rewrite bv_extract_unsigned, E. apply Z.bits_inj'. intros i Hi.
    change (bv_wrap 32 ?x) with (x mod 2^32)%Z. change (Z.of_N 32) with 32%Z.
    destruct (Z.lt_ge_cases i 32).
    - rewrite testbit_mod_pow2_low, Z.shiftr_spec, Z.lor_spec, Z.shiftl_spec, Z.ones_spec_low by lia.
      replace (i + 32 - 32)%Z with i by lia. change (2^32 - 1)%Z with (Z.ones 32).
      rewrite Z.ones_spec_low by lia. reflexivity.
    - rewrite Z.ones_spec_high by lia. rewrite <- Z.land_ones, Z.land_spec, Z.ones_spec_high by lia.
      apply andb_false_r. }
  rewrite Hhi, Z.eqb_refl.
  apply bv_eq. rewrite bv_extract_unsigned, E, Z.shiftr_0_r. change (bv_wrap 32 ?x) with (x mod 2^32)%Z.
  apply Z.bits_inj'. intros i Hi. destruct (Z.lt_ge_cases i 32).
  - rewrite testbit_mod_pow2_low, Z.lor_spec, Z.shiftl_spec_low by lia. reflexivity.
  - rewrite <- Z.land_ones, Z.land_spec, Z.ones_spec_high, andb_false_r by lia.
    symmetry. destruct (Z.eq_dec (bv_unsigned v) 0) as [->|]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 32%Z; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Lemma pf_rfn_d_unsigned b : 0 <= b < 2^32 -> bv_unsigned (rfn_d b) = pf_dz b.
Proof.
  intros Hb. unfold rfn_d, fadd_d, fcvt_d_s. rewrite pf_unbox_nan_box, (pf_bv32 b Hb).
  rewrite (pf_bv64 _ (pf_cvt_range b)).
  rewrite (pf_bv64 0x3FE0000000000000) by pf_crange.
  apply pf_bv64. apply pf_dz_range.
Qed.

Lemma pf_is_int_val (x : word) k : f64_is_int x k = true ->
  pf_Dfin (bv_unsigned x) /\ pf_Dval (bv_unsigned x) = IZR k.
Proof.
  unfold f64_is_int. rewrite pf_f64_ratio.
  destruct (pf_ratio (fp_decode fmt_double (bv_unsigned x))) as [[N D]|] eqn:E; [|intros H; discriminate H].
  intros H. apply Z.eqb_eq in H.
  destruct (pf_ratio_val _ _ _ E) as (HD & F & V).
  assert (ND : IZR D <> 0%R) by (apply not_0_IZR; lia).
  split; [exact F|]. unfold pf_Dval. rewrite V, H, mult_IZR. field; repeat split; assumption.
Qed.

(** fcvt.l.d with round toward zero: no saturation below 2^63 in magnitude. *)
Definition pf_trunc_pat (a : Z) : Z :=
  match fp_decode fmt_double a with
  | S754_finite s m e => cond_Zopp s (if 0 <=? e then Z.pos m * 2 ^ e else Z.pos m / 2 ^ (- e))
  | _ => 0
  end.

Lemma pf_trunc_mag (m : positive) (e : Z) :
  (if 0 <=? e then Z.pos m * 2 ^ e else Z.pos m / 2 ^ (- e)) = Ztrunc (F2R (Float radix2 (Z.pos m) e)).
Proof.
  rewrite pf_F2R_IZR_bpow. destruct (Z.leb_spec 0 e) as [He|He].
  - rewrite <- (pf_IZR_mul_pow _ _ He). rewrite Ztrunc_IZR. reflexivity.
  - assert (P : 0 < 2 ^ (- e)) by (apply Z.pow_pos_nonneg; lia).
    assert (B : bpow radix2 e = (/ IZR (2 ^ (- e)))%R).
    { rewrite pf_IZR_pow by lia. rewrite <- bpow_opp, Z.opp_involutive. reflexivity. }
    rewrite B. rewrite Ztrunc_floor.
    + rewrite <- (Zfloor_div (Z.pos m) (2 ^ (- e))) by lia. reflexivity.
    + apply Rmult_le_pos; [apply IZR_le; lia|]. apply Rlt_le, Rinv_0_lt_compat, IZR_lt. exact P.
Qed.

Lemma pf_trunc_val a : pf_Dfin a -> pf_trunc_pat a = Ztrunc (pf_Dval a).
Proof.
  unfold pf_Dfin, pf_trunc_pat, pf_Dval.
  destruct (fp_decode fmt_double a) as [s|s| |s m e]; intros F; cbn [is_finite_SF] in F; try discriminate F.
  - cbn [SF2R]. symmetry. apply (Ztrunc_IZR 0).
  - cbn [SF2R]. rewrite pf_trunc_mag. destruct s; cbn [cond_Zopp]; [|reflexivity].
    rewrite <- Ztrunc_opp, <- F2R_Zopp. reflexivity.
Qed.

Lemma pf_to_int_RTZ a : pf_Dfin a -> -2^63 <= pf_trunc_pat a < 2^63 ->
  fst (fp_to_int fmt_double RTZ true 64 a) = int_wrap 64 (pf_trunc_pat a).
Proof.
  intros Ha. unfold fp_to_int. rewrite (pf_Dfin_not_nan a Ha). revert Ha.
  unfold pf_Dfin, pf_trunc_pat.
  destruct (fp_decode fmt_double a) as [s|s| |s m e]; intros Ha; cbn [is_finite_SF] in Ha; try discriminate Ha.
  - intros _. reflexivity.
  - change (int_lo true 64) with (-2^63). change (int_hi true 64) with (2^63 - 1).
    cbv beta iota zeta. unfold BinarySingleNaN.choice_mode, flocq_mode. cbv beta iota zeta.
    destruct (Z.leb_spec 0 e) as [He|He]; cbv beta iota zeta; intros R.
    + rewrite Z.shiftl_mul_pow2 by lia.
      replace (if s then - (Z.pos m * 2 ^ e) else Z.pos m * 2 ^ e) with (cond_Zopp s (Z.pos m * 2 ^ e))
        by (destruct s; reflexivity).
      destruct (cond_Zopp s (Z.pos m * 2 ^ e) <? -2^63) eqn:C1; [apply Z.ltb_lt in C1; lia|].
      destruct (2^63 - 1 <? cond_Zopp s (Z.pos m * 2 ^ e)) eqn:C2; [apply Z.ltb_lt in C2; lia|].
      reflexivity.
    + rewrite Z.shiftl_1_l.
      destruct (Z.div_eucl (Z.pos m) (2 ^ (- e))) as [q r] eqn:DE. cbv beta iota zeta.
      assert (Hq : Z.pos m / 2 ^ (- e) = q) by (unfold Z.div; rewrite DE; reflexivity).
      rewrite Hq in R |- *.
      replace (if s then - q else q) with (cond_Zopp s q) by (destruct s; reflexivity).
      destruct (cond_Zopp s q <? -2^63) eqn:C1; [apply Z.ltb_lt in C1; lia|].
      destruct (2^63 - 1 <? cond_Zopp s q) eqn:C2; [apply Z.ltb_lt in C2; lia|].
      reflexivity.
Qed.

Lemma pf_to_int_trunc a : pf_Dfin a -> -2^63 <= Ztrunc (pf_Dval a) < 2^63 ->
  fst (fp_to_int fmt_double RTZ true 64 a) = int_wrap 64 (Ztrunc (pf_Dval a)).
Proof.
  intros F R. rewrite <- (pf_trunc_val a F). apply pf_to_int_RTZ; [exact F|].
  rewrite (pf_trunc_val a F). exact R.
Qed.

Lemma pf_signed_wrap T : -2^63 <= T < 2^63 -> bv_signed (Z_to_bv 64 (int_wrap 64 T)) = T.
Proof.
  intros H. rewrite Z_to_bv_signed. unfold int_wrap. rewrite Z.land_ones by lia.
  change (T mod 2^64) with (bv_wrap 64 T). rewrite bv_swrap_wrap.
  apply bv_swrap_small. change (bv_half_modulus 64) with (2^63). lia.
Qed.

(** fcvt.d.l with round to nearest-even: the signed read of the source, exact up to 2^53. *)
Definition pf_sread (v : Z) : Z :=
  if Z.testbit (int_wrap 64 v) 63 then int_wrap 64 v - 2^64 else int_wrap 64 v.

Lemma pf_of_int_eq v :
  fp_of_int fmt_double RNE true 64 v = enc fmt_double (round_scaled fmt_double RNE false (pf_sread v, 0)).
Proof. reflexivity. Qed.

Lemma pf_sread_wrap T : -2^63 <= T < 2^63 -> pf_sread (bv_unsigned (Z_to_bv 64 (int_wrap 64 T))) = T.
Proof.
  intros H. unfold pf_sread.
  assert (Hu : int_wrap 64 (bv_unsigned (Z_to_bv 64 (int_wrap 64 T))) = T mod 2^64).
  { rewrite Z_to_bv_unsigned. unfold int_wrap, bv_wrap, bv_modulus. change (Z.of_N 64) with 64.
    rewrite !Z.land_ones by lia. rewrite !Z.mod_mod by lia. reflexivity. }
  rewrite Hu.
  pose proof (Z.mod_pos_bound T (2^64) ltac:(lia)) as MB. pose proof (Z.div_mod T (2^64) ltac:(lia)) as DM.
  destruct (Z_lt_le_dec T 0) as [Neg|Pos].
  - assert (M : T mod 2^64 = T + 2^64) by lia.
    assert (TB : Z.testbit (T + 2^64) 63 = true).
    { apply Z.testbit_true; [lia|].
      assert (Q : (T + 2^64) / 2^63 = 1) by (symmetry; apply (Z.div_unique _ _ _ (T + 2^64 - 2^63)); lia).
      rewrite Q. reflexivity. }
    rewrite M, TB. cbv iota. lia.
  - assert (M : T mod 2^64 = T) by lia.
    assert (TB : Z.testbit T 63 = false).
    { apply Z.testbit_false; [lia|].
      assert (Q : T / 2^63 = 0) by (symmetry; apply (Z.div_unique _ _ _ T); lia).
      rewrite Q. reflexivity. }
    rewrite M, TB. cbv iota. reflexivity.
Qed.

Lemma pf_fmt_IZR_le n : Z.abs n <= 2^53 -> pf_fmt (IZR n).
Proof.
  intros H. destruct (Z_lt_le_dec (Z.abs n) (2^53)) as [L|L].
  - apply pf_fmt_IZR. exact L.
  - assert (E : n = 2^53 \/ n = - 2^53) by lia. destruct E as [E|E]; subst n.
    + rewrite pf_IZR_pow by lia. apply pf_fmt_bpow. lia.
    + rewrite opp_IZR, pf_IZR_pow by lia. apply pf_fmt_opp. apply pf_fmt_bpow. lia.
Qed.

Lemma pf_of_int_val v T : pf_sread v = T -> -2^53 <= T <= 2^53 ->
  pf_Dfin (fst (fp_of_int fmt_double RNE true 64 v)) /\
  pf_Dval (fst (fp_of_int fmt_double RNE true 64 v)) = IZR T /\
  0 <= fst (fp_of_int fmt_double RNE true 64 v) < 2^64.
Proof.
  intros Hs HT. rewrite pf_of_int_eq, Hs. unfold enc. cbn [fst].
  assert (Z0 : pf_ZZval (T, 0) = IZR T).
  { unfold pf_ZZval. cbn [fst snd]. rewrite pf_F2R_IZR_bpow. cbn [bpow]. ring. }
  assert (FT : pf_fmt (IZR T)) by (apply pf_fmt_IZR_le; lia).
  destruct (pf_round_scaled_correct false (T, 0)) as (A & B & C).
  { rewrite Z0, pf_rnd_generic by exact FT. rewrite Rabs_Zabs.
    apply Rle_lt_trans with (bpow radix2 53).
    - rewrite <- pf_IZR_pow by lia. apply IZR_le. lia.
    - apply bpow_lt. lia. }
  rewrite Z0, pf_rnd_generic in B by exact FT.
  split; [exact A|]. split; [exact B | exact C].
Qed.

(** t = fcvt.l.d RTZ d and t - [d < fcvt.d.l t], for a finite d with lo <= d < hi + 1. *)
Lemma pf_hw_floor (x : word) lo hi : -2^53 <= lo -> hi < 2^53 -> pf_Dfin (bv_unsigned x) ->
  (IZR lo <= pf_Dval (bv_unsigned x) < IZR (hi + 1))%R ->
  bv_signed (fcvt_l_d RTZ x) = Ztrunc (pf_Dval (bv_unsigned x)) /\
  bv_signed (fcvt_l_d RTZ x) - (if flt_d x (fcvt_d_l RNE (fcvt_l_d RTZ x)) then 1 else 0) =
    Zfloor (pf_Dval (bv_unsigned x)).
Proof.
  intros Hlo Hhi F [Y1 Y2].
  pose proof (Ztrunc_le _ _ Y1) as T1. rewrite Ztrunc_IZR in T1.
  pose proof (Ztrunc_le _ _ (Rlt_le _ _ Y2)) as T2. rewrite Ztrunc_IZR in T2.
  assert (Ht : fcvt_l_d RTZ x = Z_to_bv 64 (int_wrap 64 (Ztrunc (pf_Dval (bv_unsigned x))))).
  { unfold fcvt_l_d. rewrite pf_to_int_trunc; [reflexivity | exact F | lia]. }
  rewrite Ht, pf_signed_wrap by lia. split; [reflexivity|].
  assert (TB : -2^53 <= Ztrunc (pf_Dval (bv_unsigned x)) <= 2^53) by lia.
  assert (SR : pf_sread (bv_unsigned (Z_to_bv 64 (int_wrap 64 (Ztrunc (pf_Dval (bv_unsigned x)))))) =
               Ztrunc (pf_Dval (bv_unsigned x))) by (apply pf_sread_wrap; lia).
  destruct (pf_of_int_val _ _ SR TB) as (Fw & Vw & Rw).
  unfold flt_d, fcvt_d_l. rewrite (pf_bv64 _ Rw).
  rewrite pf_dlt_correct by assumption. rewrite Vw. apply pf_trunc_floor.
Qed.

Lemma pf_rfn_hw b lo hi : 0 <= b < 2^32 -> -2^53 <= lo -> hi < 2^53 -> pf_Dfin (pf_dz b) ->
  (IZR lo <= pf_Dval (pf_dz b) < IZR (hi + 1))%R ->
  bv_signed (rfn_t b) = Ztrunc (pf_Dval (pf_dz b)) /\ rfn_r b = Zfloor (pf_Dval (pf_dz b)).
Proof.
  intros Hb Hlo Hhi F Y. unfold rfn_r, rfn_t.
  rewrite <- (pf_rfn_d_unsigned b Hb) in F, Y |- *.
  exact (pf_hw_floor (rfn_d b) lo hi Hlo Hhi F Y).
Qed.

(** fle.d / flt.d against the two constants. *)
Lemma pf_decode_canon : fp_decode fmt_double (fp_canonical_nan fmt_double) = S754_nan.
Proof. vm_compute. reflexivity. Qed.

Lemma pf_decode_inf s : fp_decode fmt_double (fp_encode fmt_double (S754_infinity s)) = S754_infinity s.
Proof. destruct s; vm_compute; reflexivity. Qed.

Lemma pf_rfn_in_fin b lo hi lod hid : 0 <= b < 2^32 -> f64_is_int lod lo = true ->
  f64_is_int hid (hi + 1) = true -> pf_Dfin (pf_dz b) ->
  rfn_in b lod hid = (lo <=? Zfloor (pf_Dval (pf_dz b))) && (Zfloor (pf_Dval (pf_dz b)) <=? hi).
Proof.
  intros Hb Hl Hh Fd.
  destruct (pf_is_int_val lod lo Hl) as [Fl Vl]. destruct (pf_is_int_val hid (hi + 1) Hh) as [Fh Vh].
  unfold rfn_in, fle_d, flt_d. rewrite (pf_rfn_d_unsigned b Hb).
  rewrite pf_dle_correct, pf_dlt_correct by assumption. rewrite Vl, Vh.
  rewrite pf_Rle_floor, pf_Rlt_floor. reflexivity.
Qed.

Lemma pf_rfn_in_nan b lod hid : 0 <= b < 2^32 -> pf_dz b = fp_canonical_nan fmt_double -> rfn_in b lod hid = false.
Proof.
  intros Hb Ed. unfold rfn_in, fle_d, fp_le, fp_compare.
  rewrite (pf_rfn_d_unsigned b Hb), Ed, pf_decode_canon.
  destruct (fp_decode fmt_double (bv_unsigned lod)); reflexivity.
Qed.

Lemma pf_rfn_in_inf b lod hid s : 0 <= b < 2^32 -> pf_Dfin (bv_unsigned lod) -> pf_Dfin (bv_unsigned hid) ->
  pf_dz b = fp_encode fmt_double (S754_infinity s) -> rfn_in b lod hid = false.
Proof.
  intros Hb Fl Fh Ed. unfold rfn_in, fle_d, flt_d, fp_le, fp_lt, fp_compare.
  rewrite (pf_rfn_d_unsigned b Hb), Ed, pf_decode_inf.
  revert Fl Fh. unfold pf_Dfin.
  destruct (fp_decode fmt_double (bv_unsigned lod)); destruct (fp_decode fmt_double (bv_unsigned hid)); destruct s;
    intros Fl Fh; cbn in Fl, Fh |- *; first [reflexivity | discriminate Fl | discriminate Fh].
Qed.

Lemma pf_rfn_in_true b lo hi lod hid : 0 <= b < 2^32 -> f64_is_int lod lo = true ->
  f64_is_int hid (hi + 1) = true -> rfn_in b lod hid = true ->
  pf_Dfin (pf_dz b) /\ (IZR lo <= pf_Dval (pf_dz b) < IZR (hi + 1))%R.
Proof.
  intros Hb Hl Hh Hin.
  destruct (pf_is_int_val lod lo Hl) as [Fl _]. destruct (pf_is_int_val hid (hi + 1) Hh) as [Fh _].
  destruct (pf_dz_cases b) as [(F & Fd & Vd & _) | [(Ed & En) | (s & Ed & En)]].
  - split; [exact Fd|].
    rewrite (pf_rfn_in_fin b lo hi lod hid Hb Hl Hh Fd) in Hin.
    apply andb_prop in Hin. destruct Hin as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    exact (pf_floor_bounds lo hi _ (conj H1 H2)).
  - rewrite (pf_rfn_in_nan b lod hid Hb Ed) in Hin. discriminate Hin.
  - rewrite (pf_rfn_in_inf b lod hid s Hb Fl Fh Ed) in Hin. discriminate Hin.
Qed.

(** * The theorems *)

Theorem rfn_f64_nearest : forall b lo hi, rfn_f64 b lo hi = nearest b lo hi.
Proof.
  intros b lo hi. unfold rfn_f64, nearest. cbv zeta.
  change (fst (fp_add fmt_double RNE (fst (fp_convert fmt_single fmt_double RNE b)) 0x3FE0000000000000))
    with (pf_dz b).
  destruct (pf_dz_cases b) as [(F & Fd & Vd & _) | [(Ed & En) | (s & Ed & En)]].
  - rewrite (pf_near_fin b F). rewrite pf_f64_ratio.
    destruct (pf_ratio_some _ Fd) as (N & D & ER). rewrite ER.
    destruct (pf_ratio_val _ _ _ ER) as (HD & _ & HV).
    assert (Er : N / D = Zfloor (pf_Sval b + /2)).
    { rewrite <- (pf_floor_key b F). rewrite <- Vd. unfold pf_Dval. rewrite HV.
      symmetry. apply Zfloor_div. lia. }
    rewrite (pf_leb_div lo N D HD), (pf_ltb_div N hi D HD), Er. reflexivity.
  - rewrite Ed, En. vm_compute. reflexivity.
  - rewrite Ed, En. destruct s; vm_compute; reflexivity.
Qed.

Theorem rfn_hw_nearest : forall b lo hi lod hid, 0 <= b < 2^32 -> -2^53 <= lo -> hi < 2^53 ->
  f64_is_int lod lo = true -> f64_is_int hid (hi + 1) = true ->
  nearest b lo hi = if rfn_in b lod hid then Some (rfn_r b) else None.
Proof.
  intros b lo hi lod hid Hb Hlo Hhi Hl Hh. unfold nearest.
  destruct (pf_is_int_val lod lo Hl) as [Fl _]. destruct (pf_is_int_val hid (hi + 1) Hh) as [Fh _].
  destruct (pf_dz_cases b) as [(F & Fd & Vd & _) | [(Ed & En) | (s & Ed & En)]].
  - rewrite (pf_near_fin b F). cbv iota.
    rewrite (pf_rfn_in_fin b lo hi lod hid Hb Hl Hh Fd).
    assert (Ef : Zfloor (pf_Dval (pf_dz b)) = Zfloor (pf_Sval b + /2)).
    { rewrite Vd. apply pf_floor_key. exact F. }
    rewrite Ef.
    destruct ((lo <=? Zfloor (pf_Sval b + /2)) && (Zfloor (pf_Sval b + /2) <=? hi)) eqn:Hin; [|reflexivity].
    cbv iota. f_equal.
    apply andb_prop in Hin. destruct Hin as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    rewrite <- Ef in H1, H2.
    destruct (pf_rfn_hw b lo hi Hb Hlo Hhi Fd (pf_floor_bounds lo hi _ (conj H1 H2))) as [_ Hr].
    rewrite Hr, Ef. reflexivity.
  - rewrite En, (pf_rfn_in_nan b lod hid Hb Ed). reflexivity.
  - rewrite En, (pf_rfn_in_inf b lod hid s Hb Fl Fh Ed). reflexivity.
Qed.

Theorem rfn_hw_t_range : forall b lo hi lod hid, 0 <= b < 2^32 -> -2^53 <= lo -> hi < 2^53 ->
  f64_is_int lod lo = true -> f64_is_int hid (hi + 1) = true -> rfn_in b lod hid = true ->
  lo <= bv_signed (rfn_t b) <= hi + 1.
Proof.
  intros b lo hi lod hid Hb Hlo Hhi Hl Hh Hin.
  destruct (pf_rfn_in_true b lo hi lod hid Hb Hl Hh Hin) as (Fd & Y).
  destruct (pf_rfn_hw b lo hi Hb Hlo Hhi Fd Y) as [Ht _]. rewrite Ht.
  destruct Y as [Y1 Y2].
  pose proof (Ztrunc_le _ _ Y1) as T1. rewrite Ztrunc_IZR in T1.
  pose proof (Ztrunc_le _ _ (Rlt_le _ _ Y2)) as T2. rewrite Ztrunc_IZR in T2. lia.
Qed.

Theorem rfn_hw_above : forall b lo hi lod hid, 0 <= b < 2^32 -> -2^53 <= lo -> hi < 2^53 ->
  f64_is_int lod lo = true -> f64_is_int hid (hi + 1) = true -> rfn_in b lod hid = true ->
  forall c k, f64_is_int c k = true -> k < lo -> flt_d c (rfn_d b) = true.
Proof.
  intros b lo hi lod hid Hb Hlo Hhi Hl Hh Hin c k Hc Hk.
  destruct (pf_rfn_in_true b lo hi lod hid Hb Hl Hh Hin) as (Fd & Y1 & Y2).
  destruct (pf_is_int_val c k Hc) as [Fc Vc].
  unfold flt_d. rewrite (pf_rfn_d_unsigned b Hb). rewrite pf_dlt_correct by assumption. rewrite Vc.
  apply Rlt_bool_true. apply Rlt_le_trans with (IZR lo); [apply IZR_lt; exact Hk | exact Y1].
Qed.

Theorem rfn_hw_below : forall b lo hi lod hid, 0 <= b < 2^32 -> -2^53 <= lo -> hi < 2^53 ->
  f64_is_int lod lo = true -> f64_is_int hid (hi + 1) = true -> rfn_in b lod hid = true ->
  forall c k, f64_is_int c k = true -> hi + 1 <= k -> flt_d (rfn_d b) c = true.
Proof.
  intros b lo hi lod hid Hb Hlo Hhi Hl Hh Hin c k Hc Hk.
  destruct (pf_rfn_in_true b lo hi lod hid Hb Hl Hh Hin) as (Fd & Y1 & Y2).
  destruct (pf_is_int_val c k Hc) as [Fc Vc].
  unfold flt_d. rewrite (pf_rfn_d_unsigned b Hb). rewrite pf_dlt_correct by assumption. rewrite Vc.
  apply Rlt_bool_true. apply Rlt_le_trans with (IZR (hi + 1)); [exact Y2 | apply IZR_le; exact Hk].
Qed.

(** The bit patterns of the double constants fuzz_role's reader compares against (-2^31, 2^31, -2^63 - 2^11, 2^63),
    kept from fuzz_role's text: statements about bit patterns only, no address. In fuzz_headamp the UBSan parse reads
    -2^63 - 2^11 at .rodata 0x10508 and 2^63 at 0x104c0; the plain build holds neither. *)
Lemma role_consts :
  f64_is_int (Z_to_bv 64 0xc1e0000000000000) (-2^31) = true /\ f64_is_int (Z_to_bv 64 0x41e0000000000000) (2^31) = true /\
  f64_is_int (Z_to_bv 64 0xc3e0000000000001) (-2^63 - 2^11) = true /\
  f64_is_int (Z_to_bv 64 0x43e0000000000000) (2^63) = true.
Proof. refine (conj _ (conj _ (conj _ _))); vm_compute; reflexivity. Qed.

