(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool Reals Psatz SpecFloat.
From Flocq Require Import Core.Zaux Core.Raux Core.Defs Core.Digits Core.Float_prop Calc.Bracket Calc.Round Calc.Operations IEEE754.BinarySingleNaN.
From LinuxProcessSemantics.Riscv Require Import Fpu.
Unset Nra Cache. Unset Nia Cache.  (* [comment removed for export] *)
Unset Lia Cache.
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
Local Open Scope Z_scope.
(* [comment removed for export] *)

Notation f32 := fmt_single.

(* [comment removed for export] *)
Lemma prec32 : fp_prec f32 = 24. Proof. reflexivity. Qed.
Lemma emax32 : fp_emax f32 = 128. Proof. reflexivity. Qed.
Lemma mw32 : fp_mw f32 = 23. Proof. reflexivity. Qed.
Lemma ew32 : fp_ew f32 = 8. Proof. reflexivity. Qed.
Lemma emin32 : fp_emin f32 = -149. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition sgn32 (x : Z) : bool := Z.testbit x 31.
Definition expo32 (x : Z) : Z := Z.land (Z.shiftr x 23) (Z.ones 8).
Definition mant32 (x : Z) : Z := Z.land x (Z.ones 23).

Lemma fp_sign_bit32 x : fp_sign_bit f32 x = sgn32 x. Proof. reflexivity. Qed.
Lemma fp_exp_field32 x : fp_exp_field f32 x = expo32 x. Proof. reflexivity. Qed.
Lemma fp_man_field32 x : fp_man_field f32 x = mant32 x. Proof. reflexivity. Qed.

Lemma expo32_eq x : expo32 x = (x / 2^23) mod 2^8.
Proof. unfold expo32. rewrite Z.land_ones by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma mant32_eq x : mant32 x = x mod 2^23.
Proof. unfold mant32. rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma expo32_range x : 0 <= expo32 x < 256.
Proof. rewrite expo32_eq. change 256 with (2^8). apply Z.mod_pos_bound. lia. Qed.
Lemma mant32_range x : 0 <= mant32 x < 2^23.
Proof. rewrite mant32_eq. apply Z.mod_pos_bound. lia. Qed.

(* [comment removed for export] *)
Definition dec (x : Z) : spec_float := fp_decode f32 x.

Lemma dec_unfold x :
  dec x =
  (if expo32 x =? 0 then
     match mant32 x with
     | Zpos p => S754_finite (sgn32 x) p (-149)
     | _ => S754_zero (sgn32 x)
     end
   else if expo32 x =? 255 then
     (if mant32 x =? 0 then S754_infinity (sgn32 x) else S754_nan)
   else
     match 2^23 + mant32 x with
     | Zpos p => S754_finite (sgn32 x) p (expo32 x - 150)
     | _ => S754_nan
     end).
Proof.
  unfold dec, fp_decode. rewrite fp_sign_bit32, fp_exp_field32, fp_man_field32.
  rewrite emin32. change (Z.ones (fp_ew f32)) with 255. change (Z.shiftl 1 (fp_mw f32)) with (2^23).
  destruct (expo32 x =? 0); [reflexivity|].
  destruct (expo32 x =? 255); [reflexivity|].
  destruct (2^23 + mant32 x) eqn:E; try reflexivity.
  replace (expo32 x + -149 - 1) with (expo32 x - 150) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma digits2_pos_le p n : Zpos p < 2^n -> Zpos (digits2_pos p) <= n.
Proof. intro H. rewrite Zpos_digits2_pos. apply Zdigits_le_Zpower. simpl. lia. Qed.
Lemma digits2_pos_ge p n : 0 <= n -> 2^n <= Zpos p -> n < Zpos (digits2_pos p).
Proof.
  intros Hn H. rewrite Zpos_digits2_pos.
  destruct (Z_lt_le_dec n (Zdigits radix2 (Z.pos p))) as [|C]; [assumption|].
  exfalso. pose proof (Zpower_gt_Zdigits radix2 n (Zpos p) C) as G. simpl in G. lia.
Qed.
Lemma digits2_pos_eq24 p : 2^23 <= Zpos p < 2^24 -> Zpos (digits2_pos p) = 24.
Proof. intros [A B]. pose proof (digits2_pos_le p 24 B). pose proof (digits2_pos_ge p 23 ltac:(lia) A). lia. Qed.

(* [comment removed for export] *)
Lemma bounded_subnormal p : Zpos p < 2^23 -> SpecFloat.bounded 24 128 p (-149) = true.
Proof.
  intro H. unfold SpecFloat.bounded, canonical_mantissa. apply andb_true_intro; split.
  - apply Z.eqb_eq. unfold fexp, emin. pose proof (digits2_pos_le p 23 H). lia.
  - apply Z.leb_le. lia.
Qed.
Lemma bounded_normal p e : 2^23 <= Zpos p < 2^24 -> -149 <= e <= 104 -> SpecFloat.bounded 24 128 p e = true.
Proof.
  intros Hp He. unfold SpecFloat.bounded, canonical_mantissa. apply andb_true_intro; split.
  - apply Z.eqb_eq. unfold fexp, emin. rewrite (digits2_pos_eq24 p Hp). lia.
  - apply Z.leb_le. lia.
Qed.

Theorem dec_valid x : valid_binary 24 128 (dec x) = true.
Proof.
  rewrite dec_unfold.
  pose proof (expo32_range x) as HE. pose proof (mant32_range x) as HM.
  destruct (expo32 x =? 0) eqn:E0.
  - destruct (mant32 x) eqn:M; try reflexivity. cbv beta iota delta [valid_binary]. apply bounded_subnormal. lia.
  - destruct (expo32 x =? 255) eqn:E255.
    + destruct (mant32 x =? 0); reflexivity.
    + apply Z.eqb_neq in E0. apply Z.eqb_neq in E255.
      destruct (2^23 + mant32 x) eqn:M. 
      * exfalso. lia.
      * cbv beta iota delta [valid_binary]. apply bounded_normal; lia.
      * exfalso; lia.
Qed.
Definition is_nan32 (x : Z) : bool := fp_is_nan f32 x.
Lemma is_nan32_spec x : fp_is_nan f32 x = (expo32 x =? 255) && negb (mant32 x =? 0).
Proof. reflexivity. Qed.

Lemma dec_nan_iff x : dec x = S754_nan <-> fp_is_nan f32 x = true.
Proof.
  rewrite is_nan32_spec, dec_unfold.
  pose proof (mant32_range x) as HM.
  destruct (expo32 x =? 0) eqn:E0.
  - apply Z.eqb_eq in E0. rewrite E0. cbn [andb negb Z.eqb Pos.eqb]. destruct (mant32 x); split; intro; congruence.
  - destruct (expo32 x =? 255) eqn:E255.
    + cbn [andb]. destruct (mant32 x =? 0); cbn [negb]; split; intro; congruence.
    + cbn [andb]. destruct (2^23 + mant32 x) eqn:M; try lia. split; intro; congruence.
Qed.
Lemma is_nan_SF_dec x : is_nan_SF (dec x) = fp_is_nan f32 x.
Proof.
  destruct (fp_is_nan f32 x) eqn:N.
  - apply dec_nan_iff in N. now rewrite N.
  - destruct (dec x) eqn:D; try reflexivity. exfalso. apply dec_nan_iff in D. congruence.
Qed.
Definition enc (z : spec_float) : Z := fp_encode f32 z.

Lemma enc_unfold z :
  enc z = match z with
          | S754_nan => 2143289344
          | S754_zero s => (if s then 2^31 else 0)
          | S754_infinity s => (if s then 2^31 else 0) + 2139095040
          | S754_finite s m e =>
              if Zpos (Pos.size m) <? 24 then (if s then 2^31 else 0) + Zpos m
              else (if s then 2^31 else 0) + Z.shiftl (e + 150) 23 + (Zpos m - 2^23)
          end.
Proof.
  unfold enc, fp_encode. rewrite prec32, mw32, ew32, emin32.
 
  destruct z as [s|s| |s m e].
  - destruct s; reflexivity.
  - destruct s; reflexivity.
  - reflexivity.
  - replace (e - -149 + 1) with (e + 150) by lia. destruct s; reflexivity.
Qed.
Lemma fields_compose (s : bool) (E M : Z) :
  0 <= E < 256 -> 0 <= M < 2^23 ->
  let x := (if s then 2^31 else 0) + E * 2^23 + M in
  expo32 x = E /\ mant32 x = M /\ sgn32 x = s /\ 0 <= x < 2^32.
Proof.
  intros HE HM. cbv zeta.
  set (S := if s then 2^31 else 0).
  assert (HS: S = (if s then 1 else 0) * 2^8 * 2^23) by (destruct s; reflexivity).
 
  split; [|split; [|split]].
  - rewrite expo32_eq. rewrite HS.
    replace ((if s then 1 else 0) * 2^8 * 2^23 + E * 2^23 + M) with (M + ((if s then 1 else 0) * 2^8 + E) * 2^23) by ring.
   
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l.
    rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite mant32_eq, HS.
    replace ((if s then 1 else 0) * 2^8 * 2^23 + E * 2^23 + M) with (M + ((if s then 1 else 0) * 2^8 + E) * 2^23) by ring.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - unfold sgn32. rewrite Z.testbit_odd, Z.shiftr_div_pow2 by lia. rewrite HS.
    replace ((if s then 1 else 0) * 2^8 * 2^23 + E * 2^23 + M) with ((E * 2^23 + M) + (if s then 1 else 0) * 2^31) by ring.
    rewrite Z.div_add by lia. rewrite Z.div_small by (destruct s; lia). destruct s; reflexivity.
  - destruct s; subst S; lia.
Qed.
Lemma Zpos_size_digits p : Zpos (Pos.size p) = Zpos (digits2_pos p).
Proof.
  induction p; cbn [Pos.size digits2_pos]; try reflexivity; rewrite !Pos2Z.inj_succ, IHp; reflexivity.
Qed.
Theorem dec_enc_finite s m e :
  SpecFloat.bounded 24 128 m e = true ->
  dec (enc (S754_finite s m e)) = S754_finite s m e /\ 0 <= enc (S754_finite s m e) < 2^32.
Proof.
  intros B. unfold SpecFloat.bounded, canonical_mantissa in B.
  apply andb_prop in B. destruct B as [B1 B2]. apply Z.eqb_eq in B1. apply Z.leb_le in B2.
  unfold fexp, emin in B1.
  rewrite enc_unfold. rewrite Zpos_size_digits.
 
  destruct (Z.pos (digits2_pos m) <? 24) eqn:D.
  - apply Z.ltb_lt in D.
    assert (He : e = -149) by lia.
    assert (Hm : Zpos m < 2^23).
    { pose proof (Zpower_gt_Zdigits radix2 23 (Zpos m)) as G. rewrite <- Zpos_digits2_pos in G.
      change (radix2 ^ 23)%Z with (2^23)%Z in G. lia. }
   
    pose proof (fields_compose s 0 (Zpos m) ltac:(lia) ltac:(lia)) as FC. cbv zeta in FC.
    replace ((if s then 2 ^ 31 else 0) + 0 * 2 ^ 23 + Z.pos m) with ((if s then 2 ^ 31 else 0) + Z.pos m) in FC by lia.
    destruct FC as (FE & FM & FS & FR).
    split; [|exact FR].
   
    rewrite dec_unfold, FE, FM, FS, He. reflexivity.
  - apply Z.ltb_ge in D.
    assert (Hd : Zpos (digits2_pos m) = 24) by lia.
    assert (Hm : 2^23 <= Zpos m < 2^24).
    { split.
      - pose proof (Zpower_le_Zdigits radix2 23 (Zpos m)) as G. rewrite <- Zpos_digits2_pos in G.
        change (radix2 ^ 23)%Z with (2^23)%Z in G. lia.
      - pose proof (Zpower_gt_Zdigits radix2 24 (Zpos m)) as G. rewrite <- Zpos_digits2_pos in G.
        change (radix2 ^ 24)%Z with (2^24)%Z in G. lia. }
    assert (He : -149 <= e <= 104) by lia.
   
    rewrite Z.shiftl_mul_pow2 by lia.
    pose proof (fields_compose s (e + 150) (Zpos m - 2^23) ltac:(lia) ltac:(lia)) as FC. cbv zeta in FC.
    destruct FC as (FE & FM & FS & FR).
    split; [|exact FR].
   
    rewrite dec_unfold, FE, FM, FS.
    replace (e + 150 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (e + 150 =? 255) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (2 ^ 23 + (Z.pos m - 2 ^ 23)) with (Z.pos m) by lia.
    replace (e + 150 - 150) with e by lia. reflexivity.
Qed.
Theorem dec_enc z : valid_binary 24 128 z = true -> dec (enc z) = z.
Proof.
  destruct z as [s|s| |s m e]; intros V.
  - destruct s; reflexivity.
  - destruct s; reflexivity.
  - reflexivity.
  - apply (proj1 (dec_enc_finite s m e V)).
Qed.

Theorem enc_range z : valid_binary 24 128 z = true -> 0 <= enc z < 2^32.
Proof.
  destruct z as [s|s| |s m e]; intros V.
  - rewrite enc_unfold; destruct s; lia.
  - rewrite enc_unfold; destruct s; lia.
  - rewrite enc_unfold; lia.
  - apply (proj2 (dec_enc_finite s m e V)).
Qed.

Lemma pattern_decomp x : 0 <= x < 2^32 ->
  x = (if sgn32 x then 2^31 else 0) + expo32 x * 2^23 + mant32 x.
Proof.
  intros Hx. rewrite expo32_eq, mant32_eq. unfold sgn32.
  rewrite Z.testbit_odd, Z.shiftr_div_pow2 by lia.
  pose proof (Z.div_mod x (2^23) ltac:(lia)) as D1.
  pose proof (Z.div_mod (x / 2^23) (2^8) ltac:(lia)) as D2.
  assert (H31 : x / 2^31 = (x / 2^23) / 2^8).
  { rewrite Z.div_div by lia. reflexivity. }
  assert (R : 0 <= x / 2^31 < 2) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  rewrite <- H31 in D2.
 
  destruct (Z.odd (x / 2^31)) eqn:O.
  - assert (x / 2^31 = 1). { destruct (Z.eq_dec (x / 2^31) 0) as [Z0|]; [rewrite Z0 in O; discriminate|lia]. } lia.
  - assert (x / 2^31 = 0). { destruct (Z.eq_dec (x / 2^31) 1) as [Z1|]; [rewrite Z1 in O; discriminate|lia]. } lia.
Qed.

(* [comment removed for export] *)
Notation fexp32 := (SpecFloat.fexp 24 128).

Lemma fexp32_eq D : fexp32 D = Z.max (D - 24) (-149).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma Pos_iter_xO (m : positive) (d : positive) :
  Zpos (Pos.iter xO m d) = Zpos m * 2 ^ (Zpos d).
Proof.
  revert m. induction d using Pos.peano_ind; intros m.
  - simpl. lia.
  - rewrite Pos.iter_succ. rewrite Pos2Z.inj_succ. rewrite Z.pow_succ_r by lia.
    change (Z.pos (Pos.iter xO m d)~0) with (2 * Z.pos (Pos.iter xO m d)). rewrite IHd. lia.
Qed.

Lemma shl_align_spec (mx : positive) (ex e : Z) :
  let '(mz, ez) := shl_align mx ex e in
  (if e <? ex then ez = e /\ Zpos mz = Zpos mx * 2 ^ (ex - e) else ez = ex /\ mz = mx).
Proof.
  unfold shl_align.
  destruct (e - ex) as [|d|d] eqn:E.
  - replace (e <? ex) with false by (symmetry; apply Z.ltb_ge; lia). auto.
  - replace (e <? ex) with false by (symmetry; apply Z.ltb_ge; lia). auto.
  - replace (e <? ex) with true by (symmetry; apply Z.ltb_lt; lia).
    split; [reflexivity|]. rewrite Pos_iter_xO. replace (ex - e) with (Zpos d) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma shr_nonpos mrs e n : n <= 0 -> shr mrs e n = (mrs, e).
Proof. intros H. destruct n; try reflexivity. lia. Qed.

Lemma shr_snd mrs e n : 0 <= n -> snd (shr mrs e n) = e + n.
Proof. intros H. destruct n; simpl; lia. Qed.

(* [comment removed for export] *)
Lemma choice_mode_exact md sx q : choice_mode md sx q loc_Exact = q.
Proof. destruct md; reflexivity. Qed.

(* [comment removed for export] *)
Lemma Zdigits_pos_bounds (M : Z) : 0 < M ->
  2 ^ (Zdigits radix2 M - 1) <= M < 2 ^ (Zdigits radix2 M).
Proof.
  intros H. pose proof (Zdigits_correct radix2 M) as [A B]. rewrite Z.abs_eq in A, B by lia.
  simpl radix_val in A, B. lia.
Qed.

Lemma Zdigits_pos_le24 (q : Z) : 0 <= q < 2^24 -> Zdigits radix2 q <= 24.
Proof. intros H. apply Zdigits_le_Zpower. simpl radix_val. lia. Qed.

Lemma Zdigits_eq_24 (q : Z) : 2^23 <= q < 2^24 -> Zdigits radix2 q = 24.
Proof.
  intros H. pose proof (Zdigits_pos_le24 q ltac:(lia)).
  destruct (Z_lt_le_dec (Zdigits radix2 q) 24) as [L|]; [|lia].
  exfalso. pose proof (Zpower_gt_Zdigits radix2 23 q ltac:(lia)) as G. simpl radix_val in G. lia.
Qed.

(* [comment removed for export] *)
Lemma pow2_pos k : 0 <= k -> 0 < 2 ^ k.
Proof. intros. apply Z.pow_pos_nonneg; lia. Qed.

(* [comment removed for export] *)
Lemma F2R_mul_pow2 (m e k : Z) : 0 <= k ->
  F2R (Float radix2 (m * 2 ^ k) e) = F2R (Float radix2 m (e + k)).
Proof.
  intros Hk. rewrite (F2R_change_exp radix2 e m (e + k)) by lia.
  replace (e + k - e) with k by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Section binary_round_pos.
  Variable md : mode.
  Variable M : positive.
  Variable E : Z.
  Let D := Zdigits radix2 (Zpos M) + E.
  Let es := fexp32 D.
  Let x := F2R (Float radix2 (Zpos M) E).
  Let z := binary_round 24 128 md false M E.

  Hypothesis HD : D <= 127.

  Theorem binary_round_pos_correct :
    valid_binary 24 128 z = true /\ is_finite_SF z = true /\ sign_SF z = false /\
    (exists q' : Z, SF2R radix2 z = F2R (Float radix2 q' es) /\
       ((F2R (Float radix2 q' es) <= x < F2R (Float radix2 (q' + 1) es))%R \/
        (F2R (Float radix2 (q' - 1) es) < x < F2R (Float radix2 q' es))%R)) /\
    (forall K, (x <= F2R (Float radix2 K es))%R -> (SF2R radix2 z <= F2R (Float radix2 K es))%R) /\
    (forall K, (F2R (Float radix2 K es) <= x)%R -> (F2R (Float radix2 K es) <= SF2R radix2 z)%R).
  Proof using HD md.
    assert (Hes : es = Z.max (D - 24) (-149)) by reflexivity.
    pose proof (Zdigits_pos_bounds (Zpos M) ltac:(lia)) as DM.
    (* [comment removed for export] *)
    unfold z, binary_round, shl_align_fexp.
    rewrite Zpos_digits2_pos. fold D. fold es.
    pose proof (shl_align_spec M E es) as SA.
    pose proof (shl_align_correct' M E es) as SA'.
    destruct (shl_align M E es) as [M1 E1].
    assert (HE1 : E1 <= es /\ F2R (Float radix2 (Zpos M1) E1) = x /\ Zdigits radix2 (Zpos M1) + E1 = D).
    { destruct (es <? E) eqn:LT.
      - apply Z.ltb_lt in LT. destruct SA as [-> HM1].
        specialize (SA' ltac:(lia)). destruct SA' as [SA' _].
        split; [lia|]. split; [exact SA'|].
        rewrite HM1. rewrite Zdigits_mult_Zpower by (simpl; lia). unfold D. lia.
      - apply Z.ltb_ge in LT. destruct SA as [-> ->]. split; [lia|]. split; [reflexivity|]. reflexivity. }
    destruct HE1 as (E1le & X1 & D1).
    (* [comment removed for export] *)
    unfold binary_round_aux.
    unfold shr_fexp. rewrite Zdigits2_Zdigits. rewrite D1. fold es.
    set (n1 := es - E1).
    pose proof (inbetween_shr x (Zpos M1) E1 loc_Exact n1 ltac:(lia)
                  ltac:(constructor; symmetry; exact X1)) as IB.
    pose proof (le_shr_le (shr_record_of_loc (Zpos M1) loc_Exact) E1 n1 ltac:(simpl; lia) ltac:(lia)) as LS.
    pose proof (shr_snd (shr_record_of_loc (Zpos M1) loc_Exact) E1 n1 ltac:(lia)) as SN.
    destruct (shr (shr_record_of_loc (Z.pos M1) loc_Exact) E1 n1) as [mrs1 e1] eqn:SH1.
    simpl in LS, SN. rewrite ?shr_m_shr_record_of_loc in LS.
    assert (He1 : e1 = es) by (subst n1; lia). clear SN. subst e1.
    set (q := shr_m mrs1) in *. set (l1 := loc_of_shr_record mrs1) in *.
    destruct LS as [Hq0 [LS1 LS2]].
    (* [comment removed for export] *)
    pose proof (Zdigits_pos_bounds (Zpos M1) ltac:(lia)) as DM1.
    assert (Hn1 : 0 <= n1) by (subst n1; lia).
    assert (Hq24 : q < 2 ^ 24).
    { assert (A : Zdigits radix2 (Z.pos M1) <= 24 + n1) by (subst n1; lia).
      assert (B : Z.pos M1 < 2 ^ (24 + n1)).
      { eapply Z.lt_le_trans; [apply (proj2 DM1)|]. apply Z.pow_le_mono_r; lia. }
      rewrite Z.pow_add_r in B by lia. pose proof (pow2_pos n1 Hn1). nia. }
    assert (Hq23 : es = D - 24 -> 2 ^ 23 <= q).
    { intros Hes'. assert (A : Zdigits radix2 (Z.pos M1) - 1 = 23 + n1) by (subst n1; lia).
      rewrite A in DM1. rewrite Z.pow_add_r in DM1 by lia. pose proof (pow2_pos n1 Hn1). nia. }
    (* [comment removed for export] *)
    pose proof (inbetween_float_bounds _ _ _ _ _ IB) as XB.
    (* [comment removed for export] *)
    set (q' := choice_mode md false q l1).
    pose proof (le_choice_mode_le md false q l1) as CM. fold q' in CM.
    assert (Hexact : l1 = loc_Exact -> q' = q).
    { intros HL. subst q'. rewrite HL. apply choice_mode_exact. }
    assert (Hq'cases : q' = q \/ (q' = q + 1 /\ (F2R (Float radix2 q es) < x)%R)).
    { destruct (Z.eq_dec q' q) as [|NE]; [now left|right]. split; [lia|].
      destruct l1 eqn:L1.
      - exfalso. apply NE. now apply Hexact.
      - inversion IB. lra. }
    (* [comment removed for export] *)
    rewrite Zdigits2_Zdigits.
    destruct (Z.eq_dec q' (2^24)) as [Q24 | Qlt].
    - (* [comment removed for export] *)
      rewrite Q24. change (Zdigits radix2 (2 ^ 24)) with 25.
      replace (fexp32 (25 + es) - es) with 1 by (rewrite fexp32_eq; lia).
      change (shr (shr_record_of_loc (2 ^ 24) loc_Exact) es 1) with (Build_shr_record 8388608 false false, es + 1).
      cbn [shr_m]. unfold binary_fit_aux.
      replace (es + 1 <=? 128 - 24) with true by (symmetry; apply Z.leb_le; lia).
      cbn [is_finite_SF sign_SF SF2R valid_binary].
      split.
      { unfold SpecFloat.bounded, canonical_mantissa. apply andb_true_intro; split.
        - apply Z.eqb_eq. unfold fexp, emin. change (Z.pos (digits2_pos 8388608)) with 24. lia.
        - apply Z.leb_le. lia. }
      split; [reflexivity|]. split; [reflexivity|].
      assert (V : F2R (Float radix2 (cond_Zopp false 8388608) (es + 1)) = F2R (Float radix2 q' es)).
      { rewrite Q24. change (cond_Zopp false 8388608) with (2^23). change (2^24) with (2^23 * 2^1).
        rewrite F2R_mul_pow2 by lia. reflexivity. }
      rewrite V.
      split.
      { exists q'. split; [reflexivity|].
        destruct Hq'cases as [A | [A B]].
        - left. rewrite A. exact XB.
        - right. rewrite A. replace (q + 1 - 1) with q by lia. lra. }
      split.
      { intros K HK. destruct Hq'cases as [A | [A B]].
        - rewrite A. apply F2R_le. apply (le_F2R radix2 es). lra.
        - rewrite A. apply F2R_le. assert (q < K); [|lia]. apply (lt_F2R radix2 es). lra. }
      { intros K HK. apply F2R_le. assert (K < q + 1); [|lia]. apply (lt_F2R radix2 es). lra. }
    - (* [comment removed for export] *)
      assert (Hq'lt : 0 <= q' < 2^24) by lia.
      assert (SH0 : fexp32 (Zdigits radix2 q' + es) - es <= 0).
      { rewrite fexp32_eq. pose proof (Zdigits_pos_le24 q' Hq'lt). lia. }
      rewrite (shr_nonpos _ _ _ SH0).
      rewrite shr_m_shr_record_of_loc.
      destruct q' as [|p'|p'] eqn:Q'.
      + (* [comment removed for export] *)
        cbn [is_finite_SF sign_SF SF2R valid_binary].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        assert (Z0R : F2R (Float radix2 0 es) = 0%R) by apply F2R_0.
        split.
        { exists 0. rewrite Z0R. split; [reflexivity|].
          destruct Hq'cases as [A | [A B]].
          - left. rewrite <- Z0R. rewrite A. replace (0 + 1) with (q + 1) by lia. exact XB.
          - right. rewrite <- Z0R. replace (0 - 1) with q by lia. rewrite A. lra. }
        split.
        { intros K HK. destruct Hq'cases as [A | [A B]].
          - rewrite <- Z0R. apply F2R_le. apply (le_F2R radix2 es). rewrite A. lra.
          - rewrite <- Z0R. apply F2R_le. assert (q < K); [|lia]. apply (lt_F2R radix2 es). lra. }
        { intros K HK. rewrite <- Z0R. apply F2R_le. assert (K < q + 1); [|lia]. apply (lt_F2R radix2 es). lra. }
      + unfold binary_fit_aux. replace (es <=? 128 - 24) with true by (symmetry; apply Z.leb_le; lia).
        cbn [is_finite_SF sign_SF SF2R valid_binary].
        split.
        { unfold SpecFloat.bounded, canonical_mantissa. apply andb_true_intro; split.
          - apply Z.eqb_eq. unfold fexp, emin. rewrite Zpos_digits2_pos.
            destruct (Z_le_gt_dec (D - 24) (-149)) as [LE|GT].
            + (* [comment removed for export] *)
              assert (es = -149) by lia.
              pose proof (Zdigits_pos_le24 (Zpos p') ltac:(lia)). lia.
            + assert (es = D - 24) by lia.
              assert (2^23 <= Zpos p') by (specialize (Hq23 ltac:(lia)); lia).
              rewrite (Zdigits_eq_24 (Zpos p')) by lia. lia.
          - apply Z.leb_le. lia. }
        split; [reflexivity|]. split; [reflexivity|].
        change (cond_Zopp false (Zpos p')) with (Zpos p').
        split.
        { exists (Zpos p'). split; [reflexivity|].
          destruct Hq'cases as [A | [A B]].
          - left. rewrite A. exact XB.
          - right. rewrite A. replace (q + 1 - 1) with q by lia. lra. }
        split.
        { intros K HK. destruct Hq'cases as [A | [A B]].
          - rewrite A. apply F2R_le. apply (le_F2R radix2 es). lra.
          - rewrite A. apply F2R_le. assert (q < K); [|lia]. apply (lt_F2R radix2 es). lra. }
        { intros K HK. apply F2R_le. assert (K < q + 1); [|lia]. apply (lt_F2R radix2 es). lra. }
      + lia.
  Qed.
End binary_round_pos.

(* [comment removed for export] *)


(* [comment removed for export] *)
Definition val (x : Z) : R := SF2R radix2 (dec x).

Lemma val_finite x s m e : dec x = S754_finite s m e ->
  val x = F2R (Float radix2 (cond_Zopp s (Zpos m)) e).
Proof. intros H. unfold val. rewrite H. reflexivity. Qed.
Lemma val_zero x s : dec x = S754_zero s -> val x = 0%R.
Proof. intros H. unfold val. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma bounded_cases m e :
  SpecFloat.bounded 24 128 m e = true ->
  (Zdigits radix2 (Zpos m) = 24 /\ -149 <= e <= 104) \/ (Zdigits radix2 (Zpos m) <= 23 /\ e = -149).
Proof.
  intros B. unfold SpecFloat.bounded, canonical_mantissa in B.
  apply andb_prop in B. destruct B as [B1 B2]. apply Z.eqb_eq in B1. apply Z.leb_le in B2.
  unfold fexp, emin in B1. rewrite Zpos_digits2_pos in B1. lia.
Qed.

Lemma bounded_mantissa_lt m e : SpecFloat.bounded 24 128 m e = true -> Zpos m < 2^24.
Proof.
  intros B. pose proof (Zdigits_pos_bounds (Zpos m) ltac:(lia)) as [_ U].
  assert (D : Zdigits radix2 (Zpos m) <= 24) by (destruct (bounded_cases m e B); lia).
  eapply Z.lt_le_trans; [exact U|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma F2R_lt_exp (m1 m2 : Z) (e1 e2 : Z) :
  e1 <= e2 -> m1 < m2 * 2^(e2 - e1) ->
  (F2R (Float radix2 m1 e1) < F2R (Float radix2 m2 e2))%R.
Proof.
  intros He Hm. rewrite (F2R_change_exp radix2 e1 m2 e2) by lia. apply F2R_lt. exact Hm.
Qed.

Lemma F2R_lt_bounded m1 e1 m2 e2 :
  SpecFloat.bounded 24 128 m1 e1 = true -> SpecFloat.bounded 24 128 m2 e2 = true ->
  e1 < e2 -> (F2R (Float radix2 (Zpos m1) e1) < F2R (Float radix2 (Zpos m2) e2))%R.
Proof.
  intros B1 B2 He.
  pose proof (bounded_mantissa_lt m1 e1 B1) as U1.
  destruct (bounded_cases m2 e2 B2) as [[D2 E2]|[D2 E2]]; [| destruct (bounded_cases m1 e1 B1) as [[? ?]|[? ?]]; lia].
  pose proof (Zdigits_pos_bounds (Zpos m2) ltac:(lia)) as [L2 _]. rewrite D2 in L2. change (2^(24-1)) with (2^23) in L2.
  apply F2R_lt_exp; [lia|].
  assert (2 ^ 24 <= Z.pos m2 * 2 ^ (e2 - e1)); [|lia].
  replace 24 with (23 + 1) by lia. rewrite Z.pow_add_r by lia.
  apply Z.mul_le_mono_nonneg; try lia. apply Z.pow_le_mono_r; lia.
Qed.

(* [comment removed for export] *)
Lemma Rcompare_pos_F2R m1 e1 m2 e2 :
  SpecFloat.bounded 24 128 m1 e1 = true -> SpecFloat.bounded 24 128 m2 e2 = true ->
  Rcompare (F2R (Float radix2 (Zpos m1) e1)) (F2R (Float radix2 (Zpos m2) e2)) =
  match Z.compare e1 e2 with Lt => Lt | Gt => Gt | Eq => Pos.compare_cont Eq m1 m2 end.
Proof.
  intros B1 B2.
  destruct (Z.compare_spec e1 e2) as [E|L|G].
  - subst e2. rewrite Rcompare_F2R. simpl. reflexivity.
  - apply Rcompare_Lt. now apply F2R_lt_bounded.
  - apply Rcompare_Gt. now apply F2R_lt_bounded.
Qed.

Theorem SFcompare_finite_correct (a b : spec_float) :
  valid_binary 24 128 a = true -> valid_binary 24 128 b = true ->
  is_finite_SF a = true -> is_finite_SF b = true ->
  SFcompare a b = Some (Rcompare (SF2R radix2 a) (SF2R radix2 b)).
Proof.
  intros Va Vb Fa Fb.
  destruct a as [sa|sa| |sa ma ea]; try discriminate;
  destruct b as [sb|sb| |sb mb eb]; try discriminate; cbn [SFcompare SF2R].
  - now rewrite Rcompare_Eq.
  - rewrite F2R_cond_Zopp. destruct sb; cbn [cond_Ropp].
    + rewrite Rcompare_Gt; [reflexivity|]. apply Ropp_lt_gt_0_contravar. apply F2R_gt_0. cbn. lia.
    + rewrite Rcompare_Lt; [reflexivity|]. apply F2R_gt_0. cbn. lia.
  - rewrite F2R_cond_Zopp. destruct sa; cbn [cond_Ropp].
    + rewrite Rcompare_Lt; [reflexivity|]. apply Ropp_lt_gt_0_contravar. apply F2R_gt_0. cbn. lia.
    + rewrite Rcompare_Gt; [reflexivity|]. apply F2R_gt_0. cbn. lia.
  - cbn [valid_binary] in Va, Vb.
    rewrite !F2R_cond_Zopp.
    pose proof (F2R_gt_0 radix2 (Float radix2 (Zpos ma) ea) ltac:(cbn; lia)) as Pa.
    pose proof (F2R_gt_0 radix2 (Float radix2 (Zpos mb) eb) ltac:(cbn; lia)) as Pb.
    destruct sa, sb; cbn [cond_Ropp].
    + rewrite Rcompare_opp. rewrite (Rcompare_pos_F2R mb eb ma ea Vb Va).
      rewrite (Z.compare_antisym ea eb).
      destruct (Z.compare ea eb); cbn [CompOpp]; try reflexivity.
      rewrite (Pos.compare_cont_antisym ma mb Eq). reflexivity.
    + rewrite Rcompare_Lt; [reflexivity|]. lra.
    + rewrite Rcompare_Gt; [reflexivity|]. lra.
    + now rewrite (Rcompare_pos_F2R ma ea mb eb Va Vb).
Qed.

(* [comment removed for export] *)
Lemma fp_compare_finite a b :
  is_finite_SF (dec a) = true -> is_finite_SF (dec b) = true ->
  fp_compare f32 a b = Some (Rcompare (val a) (val b)).
Proof.
  intros Ha Hb. unfold fp_compare, val. change (fp_decode f32 a) with (dec a). change (fp_decode f32 b) with (dec b).
  apply SFcompare_finite_correct; auto using dec_valid.
Qed.

Lemma fp_lt_finite a b :
  is_finite_SF (dec a) = true -> is_finite_SF (dec b) = true ->
  fst (fp_lt f32 a b) = Rlt_bool (val a) (val b).
Proof.
  intros Ha Hb. unfold fp_lt. cbn [fst]. rewrite (fp_compare_finite a b Ha Hb).
  unfold Rlt_bool. destruct (Rcompare (val a) (val b)); reflexivity.
Qed.

Lemma fp_le_finite a b :
  is_finite_SF (dec a) = true -> is_finite_SF (dec b) = true ->
  fst (fp_le f32 a b) = Rle_bool (val a) (val b).
Proof.
  intros Ha Hb. unfold fp_le. cbn [fst]. rewrite (fp_compare_finite a b Ha Hb).
  unfold Rle_bool. destruct (Rcompare (val a) (val b)); reflexivity.
Qed.

Lemma fp_eq_finite a b :
  is_finite_SF (dec a) = true -> is_finite_SF (dec b) = true ->
  fst (fp_eq f32 a b) = Req_bool (val a) (val b).
Proof.
  intros Ha Hb. unfold fp_eq. cbn [fst]. rewrite (fp_compare_finite a b Ha Hb).
  unfold Req_bool. destruct (Rcompare (val a) (val b)); reflexivity.
Qed.

Lemma fp_compare_nan_l a b : dec a = S754_nan -> fp_compare f32 a b = None.
Proof. intros H. unfold fp_compare. change (fp_decode f32 a) with (dec a). rewrite H. reflexivity. Qed.
Lemma fp_compare_nan_r a b : dec b = S754_nan -> fp_compare f32 a b = None.
Proof. intros H. unfold fp_compare. change (fp_decode f32 b) with (dec b). rewrite H. destruct (fp_decode f32 a); reflexivity. Qed.

Lemma fp_lt_true_not_nan a b : fst (fp_lt f32 a b) = true -> dec a <> S754_nan /\ dec b <> S754_nan.
Proof.
  unfold fp_lt; cbn [fst]. intros H. split; intros N.
  - rewrite (fp_compare_nan_l a b N) in H. discriminate.
  - rewrite (fp_compare_nan_r a b N) in H. discriminate.
Qed.
Lemma fp_le_true_not_nan a b : fst (fp_le f32 a b) = true -> dec a <> S754_nan /\ dec b <> S754_nan.
Proof.
  unfold fp_le; cbn [fst]. intros H. split; intros N.
  - rewrite (fp_compare_nan_l a b N) in H. discriminate.
  - rewrite (fp_compare_nan_r a b N) in H. discriminate.
Qed.
Lemma fp_eq_true_not_nan a b : fst (fp_eq f32 a b) = true -> dec a <> S754_nan /\ dec b <> S754_nan.
Proof.
  unfold fp_eq; cbn [fst]. intros H. split; intros N.
  - rewrite (fp_compare_nan_l a b N) in H. discriminate.
  - rewrite (fp_compare_nan_r a b N) in H. discriminate.
Qed.

(* [comment removed for export] *)


(* [comment removed for export] *)
Lemma round_exact_binary_round md sx mx ex :
  fst (round_exact f32 md sx mx ex) = binary_round 24 128 (flocq_mode md) sx mx ex.
Proof.
  unfold round_exact, binary_round, shl_align_fexp.
  change (fp_prec f32) with 24. change (fp_emax f32) with 128.
  destruct (shl_align mx ex (SpecFloat.fexp 24 128 (Z.pos (digits2_pos mx) + ex))) as [mz ez].
  apply (round_aux_value f32 md sx (Zpos mz) ez loc_Exact).
Qed.

Lemma fst_enc' r : fst (Fpu.enc f32 r) = enc (fst r).
Proof. destruct r; reflexivity. Qed.

Lemma is_nan_false_of_finite x : is_finite_SF (dec x) = true -> fp_is_nan f32 x = false.
Proof. intros H. rewrite <- is_nan_SF_dec. destruct (dec x); simpl in *; congruence. Qed.

Lemma nan_pass2_none a b :
  is_finite_SF (dec a) = true -> is_finite_SF (dec b) = true -> nan_pass2 f32 a b = None.
Proof.
  intros Ha Hb. unfold nan_pass2. rewrite (is_nan_false_of_finite a Ha), (is_nan_false_of_finite b Hb). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma F2R_int_scaled (H k : Z) : 0 <= k ->
  F2R (Float radix2 (H * 2 ^ k) (- k)) = IZR H.
Proof.
  intros Hk. rewrite F2R_mul_pow2 by lia. replace (- k + k) with 0 by lia.
  unfold F2R. simpl. ring.
Qed.

Lemma x_ge_bpow (M : positive) (E : Z) :
  (bpow radix2 (Zdigits radix2 (Zpos M) + E - 1) <= F2R (Float radix2 (Zpos M) E))%R.
Proof.
  pose proof (Zdigits_pos_bounds (Zpos M) ltac:(lia)) as [L _].
  pose proof (Zdigits_gt_0 radix2 (Zpos M) ltac:(lia)) as Dpos.
  set (d := Zdigits radix2 (Zpos M)) in *.
  replace (d + E - 1) with (E + (d - 1)) by lia.
  rewrite <- F2R_bpow. rewrite <- (F2R_mul_pow2 1 E (d - 1)) by lia.
  apply F2R_le. lia.
Qed.

Theorem binary_round_pos_int_bounds md (M : positive) (E G H : Z) :
  let x := F2R (Float radix2 (Zpos M) E) in
  (IZR G <= x <= IZR H)%R -> H <= 2^24 ->
  let z := binary_round 24 128 md false M E in
  valid_binary 24 128 z = true /\ is_finite_SF z = true /\ sign_SF z = false /\
  (IZR G <= SF2R radix2 z <= IZR H)%R.
Proof.
  intros x [HG HH] H24 z.
  set (D := Zdigits radix2 (Zpos M) + E).
  pose proof (x_ge_bpow M E) as XL. fold D in XL. change (F2R _) with x in XL.
  assert (HD : D <= 25).
  { destruct (Z_le_gt_dec D 25) as [|G25]; [assumption|exfalso].
    assert (B25 : (bpow radix2 25 <= bpow radix2 (D - 1))%R) by (apply bpow_le; lia).
    assert (H24R : (IZR H <= IZR (2^24))%R) by (apply IZR_le; lia).
    change (bpow radix2 25) with (IZR (2^25)) in B25.
    assert (LT : (IZR (2^24) < IZR (2^25))%R) by (apply IZR_lt; lia). lra. }
  pose proof (binary_round_pos_correct md M E ltac:(unfold D in HD; lia)) as (V & F & S & _ & UB & LB).
  fold z in V, F, S, UB, LB.
  set (es := fexp32 (Zdigits radix2 (Z.pos M) + E)) in *.
  assert (Hes : es = Z.max (D - 24) (-149)) by reflexivity.
  refine (conj V (conj F (conj S _))).
  destruct (Z_le_gt_dec D 24) as [D24|D25].
  - (* [comment removed for export] *)
    assert (Hk : 0 <= - es) by lia.
    split.
    + rewrite <- (F2R_int_scaled G (- es)) by lia. replace (- - es) with es by lia.
      apply LB. rewrite F2R_mul_pow2 by lia. replace (es + - es) with 0 by lia.
      unfold F2R; simpl. rewrite Rmult_1_r. exact HG.
    + rewrite <- (F2R_int_scaled H (- es)) by lia. replace (- - es) with es by lia.
      apply UB. rewrite F2R_mul_pow2 by lia. replace (es + - es) with 0 by lia.
      unfold F2R; simpl. rewrite Rmult_1_r. exact HH.
  - (* [comment removed for export] *)
    assert (D = 25) by lia. assert (Hes1 : es = 1) by lia.
    replace (D - 1) with 24 in XL by lia.
    change (bpow radix2 24) with (IZR (2 ^ 24)) in XL.
    assert (IZR H <= IZR (2^24))%R by (apply IZR_le; lia).
    assert (X24 : x = IZR (2^24)) by lra.
    assert (K : F2R (Float radix2 (2^23) es) = IZR (2^24)).
    { rewrite Hes1. unfold F2R. simpl Fnum. simpl Fexp. change (bpow radix2 1) with 2%R.
      rewrite <- (mult_IZR _ 2). reflexivity. }
    split.
    + apply Rle_trans with (IZR (2^24)); [lra|]. rewrite <- K. apply LB. rewrite K. fold x. lra.
    + apply Rle_trans with (IZR (2^24)); [|lra]. rewrite <- K. apply UB. rewrite K. fold x. lra.
Qed.

(* [comment removed for export] *)
Lemma cond_Zopp_mul sa sb (ma mb : positive) :
  cond_Zopp sa (Zpos ma) * cond_Zopp sb (Zpos mb) = cond_Zopp (xorb sa sb) (Zpos (ma * mb)).
Proof. destruct sa, sb; simpl; lia. Qed.

Lemma fp_mul_finite md a b sa ma ea sb mb eb :
  dec a = S754_finite sa ma ea -> dec b = S754_finite sb mb eb ->
  fst (fp_mul f32 md a b) = enc (binary_round 24 128 (flocq_mode md) (xorb sa sb) (ma * mb)%positive (ea + eb)).
Proof.
  intros Ha Hb. unfold fp_mul.
  rewrite nan_pass2_none by (rewrite ?Ha, ?Hb; reflexivity).
  change (fp_decode f32 a) with (dec a). change (fp_decode f32 b) with (dec b).
  rewrite Ha, Hb. rewrite fst_enc'. f_equal. apply round_exact_binary_round.
Qed.

Lemma fp_mul_zero_l md a b sa :
  dec a = S754_zero sa -> is_finite_SF (dec b) = true ->
  fst (fp_mul f32 md a b) = enc (S754_zero (xorb sa (sign_SF (dec b)))).
Proof.
  intros Ha Hb. unfold fp_mul.
  rewrite nan_pass2_none by (rewrite ?Ha; auto).
  change (fp_decode f32 a) with (dec a). change (fp_decode f32 b) with (dec b).
  rewrite Ha. destruct (dec b); try discriminate; reflexivity.
Qed.

Lemma fp_mul_zero_r md a b sb :
  is_finite_SF (dec a) = true -> dec b = S754_zero sb ->
  fst (fp_mul f32 md a b) = enc (S754_zero (xorb (sign_SF (dec a)) sb)).
Proof.
  intros Ha Hb. unfold fp_mul.
  rewrite nan_pass2_none by (rewrite ?Hb; auto).
  change (fp_decode f32 a) with (dec a). change (fp_decode f32 b) with (dec b).
  rewrite Hb. destruct (dec a); try discriminate; reflexivity.
Qed.

(* [comment removed for export] *)
Theorem fp_mul_pos_correct md a b ma ea mb eb (G H : Z) :
  dec a = S754_finite false ma ea -> dec b = S754_finite false mb eb ->
  (IZR G <= val a * val b <= IZR H)%R -> H <= 2^24 ->
  let r := fst (fp_mul f32 md a b) in
  is_finite_SF (dec r) = true /\ sign_SF (dec r) = false /\ (IZR G <= val r <= IZR H)%R /\
  0 <= r < 2^32 /\ enc (dec r) = r.
Proof.
  intros Ha Hb HGH H24 r.
  assert (Hx : F2R (Float radix2 (Zpos (ma*mb)) (ea+eb)) = (val a * val b)%R).
  { rewrite (val_finite a false ma ea Ha), (val_finite b false mb eb Hb).
    rewrite <- F2R_mult. unfold Fmult. reflexivity. }
  pose proof (binary_round_pos_int_bounds (flocq_mode md) (ma*mb)%positive (ea+eb) G H) as BR.
  cbv zeta in BR. rewrite Hx in BR. specialize (BR HGH H24). destruct BR as (V & F & S & B).
  assert (Hr : r = enc (binary_round 24 128 (flocq_mode md) false (ma*mb)%positive (ea+eb))).
  { subst r. apply (fp_mul_finite md a b false ma ea false mb eb Ha Hb). }
  rewrite Hr. unfold val. rewrite (dec_enc _ V).
  repeat split; try assumption; try apply B; try apply (enc_range _ V).
Qed.

(* [comment removed for export] *)
Lemma int_wrap_small bits v : 0 <= bits -> 0 <= v < 2^bits -> int_wrap bits v = v.
Proof. intros Hb Hv. unfold int_wrap. rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma fp_of_int_u32_pos md n (p : positive) :
  n = Zpos p -> n < 2^32 ->
  fst (fp_of_int f32 md false 32 n) = enc (binary_round 24 128 (flocq_mode md) false p 0).
Proof.
  intros Hn Hlt. unfold fp_of_int. rewrite int_wrap_small by lia.
  cbn [andb]. rewrite Hn. unfold round_scaled. rewrite fst_enc'. f_equal. apply round_exact_binary_round.
Qed.

Theorem fp_of_int_u32_correct md n :
  0 < n <= 2^24 ->
  let r := fst (fp_of_int f32 md false 32 n) in
  is_finite_SF (dec r) = true /\ val r = IZR n /\ sign_SF (dec r) = false /\ 0 <= r < 2^32 /\ enc (dec r) = r.
Proof.
  intros Hn r.
  destruct n as [|p|p]; try lia.
  pose proof (binary_round_pos_int_bounds (flocq_mode md) p 0 (Zpos p) (Zpos p)) as BR. cbv zeta in BR.
  assert (Hx : F2R (Float radix2 (Zpos p) 0) = IZR (Zpos p)) by (unfold F2R; simpl; ring).
  rewrite Hx in BR. specialize (BR ltac:(lra) ltac:(lia)). destruct BR as (V & F & S & B).
  assert (Hr : r = enc (binary_round 24 128 (flocq_mode md) false p 0)).
  { subst r. apply (fp_of_int_u32_pos md (Zpos p) p eq_refl). lia. }
  rewrite Hr. unfold val. rewrite (dec_enc _ V).
  repeat split; try assumption; try apply (enc_range _ V). lra.
Qed.

(* [comment removed for export] *)
Lemma F2R_shiftl (m e k : Z) : 0 <= k ->
  F2R (Float radix2 (Z.shiftl m k) e) = F2R (Float radix2 m (e + k)).
Proof. intros Hk. rewrite Z.shiftl_mul_pow2 by lia. apply F2R_mul_pow2. lia. Qed.

Lemma F2R_plus_same (a b e : Z) :
  F2R (Float radix2 (a + b) e) = (F2R (Float radix2 a e) + F2R (Float radix2 b e))%R.
Proof. unfold F2R. simpl. rewrite plus_IZR. ring. Qed.

Lemma scaled_value x :
  is_finite_SF x = true ->
  let '(m, e) := sf_scaled x in F2R (Float radix2 m e) = SF2R radix2 x.
Proof.
  destruct x as [s|s| |s m e]; simpl; try discriminate; intros _.
  - apply F2R_0.
  - destruct s; reflexivity.
Qed.

Lemma scaled_add_value x y :
  is_finite_SF x = true -> is_finite_SF y = true ->
  let '(m, e) := scaled_add (sf_scaled x) (sf_scaled y) in
  F2R (Float radix2 m e) = (SF2R radix2 x + SF2R radix2 y)%R.
Proof.
  intros Hx Hy.
  pose proof (scaled_value x Hx) as Vx. pose proof (scaled_value y Hy) as Vy.
  destruct (sf_scaled x) as [ma ea]. destruct (sf_scaled y) as [mb eb].
  unfold scaled_add.
  rewrite F2R_plus_same.
  rewrite !F2R_shiftl by lia.
  replace (Z.min ea eb + (ea - Z.min ea eb)) with ea by lia.
  replace (Z.min ea eb + (eb - Z.min ea eb)) with eb by lia.
  rewrite Vx, Vy. reflexivity.
Qed.

Lemma fp_add_finite md a b :
  is_finite_SF (dec a) = true -> is_finite_SF (dec b) = true ->
  fst (fp_add f32 md a b) =
    enc (fst (round_scaled f32 md (zero_sign md (sf_sign (dec a)) (sf_sign (dec b)))
                           (scaled_add (sf_scaled (dec a)) (sf_scaled (dec b))))).
Proof.
  intros Ha Hb. unfold fp_add. rewrite (nan_pass2_none a b Ha Hb).
  change (fp_decode f32 a) with (dec a). change (fp_decode f32 b) with (dec b).
  destruct (dec a); try discriminate; destruct (dec b); try discriminate; rewrite fst_enc'; reflexivity.
Qed.

Lemma round_scaled_cases md sz m e :
  fst (round_scaled f32 md sz (m, e)) =
  match m with
  | Z0 => S754_zero sz
  | Zpos p => binary_round 24 128 (flocq_mode md) false p e
  | Zneg p => binary_round 24 128 (flocq_mode md) true p e
  end.
Proof. unfold round_scaled. destruct m; try reflexivity; apply round_exact_binary_round. Qed.

(* [comment removed for export] *)
Theorem fp_add_pos_correct md a b (G H : Z) :
  is_finite_SF (dec a) = true -> is_finite_SF (dec b) = true ->
  (IZR G <= val a + val b <= IZR H)%R -> 1 <= G -> H <= 2^24 ->
  let r := fst (fp_add f32 md a b) in
  is_finite_SF (dec r) = true /\ sign_SF (dec r) = false /\ (IZR G <= val r <= IZR H)%R /\
  0 <= r < 2^32 /\ enc (dec r) = r.
Proof.
  intros Ha Hb HGH HG1 H24 r.
  pose proof (fp_add_finite md a b Ha Hb) as Hr. fold r in Hr.
  pose proof (scaled_add_value (dec a) (dec b) Ha Hb) as SV.
  destruct (scaled_add (sf_scaled (dec a)) (sf_scaled (dec b))) as [m e] eqn:SA.
  rewrite round_scaled_cases in Hr.
  change (SF2R radix2 (dec a)) with (val a) in SV. change (SF2R radix2 (dec b)) with (val b) in SV.
  assert (HG1' : (1 <= IZR G)%R) by (apply (IZR_le 1); lia).
  destruct m as [|p|p].
  - exfalso. rewrite F2R_0 in SV. lra.
  - pose proof (binary_round_pos_int_bounds (flocq_mode md) p e G H) as BR. cbv zeta in BR.
    rewrite SV in BR. specialize (BR HGH H24). destruct BR as (V & F & S & B).
    rewrite Hr. unfold val. rewrite (dec_enc _ V).
    repeat split; try assumption; try apply B; try apply (enc_range _ V).
  - exfalso. pose proof (F2R_lt_0 radix2 (Float radix2 (Z.neg p) e) ltac:(simpl; lia)). lra.
Qed.

(* [comment removed for export] *)


(* [comment removed for export] *)

Lemma F2R_pos_e_ge0 (m : positive) e : 0 <= e ->
  F2R (Float radix2 (Zpos m) e) = IZR (Zpos m * 2^e).
Proof.
  intros He. unfold F2R. simpl Fnum. simpl Fexp. rewrite mult_IZR. rewrite (IZR_Zpower radix2) by lia. reflexivity.
Qed.

Lemma F2R_pos_e_lt0 (m : positive) e : e < 0 ->
  F2R (Float radix2 (Zpos m) e) = (IZR (Zpos m) / IZR (2^(-e)))%R.
Proof.
  intros He. unfold F2R. simpl Fnum. simpl Fexp.
  rewrite (IZR_Zpower radix2) by lia.
  replace e with (- (- e)) at 1 by lia. rewrite bpow_opp. unfold Rdiv. reflexivity.
Qed.

Lemma Zfloor_scaled (m : positive) e :
  Zfloor (F2R (Float radix2 (Zpos m) e)) =
  (if 0 <=? e then Z.shiftl (Zpos m) e else Zpos m / 2^(-e)).
Proof.
  destruct (0 <=? e) eqn:E.
  - apply Z.leb_le in E. rewrite F2R_pos_e_ge0 by lia. rewrite Zfloor_IZR. rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
  - apply Z.leb_gt in E. rewrite F2R_pos_e_lt0 by lia. apply Zfloor_div. assert (0 < 2^(-e)) by (apply Z.pow_pos_nonneg; lia). lia.
Qed.

Lemma fp_to_int_RTZ32_finite a s m e :
  dec a = S754_finite s m e ->
  let q := Zfloor (F2R (Float radix2 (Zpos m) e)) in
  let v := cond_Zopp s q in
  - 2^31 <= v <= 2^31 - 1 ->
  fst (fp_to_int f32 RTZ true 32 a) = int_wrap 32 v.
Proof.
  intros Ha q v Hv. unfold fp_to_int.
  rewrite (is_nan_false_of_finite a) by (rewrite Ha; reflexivity).
  change (fp_decode f32 a) with (dec a). rewrite Ha.
  change (int_lo true 32) with (- 2^31). change (int_hi true 32) with (2^31 - 1).
  pose proof (Zfloor_scaled m e) as ZS. fold q in ZS.
  assert (KEY : forall l (q0 : Z), q0 = q ->
    fst (let q' := choice_mode (flocq_mode RTZ) s q0 l in
         let v0 := if s then - q' else q' in
         if (v0 <? - 2^31) || (2^31 - 1 <? v0) then (int_wrap 32 (if s then - 2^31 else 2^31 - 1), nv_flag)
         else (int_wrap 32 v0, match l with loc_Exact => no_flags | _ => nx_flag end)) = int_wrap 32 v).
  { intros l q0 ->. cbn [choice_mode flocq_mode].
    assert (Ev : (if s then - q else q) = v) by (subst v; destruct s; reflexivity).
    rewrite Ev.
    destruct ((v <? - 2 ^ 31) || (2 ^ 31 - 1 <? v)) eqn:C.
    - exfalso. apply Bool.orb_true_iff in C. destruct C as [C|C]; apply Z.ltb_lt in C; lia.
    - reflexivity. }
  destruct (0 <=? e) eqn:E.
  - apply KEY. symmetry. exact ZS.
  - destruct (Z.div_eucl (Z.pos m) (Z.shiftl 1 (- e))) as [q1 r] eqn:DE.
    apply KEY. rewrite ZS.
    assert (Hd : Z.shiftl 1 (-e) = 2^(-e)). { rewrite Z.shiftl_mul_pow2 by (apply Z.leb_gt in E; lia). lia. }
    unfold Z.div. rewrite <- Hd. rewrite DE. reflexivity.
Qed.

Lemma fp_to_int_zero md sg bits a s :
  dec a = S754_zero s -> fst (fp_to_int f32 md sg bits a) = 0.
Proof.
  intros Ha. unfold fp_to_int.
  rewrite (is_nan_false_of_finite a) by (rewrite Ha; reflexivity).
  change (fp_decode f32 a) with (dec a). rewrite Ha. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma Rabs_val_finite a s m e : dec a = S754_finite s m e ->
  F2R (Float radix2 (Zpos m) e) = Rabs (val a).
Proof.
  intros Ha. rewrite (val_finite a s m e Ha). rewrite F2R_cond_Zopp.
  unfold cond_Ropp. destruct s.
  - rewrite Rabs_Ropp. rewrite Rabs_pos_eq; [reflexivity|]. apply F2R_ge_0. simpl. lia.
  - rewrite Rabs_pos_eq; [reflexivity|]. apply F2R_ge_0. simpl. lia.
Qed.

Lemma fp_to_int_RTZ32_nonneg a (M : Z) :
  is_finite_SF (dec a) = true ->
  (0 <= val a)%R -> (val a < IZR (M + 1))%R -> 0 <= M -> M + 1 <= 2^31 ->
  0 <= fst (fp_to_int f32 RTZ true 32 a) <= M /\
  fst (fp_to_int f32 RTZ true 32 a) = Zfloor (val a).
Proof.
  intros Hf H0 HM HM0 HM1.
  destruct (dec a) as [s|s| |s m e] eqn:Ha; try discriminate.
  - rewrite (fp_to_int_zero RTZ true 32 a s Ha). rewrite (val_zero a s Ha). rewrite Zfloor_IZR. lia.
  - assert (Hs : s = false).
    { destruct s; [|reflexivity]. exfalso.
      pose proof (val_finite a true m e Ha) as V. rewrite V in H0.
      pose proof (F2R_lt_0 radix2 (Float radix2 (cond_Zopp true (Z.pos m)) e) ltac:(simpl; lia)). lra. }
    subst s.
    pose proof (Rabs_val_finite a false m e Ha) as RV. rewrite Rabs_pos_eq in RV by lra.
    assert (HZ : 0 <= Zfloor (val a) <= M).
    { split.
      - rewrite <- (Zfloor_IZR 0). apply Zfloor_le. simpl. lra.
      - assert (Zfloor (val a) < M + 1); [|lia]. apply lt_IZR. eapply Rle_lt_trans; [apply Zfloor_lb| exact HM]. }
    rewrite (fp_to_int_RTZ32_finite a false m e Ha); cbv zeta; rewrite RV; cbn [cond_Zopp].
    + rewrite int_wrap_small by lia. lia.
    + lia.
Qed.

(* [comment removed for export] *)
Definition one32 : Z := 0x3f800000.
Definition two31f : Z := 0x4f000000.
Definition K32 : Z := 0xcf000001.     (* [comment removed for export] *)
Definition m128f : Z := 0xc3000000.   (* [comment removed for export] *)

Lemma dec_one : dec one32 = S754_finite false 8388608 (-23). Proof. reflexivity. Qed.
Lemma dec_two31 : dec two31f = S754_finite false 8388608 8. Proof. reflexivity. Qed.
Lemma dec_K : dec K32 = S754_finite true 8388609 8. Proof. reflexivity. Qed.
Lemma dec_m128 : dec m128f = S754_finite true 8388608 (-16). Proof. reflexivity. Qed.
Lemma dec_pzero : dec 0 = S754_zero false. Proof. reflexivity. Qed.

Lemma val_finite_pos_e x s m e : dec x = S754_finite s m e -> 0 <= e ->
  val x = IZR (cond_Zopp s (Zpos m) * 2^e).
Proof.
  intros Hx He. rewrite (val_finite x s m e Hx). unfold F2R. simpl Fnum. simpl Fexp.
  rewrite mult_IZR. rewrite (IZR_Zpower radix2) by lia. reflexivity.
Qed.
Lemma val_finite_neg_e x s m e : dec x = S754_finite s m e -> e < 0 ->
  val x = (IZR (cond_Zopp s (Zpos m)) / IZR (2^(-e)))%R.
Proof.
  intros Hx He. rewrite (val_finite x s m e Hx). unfold F2R. simpl Fnum. simpl Fexp.
  rewrite (IZR_Zpower radix2) by lia.
  replace e with (- (- e)) at 1 by lia. rewrite bpow_opp. unfold Rdiv. reflexivity.
Qed.

Lemma IZR_div_exact (a b k : Z) : b <> 0 -> a = k * b -> (IZR a / IZR b)%R = IZR k.
Proof.
  intros Hb ->. rewrite mult_IZR. unfold Rdiv. rewrite Rmult_assoc, Rinv_r, Rmult_1_r; [reflexivity|].
  apply not_0_IZR. exact Hb.
Qed.

Lemma val_one : val one32 = 1%R.
Proof.
  rewrite (val_finite_neg_e _ _ _ _ dec_one) by lia.
  apply (IZR_div_exact _ _ 1); [lia|reflexivity].
Qed.
Lemma val_two31 : val two31f = IZR (2^31).
Proof. rewrite (val_finite_pos_e _ _ _ _ dec_two31) by lia. reflexivity. Qed.
Lemma val_K : val K32 = IZR (- 2147483904).
Proof. rewrite (val_finite_pos_e _ _ _ _ dec_K) by lia. reflexivity. Qed.
Lemma val_m128 : val m128f = IZR (-128).
Proof.
  rewrite (val_finite_neg_e _ _ _ _ dec_m128) by lia.
  apply (IZR_div_exact _ _ (-128)); [lia|reflexivity].
Qed.
Lemma val_pzero : val 0 = 0%R. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma fp_min_one_cases X :
  let t := fst (fp_minmax f32 false X one32) in
  t = one32 \/ (t = X /\ fp_is_nan f32 X = false /\
                (dec X = S754_infinity true \/ (is_finite_SF (dec X) = true /\ (val X <= 1)%R))).
Proof.
  cbv zeta. unfold fp_minmax.
  change (fp_is_nan f32 one32) with false. change (fp_is_snan f32 one32) with false.
  rewrite Bool.andb_false_r.
  destruct (fp_is_nan f32 X) eqn:N; [left; reflexivity|].
  cbv iota.
  change (fp_sign_bit f32 one32) with false. cbn [negb andb xorb].
  destruct (dec X) as [s|s| |s m e] eqn:DX.
  - (* [comment removed for export] *) rewrite (fp_compare_finite X one32) by (rewrite ?DX, ?dec_one; reflexivity).
    rewrite (val_zero X s DX), val_one.
    rewrite Rcompare_Lt by lra. right. repeat split; auto. right. split; [reflexivity|]. lra.
  - (* [comment removed for export] *) unfold fp_compare. change (fp_decode f32 X) with (dec X). change (fp_decode f32 one32) with (dec one32).
    rewrite DX, dec_one. destruct s; cbn.
    + right. repeat split; auto.
    + left; reflexivity.
  - (* [comment removed for export] *) exfalso. apply dec_nan_iff in DX. congruence.
  - rewrite (fp_compare_finite X one32) by (rewrite ?DX, ?dec_one; reflexivity).
    rewrite val_one.
    destruct (Rcompare_spec (val X) 1) as [L|E|G].
    + right. repeat split; auto. right. split; [reflexivity|lra].
    + rewrite Bool.andb_true_r. destruct (fp_sign_bit f32 X).
      * right. repeat split; auto. right. split; [reflexivity|lra].
      * left; reflexivity.
    + left; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma enc_pos_finite m e :
  SpecFloat.bounded 24 128 m e = true ->
  0 < enc (S754_finite false m e) < 2139095040.
Proof.
  intros B. pose proof B as B0. unfold SpecFloat.bounded, canonical_mantissa in B.
  apply andb_prop in B. destruct B as [B1 B2]. apply Z.eqb_eq in B1. apply Z.leb_le in B2.
  unfold fexp, emin in B1.
  rewrite enc_unfold. rewrite Zpos_size_digits.
  destruct (Z.pos (digits2_pos m) <? 24) eqn:D.
  - apply Z.ltb_lt in D.
    pose proof (Zpower_gt_Zdigits radix2 23 (Zpos m)) as G. rewrite <- Zpos_digits2_pos in G.
    change (radix2 ^ 23)%Z with (2^23)%Z in G. lia.
  - apply Z.ltb_ge in D.
    assert (Hm : 2^23 <= Zpos m < 2^24).
    { split.
      - pose proof (Zpower_le_Zdigits radix2 23 (Zpos m)) as G. rewrite <- Zpos_digits2_pos in G.
        change (radix2 ^ 23)%Z with (2^23)%Z in G. lia.
      - pose proof (Zpower_gt_Zdigits radix2 24 (Zpos m)) as G. rewrite <- Zpos_digits2_pos in G.
        change (radix2 ^ 24)%Z with (2^24)%Z in G. lia. }
    rewrite Z.shiftl_mul_pow2 by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma dec_fields x : 0 <= x < 2^32 ->
  x = (if sgn32 x then 2^31 else 0) + expo32 x * 2^23 + mant32 x.
Proof. apply pattern_decomp. Qed.

Lemma pos_pattern_fields x : 0 < x < 2139095040 ->
  sgn32 x = false /\ 0 <= expo32 x <= 254 /\ (expo32 x = 0 -> 0 < mant32 x).
Proof.
  intros Hx.
  pose proof (pattern_decomp x ltac:(lia)) as D.
  pose proof (expo32_range x) as E. pose proof (mant32_range x) as M.
  destruct (sgn32 x); [exfalso; lia|].
  repeat split; try lia.
Qed.


Theorem pred_pattern x :
  0 < x < 2139095040 ->
  is_finite_SF (dec (x - 1)) = true /\ sgn32 (x - 1) = false /\
  (0 <= val (x - 1))%R /\ (val (x - 1) < val x)%R.
Proof.
  intros Hx.
  pose proof (pos_pattern_fields x Hx) as (S & E & EM).
  pose proof (pattern_decomp x ltac:(lia)) as D. rewrite S in D.
  pose proof (mant32_range x) as M.
  set (Ex := expo32 x) in *. set (Mx := mant32 x) in *.
  (* [comment removed for export] *)
  assert (FLD : exists E' M', 0 <= E' <= 254 /\ 0 <= M' < 2^23 /\ x - 1 = E' * 2^23 + M' /\
            ((Mx > 0 /\ E' = Ex /\ M' = Mx - 1) \/ (Mx = 0 /\ Ex >= 1 /\ E' = Ex - 1 /\ M' = 2^23 - 1))).
  { destruct (Z.eq_dec Mx 0) as [Z0|NZ].
    - exists (Ex - 1), (2^23 - 1). assert (Ex >= 1) by lia. repeat split; try lia.
    - exists Ex, (Mx - 1). repeat split; try lia. }
  destruct FLD as (E' & M' & HE' & HM' & Hx1 & CASES).
  pose proof (fields_compose false E' M' ltac:(lia) HM') as FC. cbv zeta in FC.
  rewrite Z.add_0_l in FC. rewrite <- Hx1 in FC. destruct FC as (XE & XM & XS & XR).
  (* [comment removed for export] *)
  assert (DX : dec x = if Ex =? 0 then match Mx with Zpos p => S754_finite false p (-149) | _ => S754_zero false end
                       else match 2^23 + Mx with Zpos p => S754_finite false p (Ex - 150) | _ => S754_nan end).
  { rewrite dec_unfold. fold Ex Mx. rewrite S.
    replace (Ex =? 255) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  assert (DX1 : dec (x-1) = if E' =? 0 then match M' with Zpos p => S754_finite false p (-149) | _ => S754_zero false end
                          else match 2^23 + M' with Zpos p => S754_finite false p (E' - 150) | _ => S754_nan end).
  { rewrite dec_unfold. rewrite XE, XM, XS.
    replace (E' =? 255) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  split; [|split; [exact XS|]].
  { rewrite DX1. destruct (E' =? 0) eqn:E0.
    - destruct M'; reflexivity.
    - destruct (2^23 + M') eqn:P; try reflexivity; lia. }
  unfold val. rewrite DX, DX1.
  destruct CASES as [(HMx & HE1 & HM1)|(HMx & HEx & HE1 & HM1)].
  - (* [comment removed for export] *)
    subst E'. destruct (Ex =? 0) eqn:E0.
    + (* [comment removed for export] *)
      rewrite HM1. destruct Mx as [|p|p] eqn:MX; try lia.
      destruct (Z.pos p - 1) as [|p'|p'] eqn:MP; try lia.
      * cbn [SF2R cond_Zopp Z.opp]. split; [lra|]. apply F2R_gt_0. cbn. lia.
      * cbn [SF2R cond_Zopp Z.opp]. split. { apply F2R_ge_0. cbn. lia. } apply F2R_lt. lia.
    + rewrite HM1. destruct (2^23 + Mx) as [|p|p] eqn:MX; try lia.
      destruct (2^23 + (Mx - 1)) as [|p'|p'] eqn:MP; try lia.
      cbn [SF2R cond_Zopp Z.opp]. split. { apply F2R_ge_0. cbn. lia. } apply F2R_lt. lia.
  - (* [comment removed for export] *)
    subst E' M'. rewrite HMx.
    replace (Ex =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    change (2^23 + 0) with 8388608.
    destruct (Ex - 1 =? 0) eqn:E0.
    + apply Z.eqb_eq in E0. change (2^23 - 1) with 8388607. cbn [SF2R cond_Zopp Z.opp].
      split. { apply F2R_ge_0. cbn. lia. }
      replace (Ex - 150) with (-149) by lia.
      apply F2R_lt. lia.
    + change (2 ^ 23 + (2 ^ 23 - 1)) with 16777215. cbn [SF2R cond_Zopp Z.opp].
      split. { apply F2R_ge_0. cbn. lia. }
      apply F2R_lt_exp; [lia|]. replace (Ex - 150 - (Ex - 1 - 150)) with 1 by lia. change (2^1) with 2. lia.
Qed.

(* [comment removed for export] *)


(* [comment removed for export] *)
Lemma finite_nonneg_cases x :
  is_finite_SF (dec x) = true -> (0 <= val x)%R ->
  (exists s, dec x = S754_zero s) \/ (exists m e, dec x = S754_finite false m e /\ (0 < val x)%R).
Proof.
  intros F V. destruct (dec x) as [s|s| |s m e] eqn:D; try discriminate.
  - left. now exists s.
  - right. destruct s.
    + exfalso. pose proof (val_finite x true m e D) as E. rewrite E in V.
      pose proof (F2R_lt_0 radix2 (Float radix2 (cond_Zopp true (Z.pos m)) e) ltac:(simpl; lia)). lra.
    + exists m, e. split; [reflexivity|]. rewrite (val_finite x false m e D). apply F2R_gt_0. simpl; lia.
Qed.

Section eval_curve_index.
  Variables X m : Z.
  Hypothesis Hm : 1 <= m <= 2^24 - 1.

  Let t := fst (fp_minmax f32 false X one32).
  Let c := if fst (fp_lt f32 t 0) then 0 else t.
  Let F := fst (fp_of_int f32 RNE false 32 m).
  Let ix := fst (fp_mul f32 RNE c F).
  Let lo := fst (fp_to_int f32 RTZ true 32 ix).
  Let s := fst (fp_add f32 RNE ix one32).
  Let p := s - 1.
  Let hi := fst (fp_to_int f32 RTZ true 32 p).

  (* [comment removed for export] *)
  Lemma clamp_props : is_finite_SF (dec c) = true /\ (0 <= val c <= 1)%R.
  Proof using t.
    pose proof (fp_min_one_cases X) as TC. cbv zeta in TC. fold t in TC.
    assert (Hone : is_finite_SF (dec one32) = true /\ (0 <= val one32 <= 1)%R).
    { rewrite dec_one, val_one. split; [reflexivity|lra]. }
    assert (Hz : is_finite_SF (dec 0) = true /\ (0 <= val 0 <= 1)%R).
    { rewrite dec_pzero, val_pzero. split; [reflexivity|lra]. }
    subst c.
    destruct TC as [Tone | (TX & NX & TCases)].
    - rewrite Tone. rewrite (fp_lt_finite one32 0) by (rewrite ?dec_one, ?dec_pzero; reflexivity).
      rewrite val_one, val_pzero. rewrite Rlt_bool_false by lra. exact Hone.
    - rewrite TX. destruct TCases as [Tinf | (TF & TV)].
      + (* [comment removed for export] *)
        replace (fst (fp_lt f32 X 0)) with true; [exact Hz|].
        unfold fp_lt, fp_compare. cbn [fst]. change (fp_decode f32 X) with (dec X). rewrite Tinf. reflexivity.
      + rewrite (fp_lt_finite X 0) by (rewrite ?dec_pzero; auto).
        rewrite val_pzero. destruct (Rlt_bool_spec (val X) 0) as [L|G].
        * exact Hz.
        * split; [exact TF| lra].
  Qed.

  Lemma F_props : is_finite_SF (dec F) = true /\ val F = IZR m /\ sign_SF (dec F) = false /\
                  exists mF eF, dec F = S754_finite false mF eF.
  Proof using Hm hi lo.
    pose proof (fp_of_int_u32_correct RNE m ltac:(lia)) as (A & B & Cs & D & E). fold F in A, B, Cs, D, E.
    repeat split; try assumption.
    destruct (dec F) as [s0|s0| |s0 m0 e0] eqn:DF; try discriminate.
    - exfalso. unfold val in B. rewrite DF in B. simpl in B. apply eq_IZR_R0 in B || (apply (eq_IZR_R0 m) in B || idtac).
      assert (IZR m = 0%R -> False) by (intros H0; apply eq_IZR in H0; lia). auto.
    - simpl in Cs. subst s0. now exists m0, e0.
  Qed.

  (* [comment removed for export] *)
  Lemma L0 : is_finite_SF (dec F) = true /\ val F = IZR m.
  Proof using Hm hi lo. pose proof F_props as (A & B & _). auto. Qed.

  Lemma ix_props : is_finite_SF (dec ix) = true /\ (0 <= val ix <= IZR m)%R /\ 0 <= ix < 2^32 /\ enc (dec ix) = ix.
  Proof using Hm hi lo.
    pose proof clamp_props as (CF & CV).
    pose proof F_props as (FF & FV & FS & (mF & eF & DF)).
    assert (Hm' : (1 <= IZR m)%R) by (apply (IZR_le 1); lia).
    destruct (finite_nonneg_cases c CF ltac:(lra)) as [(sc & Dc) | (mc & ec & Dc & Vc)].
    - (* [comment removed for export] *)
      pose proof (fp_mul_zero_l RNE c F sc Dc FF) as M. fold ix in M.
      rewrite M. unfold val. rewrite dec_enc by reflexivity. cbn [is_finite_SF SF2R].
      assert (0 <= enc (S754_zero (xorb sc (sign_SF (dec F)))) < 2^32) by (rewrite enc_unfold; destruct (xorb _ _); lia).
      repeat split; try lra; try lia; try (rewrite dec_enc by reflexivity; reflexivity).
    - assert (RB : (IZR 0 <= val c * val F <= IZR m)%R).
      { rewrite FV. split; [|nra]. apply Rmult_le_pos; lra. }
      pose proof (fp_mul_pos_correct RNE c F mc ec mF eF 0 m Dc DF RB ltac:(lia)) as MC. cbv zeta in MC. fold ix in MC.
      destruct MC as (A & Sg & B & D & E).
      repeat split; try lra; try lia; try exact A; try exact E.
  Qed.

  (* [comment removed for export] *)
  Lemma L1 : fst (fp_lt f32 K32 ix) = true.
  Proof using Hm hi lo.
    pose proof ix_props as (A & B & _).
    rewrite (fp_lt_finite K32 ix) by (rewrite ?dec_K; auto). rewrite val_K. apply Rlt_bool_true.
    apply Rlt_le_trans with 0%R; [|lra]. apply (IZR_lt _ 0). lia.
  Qed.
  Lemma L2 : fst (fp_lt f32 ix two31f) = true.
  Proof using Hm hi lo.
    pose proof ix_props as (A & B & _).
    rewrite (fp_lt_finite ix two31f) by (rewrite ?dec_two31; auto). rewrite val_two31. apply Rlt_bool_true.
    apply Rle_lt_trans with (IZR m); [lra|]. apply IZR_lt. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma L3 : 0 <= lo <= m /\ lo = Zfloor (val ix) /\ int_wrap 32 lo = lo.
  Proof using Hm hi.
    pose proof ix_props as (A & B & _).
    pose proof (fp_to_int_RTZ32_nonneg ix m A ltac:(lra) ltac:(rewrite plus_IZR; lra) ltac:(lia) ltac:(lia)) as [P Q].
    fold lo in P, Q. repeat split; try lia. rewrite int_wrap_small; lia.
  Qed.

  Lemma s_props : (exists ms es, dec s = S754_finite false ms es) /\ (1 <= val s <= IZR m + 1)%R /\
                  0 < s < 2139095040.
  Proof using Hm hi lo.
    pose proof ix_props as (A & B & _).
    assert (RB : (IZR 1 <= val ix + val one32 <= IZR (m + 1))%R).
    { rewrite val_one, plus_IZR. lra. }
    pose proof (fp_add_pos_correct RNE ix one32 1 (m + 1) A ltac:(rewrite dec_one; reflexivity) RB ltac:(lia) ltac:(lia)) as AC.
    cbv zeta in AC. fold s in AC. rewrite plus_IZR in AC.
    destruct AC as (F1 & SG & V1 & R1 & E1).
    destruct (finite_nonneg_cases s F1 ltac:(lra)) as [(ss & Ds) | (ms & es & Ds & Vs)].
    - exfalso. rewrite (val_zero s ss Ds) in V1. lra.
    - split; [now exists ms, es|]. split; [lra|].
      rewrite <- E1, Ds. apply enc_pos_finite.
      pose proof (dec_valid s) as VB. rewrite Ds in VB. exact VB.
  Qed.

  (* [comment removed for export] *)
  Lemma Ls : 0 < s < 2139095040.
  Proof using Hm hi lo. apply (proj2 (proj2 s_props)). Qed.

  Lemma p_props : is_finite_SF (dec p) = true /\ (0 <= val p < IZR m + 1)%R.
  Proof using Hm hi lo.
    pose proof s_props as (_ & SV & SR).
    pose proof (pred_pattern s SR) as (PF & PS & PV0 & PV1). fold p in PF, PS, PV0, PV1.
    repeat split; try assumption. lra.
  Qed.

  Lemma L4a : fst (fp_lt f32 K32 p) = true.
  Proof using Hm hi lo.
    pose proof p_props as (A & B).
    rewrite (fp_lt_finite K32 p) by (rewrite ?dec_K; auto). rewrite val_K. apply Rlt_bool_true.
    apply Rlt_le_trans with 0%R; [|lra]. apply (IZR_lt _ 0). lia.
  Qed.
  Lemma L4b : fst (fp_lt f32 p two31f) = true.
  Proof using Hm hi lo.
    pose proof p_props as (A & B).
    rewrite (fp_lt_finite p two31f) by (rewrite ?dec_two31; auto). rewrite val_two31. apply Rlt_bool_true.
    apply Rlt_trans with (IZR m + 1)%R; [lra|]. rewrite <- plus_IZR. apply IZR_lt. lia.
  Qed.
  Lemma L4c : 0 <= hi <= m /\ hi = Zfloor (val p) /\ int_wrap 32 hi = hi.
  Proof using Hm lo s.
    pose proof p_props as (A & B).
    pose proof (fp_to_int_RTZ32_nonneg p m A ltac:(lra) ltac:(rewrite plus_IZR; lra) ltac:(lia) ltac:(lia)) as [P Q].
    fold hi in P, Q. repeat split; try lia. rewrite int_wrap_small; lia.
  Qed.

  (* [comment removed for export] *)
End eval_curve_index.

(* [comment removed for export] *)
Theorem classify_cast_ok (g : Z) :
  fst (fp_lt f32 g 0) = true ->
  fst (fp_lt f32 g m128f) = false ->
  fst (fp_lt f32 K32 g) = true /\ fst (fp_lt f32 g two31f) = true /\
  exists v, -128 <= v <= 0 /\ fst (fp_to_int f32 RTZ true 32 g) = int_wrap 32 v /\
            (IZR v - 1 < val g <= IZR v)%R /\ is_finite_SF (dec g) = true /\ (-128 <= val g < 0)%R.
Proof.
  intros Hlt0 Hge.
  pose proof (fp_lt_true_not_nan g 0 Hlt0) as [NN _].
  destruct (dec g) as [s|s| |s mg eg] eqn:Dg.
  - exfalso. rewrite (fp_lt_finite g 0) in Hlt0 by (rewrite ?Dg, ?dec_pzero; reflexivity).
    rewrite (val_zero g s Dg), val_pzero in Hlt0. rewrite Rlt_bool_false in Hlt0 by lra. discriminate.
  - exfalso. destruct s.
    + (* [comment removed for export] *)
      unfold fp_lt, fp_compare in Hge. cbn [fst] in Hge. change (fp_decode f32 g) with (dec g) in Hge.
      rewrite Dg in Hge. change (fp_decode f32 m128f) with (dec m128f) in Hge. rewrite dec_m128 in Hge. discriminate.
    + unfold fp_lt, fp_compare in Hlt0. cbn [fst] in Hlt0. change (fp_decode f32 g) with (dec g) in Hlt0.
      rewrite Dg in Hlt0. change (fp_decode f32 0) with (dec 0) in Hlt0. rewrite dec_pzero in Hlt0. discriminate.
  - exfalso. apply NN. reflexivity.
  - assert (Fg : is_finite_SF (dec g) = true) by (rewrite Dg; reflexivity).
    rewrite (fp_lt_finite g 0) in Hlt0 by (rewrite ?dec_pzero; auto). rewrite val_pzero in Hlt0.
    rewrite (fp_lt_finite g m128f) in Hge by (rewrite ?dec_m128; auto). rewrite val_m128 in Hge.
    destruct (Rlt_bool_spec (val g) 0) as [L0|]; [|discriminate].
    destruct (Rlt_bool_spec (val g) (IZR (-128))) as [|G128]; [discriminate|].
    split. { rewrite (fp_lt_finite K32 g) by (rewrite ?dec_K; auto). rewrite val_K. apply Rlt_bool_true.
             apply Rlt_le_trans with (IZR (-128)); [apply IZR_lt; lia| lra]. }
    split. { rewrite (fp_lt_finite g two31f) by (rewrite ?dec_two31; auto). rewrite val_two31. apply Rlt_bool_true.
             apply Rlt_trans with 0%R; [lra|]. apply (IZR_lt 0). lia. }
    (* [comment removed for export] *)
    destruct s.
    2:{ exfalso. pose proof (val_finite g false mg eg Dg) as E.
        pose proof (F2R_gt_0 radix2 (Float radix2 (cond_Zopp false (Z.pos mg)) eg) ltac:(simpl; lia)). lra. }
    pose proof (Rabs_val_finite g true mg eg Dg) as RV.
    rewrite Rabs_left in RV by lra.
    set (q := Zfloor (F2R (Float radix2 (Z.pos mg) eg))).
    assert (Hq : 0 <= q <= 128).
    { subst q. rewrite RV. split.
      - rewrite <- (Zfloor_IZR 0). apply Zfloor_le. simpl; lra.
      - rewrite <- (Zfloor_IZR 128). apply Zfloor_le. lra. }
    exists (- q). split; [lia|]. split.
    + rewrite (fp_to_int_RTZ32_finite g true mg eg Dg); cbv zeta; fold q; cbn [cond_Zopp]; [reflexivity| lia].
    + pose proof (Zfloor_lb (F2R (Float radix2 (Z.pos mg) eg))) as LB.
      pose proof (Zfloor_ub (F2R (Float radix2 (Z.pos mg) eg))) as UB.
      fold q in LB, UB. rewrite RV in LB, UB. rewrite opp_IZR.
      repeat split; try lra; try exact Fg.
Qed.
