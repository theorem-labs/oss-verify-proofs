From Stdlib Require Import ZArith Bool Lia SpecFloat.
From Flocq.IEEE754 Require BinarySingleNaN.
From LinuxProcessSemantics.Riscv Require Import Fpu.
Open Scope Z_scope.

Definition F2M23 : Z := 0x34000000.
Definition F2P23 : Z := 0x4b000000.
Definition FCLAMP_HI : Z := 0x4afffffe.
Definition FCLAMP_LO : Z := 0xcb000000.

Definition nd (p : positive) : Z := Zpos (digits2_pos p).

Definition fnorm (p : positive) : positive :=
  match Z.sub (nd p) 24 with Zneg d => Pos.iter xO p d | _ => p end.

Definition sf_of (k e : Z) : spec_float :=
  match k with
  | Z0 => S754_zero false
  | Zpos p => S754_finite false (fnorm p) (e + nd p - 24)
  | Zneg p => S754_finite true (fnorm p) (e + nd p - 24)
  end.

Definition f32 (k e : Z) : Z := fp_encode fmt_single (sf_of k e).

Lemma nd_xO : forall p, nd (xO p) = nd p + 1.
Proof. intros p. unfold nd. cbn [digits2_pos]. apply Pos2Z.inj_succ. Qed.

Lemma nd_xI : forall p, nd (xI p) = nd p + 1.
Proof. intros p. unfold nd. cbn [digits2_pos]. apply Pos2Z.inj_succ. Qed.

Lemma nd_pos : forall p, 1 <= nd p.
Proof. intros p. unfold nd. lia. Qed.

Lemma nd_bounds : forall p, 2 ^ (nd p - 1) <= Zpos p < 2 ^ nd p.
Proof.
  induction p as [p IH|p IH|].
  - rewrite nd_xI, (Pos2Z.inj_xI p). pose proof (nd_pos p).
    replace (nd p + 1 - 1) with (nd p) by lia.
    assert (E1 : 2 ^ (nd p + 1) = 2 * 2 ^ nd p) by (rewrite Z.pow_add_r by lia; lia).
    assert (E2 : 2 ^ nd p = 2 * 2 ^ (nd p - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    lia.
  - rewrite nd_xO, (Pos2Z.inj_xO p). pose proof (nd_pos p).
    replace (nd p + 1 - 1) with (nd p) by lia.
    assert (E1 : 2 ^ (nd p + 1) = 2 * 2 ^ nd p) by (rewrite Z.pow_add_r by lia; lia).
    assert (E2 : 2 ^ nd p = 2 * 2 ^ (nd p - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    lia.
  - unfold nd. cbn. lia.
Qed.

Lemma nd_iter_xO : forall n p, nd (Pos.iter xO p n) = nd p + Zpos n.
Proof.
  intros n p. induction n as [|n IH] using Pos.peano_ind.
  - cbn [Pos.iter]. rewrite nd_xO. reflexivity.
  - rewrite Pos.iter_succ, nd_xO, IH, Pos2Z.inj_succ. lia.
Qed.

Lemma iter_xO_val : forall n p, Zpos (Pos.iter xO p n) = Zpos p * 2 ^ Zpos n.
Proof.
  intros n p. induction n as [|n IH] using Pos.peano_ind.
  - cbn [Pos.iter]. rewrite (Pos2Z.inj_xO p). lia.
  - rewrite Pos.iter_succ, (Pos2Z.inj_xO (Pos.iter xO p n)), IH, (Pos2Z.inj_succ n), Z.pow_succ_r by lia. lia.
Qed.

Lemma digits2_pos_size : forall p, digits2_pos p = Pos.size p.
Proof. induction p as [p IH|p IH|]; cbn; try rewrite IH; reflexivity. Qed.

Lemma nd24 : forall m, nd m = 24 -> digits2_pos m = 24%positive.
Proof. intros m H. unfold nd in H. injection H. auto. Qed.

Lemma fnorm_spec : forall p, nd p <= 24 -> Zpos (fnorm p) = Zpos p * 2 ^ (24 - nd p) /\ nd (fnorm p) = 24.
Proof.
  intros p H. unfold fnorm. destruct (nd p - 24) eqn:E.
  - replace (24 - nd p) with 0 by lia. rewrite Z.pow_0_r, Z.mul_1_r. lia.
  - lia.
  - rewrite iter_xO_val, nd_iter_xO. replace (24 - nd p) with (Zpos p0) by lia. lia.
Qed.

Lemma nd_le24 : forall p, Zpos p <= 8388608 -> nd p <= 24.
Proof.
  intros p H. pose proof (nd_bounds p) as [B _].
  assert (nd p - 1 <= 23); [|lia].
  apply (Z.pow_le_mono_r_iff 2); [lia | pose proof (nd_pos p); lia |].
  change (2 ^ 23) with 8388608. lia.
Qed.

Lemma fnorm_bounds : forall p, nd p <= 24 -> 8388608 <= Zpos (fnorm p) < 16777216.
Proof.
  intros p H. destruct (fnorm_spec p H) as [_ D]. pose proof (nd_bounds (fnorm p)) as B.
  rewrite D in B. change (2 ^ (24 - 1)) with 8388608 in B. change (2 ^ 24) with 16777216 in B. exact B.
Qed.

Lemma choice_exact : forall md s q,
  BinarySingleNaN.choice_mode (flocq_mode md) s q loc_Exact = q.
Proof. intros md s q. destruct md; reflexivity. Qed.

Lemma shr_fexp_24 : forall m e, digits2_pos m = 24%positive -> -149 <= e ->
  shr_fexp 24 128 (Zpos m) e loc_Exact = (Build_shr_record (Zpos m) false false, e).
Proof.
  intros m e H He. unfold shr_fexp. cbn [Zdigits2]. rewrite H.
  unfold SpecFloat.fexp, SpecFloat.emin.
  match goal with |- shr _ _ ?t = _ => replace t with 0 by lia end.
  reflexivity.
Qed.

Lemma shr_fexp_47 : forall m e, digits2_pos m = 24%positive -> -149 <= e + 23 ->
  shr_fexp 24 128 (Zpos (Pos.iter xO m 23)) e loc_Exact = (Build_shr_record (Zpos m) false false, e + 23).
Proof.
  intros m e H He. unfold shr_fexp. cbn [Zdigits2].
  assert (D : digits2_pos (Pos.iter xO m 23) = 47%positive).
  { apply Pos2Z.inj. pose proof (nd_iter_xO 23 m) as N. unfold nd in N. rewrite N, H. reflexivity. }
  rewrite D. unfold SpecFloat.fexp, SpecFloat.emin.
  match goal with |- shr _ _ ?t = _ => replace t with 23 by lia end.
  reflexivity.
Qed.

Lemma round_aux_24 : forall md sx m e, digits2_pos m = 24%positive -> -149 <= e <= 104 ->
  round_aux fmt_single md sx (Zpos m) e loc_Exact = (S754_finite sx m e, no_flags).
Proof.
  intros md sx m e H He. unfold round_aux. cbv zeta. cbn [fp_prec fp_emax fmt_single].
  rewrite (shr_fexp_24 m e H) by lia. cbv beta iota. cbn [loc_of_shr_record shr_m].
  rewrite choice_exact. rewrite (shr_fexp_24 m e H) by lia. cbv beta iota. cbn [shr_m].
  rewrite (proj2 (Z.leb_le e (128 - 24))) by lia. reflexivity.
Qed.

Lemma round_aux_47 : forall md sx m e, digits2_pos m = 24%positive -> -149 <= e + 23 <= 104 ->
  round_aux fmt_single md sx (Zpos (Pos.iter xO m 23)) e loc_Exact = (S754_finite sx m (e + 23), no_flags).
Proof.
  intros md sx m e H He. unfold round_aux. cbv zeta. cbn [fp_prec fp_emax fmt_single].
  rewrite (shr_fexp_47 m e H) by lia. cbv beta iota. cbn [loc_of_shr_record shr_m].
  rewrite choice_exact. rewrite (shr_fexp_24 m (e + 23) H) by lia. cbv beta iota. cbn [shr_m].
  rewrite (proj2 (Z.leb_le (e + 23) (128 - 24))) by lia. reflexivity.
Qed.

Lemma round_exact_small : forall md s p e, nd p <= 24 -> -149 <= e + nd p - 24 <= 104 ->
  round_exact fmt_single md s p e = (S754_finite s (fnorm p) (e + nd p - 24), no_flags).
Proof.
  intros md s p e H He. unfold round_exact. cbn [fp_prec fp_emax fmt_single].
  unfold SpecFloat.fexp, SpecFloat.emin.
  match goal with |- context [shl_align p e ?t] => replace t with (e + nd p - 24) by (unfold nd in *; lia) end.
  assert (S : shl_align p e (e + nd p - 24) = (fnorm p, e + nd p - 24)).
  { unfold shl_align, fnorm. replace (e + nd p - 24 - e) with (nd p - 24) by lia.
    destruct (nd p - 24) eqn:E; cbn; try reflexivity; f_equal; lia. }
  rewrite S. cbv beta iota. apply round_aux_24; [apply nd24, fnorm_spec, H | exact He].
Qed.

Lemma mul_2p23 : forall m, Pos.mul m 8388608 = Pos.iter xO m 23.
Proof. intros m. apply Pos2Z.inj. rewrite iter_xO_val, Pos2Z.inj_mul. reflexivity. Qed.

Lemma round_exact_47 : forall md s m e, digits2_pos m = 24%positive -> -149 <= e + 23 <= 104 ->
  round_exact fmt_single md s (Pos.mul m 8388608) e = (S754_finite s m (e + 23), no_flags).
Proof.
  intros md s m e H He. rewrite mul_2p23. unfold round_exact. cbn [fp_prec fp_emax fmt_single].
  assert (D : digits2_pos (Pos.iter xO m 23) = 47%positive).
  { apply Pos2Z.inj. pose proof (nd_iter_xO 23 m) as N. unfold nd in N. rewrite N, H. reflexivity. }
  rewrite D. unfold SpecFloat.fexp, SpecFloat.emin.
  match goal with |- context [shl_align _ e ?t] => replace t with (e + 23) by lia end.
  assert (S : shl_align (Pos.iter xO m 23) e (e + 23) = (Pos.iter xO m 23, e)).
  { unfold shl_align. replace (e + 23 - e) with 23 by lia. reflexivity. }
  rewrite S. cbv beta iota. apply round_aux_47; assumption.
Qed.

Lemma enc_fin : forall s m e, nd m = 24 ->
  fp_encode fmt_single (S754_finite s m e) = (if s then 2147483648 else 0) + (e + 150) * 8388608 + (Zpos m - 8388608).
Proof.
  intros s m e H. unfold fp_encode. cbv zeta. rewrite <- digits2_pos_size, (nd24 m H).
  change (fp_prec fmt_single) with 24. change (fp_mw fmt_single) with 23.
  change (fp_ew fmt_single) with 8. change (fp_emin fmt_single) with (-149).
  cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont].
  rewrite (Z.shiftl_mul_pow2 (e - -149 + 1) 23) by lia.
  change (Z.shiftl 1 (23 + 8)) with 2147483648. change (Z.shiftl 1 23) with 8388608.
  change (2 ^ 23) with 8388608. destruct s; lia.
Qed.

Lemma testbit_odd : forall a n, 0 <= n -> Z.testbit a n = Z.odd (a / 2 ^ n).
Proof.
  intros a n Hn. rewrite <- Z.bit0_odd, <- Z.shiftr_div_pow2 by lia. rewrite Z.shiftr_spec by lia. reflexivity.
Qed.

Lemma dec_fin : forall (s : bool) (E M : Z), 1 <= E <= 254 -> 0 <= M < 8388608 ->
  fp_decode fmt_single ((if s then 2147483648 else 0) + E * 8388608 + M) = S754_finite s (Z.to_pos (8388608 + M)) (E - 150) /\
  fp_is_nan fmt_single ((if s then 2147483648 else 0) + E * 8388608 + M) = false.
Proof.
  intros s E M HE HM. set (x := (if s then 2147483648 else 0) + E * 8388608 + M).
  assert (HS : Z.testbit x 31 = s).
  { rewrite testbit_odd by lia. change (2 ^ 31) with 2147483648.
    assert (Q : x / 2147483648 = if s then 1 else 0) by (unfold x; destruct s; Z.div_mod_to_equations; lia).
    rewrite Q. destruct s; reflexivity. }
  assert (HX : Z.land (Z.shiftr x 23) (Z.ones 8) = E).
  { rewrite Z.land_ones, Z.shiftr_div_pow2 by lia. change (2 ^ 23) with 8388608. change (2 ^ 8) with 256.
    unfold x; destruct s; Z.div_mod_to_equations; lia. }
  assert (HMf : Z.land x (Z.ones 23) = M).
  { rewrite Z.land_ones by lia. change (2 ^ 23) with 8388608. unfold x; destruct s; Z.div_mod_to_equations; lia. }
  unfold fp_decode, fp_is_nan, fp_sign_bit, fp_exp_field, fp_man_field.
  change (fp_mw fmt_single) with 23. change (fp_ew fmt_single) with 8. change (fp_emin fmt_single) with (-149).
  change (23 + 8) with 31. rewrite HS, HX, HMf.
  rewrite (proj2 (Z.eqb_neq E 0)) by lia. change (Z.ones 8) with 255.
  rewrite (proj2 (Z.eqb_neq E 255)) by lia. change (Z.shiftl 1 23) with 8388608.
  replace (8388608 + M) with (Zpos (Z.to_pos (8388608 + M))) by (rewrite Z2Pos.id by lia; reflexivity).
  split; [f_equal; lia | reflexivity].
Qed.

Lemma f32_dec : forall k e, -8388608 <= k <= 8388608 -> -126 <= e <= 104 ->
  fp_decode fmt_single (f32 k e) = sf_of k e /\ fp_is_nan fmt_single (f32 k e) = false.
Proof.
  intros k e Hk He. destruct k as [|p|p].
  - split; reflexivity.
  - assert (N : nd p <= 24) by (apply nd_le24; lia). pose proof (nd_pos p).
    destruct (fnorm_spec p N) as [_ D]. pose proof (fnorm_bounds p N) as B.
    unfold f32, sf_of. rewrite (enc_fin false (fnorm p) _ D).
    destruct (dec_fin false (e + nd p - 24 + 150) (Zpos (fnorm p) - 8388608) ltac:(lia) ltac:(lia)) as [Dd Dn].
    replace (8388608 + (Zpos (fnorm p) - 8388608)) with (Zpos (fnorm p)) in Dd by lia.
    split; [rewrite Dd; cbn [Z.to_pos]; f_equal; lia | exact Dn].
  - assert (N : nd p <= 24) by (apply nd_le24; lia). pose proof (nd_pos p).
    destruct (fnorm_spec p N) as [_ D]. pose proof (fnorm_bounds p N) as B.
    unfold f32, sf_of. rewrite (enc_fin true (fnorm p) _ D).
    destruct (dec_fin true (e + nd p - 24 + 150) (Zpos (fnorm p) - 8388608) ltac:(lia) ltac:(lia)) as [Dd Dn].
    replace (8388608 + (Zpos (fnorm p) - 8388608)) with (Zpos (fnorm p)) in Dd by lia.
    split; [rewrite Dd; cbn [Z.to_pos]; f_equal; lia | exact Dn].
Qed.

Lemma f32_range : forall k e, -8388608 <= k <= 8388608 -> -126 <= e <= 104 -> 0 <= f32 k e < 2 ^ 32.
Proof.
  intros k e Hk He. change (2 ^ 32) with 4294967296. destruct k as [|p|p].
  - unfold f32, sf_of. cbn. lia.
  - assert (N : nd p <= 24) by (apply nd_le24; lia). pose proof (nd_pos p).
    destruct (fnorm_spec p N) as [_ D]. pose proof (fnorm_bounds p N).
    unfold f32, sf_of. rewrite (enc_fin false (fnorm p) _ D). lia.
  - assert (N : nd p <= 24) by (apply nd_le24; lia). pose proof (nd_pos p).
    destruct (fnorm_spec p N) as [_ D]. pose proof (fnorm_bounds p N).
    unfold f32, sf_of. rewrite (enc_fin true (fnorm p) _ D). lia.
Qed.

Lemma f32_of_int : forall md k x, -8388608 <= k < 8388608 -> x mod 2 ^ 32 = k mod 2 ^ 32 ->
  fp_of_int fmt_single md true 32 x = (f32 k 0, no_flags).
Proof.
  intros md k x Hk Hx. unfold fp_of_int. cbv zeta.
  assert (Hu : int_wrap 32 x = k mod 4294967296) by (unfold int_wrap; rewrite Z.land_ones by lia; exact Hx).
  rewrite Hu.
  assert (Hn : (if andb true (Z.testbit (k mod 4294967296) (32 - 1)) then k mod 4294967296 - Z.shiftl 1 32
                else k mod 4294967296) = k).
  { change (32 - 1) with 31. change (Z.shiftl 1 32) with 4294967296. rewrite testbit_odd by lia.
    change (2 ^ 31) with 2147483648. cbn [andb].
    destruct (Z_lt_le_dec k 0).
    - assert (M : k mod 4294967296 = k + 4294967296) by (Z.div_mod_to_equations; lia).
      rewrite M. replace ((k + 4294967296) / 2147483648) with 1 by (Z.div_mod_to_equations; lia).
      cbn [Z.odd]. lia.
    - assert (M : k mod 4294967296 = k) by (apply Z.mod_small; lia).
      rewrite M. replace (k / 2147483648) with 0 by (Z.div_mod_to_equations; lia). reflexivity. }
  rewrite Hn. destruct k as [|p|p].
  - reflexivity.
  - assert (N : nd p <= 24) by (apply nd_le24; lia). pose proof (nd_pos p).
    unfold round_scaled. rewrite (round_exact_small md false p 0 N) by lia. reflexivity.
  - assert (N : nd p <= 24) by (apply nd_le24; lia). pose proof (nd_pos p).
    unfold round_scaled. rewrite (round_exact_small md true p 0 N) by lia. reflexivity.
Qed.

Lemma dec_F2M23 : fp_decode fmt_single F2M23 = S754_finite false 8388608 (-46).
Proof. vm_compute. reflexivity. Qed.
Lemma dec_F2P23 : fp_decode fmt_single F2P23 = S754_finite false 8388608 0.
Proof. vm_compute. reflexivity. Qed.
Lemma dec_HI : fp_decode fmt_single FCLAMP_HI = S754_finite false 16777214 (-1).
Proof. vm_compute. reflexivity. Qed.
Lemma dec_LO : fp_decode fmt_single FCLAMP_LO = S754_finite true 8388608 0.
Proof. vm_compute. reflexivity. Qed.
Lemma nan_consts : fp_is_nan fmt_single F2M23 = false /\ fp_is_nan fmt_single F2P23 = false /\
  fp_is_nan fmt_single FCLAMP_HI = false /\ fp_is_nan fmt_single FCLAMP_LO = false.
Proof. vm_compute. repeat split. Qed.

Lemma mul_fin : forall md a c s1 m1 e1 sc mc ec,
  fp_is_nan fmt_single a = false -> fp_is_nan fmt_single c = false ->
  fp_decode fmt_single a = S754_finite s1 m1 e1 -> fp_decode fmt_single c = S754_finite sc mc ec ->
  fp_mul fmt_single md a c = enc fmt_single (round_exact fmt_single md (xorb s1 sc) (Pos.mul m1 mc) (e1 + ec)).
Proof.
  intros md a c s1 m1 e1 sc mc ec Na Nc Da Dc. unfold fp_mul, nan_pass2. rewrite Na, Nc. cbn [orb].
  rewrite Da, Dc. reflexivity.
Qed.

Lemma f32_mul_m23 : forall md k, -8388608 <= k < 8388608 ->
  fp_mul fmt_single md (f32 k 0) F2M23 = (f32 k (-23), no_flags).
Proof.
  intros md k Hk. destruct nan_consts as (N1 & _ & _ & _).
  destruct (f32_dec k 0 ltac:(lia) ltac:(lia)) as [Dk Nk].
  destruct k as [|p|p].
  - destruct md; reflexivity.
  - assert (N : nd p <= 24) by (apply nd_le24; lia). pose proof (nd_pos p).
    destruct (fnorm_spec p N) as [_ D].
    rewrite (mul_fin md _ _ false (fnorm p) (0 + nd p - 24) false 8388608 (-46) Nk N1 Dk dec_F2M23).
    rewrite round_exact_47 by (try apply nd24; auto; lia).
    unfold enc, f32, sf_of. cbn [fst snd xorb]. do 3 f_equal. lia.
  - assert (N : nd p <= 24) by (apply nd_le24; lia). pose proof (nd_pos p).
    destruct (fnorm_spec p N) as [_ D].
    rewrite (mul_fin md _ _ true (fnorm p) (0 + nd p - 24) false 8388608 (-46) Nk N1 Dk dec_F2M23).
    rewrite round_exact_47 by (try apply nd24; auto; lia).
    unfold enc, f32, sf_of. cbn [fst snd xorb]. do 3 f_equal. lia.
Qed.

Lemma f32_mul_p23 : forall md k, -8388608 <= k < 8388608 ->
  fp_mul fmt_single md (f32 k (-23)) F2P23 = (f32 k 0, no_flags).
Proof.
  intros md k Hk. destruct nan_consts as (_ & N2 & _ & _).
  destruct (f32_dec k (-23) ltac:(lia) ltac:(lia)) as [Dk Nk].
  destruct k as [|p|p].
  - destruct md; reflexivity.
  - assert (N : nd p <= 24) by (apply nd_le24; lia). pose proof (nd_pos p).
    destruct (fnorm_spec p N) as [_ D].
    rewrite (mul_fin md _ _ false (fnorm p) (-23 + nd p - 24) false 8388608 0 Nk N2 Dk dec_F2P23).
    rewrite round_exact_47 by (try apply nd24; auto; lia).
    unfold enc, f32, sf_of. cbn [fst snd xorb]. do 3 f_equal. lia.
  - assert (N : nd p <= 24) by (apply nd_le24; lia). pose proof (nd_pos p).
    destruct (fnorm_spec p N) as [_ D].
    rewrite (mul_fin md _ _ true (fnorm p) (-23 + nd p - 24) false 8388608 0 Nk N2 Dk dec_F2P23).
    rewrite round_exact_47 by (try apply nd24; auto; lia).
    unfold enc, f32, sf_of. cbn [fst snd xorb]. do 3 f_equal. lia.
Qed.

Lemma split_exact : forall p, nd p <= 24 ->
  (if Z.leb 0 (0 + nd p - 24) then (Z.shiftl (Zpos (fnorm p)) (0 + nd p - 24), loc_Exact)
   else let '(q, r) := Z.div_eucl (Zpos (fnorm p)) (Z.shiftl 1 (Z.opp (0 + nd p - 24))) in
        (q, new_location (Z.shiftl 1 (Z.opp (0 + nd p - 24))) r)) = (Zpos p, loc_Exact).
Proof.
  intros p N. destruct (fnorm_spec p N) as [V _]. pose proof (nd_pos p).
  destruct (Z.leb_spec 0 (0 + nd p - 24)).
  - replace (0 + nd p - 24) with 0 by lia. rewrite V. replace (24 - nd p) with 0 by lia.
    rewrite Z.pow_0_r, Z.mul_1_r. reflexivity.
  - rewrite Z.shiftl_1_l. replace (Z.opp (0 + nd p - 24)) with (24 - nd p) by lia.
    assert (Dp : 0 < 2 ^ (24 - nd p)) by (apply Z.pow_pos_nonneg; lia).
    assert (E : Z.div_eucl (Zpos (fnorm p)) (2 ^ (24 - nd p)) =
                (Zpos (fnorm p) / 2 ^ (24 - nd p), Zpos (fnorm p) mod 2 ^ (24 - nd p)))
      by (unfold Z.div, Z.modulo; destruct (Z.div_eucl _ _); reflexivity).
    rewrite E, V, Z.div_mul, Z.mod_mul by lia. cbv beta iota.
    unfold new_location, new_location_even, new_location_odd.
    destruct (Z.even (2 ^ (24 - nd p))); reflexivity.
Qed.

Lemma f32_to_int : forall md k, -8388608 <= k < 8388608 ->
  fp_to_int fmt_single md true 64 (f32 k 0) = (k mod 2 ^ 64, no_flags).
Proof.
  intros md k Hk. destruct (f32_dec k 0 ltac:(lia) ltac:(lia)) as [Dk Nk].
  destruct k as [|p|p].
  - destruct md; reflexivity.
  - assert (N : nd p <= 24) by (apply nd_le24; lia).
    unfold fp_to_int. rewrite Nk, Dk. unfold sf_of. cbv zeta. rewrite (split_exact p N). cbv beta iota.
    rewrite choice_exact. unfold int_lo, int_hi. cbv beta iota. change (Z.shiftl 1 (64 - 1)) with 9223372036854775808. change (Z.opp 9223372036854775808) with (-9223372036854775808).
    rewrite (proj2 (Z.ltb_ge (Zpos p) (- 9223372036854775808))) by lia.
    rewrite (proj2 (Z.ltb_ge (9223372036854775808 - 1) (Zpos p))) by lia. cbn [orb].
    unfold int_wrap. rewrite Z.land_ones by lia. reflexivity.
  - assert (N : nd p <= 24) by (apply nd_le24; lia).
    unfold fp_to_int. rewrite Nk, Dk. unfold sf_of. cbv zeta. rewrite (split_exact p N). cbv beta iota.
    rewrite choice_exact. unfold int_lo, int_hi. cbv beta iota. change (Z.shiftl 1 (64 - 1)) with 9223372036854775808. change (Z.opp 9223372036854775808) with (-9223372036854775808).
    change (Z.opp (Zpos p)) with (Zneg p).
    rewrite (proj2 (Z.ltb_ge (Zneg p) (- 9223372036854775808))) by lia.
    rewrite (proj2 (Z.ltb_ge (9223372036854775808 - 1) (Zneg p))) by lia. cbn [orb].
    unfold int_wrap. rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma f32_lt_hi : forall k, -8388608 <= k < 8388608 ->
  fp_lt fmt_single FCLAMP_HI (f32 k 0) = (false, no_flags).
Proof.
  intros k Hk. destruct nan_consts as (_ & _ & N3 & _).
  destruct (f32_dec k 0 ltac:(lia) ltac:(lia)) as [Dk Nk].
  unfold fp_lt, fp_compare. rewrite N3, Nk, Dk, dec_HI. cbn [orb]. f_equal.
  destruct k as [|p|p]; cbn [sf_of SFcompare]; try reflexivity.
  assert (N : nd p <= 24) by (apply nd_le24; lia). pose proof (nd_pos p).
  destruct (fnorm_spec p N) as [V _]. pose proof (nd_bounds p) as [B _].
  assert (N23 : nd p - 1 < 23)
    by (apply (Z.pow_lt_mono_r_iff 2 (nd p - 1) 23); [lia | lia | change (2 ^ 23) with 8388608; lia]).
  destruct (Z.compare_spec (-1) (0 + nd p - 24)); try reflexivity.
  - change (Pos.compare_cont Eq 16777214 (fnorm p)) with (Pos.compare 16777214 (fnorm p)).
    destruct (Pos.compare_spec 16777214 (fnorm p)) as [|L|]; try reflexivity.
    exfalso. replace (24 - nd p) with 1 in V by lia. change (2 ^ 1) with 2 in V. lia.
  - lia.
Qed.

Lemma f32_lt_lo : forall k, -8388608 <= k < 8388608 ->
  fp_lt fmt_single (f32 k 0) FCLAMP_LO = (false, no_flags).
Proof.
  intros k Hk. destruct nan_consts as (_ & _ & _ & N4).
  destruct (f32_dec k 0 ltac:(lia) ltac:(lia)) as [Dk Nk].
  unfold fp_lt, fp_compare. rewrite N4, Nk, Dk, dec_LO. cbn [orb]. f_equal.
  destruct k as [|p|p]; cbn [sf_of SFcompare]; try reflexivity.
  assert (N : nd p <= 24) by (apply nd_le24; lia). pose proof (nd_pos p).
  destruct (fnorm_spec p N) as [V _]. pose proof (nd_bounds p) as [B _].
  destruct (Z.compare_spec (0 + nd p - 24) 0); try reflexivity.
  - change (Pos.compare_cont Eq (fnorm p) 8388608) with (Pos.compare (fnorm p) 8388608).
    assert (P : fnorm p = 8388608%positive).
    { apply Pos2Z.inj. rewrite V. replace (24 - nd p) with 0 by lia. replace (nd p - 1) with 23 in B by lia.
      change (2 ^ 23) with 8388608 in B. rewrite Z.pow_0_r. lia. }
    rewrite P. reflexivity.
  - lia.
Qed.
