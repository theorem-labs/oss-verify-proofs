(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Reals Psatz SpecFloat Bool.
From Flocq Require Import Core.Core Calc.Bracket Calc.Round Calc.Operations
Calc.Div IEEE754.BinarySingleNaN.
From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM00 YM07 YM05.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section g.
Variable f : format.
Hypothesis Hf : format_ok f.
Local Abbreviation prec := (fp_prec f).
Local Abbreviation emax := (fp_emax f).
Local Abbreviation emin := (fp_emin f).
Local Abbreviation fexp := (SpecFloat.fexp (fp_prec f) (fp_emax f)).
Local Abbreviation W := (2 ^ fp_width f).
Lemma canonical_nan_range : 0 <= fp_canonical_nan f < W.
Proof.
change (fp_canonical_nan f) with (fp_encode f S754_nan).
apply (fp_encode_range f Hf). reflexivity.
Qed.
Lemma encode_zero_range s : 0 <= fp_encode f (S754_zero s) < W.
Proof. apply (fp_encode_range f Hf). reflexivity. Qed.
Lemma encode_inf_range s : 0 <= fp_encode f (S754_infinity s) < W.
Proof. apply (fp_encode_range f Hf). reflexivity. Qed.
Lemma enc_range r :
valid_binary prec emax (fst r) = true -> 0 <= fst (enc f r) < W.
Proof. intros Hv. unfold enc. cbn [fst snd]. apply (fp_encode_range f Hf). exact Hv. Qed.
Lemma round_scaled_valid' md sz v :
valid_binary prec emax (fst (round_scaled f md sz v)) = true.
Proof. destruct v as [m e]. apply (proj1 (round_scaled_valid f Hf md sz m e)). Qed.
Lemma round_exact_valid' md sx mx ex :
valid_binary prec emax (fst (round_exact f md sx mx ex)) = true.
Proof. apply (proj1 (round_exact_valid f Hf md sx mx ex)). Qed.
Lemma nan_pass2_fval a b ra rb :
fval f a = Some ra -> fval f b = Some rb -> nan_pass2 f a b = None.
Proof.
intros Ha Hb. unfold nan_pass2.
rewrite (fval_is_nan f Hf a ra Ha), (fval_is_nan f Hf b rb Hb). reflexivity.
Qed.
Lemma nan_pass3_fval a b c ra rb rc :
fval f a = Some ra -> fval f b = Some rb -> fval f c = Some rc ->
nan_pass3 f a b c = None.
Proof.
intros Ha Hb Hc. unfold nan_pass3.
rewrite (fval_is_nan f Hf a ra Ha), (fval_is_nan f Hf b rb Hb), (fval_is_nan f Hf c rc Hc).
reflexivity.
Qed.
Definition no_nv_dz (fl : fflags) : Prop := fl_nv fl = false /\ fl_dz fl = false.
Lemma no_nv_dz_no_flags : no_nv_dz no_flags.
Proof. split; reflexivity. Qed.
Definition rounds_to (md : rmode) (x : R) (r : Z * fflags) : Prop :=
no_nv_dz (snd r) /\
(md = RNE -> forall B : R, Rep f B -> (Rabs x <= B)%R -> (B < bpow radix2 emax)%R ->
exists v, fval f (fst r) = Some v /\ Nearest f x v /\ (Rabs v <= B)%R) /\
(Rep f x -> (Rabs x < bpow radix2 emax)%R -> fval f (fst r) = Some x /\ snd r = no_flags).
Lemma scaled_core_correct md sz (m e : Z) :
let r := enc f (round_scaled f md sz (m, e)) in
0 <= fst r < W /\ rounds_to md (F2R (Float radix2 m e)) r.
Proof.
intros r. split; [apply enc_range, round_scaled_valid'|].
split; [apply (round_scaled_valid f Hf)|]. split.
- intros -> B HB Hx HBlt.
destruct (round_scaled_nearest f Hf sz m e B HB Hx HBlt) as (v & Hn & Hv & Hs & _).
exists v. split; [|split; [exact Hn|exact Hv]].
unfold r, enc. cbn [fst]. apply (fval_encode f Hf); [apply round_scaled_valid'|exact Hs].
- intros Hrep Hlt.
destruct (round_scaled_exact f Hf md sz m e Hrep Hlt) as (Hfl & Hv & Hs & _).
split; [|exact Hfl].
unfold r, enc. cbn [fst]. apply (fval_encode f Hf); assumption.
Qed.
Lemma rounds_to_exact md x v :
fval f v = Some x -> rounds_to md x (v, no_flags).
Proof.
intros Hv. split; [apply no_nv_dz_no_flags|]. split.
- intros _ B HB Hx _. exists x. cbn [fst]. split; [exact Hv|]. split; [|exact Hx].
apply (Nearest_of_rep f). apply (fval_rep f Hf v). exact Hv.
- intros _ _. split; [exact Hv|reflexivity].
Qed.
Lemma F2R_prod (sa sb : bool) (ma mb : positive) (ea eb : Z) :
F2R (Float radix2 (cond_Zopp (xorb sa sb) (Z.pos (ma * mb))) (ea + eb)) =
(F2R (Float radix2 (cond_Zopp sa (Z.pos ma)) ea) *
F2R (Float radix2 (cond_Zopp sb (Z.pos mb)) eb))%R.
Proof.
rewrite <- F2R_mult. unfold Fmult. f_equal. f_equal.
destruct sa, sb; simpl; lia.
Qed.
Theorem fp_add_finite md a b ra rb :
fval f a = Some ra -> fval f b = Some rb ->
rounds_to md (ra + rb)%R (fp_add f md a b).
Proof.
intros Ha Hb. unfold fp_add. rewrite (nan_pass2_fval a b ra rb Ha Hb).
unfold fval in Ha, Hb.
pose proof (sf_scaled_correct _ _ Ha) as Sa. pose proof (sf_scaled_correct _ _ Hb) as Sb.
destruct (sf_scaled (fp_decode f a)) as [ma ea] eqn:Ea.
destruct (sf_scaled (fp_decode f b)) as [mb eb] eqn:Eb.
generalize (scaled_add_correct ma ea mb eb).
destruct (scaled_add (ma, ea) (mb, eb)) as [m e] eqn:Es. intros Hsum.
rewrite Sa, Sb in Hsum.
assert (K : forall sz, rounds_to md (ra + rb)%R (enc f (round_scaled f md sz (m, e)))).
{ intros sz. rewrite <- Hsum. apply (proj2 (scaled_core_correct md sz m e)). }
destruct (fp_decode f a) as [sa|sa| |sa pa xa]; try discriminate;
destruct (fp_decode f b) as [sb|sb| |sb pb xb]; try discriminate; apply K.
Qed.
Theorem fp_add_range md a b : 0 <= fst (fp_add f md a b) < W.
Proof.
unfold fp_add. destruct (nan_pass2 f a b) as [r|] eqn:En.
{ unfold nan_pass2 in En. destruct (_ || _)%bool; inversion En. simpl. apply canonical_nan_range. }
destruct (fp_decode f a) as [sa|sa| |sa pa xa]; destruct (fp_decode f b) as [sb|sb| |sb pb xb];
try (apply enc_range; apply round_scaled_valid');
try apply encode_inf_range; simpl.
destruct (Bool.eqb sa sb); [apply encode_inf_range | apply canonical_nan_range].
Qed.
Theorem fp_sub_finite md a b ra rb :
fval f a = Some ra -> fval f b = Some rb ->
rounds_to md (ra - rb)%R (fp_sub f md a b).
Proof.
intros Ha Hb. unfold fp_sub, Rminus.
apply fp_add_finite; [exact Ha|]. apply (fval_neg f Hf). exact Hb.
Qed.
Theorem fp_sub_range md a b : 0 <= fst (fp_sub f md a b) < W.
Proof. unfold fp_sub. apply fp_add_range. Qed.
Lemma round_exact_rounds_to md sx mx ex :
rounds_to md (F2R (Float radix2 (cond_Zopp sx (Z.pos mx)) ex)) (enc f (round_exact f md sx mx ex)).
Proof.
split; [apply (round_exact_valid f Hf)|]. split.
- intros -> B HB Hx HBlt.
rewrite <- F2R_Zabs, abs_cond_Zopp in Hx. cbn [Z.abs] in Hx.
destruct (round_exact_nearest f Hf sx mx ex B HB Hx HBlt) as (v & Hn & Hv & Hs & _).
exists (if sx then (- v)%R else v). split; [|split].
+ unfold enc. cbn [fst]. apply (fval_encode f Hf); [apply round_exact_valid'|exact Hs].
+ destruct sx.
* cbn [cond_Zopp]. change (Z.neg mx) with (- Z.pos mx)%Z. rewrite F2R_Zopp. apply (Nearest_opp f). exact Hn.
* exact Hn.
+ destruct sx; [rewrite Rabs_Ropp|]; rewrite Rabs_pos_eq by lra; lra.
- intros Hrep Hlt.
destruct (round_exact_exact f Hf md sx mx ex Hrep Hlt) as (m' & e' & Hr & Hb' & Hv').
rewrite Hr. unfold enc; cbn [fst snd]. split; [|reflexivity].
apply (fval_encode f Hf); [exact Hb'|]. cbn [SFval]. rewrite Hv'. reflexivity.
Qed.
Theorem fp_mul_finite md a b ra rb :
fval f a = Some ra -> fval f b = Some rb ->
rounds_to md (ra * rb)%R (fp_mul f md a b).
Proof.
intros Ha Hb. unfold fp_mul. rewrite (nan_pass2_fval a b ra rb Ha Hb).
unfold fval in Ha, Hb.
assert (Z0 : forall s, fval f (fp_encode f (S754_zero s)) = Some 0%R).
{ intros s. apply (fval_encode f Hf); reflexivity. }
destruct (fp_decode f a) as [sa|sa| |sa pa xa]; try discriminate;
destruct (fp_decode f b) as [sb|sb| |sb pb xb]; try discriminate;
cbn [SFval] in Ha, Hb; apply Some_inj in Ha; apply Some_inj in Hb; subst; cbn [sf_sign].
- rewrite Rmult_0_l. apply rounds_to_exact. apply Z0.
- rewrite Rmult_0_l. apply rounds_to_exact. apply Z0.
- rewrite Rmult_0_r. apply rounds_to_exact. apply Z0.
- rewrite <- F2R_prod. apply round_exact_rounds_to.
Qed.
Theorem fp_mul_range md a b : 0 <= fst (fp_mul f md a b) < W.
Proof.
unfold fp_mul. destruct (nan_pass2 f a b) as [r|] eqn:En.
{ unfold nan_pass2 in En. destruct (_ || _)%bool; inversion En. simpl. apply canonical_nan_range. }
destruct (fp_decode f a) as [sa|sa| |sa pa xa]; destruct (fp_decode f b) as [sb|sb| |sb pb xb]; simpl;
try apply encode_inf_range; try apply encode_zero_range; try apply canonical_nan_range.
apply enc_range. apply round_exact_valid'.
Qed.
Lemma new_location_SpecFloat d r :
SpecFloat.new_location d r = Bracket.new_location d r loc_Exact.
Proof.
unfold SpecFloat.new_location, Bracket.new_location,
SpecFloat.new_location_even, Bracket.new_location_even,
SpecFloat.new_location_odd, Bracket.new_location_odd.
destruct (Z.even d); destruct (r =? 0); try reflexivity;
destruct (_ ?= _); reflexivity.
Qed.

Lemma div_core_props (ma mb : positive) (ea eb : Z) :
let '(mz, ez, lz) := SFdiv_core_binary prec emax (Z.pos ma) ea (Z.pos mb) eb in
0 <= mz /\
inbetween_float radix2 mz ez (F2R (Float radix2 (Z.pos ma) ea) / F2R (Float radix2 (Z.pos mb) eb)) lz /\
ez <= fexp (Zdigits radix2 mz + ez).
Proof.
unfold SFdiv_core_binary. rewrite !Zdigits2_Zdigits.
set (d1 := Zdigits radix2 (Z.pos ma)). set (d2 := Zdigits radix2 (Z.pos mb)).
set (e' := Z.min (fexp (d1 + ea - (d2 + eb))) (ea - eb)).
set (s := ea - eb - e').
assert (Hs : 0 <= s) by (unfold s, e'; lia).
assert (He' : e' <= fexp (d1 + ea - (d2 + eb))) by (unfold e'; lia).
set (m' := match s with 0 => Z.pos ma | Z.pos _ => Z.shiftl (Z.pos ma) s | Z.neg _ => 0 end).
assert (Hm' : m' = Z.pos ma * 2 ^ s).
{ unfold m'. destruct s as [|p|p]; [lia| |lia]. apply Z.shiftl_mul_pow2. lia. }
clearbody m'. subst m'.
generalize (Fdiv_core_correct radix2 (Z.pos ma) ea (Z.pos mb) eb e' eq_refl eq_refl).
unfold Fdiv_core. rewrite (Zle_imp_le_bool e' (ea - eb)) by (unfold e'; lia).
replace (Zpower radix2 (ea - eb - e')) with (2 ^ s) by reflexivity.
rewrite (Zaux.Zdiv_eucl_unique (Z.pos ma * 2 ^ s) (Z.pos mb)).
set (q := Z.pos ma * 2 ^ s / Z.pos mb). set (r := (Z.pos ma * 2 ^ s) mod (Z.pos mb)).
intros Hin. rewrite <- new_location_SpecFloat in Hin.
pose proof (pow2_pos s Hs) as Ps.
assert (Hq0 : 0 <= q) by (unfold q; apply Z.div_pos; lia).
split; [exact Hq0|]. split; [exact Hin|].
pose proof (Zdigits_correct radix2 (Z.pos ma)) as Da. pose proof (Zdigits_correct radix2 (Z.pos mb)) as Db.
cbn [Z.abs] in Da, Db. fold d1 in Da. fold d2 in Db. change (radix_val radix2) with 2 in Da, Db.
clearbody e'. clear Hin r.
set (D := d1 + ea - (d2 + eb)) in *.
assert (Hd1 : 0 < d1) by (unfold d1; apply Zdigits_gt_0; lia).
assert (Hd2 : 0 < d2) by (unfold d2; apply Zdigits_gt_0; lia).
rewrite (fexp_unfold f) in He' |- *.
destruct (Z.eq_dec q 0) as [Hqz|Hqnz].
-
rewrite Hqz. cbn [Zdigits].
assert (Hlt : Z.pos ma * 2 ^ s < Z.pos mb).
{ destruct (Z.lt_ge_cases (Z.pos ma * 2 ^ s) (Z.pos mb)) as [H|H]; [exact H|exfalso].
assert (1 <= q); [|lia]. unfold q. apply Z.div_le_lower_bound; lia. }
assert (Hds : d1 - 1 + s < d2).
{ apply (Z.pow_lt_mono_r_iff 2); try lia. rewrite Z.pow_add_r by lia. nia. }
unfold s in Hds. lia.
-
assert (Hq1 : 1 <= q) by lia.
destruct (Z.le_gt_cases (D - e') 0) as [HD|HD].
+ pose proof (Zdigits_gt_0 radix2 q ltac:(lia)). lia.
+
set (k := D - 1 - e') in *.
assert (Hk : 0 <= k) by lia.
assert (Hqk : 2 ^ k <= q).
{ unfold q. apply Z.div_le_lower_bound; [lia|].
apply Z.le_trans with (2 ^ d2 * 2 ^ k).
- apply Z.mul_le_mono_nonneg_r; [apply Z.pow_nonneg; lia|lia].
- rewrite <- Z.pow_add_r by lia.
apply Z.le_trans with (2 ^ (d1 - 1) * 2 ^ s); [|nia].
rewrite <- Z.pow_add_r by lia. apply Z.pow_le_mono_r; [lia|]. unfold k, D, s. lia. }
assert (Hdq : k < Zdigits radix2 q).
{ apply Zdigits_gt_Zpower. rewrite Z.abs_eq by lia. exact Hqk. }
lia.
Qed.
Theorem fp_div_finite md a b ra rb :
fval f a = Some ra -> fval f b = Some rb -> rb <> 0%R ->
no_nv_dz (snd (fp_div f md a b)) /\
(md = RNE -> forall B : R, Rep f B -> (Rabs (ra / rb) <= B)%R -> (B < bpow radix2 emax)%R ->
exists v, fval f (fst (fp_div f md a b)) = Some v /\ Nearest f (ra / rb) v /\ (Rabs v <= B)%R).
Proof.
intros Ha Hb Hbnz. unfold fp_div. rewrite (nan_pass2_fval a b ra rb Ha Hb).
unfold fval in Ha, Hb.
assert (Z0 : forall s, fval f (fp_encode f (S754_zero s)) = Some 0%R).
{ intros s. apply (fval_encode f Hf); reflexivity. }
destruct (fp_decode f a) as [sa|sa| |sa pa xa]; try discriminate;
destruct (fp_decode f b) as [sb|sb| |sb pb xb]; try discriminate;
cbn [SFval] in Ha, Hb; apply Some_inj in Ha; apply Some_inj in Hb; subst; try (exfalso; apply Hbnz; reflexivity).
-
cbn [fst snd sf_sign]. split; [apply no_nv_dz_no_flags|].
intros _ B HB Hx _. exists 0%R. split; [apply Z0|].
unfold Rdiv. rewrite Rmult_0_l. split; [apply (Nearest_of_rep f), (Rep_0 f Hf)|].
rewrite Rabs_R0. eapply Rle_trans; [apply Rabs_pos|exact Hx].
-
generalize (div_core_props pa pb xa xb).
destruct (SFdiv_core_binary prec emax (Z.pos pa) xa (Z.pos pb) xb) as [[mz ez] lz].
intros (Hmz & Hin & Hez).
set (q := (F2R (Float radix2 (Z.pos pa) xa) / F2R (Float radix2 (Z.pos pb) xb))%R) in *.
assert (Hq : (F2R (Float radix2 (cond_Zopp sa (Z.pos pa)) xa) / F2R (Float radix2 (cond_Zopp sb (Z.pos pb)) xb))%R
= (if xorb sa sb then - q else q)%R).
{ unfold q. rewrite !F2R_cond_Zopp.
assert (F2R (Float radix2 (Z.pos pb) xb) <> 0)%R.
{ apply Rgt_not_eq. apply F2R_gt_0. cbn. lia. }
destruct sa, sb; cbn [xorb cond_Ropp]; field; exact H. }
assert (Hqpos : (0 < q)%R).
{ unfold q. apply Rdiv_lt_0_compat; apply F2R_gt_0; cbn; lia. }
split.
+ destruct (round_aux_valid f Hf md (xorb sa sb) mz ez lz q Hmz Hin Hez) as (_ & H1 & H2).
unfold enc. cbn [snd]. split; assumption.
+ intros -> B HB Hx HBlt. rewrite Hq in Hx |- *.
assert (HqB : (q <= B)%R).
{ destruct (xorb sa sb); [rewrite Rabs_Ropp in Hx|]; rewrite Rabs_pos_eq in Hx by lra; exact Hx. }
destruct (round_aux_nearest f Hf (xorb sa sb) mz ez lz q B Hmz Hin Hez HB HqB HBlt) as (v & Hn & Hv & Hs & _).
exists (if xorb sa sb then (- v)%R else v). split; [|split].
* unfold enc. cbn [fst]. apply (fval_encode f Hf); [|exact Hs].
apply (proj1 (round_aux_valid f Hf RNE (xorb sa sb) mz ez lz q Hmz Hin Hez)).
* destruct (xorb sa sb); [apply (Nearest_opp f); exact Hn|exact Hn].
* destruct (xorb sa sb); [rewrite Rabs_Ropp|]; rewrite Rabs_pos_eq by lra; lra.
Qed.
Theorem fp_div_range md a b : 0 <= fst (fp_div f md a b) < W.
Proof.
unfold fp_div. destruct (nan_pass2 f a b) as [r|] eqn:En.
{ unfold nan_pass2 in En. destruct (_ || _)%bool; inversion En. simpl. apply canonical_nan_range. }
destruct (fp_decode f a) as [sa|sa| |sa pa xa]; destruct (fp_decode f b) as [sb|sb| |sb pb xb]; simpl;
try apply encode_inf_range; try apply encode_zero_range; try apply canonical_nan_range.
generalize (div_core_props pa pb xa xb).
destruct (SFdiv_core_binary prec emax (Z.pos pa) xa (Z.pos pb) xb) as [[mz ez] lz].
intros (Hmz & Hin & Hez). apply enc_range.
apply (proj1 (round_aux_valid f Hf md (xorb sa sb) mz ez lz _ Hmz Hin Hez)).
Qed.
Theorem fp_fma_finite md a b c ra rb rc :
fval f a = Some ra -> fval f b = Some rb -> fval f c = Some rc ->
rounds_to md (ra * rb + rc)%R (fp_fma f md a b c).
Proof.
intros Ha Hb Hc. unfold fp_fma.
rewrite (nan_pass3_fval a b c ra rb rc Ha Hb Hc).
rewrite (fval_is_nan f Hf a ra Ha), (fval_is_nan f Hf b rb Hb).
unfold fval in Ha, Hb, Hc.
pose proof (sf_scaled_correct _ _ Hc) as Sc.
assert (KZ : forall sz, (ra * rb = 0)%R ->
rounds_to md (ra * rb + rc)%R (enc f (round_scaled f md sz (sf_scaled (fp_decode f c))))).
{ intros sz Hz. rewrite Hz, Rplus_0_l.
destruct (sf_scaled (fp_decode f c)) as [mc ec]. rewrite <- Sc.
apply (proj2 (scaled_core_correct md sz mc ec)). }
destruct (fp_decode f a) as [sa|sa| |sa pa xa]; try discriminate;
destruct (fp_decode f b) as [sb|sb| |sb pb xb]; try discriminate;
cbn [SFval] in Ha, Hb; apply Some_inj in Ha; apply Some_inj in Hb; subst; cbn [andb negb orb].
- destruct (fp_decode f c); try discriminate; apply KZ; ring.
- destruct (fp_decode f c); try discriminate; apply KZ; ring.
- destruct (fp_decode f c); try discriminate; apply KZ; ring.
-
set (prod := ((if xorb sa sb then - Z.pos (pa * pb) else Z.pos (pa * pb)), xa + xb)).
set (ra := F2R (Float radix2 (cond_Zopp sa (Z.pos pa)) xa)) in *.
set (rb := F2R (Float radix2 (cond_Zopp sb (Z.pos pb)) xb)) in *.
assert (KF : forall sz,
rounds_to md (ra * rb + rc)%R (enc f (round_scaled f md sz (scaled_add prod (sf_scaled (fp_decode f c)))))).
{ intros sz.
destruct (sf_scaled (fp_decode f c)) as [mc ec].
generalize (scaled_add_correct (fst prod) (snd prod) mc ec).
unfold prod. cbn [fst snd].
destruct (scaled_add _ _) as [m e]. intros Hsum.
rewrite Sc in Hsum.
change (if xorb sa sb then - Z.pos (pa * pb) else Z.pos (pa * pb))
with (cond_Zopp (xorb sa sb) (Z.pos (pa * pb))) in Hsum.
rewrite F2R_prod in Hsum. fold ra rb in Hsum. rewrite <- Hsum.
apply (proj2 (scaled_core_correct md sz m e)). }
destruct (fp_decode f c); try discriminate; apply KF.
Qed.
Theorem fp_fma_range md a b c : 0 <= fst (fp_fma f md a b c) < W.
Proof.
unfold fp_fma.
destruct (_ && _)%bool; [apply canonical_nan_range|].
destruct (nan_pass3 f a b c) as [r|] eqn:En.
{ unfold nan_pass3 in En. destruct (_ || _)%bool; inversion En. simpl. apply canonical_nan_range. }
destruct (fp_decode f a) as [sa|sa| |sa pa xa]; destruct (fp_decode f b) as [sb|sb| |sb pb xb];
destruct (fp_decode f c) as [sc|sc| |sc pc xc]; cbn [sf_sign];
try apply encode_inf_range; try apply canonical_nan_range;
try (apply enc_range; apply round_scaled_valid');
try (destruct (Bool.eqb _ _); [apply encode_inf_range|apply canonical_nan_range]).
Qed.
Definition int_val (signed : bool) (bits v : Z) : Z :=
let u := int_wrap bits v in
if andb signed (Z.testbit u (bits - 1)) then u - Z.shiftl 1 bits else u.
Lemma F2R_int (n : Z) : F2R (Float radix2 n 0) = IZR n.
Proof. unfold F2R. simpl. ring. Qed.
Theorem fp_of_int_finite md signed bits v :
rounds_to md (IZR (int_val signed bits v)) (fp_of_int f md signed bits v).
Proof.
unfold fp_of_int. change (if (signed && _)%bool then _ else _) with (int_val signed bits v).
rewrite <- F2R_int. apply (proj2 (scaled_core_correct md false _ 0)).
Qed.
Theorem fp_of_int_range md signed bits v : 0 <= fst (fp_of_int f md signed bits v) < W.
Proof. unfold fp_of_int. apply enc_range. apply round_scaled_valid'. Qed.
Lemma inbetween_float_0_int q x l :
inbetween_float radix2 q 0 x l -> inbetween_int q x l.
Proof. unfold inbetween_float, inbetween_int. rewrite !F2R_int. exact (fun H => H). Qed.
Lemma int_wrap_0 bits : int_wrap bits 0 = 0.
Proof. unfold int_wrap. apply Z.land_0_l. Qed.
Theorem fp_to_int_finite md signed bits a ra :
fval f a = Some ra ->
let n := round_mode (flocq_mode md) ra in
int_lo signed bits <= n <= int_hi signed bits ->
fst (fp_to_int f md signed bits a) = int_wrap bits n /\
fl_nv (snd (fp_to_int f md signed bits a)) = false /\
(IZR n = ra -> snd (fp_to_int f md signed bits a) = no_flags).
Proof.
intros Ha n Hrange. unfold fp_to_int.
rewrite (fval_is_nan f Hf a ra Ha). unfold fval in Ha.
destruct (fp_decode f a) as [sa|sa| |sa pa xa] eqn:Da; try discriminate; cbn [SFval] in Ha; apply Some_inj in Ha.
- subst. assert (Hn : n = 0) by (unfold n; apply Zrnd_IZR, valid_rnd_round_mode).
rewrite Hn, int_wrap_0. repeat split; reflexivity.
- subst ra.
set (x := F2R (Float radix2 (cond_Zopp sa (Z.pos pa)) xa)) in *.
assert (Hs : Rlt_bool x 0 = sa).
{ unfold x. destruct sa.
- apply Rlt_bool_true. apply F2R_lt_0. cbn. lia.
- apply Rlt_bool_false. apply Rlt_le, F2R_gt_0. cbn. lia. }
assert (Habs : Rabs x = F2R (Float radix2 (Z.pos pa) xa)).
{ unfold x. rewrite <- F2R_Zabs, abs_cond_Zopp. reflexivity. }
assert (K : forall q l, inbetween_int q (Rabs x) l ->
let q' := choice_mode (flocq_mode md) sa q l in
let v := if sa then - q' else q' in
v = n /\ (IZR n = x -> l = loc_Exact)).
{ intros q l Hql q' v.
assert (Hv : v = n).
{ unfold v, q', n. rewrite (round_mode_choice_mode (flocq_mode md) x q l Hql), Hs.
destruct sa; reflexivity. }
split; [exact Hv|]. intros Hint.
assert (Hax : Rabs x = IZR (Z.abs n)) by (rewrite <- Hint, <- abs_IZR; reflexivity).
destruct l as [|cmp]; [reflexivity|]. exfalso.
apply inbetween_bounds_not_Eq in Hql. 2: discriminate.
rewrite Hax in Hql. destruct Hql as [H1 H2].
apply lt_IZR in H1. apply lt_IZR in H2. lia. }
destruct (Z.leb_spec 0 xa) as [Hxa|Hxa].
+ assert (Hql : inbetween_int (Z.shiftl (Z.pos pa) xa) (Rabs x) loc_Exact).
{ apply inbetween_Exact. rewrite Habs, Z.shiftl_mul_pow2 by lia.
unfold F2R. cbn [Fnum Fexp]. rewrite mult_IZR.
replace (IZR (2 ^ xa)) with (bpow radix2 xa) by (symmetry; apply (IZR_Zpower radix2); lia).
reflexivity. }
destruct (K _ _ Hql) as [Hv Hex].
cbv zeta in Hv. rewrite Hv.
replace ((n <? int_lo signed bits) || (int_hi signed bits <? n))%bool with false.
2:{ symmetry. apply Bool.orb_false_intro; apply Z.ltb_ge; lia. }
cbn [fst snd]. repeat split; reflexivity.
+ set (d := Z.shiftl 1 (- xa)).
assert (Hd : d = 2 ^ (- xa)) by (unfold d; rewrite Z.shiftl_mul_pow2 by lia; lia).
rewrite (Zaux.Zdiv_eucl_unique (Z.pos pa) d).
assert (Hql : inbetween_int (Z.pos pa / d) (Rabs x) (SpecFloat.new_location d (Z.pos pa mod d))).
{ rewrite new_location_SpecFloat, Hd. apply inbetween_float_0_int.
replace 0 with (xa + (- xa)) by lia.
change 2 with (radix_val radix2).
apply inbetween_float_new_location; [lia|].
apply inbetween_Exact. exact Habs. }
destruct (K _ _ Hql) as [Hv Hex].
cbv zeta in Hv. rewrite Hv.
replace ((n <? int_lo signed bits) || (int_hi signed bits <? n))%bool with false.
2:{ symmetry. apply Bool.orb_false_intro; apply Z.ltb_ge; lia. }
cbn [fst snd]. split; [reflexivity|]. split.
* destruct (SpecFloat.new_location _ _); reflexivity.
* intros Hint. rewrite (Hex Hint). reflexivity.
Qed.
End g.
Section h.
Variables fs fd : format.
Hypothesis Hfs : format_ok fs.
Hypothesis Hfd : format_ok fd.


End h.
