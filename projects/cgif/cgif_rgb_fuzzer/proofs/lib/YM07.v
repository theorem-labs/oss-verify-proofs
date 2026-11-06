(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Reals Psatz SpecFloat Bool.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM00.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Local Open Scope R_scope.
Definition SFval (x : spec_float) : option R :=
match x with
| S754_zero _ => Some 0%R
| S754_finite s m e => Some (F2R (Float radix2 (cond_Zopp s (Z.pos m)) e))
| _ => None
end.

Lemma SFval_of_finite x : is_finite_SF x = true -> SFval x = Some (SF2R radix2 x).
Proof. destruct x; simpl; intros H; auto; discriminate. Qed.
Lemma Some_inj {A} (a b : A) : Some a = Some b -> a = b.
Proof. intros H. exact (f_equal (fun o => match o with Some y => y | None => a end) H). Qed.
Definition fval (f : format) (x : Z) : option R := SFval (fp_decode f x).
Definition Rep (f : format) (x : R) : Prop :=
exists m e : Z, x = F2R (Float radix2 m e) /\ (Z.abs m < 2 ^ fp_prec f)%Z /\ (fp_emin f <= e)%Z.
Section c.
Variable f : format.
Hypothesis Hf : format_ok f.
Local Abbreviation prec := (fp_prec f).
Local Abbreviation emax := (fp_emax f).
Local Abbreviation emin := (fp_emin f).
Local Abbreviation mw := (fp_mw f).
Lemma Rep_intro m e :
(Z.abs m < 2 ^ prec)%Z -> (emin <= e)%Z -> Rep f (F2R (Float radix2 m e)).
Proof. intros Hm He. exists m, e. auto. Qed.
Lemma Rep_0 : Rep f 0.
Proof.
exists 0%Z, emin. split; [symmetry; apply F2R_0|]. split; [|lia].
pose proof (prec_gt_0_f f Hf) as Hp. unfold Prec_gt_0 in Hp.
apply Z.pow_pos_nonneg; lia.
Qed.
Lemma Rep_opp x : Rep f x -> Rep f (- x).
Proof.
intros (m & e & -> & Hm & He). exists (- m)%Z, e. rewrite <- F2R_Zopp.
repeat split; auto. lia.
Qed.
Lemma Rep_abs x : Rep f x -> Rep f (Rabs x).
Proof.
intros H. unfold Rabs. destruct (Rcase_abs x); [apply Rep_opp, H|exact H].
Qed.

Lemma Rep_int n : (Z.abs n <= 2 ^ prec)%Z -> Rep f (IZR n).
Proof.
intros Hn. pose proof (prec_gt_0_f f Hf) as Hp. unfold Prec_gt_0 in Hp.
pose proof (fok_prec_emax f Hf). pose proof (emax_ge_2 f Hf).
assert (Hemin : (emin <= 0)%Z) by (unfold fp_emin in *; lia).
destruct (Z.eq_dec (Z.abs n) (2 ^ prec)) as [E|NE].
-
assert (Hn' : (n = Z.sgn n * 2 ^ (prec - 1) * 2)%Z).
{ rewrite <- Z.mul_assoc. replace (2 ^ (prec - 1) * 2)%Z with (2 ^ prec)%Z.
2:{ replace prec with (Z.succ (prec - 1)) at 1 by lia. rewrite Z.pow_succ_r; lia. }
rewrite <- E. symmetry. rewrite Z.mul_comm. apply Z.abs_sgn. }
exists (Z.sgn n * 2 ^ (prec - 1))%Z, 1%Z. split.
+ unfold F2R, Fnum, Fexp. change (bpow radix2 1) with 2. rewrite <- (mult_IZR _ 2). f_equal. exact Hn'.
+ split; [|lia]. rewrite Z.abs_mul, (Z.abs_eq (2 ^ (prec - 1))) by (apply Z.pow_nonneg; lia).
assert (2 ^ (prec - 1) < 2 ^ prec)%Z by (apply Z.pow_lt_mono_r; lia).
destruct n; cbn [Z.sgn Z.abs]; lia.
- exists n, 0%Z. split. { unfold F2R, Fnum, Fexp. simpl. ring. } lia.
Qed.
Lemma Rep_bpow e : (emin <= e)%Z -> Rep f (bpow radix2 e).
Proof.
intros He. exists 1%Z, e. split; [symmetry; apply F2R_bpow|]. split; [|exact He].
pose proof (prec_gt_0_f f Hf) as Hp. unfold Prec_gt_0 in Hp.
change (Z.abs 1) with (2 ^ 0)%Z. apply Z.pow_lt_mono_r; lia.
Qed.
Lemma Rep_int_bpow n e :
(Z.abs n < 2 ^ prec)%Z -> (emin <= e)%Z -> Rep f (IZR n * bpow radix2 e).
Proof. intros Hn He. exists n, e. auto. Qed.
Lemma fval_is_nan x r : fval f x = Some r -> fp_is_nan f x = false.
Proof.
unfold fval. rewrite (fp_is_nan_decode f Hf). destruct (fp_decode f x); simpl; congruence.
Qed.

Lemma fval_shape x r :
fval f x = Some r ->
r = 0 \/
exists (s : bool) (m : positive) (e : Z),
fp_decode f x = S754_finite s m e /\
r = F2R (Float radix2 (cond_Zopp s (Z.pos m)) e) /\
(Z.pos m < 2 ^ prec)%Z /\ (emin <= e <= emax - prec)%Z /\
((2 ^ (prec - 1) <= Z.pos m)%Z \/ e = emin).
Proof.
unfold fval. intros Hx.
pose proof (prec_eq f) as Hpq. pose proof (mw_ge_2 f Hf) as Hmw. pose proof (pow_mw_pos f Hf) as Pm.
pose proof (two_emax f Hf) as H2e. pose proof (fok_prec_emax f Hf) as Hpe. pose proof (emax_ge_2 f Hf).
pose proof (man_field_range f Hf x) as HM.
destruct (fp_decode_cases f Hf x) as [(He&HM0&E)|[(He&HM0&E)|[(He&HM0&E)|[(He&HM0&E)|(He&E)]]]];
rewrite E in Hx; cbn [SFval] in Hx; try discriminate; apply Some_inj in Hx; subst r.
- left. reflexivity.
- right. eexists _, _, _. split; [exact E|]. split; [reflexivity|].
rewrite Z2Pos.id by lia. unfold fp_emin in *.
assert (2 ^ fp_mw f < 2 ^ fp_prec f)%Z by (apply Z.pow_lt_mono_r; lia). lia.
- right. eexists _, _, _. split; [exact E|]. split; [reflexivity|].
rewrite Z2Pos.id by lia.
replace (fp_prec f - 1)%Z with (fp_mw f) by lia.
assert (2 ^ fp_prec f = 2 * 2 ^ fp_mw f)%Z.
{ replace (fp_prec f) with (Z.succ (fp_mw f)) by lia. rewrite Z.pow_succ_r; lia. }
unfold fp_emin in *. lia.
Qed.
Lemma fval_rep x r : fval f x = Some r -> Rep f r.
Proof.
intros H. destruct (fval_shape x r H) as [->|(s & m & e & _ & -> & Hm & He & _)].
- apply Rep_0.
- apply Rep_intro; [|lia]. rewrite abs_cond_Zopp. cbn [Z.abs]. exact Hm.
Qed.

Lemma fval_encode sf r :
valid_binary prec emax sf = true -> SFval sf = Some r ->
fval f (fp_encode f sf) = Some r.
Proof.
intros Hv Hs. unfold fval. rewrite (fp_decode_encode f Hf) by exact Hv. exact Hs.
Qed.
Lemma fval_neg x r : fval f x = Some r -> fval f (fp_neg f x) = Some (- r)%R.
Proof.
unfold fval. rewrite (fp_decode_neg f Hf).
destruct (fp_decode f x); cbn [SFopp SFval]; intros H; try discriminate; apply Some_inj in H; subst.
- f_equal. ring.
- f_equal. rewrite <- F2R_Zopp. destruct s; reflexivity.
Qed.

Lemma fval_sign_bit x r :
fval f x = Some r -> (r <> 0)%R -> fp_sign_bit f x = Rlt_bool r 0.
Proof.
unfold fval. intros H Hr.
rewrite <- (fp_sign_bit_decode f Hf x) by (destruct (fp_decode f x); cbn [SFval] in H; congruence).
destruct (fp_decode f x) as [s|s| |s m e]; cbn [SFval] in H; try discriminate; apply Some_inj in H; subst.
- exfalso. apply Hr. reflexivity.
- simpl. symmetry. destruct s.
+ apply Rlt_bool_true. apply F2R_lt_0. cbn. lia.
+ apply Rlt_bool_false. apply Rlt_le, F2R_gt_0. cbn. lia.
Qed.
Lemma fval_0 : fval f 0 = Some 0%R.
Proof. unfold fval. rewrite (fp_decode_0 f Hf). reflexivity. Qed.
Lemma decoded_lt_exp (m1 m2 : positive) (e1 e2 : Z) :
(Z.pos m1 < 2 ^ prec)%Z -> ((2 ^ (prec - 1) <= Z.pos m2)%Z \/ e2 = emin) -> (emin <= e1)%Z ->
(e1 < e2)%Z ->
F2R (Float radix2 (Z.pos m1) e1) < F2R (Float radix2 (Z.pos m2) e2).
Proof.
intros Hm1 Hm2 He1 Hlt.
destruct Hm2 as [Hm2| ->]; [|lia].
pose proof (prec_gt_0_f f Hf) as Hp. unfold Prec_gt_0 in Hp.
apply Rlt_le_trans with (bpow radix2 (prec + e1)).
- apply Rle_lt_trans with (Rabs (F2R (Float radix2 (Z.pos m1) e1))); [apply Rle_abs|].
apply F2R_lt_bpow. cbn [Fnum Fexp Z.abs]. replace (prec + e1 - e1)%Z with prec by lia. exact Hm1.
- apply Rle_trans with (F2R (Float radix2 (2 ^ (prec - 1)) e2)).
+ unfold F2R, Fnum, Fexp. rewrite (IZR_Zpower radix2) by lia. rewrite <- bpow_plus.
apply bpow_le. lia.
+ apply F2R_le. exact Hm2.
Qed.
Theorem fp_compare_fval a b ra rb :
fval f a = Some ra -> fval f b = Some rb ->
fp_compare f a b = Some (Rcompare ra rb).
Proof.
intros Ha Hb. unfold fp_compare.
destruct (fval_shape a ra Ha) as [Za|(sa & ma & ea & Da & Ra & Hma & Hea & Ca)];
destruct (fval_shape b rb Hb) as [Zb|(sb & mb & eb & Db & Rb & Hmb & Heb & Cb)].
-
unfold fval in Ha, Hb. subst.
destruct (fp_decode f a); cbn [SFval] in Ha; try discriminate;
destruct (fp_decode f b); cbn [SFval] in Hb; try discriminate.
+ cbn. rewrite Rcompare_Eq; reflexivity.
+ apply Some_inj in Hb. apply (eq_0_F2R radix2) in Hb. destruct s0; cbn in Hb; lia.
+ apply Some_inj in Ha. apply (eq_0_F2R radix2) in Ha. destruct s; cbn in Ha; lia.
+ apply Some_inj in Ha. apply (eq_0_F2R radix2) in Ha. destruct s; cbn in Ha; lia.
-
unfold fval in Ha. subst ra. rewrite Db.
destruct (fp_decode f a); cbn [SFval] in Ha; try discriminate.
2:{ apply Some_inj in Ha. apply (eq_0_F2R radix2) in Ha. destruct s; cbn in Ha; lia. }
cbn [SFcompare]. f_equal. subst rb. symmetry. destruct sb.
+ apply Rcompare_Gt. apply F2R_lt_0. cbn; lia.
+ apply Rcompare_Lt. apply F2R_gt_0. cbn; lia.
-
unfold fval in Hb. subst rb. rewrite Da.
destruct (fp_decode f b); cbn [SFval] in Hb; try discriminate.
2:{ apply Some_inj in Hb. apply (eq_0_F2R radix2) in Hb. destruct s; cbn in Hb; lia. }
cbn [SFcompare]. f_equal. subst ra. symmetry. destruct sa.
+ apply Rcompare_Lt. apply F2R_lt_0. cbn; lia.
+ apply Rcompare_Gt. apply F2R_gt_0. cbn; lia.
-
rewrite Da, Db. cbn [SFcompare]. f_equal. subst ra rb.
assert (Hpos : forall (m : positive) e, 0 < F2R (Float radix2 (Z.pos m) e)).
{ intros. apply F2R_gt_0. cbn. lia. }
destruct sa, sb; cbn [cond_Zopp].
+
change (Z.neg ma) with (- Z.pos ma)%Z. change (Z.neg mb) with (- Z.pos mb)%Z.
rewrite !F2R_Zopp, Rcompare_opp.
destruct (Z.compare_spec ea eb) as [->|Hlt|Hgt].
* rewrite Rcompare_F2R. change (Pos.compare_cont Eq ma mb) with (Pos.compare ma mb). cbn [Z.compare].
rewrite (Pos.compare_antisym ma mb). destruct (ma ?= mb)%positive; reflexivity.
* symmetry. apply Rcompare_Gt. apply decoded_lt_exp; auto; lia.
* symmetry. apply Rcompare_Lt. apply decoded_lt_exp; auto; lia.
+ symmetry. apply Rcompare_Lt. apply Rlt_trans with 0. apply F2R_lt_0; cbn; lia. apply Hpos.
+ symmetry. apply Rcompare_Gt. apply Rlt_trans with 0. apply F2R_lt_0; cbn; lia. apply Hpos.
+ destruct (Z.compare_spec ea eb) as [->|Hlt|Hgt].
* rewrite Rcompare_F2R. change (Pos.compare_cont Eq ma mb) with (Pos.compare ma mb). cbn [Z.compare].
reflexivity.
* symmetry. apply Rcompare_Lt. apply decoded_lt_exp; auto; lia.
* symmetry. apply Rcompare_Gt. apply decoded_lt_exp; auto; lia.
Qed.

Theorem fp_lt_fval a b ra rb :
fval f a = Some ra -> fval f b = Some rb ->
fp_lt f a b = (Rlt_bool ra rb, no_flags).
Proof.
intros Ha Hb. unfold fp_lt. rewrite (fp_compare_fval a b ra rb Ha Hb).
rewrite (fval_is_nan a ra Ha), (fval_is_nan b rb Hb). simpl.
unfold Rlt_bool. destruct (Rcompare ra rb); reflexivity.
Qed.
Theorem fp_le_fval a b ra rb :
fval f a = Some ra -> fval f b = Some rb ->
fp_le f a b = (Rle_bool ra rb, no_flags).
Proof.
intros Ha Hb. unfold fp_le. rewrite (fp_compare_fval a b ra rb Ha Hb).
rewrite (fval_is_nan a ra Ha), (fval_is_nan b rb Hb). simpl.
unfold Rle_bool. destruct (Rcompare ra rb); reflexivity.
Qed.
End c.
