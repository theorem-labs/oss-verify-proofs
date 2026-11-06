(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Reals Psatz SpecFloat Bool.
From Flocq Require Import Core.Core Calc.Bracket Calc.Round Calc.Operations IEEE754.BinarySingleNaN.
From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM00 YM07.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Local Open Scope R_scope.
Lemma F2R_shiftl (m : Z) (e k : Z) :
(0 <= k)%Z -> F2R (Float radix2 (Z.shiftl m k) (e - k)) = F2R (Float radix2 m e).
Proof.
intros Hk. rewrite Z.shiftl_mul_pow2 by exact Hk.
replace e with ((e - k) + k)%Z at 2 by lia.
symmetry. replace (2 ^ k)%Z with (radix2 ^ (e - k + k - (e - k)))%Z by (f_equal; lia).
apply (F2R_change_exp radix2). lia.
Qed.
Lemma scaled_add_correct (ma ea mb eb : Z) :
let '(m, e) := scaled_add (ma, ea) (mb, eb) in
F2R (Float radix2 m e) = (F2R (Float radix2 ma ea) + F2R (Float radix2 mb eb))%R.
Proof.
unfold scaled_add.
set (e := Z.min ea eb).
rewrite <- (F2R_shiftl ma ea (ea - e)) by lia.
rewrite <- (F2R_shiftl mb eb (eb - e)) by lia.
replace (ea - (ea - e))%Z with e by lia. replace (eb - (eb - e))%Z with e by lia.
rewrite <- F2R_plus. unfold Fplus, Falign. rewrite Z.leb_refl, Z.sub_diag, Z.pow_0_r, Z.mul_1_r.
reflexivity.
Qed.
Lemma sf_scaled_correct (sf : spec_float) r :
SFval sf = Some r ->
let '(m, e) := sf_scaled sf in F2R (Float radix2 m e) = r.
Proof.
destruct sf; cbn [SFval sf_scaled]; intros H; try discriminate; apply Some_inj in H; subst.
- apply F2R_0.
- destruct s; reflexivity.
Qed.
Lemma bpow_bracket (lo : Z) (n : nat) (x : R) :
bpow radix2 lo <= x < bpow radix2 (lo + Z.of_nat n) ->
exists k, (lo <= k < lo + Z.of_nat n)%Z /\ bpow radix2 k <= x < bpow radix2 (k + 1).
Proof.
revert lo. induction n as [|n IH]; intros lo Hx.
- simpl in Hx. rewrite Z.add_0_r in Hx. lra.
- destruct (Rlt_dec x (bpow radix2 (lo + 1))) as [Hlt|Hge].
+ exists lo. split; [lia|lra].
+ destruct (IH (lo + 1)%Z) as (k & Hk & Hb).
{ split; [lra|]. replace (lo + 1 + Z.of_nat n)%Z with (lo + Z.of_nat (S n))%Z by lia. lra. }
exists k. split; [lia|exact Hb].
Qed.
Lemma mag_exists (lo hi : Z) (x : R) :
bpow radix2 lo <= x < bpow radix2 hi ->
exists k, (lo <= k < hi)%Z /\ bpow radix2 k <= x < bpow radix2 (k + 1).
Proof.
intros Hx.
assert (Hlh : (lo < hi)%Z).
{ apply (lt_bpow radix2). lra. }
destruct (bpow_bracket lo (Z.to_nat (hi - lo)) x) as (k & Hk & Hb).
{ rewrite Z2Nat.id by lia. replace (lo + (hi - lo))%Z with hi by lia. exact Hx. }
exists k. split; [lia|exact Hb].
Qed.
Section a.
Variable f : format.
Hypothesis Hf : format_ok f.
Local Abbreviation prec := (fp_prec f).
Local Abbreviation emax := (fp_emax f).
Local Abbreviation emin := (fp_emin f).
Local Abbreviation fexp := (SpecFloat.fexp (fp_prec f) (fp_emax f)).
Lemma prec_pos : (0 < prec)%Z.
Proof. exact (prec_gt_0_f f Hf). Qed.
Lemma prec_ge_3 : (3 <= prec)%Z.
Proof. pose proof (mw_ge_2 f Hf) as H. unfold fp_mw in H. lia. Qed.
Lemma prec_lt_emax : (prec < emax)%Z.
Proof. exact (fok_prec_emax f Hf). Qed.
Lemma emin_lt : (emin < emax - prec)%Z.
Proof. pose proof prec_ge_3. pose proof prec_lt_emax. unfold fp_emin. lia. Qed.

Lemma fexp_unfold e : fexp e = Z.max (e - prec) emin.
Proof. reflexivity. Qed.
Definition Nearest (x v : R) : Prop :=
Rep f v /\ forall y, Rep f y -> Rabs (v - x) <= Rabs (y - x).
Lemma Nearest_rep x v : Nearest x v -> Rep f v.
Proof. intros [H _]; exact H. Qed.
Lemma Nearest_ge x v b : Nearest x v -> Rep f b -> b <= x -> b <= v.
Proof.
intros [_ Hn] Hb Hbx. specialize (Hn b Hb).
destruct (Rle_or_lt b v) as [H|H]; [exact H|exfalso].
rewrite (Rabs_left (v - x)) in Hn by lra. rewrite (Rabs_left1 (b - x)) in Hn by lra. lra.
Qed.
Lemma Nearest_le x v b : Nearest x v -> Rep f b -> x <= b -> v <= b.
Proof.
intros [_ Hn] Hb Hbx. specialize (Hn b Hb).
destruct (Rle_or_lt v b) as [H|H]; [exact H|exfalso].
rewrite (Rabs_right (v - x)) in Hn by lra. rewrite (Rabs_right (b - x)) in Hn by lra. lra.
Qed.
Lemma Nearest_id x v : Rep f x -> Nearest x v -> v = x.
Proof.
intros Hx [_ Hn]. specialize (Hn x Hx). replace (x - x) with 0 in Hn by ring. rewrite Rabs_R0 in Hn.
destruct (Req_dec v x) as [E|NE]; [exact E|]. exfalso.
assert (0 < Rabs (v - x)) by (apply Rabs_pos_lt; lra). lra.
Qed.

Lemma Nearest_0 v : Nearest 0 v -> v = 0.
Proof. intros H. apply Nearest_id; [apply (Rep_0 f Hf)|exact H]. Qed.
Lemma Nearest_nonneg x v : Nearest x v -> 0 <= x -> 0 <= v.
Proof. intros Hn Hx. apply (Nearest_ge x v 0 Hn (Rep_0 f Hf) Hx). Qed.

Lemma Nearest_of_rep x : Rep f x -> Nearest x x.
Proof.
intros Hx. split; [exact Hx|]. intros y _. replace (x - x) with 0 by ring. rewrite Rabs_R0. apply Rabs_pos.
Qed.
Lemma Nearest_error_pos x v lo hi :
Nearest x v -> (emin + prec - 1 <= lo)%Z ->
bpow radix2 lo <= x < bpow radix2 hi ->
Rabs (v - x) <= x * bpow radix2 (- prec).
Proof.
intros Hn Hlo Hx. pose proof prec_pos as Hp.
destruct (mag_exists lo hi x Hx) as (k & Hk & Hbk).
set (g := bpow radix2 (k + 1 - prec)).
assert (Hg : 0 < g) by apply bpow_gt_0.
set (q := Zfloor (x / g)).
pose proof (Zfloor_lb (x / g)) as L. pose proof (Zfloor_ub (x / g)) as U. fold q in L, U.
assert (Hxg : x / g < bpow radix2 prec).
{ unfold g, Rdiv. rewrite <- bpow_opp. apply Rlt_le_trans with (bpow radix2 (k + 1) * bpow radix2 (- (k + 1 - prec))).
- apply Rmult_lt_compat_r. apply bpow_gt_0. lra.
- rewrite <- bpow_plus. apply bpow_le. lia. }
assert (Hq0 : (0 <= q)%Z).
{ apply Zfloor_lub. unfold Rdiv. apply Rmult_le_pos. pose proof (bpow_ge_0 radix2 k); lra. left. apply Rinv_0_lt_compat. exact Hg. }
assert (Hqhi : (q < 2 ^ prec)%Z).
{ apply lt_IZR. rewrite (IZR_Zpower radix2) by lia. lra. }
assert (Hy1 : Rep f (IZR q * g)).
{ unfold g. apply (Rep_int_bpow f); [rewrite Z.abs_eq by lia; exact Hqhi|lia]. }
assert (Hy2 : Rep f (IZR (q + 1) * g)).
{ destruct (Z.eq_dec (q + 1) (2 ^ prec)) as [E|NE].
- rewrite E, (IZR_Zpower radix2) by lia. unfold g. rewrite <- bpow_plus. apply (Rep_bpow f Hf). lia.
- unfold g. apply (Rep_int_bpow f); [rewrite Z.abs_eq by lia; lia|lia]. }
assert (Hhalf : g <= 2 * (x * bpow radix2 (- prec))).
{ unfold g. replace (k + 1 - prec)%Z with (1 + (k + - prec))%Z by lia. rewrite !bpow_plus.
change (bpow radix2 1) with 2. apply Rmult_le_compat_l; [lra|]. apply Rmult_le_compat_r; [apply bpow_ge_0|lra]. }
assert (Hx1 : IZR q * g <= x) by (apply (Rmult_le_reg_r (/ g)); [apply Rinv_0_lt_compat, Hg|];
rewrite Rmult_assoc, Rinv_r, Rmult_1_r by lra; exact L).
assert (Hx2 : x < IZR (q + 1) * g) by (apply (Rmult_lt_reg_r (/ g)); [apply Rinv_0_lt_compat, Hg|];
rewrite Rmult_assoc, Rinv_r, Rmult_1_r by lra; rewrite plus_IZR; exact U).
destruct Hn as [_ Hn].
destruct (Rle_or_lt (x - IZR q * g) (IZR (q + 1) * g - x)) as [C|C].
- specialize (Hn _ Hy1). rewrite (Rabs_left1 (IZR q * g - x)) in Hn by lra. rewrite plus_IZR in *. lra.
- specialize (Hn _ Hy2). rewrite (Rabs_right (IZR (q + 1) * g - x)) in Hn by lra. rewrite plus_IZR in *. lra.
Qed.
Lemma Nearest_opp x v : Nearest x v -> Nearest (- x) (- v).
Proof.
intros [Hv Hn]. split; [apply (Rep_opp f), Hv|]. intros y Hy.
specialize (Hn (- y) (Rep_opp f y Hy)).
replace (- v - - x) with (- (v - x)) by ring. replace (y - - x) with (- (- y - x)) by ring.
rewrite !Rabs_Ropp. exact Hn.
Qed.
Lemma Nearest_error x v lo hi :
Nearest x v -> (emin + prec - 1 <= lo)%Z ->
bpow radix2 lo <= Rabs x < bpow radix2 hi ->
Rabs (v - x) <= Rabs x * bpow radix2 (- prec).
Proof.
intros Hn Hlo Hx. unfold Rabs in Hx |- *. destruct (Rcase_abs x).
- pose proof (Nearest_error_pos (- x) (- v) lo hi (Nearest_opp x v Hn) Hlo Hx) as H.
replace (- v - - x) with (- (v - x)) in H by ring. rewrite Rabs_Ropp in H.
unfold Rabs in H. exact H.
- pose proof (Nearest_error_pos x v lo hi Hn Hlo Hx) as H. unfold Rabs in H. exact H.
Qed.
Lemma shr_fexp_eq m e l :
shr_fexp prec emax m e l = shr (shr_record_of_loc m l) e (fexp (Zdigits radix2 m + e) - e).
Proof. unfold shr_fexp. rewrite Zdigits2_Zdigits. reflexivity. Qed.
Lemma shr_le0 mrs e n : (n <= 0)%Z -> shr mrs e n = (mrs, e).
Proof. destruct n; intros; [reflexivity|lia|reflexivity]. Qed.
Lemma snd_shr mrs e n : (0 <= n)%Z -> snd (shr mrs e n) = (e + n)%Z.
Proof. destruct n; intros; cbn [shr snd]; lia. Qed.
Lemma pow2_pos k : (0 <= k)%Z -> (0 < 2 ^ k)%Z.
Proof. intros. apply Z.pow_pos_nonneg; lia. Qed.
Lemma trunc_props mx ex lx x :
(0 <= mx)%Z -> inbetween_float radix2 mx ex x lx -> (ex <= fexp (Zdigits radix2 mx + ex))%Z ->
let '(mrs1, e1) := shr_fexp prec emax mx ex lx in
e1 = fexp (Zdigits radix2 mx + ex) /\
inbetween_float radix2 (shr_m mrs1) e1 x (loc_of_shr_record mrs1) /\
(0 <= shr_m mrs1 < 2 ^ prec)%Z /\ (emin <= e1)%Z /\
((2 ^ (prec - 1) <= shr_m mrs1)%Z \/ e1 = emin) /\
(lx = loc_Exact -> (shr_m mrs1 * 2 ^ (e1 - ex) = mx)%Z -> loc_of_shr_record mrs1 = loc_Exact).
Proof.
intros Hmx Hin Hex. rewrite shr_fexp_eq.
pose proof prec_pos as Hp.
set (d := Zdigits radix2 mx) in *. set (n := (fexp (d + ex) - ex)%Z).
assert (Hn : (0 <= n)%Z) by (unfold n; lia).
pose proof (inbetween_shr x mx ex lx n Hmx Hin) as Hsh.
pose proof (le_shr_le (shr_record_of_loc mx lx) ex n) as Hle.
rewrite shr_m_shr_record_of_loc in Hle. specialize (Hle Hmx Hn).
pose proof (snd_shr (shr_record_of_loc mx lx) ex n Hn) as He1.
destruct (shr (shr_record_of_loc mx lx) ex n) as [mrs1 e1] eqn:Hshr. cbn [fst snd] in Hle, He1.
set (m1 := shr_m mrs1) in *.
assert (He1' : e1 = fexp (d + ex)) by (unfold n in He1; lia).
rewrite fexp_unfold in He1'.
assert (Hdx : mx = 0%Z \/ (2 ^ (d - 1) <= mx < 2 ^ d)%Z).
{ destruct (Z.eq_dec mx 0) as [->|NE]; [left; reflexivity|right].
pose proof (Zdigits_correct radix2 mx) as [H1 H2]. rewrite Z.abs_eq in H1, H2 by lia.
unfold d. change (radix_val radix2) with 2%Z in H1, H2. lia. }
assert (Hd0 : (0 <= d)%Z) by (unfold d; apply Zdigits_ge_0).
pose proof (pow2_pos n Hn) as Pn. pose proof (pow2_pos prec ltac:(lia)) as Pp.
assert (Hm1_lt : (m1 < 2 ^ prec)%Z).
{ destruct Hdx as [->|[Hlo Hhi]]; [nia|].
destruct (Z.le_gt_cases n d) as [Hnd|Hnd].
- assert (Hsplit : (2 ^ d = 2 ^ n * 2 ^ (d - n))%Z).
{ rewrite <- Z.pow_add_r by lia. f_equal. lia. }
assert (m1 < 2 ^ (d - n))%Z by nia.
apply Z.lt_le_trans with (2 ^ (d - n))%Z; [assumption|]. apply Z.pow_le_mono_r; lia.
- assert (2 ^ d < 2 ^ n)%Z by (apply Z.pow_lt_mono_r; lia).
assert (m1 < 1)%Z by nia. apply Z.le_lt_trans with 0%Z; [lia|]. apply pow2_pos; lia. }
assert (Hcanon : ((2 ^ (prec - 1) <= m1)%Z \/ e1 = emin)).
{ destruct (Z.eq_dec e1 emin) as [|NE]; [right; assumption|left].
assert (He1d : (e1 = d + ex - prec)%Z) by lia.
assert (Hnd : (n = d - prec)%Z) by (unfold n; rewrite fexp_unfold; lia).
destruct Hdx as [->|[Hlo Hhi]].
{ exfalso. unfold d in Hnd. cbn in Hnd. lia. }
assert (Hsplit : (2 ^ (d - 1) = 2 ^ n * 2 ^ (prec - 1))%Z).
{ rewrite <- Z.pow_add_r by lia. f_equal. lia. }
nia. }
repeat split; try assumption; try lia.
-
intros Hlx Hval. subst lx.
replace (e1 - ex)%Z with n in Hval by lia.
assert (Hx : x = F2R (Float radix2 mx ex)) by (inversion Hin; assumption).
assert (Heq : F2R (Float radix2 mx ex) = F2R (Float radix2 m1 e1)).
{ rewrite He1. rewrite <- (F2R_shiftl m1 (ex + n) n) by lia.
rewrite Z.shiftl_mul_pow2 by lia. replace (ex + n - n)%Z with ex by lia. rewrite Hval. reflexivity. }
unfold inbetween_float in Hsh. rewrite Hx, Heq in Hsh.
destruct (loc_of_shr_record mrs1) as [|l'] eqn:El; [reflexivity|exfalso].
inversion Hsh as [|l'' Hbounds Hcmp Hl'']. lra.
Qed.
Lemma shr_fexp_id mr e1 l :
(0 <= mr < 2 ^ prec)%Z -> (emin <= e1)%Z ->
shr_fexp prec emax mr e1 l = (shr_record_of_loc mr l, e1).
Proof.
intros Hmr He1. rewrite shr_fexp_eq. apply shr_le0. rewrite fexp_unfold.
assert (Zdigits radix2 mr <= prec)%Z.
{ apply Zdigits_le_Zpower. rewrite Z.abs_eq by lia. exact (proj2 Hmr). }
lia.
Qed.
Lemma pow_prec_split : (2 ^ prec = 2 * 2 ^ (prec - 1))%Z.
Proof.
pose proof prec_pos. replace (fp_prec f) with (Z.succ (prec - 1)) at 1 by lia.
rewrite Z.pow_succ_r; lia.
Qed.
Lemma shr_fexp_carry e1 :
(emin <= e1)%Z ->
shr_fexp prec emax (2 ^ prec) e1 loc_Exact = (Build_shr_record (2 ^ (prec - 1)) false false, (e1 + 1)%Z).
Proof.
intros He1. pose proof prec_pos as Hp. rewrite shr_fexp_eq.
rewrite (Zdigits_Zpower radix2) by lia. rewrite fexp_unfold.
replace (Z.max (prec + 1 + e1 - prec) emin - e1)%Z with 1%Z by lia.
cbn [shr iter_pos shr_record_of_loc].
rewrite pow_prec_split.
destruct (2 ^ (prec - 1))%Z as [|p|p] eqn:E.
- exfalso. pose proof (pow2_pos (prec - 1) ltac:(lia)). lia.
- reflexivity.
- exfalso. pose proof (pow2_pos (prec - 1) ltac:(lia)). lia.
Qed.
Lemma choice_mode_exact m sx mx : choice_mode m sx mx loc_Exact = mx.
Proof. destruct m; reflexivity. Qed.
Lemma bounded_of_range (mz : positive) (ez : Z) :
(Z.pos mz < 2 ^ prec)%Z -> ((2 ^ (prec - 1) <= Z.pos mz)%Z \/ ez = emin) ->
(emin <= ez <= emax - prec)%Z ->
SpecFloat.bounded prec emax mz ez = true.
Proof.
intros Hlt Hcanon Hez. pose proof prec_pos.
apply (proj2 (bounded_iff f Hf mz ez)).
pose proof (proj2 (Zdigits_pos_lt_pow mz prec) Hlt).
destruct Hcanon as [Hge| ->].
- left. pose proof (proj2 (Zdigits_pos_gt_pow mz (prec - 1)) Hge). lia.
- destruct (Z.lt_ge_cases (Z.pos mz) (2 ^ (prec - 1))).
+ right. pose proof (proj2 (Zdigits_pos_lt_pow mz (prec - 1)) ltac:(assumption)). lia.
+ left. pose proof (proj2 (Zdigits_pos_gt_pow mz (prec - 1)) ltac:(lia)). lia.
Qed.
Lemma binary_overflow_valid m s :
valid_binary prec emax (binary_overflow prec emax m s) = true.
Proof.
pose proof prec_pos as Hp. pose proof emin_lt.
unfold binary_overflow. destruct (overflow_to_inf m s); [reflexivity|].
cbn [valid_binary].
assert (E : Z.pos (Z.to_pos (2 ^ prec - 1)) = (2 ^ prec - 1)%Z).
{ apply Z2Pos.id. pose proof (pow2_pos (prec - 1) ltac:(lia)). rewrite pow_prec_split. lia. }
apply bounded_of_range; rewrite ?E; try lia.
left. rewrite pow_prec_split. pose proof (pow2_pos (prec - 1) ltac:(lia)). lia.
Qed.
Lemma round_aux_cases md sx mx ex lx x :
(0 <= mx)%Z -> inbetween_float radix2 mx ex x lx -> (ex <= fexp (Zdigits radix2 mx + ex))%Z ->
exists (m1 e1 : Z) (l1 : location),
inbetween_float radix2 m1 e1 x l1 /\
(0 <= m1 < 2 ^ prec)%Z /\ (emin <= e1)%Z /\ ((2 ^ (prec - 1) <= m1)%Z \/ e1 = emin) /\
(lx = loc_Exact -> (m1 * 2 ^ (e1 - ex) = mx)%Z -> l1 = loc_Exact) /\
let mr := choice_mode (flocq_mode md) sx m1 l1 in
let nx := match l1 with loc_Exact => false | _ => true end in
let tiny := round_tiny f md sx mx ex lx in
(m1 <= mr <= m1 + 1)%Z /\
( (mr = 0%Z /\ round_aux f md sx mx ex lx = (S754_zero sx, mk_round_flags false nx nx))
\/ (exists (mz : positive) (ez : Z),
F2R (Float radix2 (Z.pos mz) ez) = F2R (Float radix2 mr e1) /\
(Z.pos mz < 2 ^ prec)%Z /\ ((2 ^ (prec - 1) <= Z.pos mz)%Z \/ ez = emin) /\ (emin <= ez)%Z /\
round_aux f md sx mx ex lx =
(if (ez <=? emax - prec)%Z
then (S754_finite sx mz ez, mk_round_flags false (nx && tiny) nx)
else (binary_overflow prec emax (flocq_mode md) sx, mk_round_flags true false true)))).
Proof.
intros Hmx Hin Hex. pose proof prec_pos as Hp.
pose proof (trunc_props mx ex lx x Hmx Hin Hex) as T.
unfold round_aux.
destruct (shr_fexp prec emax mx ex lx) as [mrs1 e1] eqn:E1.
destruct T as (He1 & Hin1 & Hm1 & Hemin & Hcanon & Hexact).
set (m1 := shr_m mrs1) in *. set (l1 := loc_of_shr_record mrs1) in *.
exists m1, e1, l1.
split; [exact Hin1|]. split; [exact Hm1|]. split; [exact Hemin|]. split; [exact Hcanon|].
split; [exact Hexact|].
cbv zeta.
set (mr := choice_mode (flocq_mode md) sx m1 l1).
pose proof (le_choice_mode_le (flocq_mode md) sx m1 l1) as Hmr. fold mr in Hmr.
split; [exact Hmr|].
destruct (Z.lt_ge_cases mr (2 ^ prec)) as [Hlt|Hge].
-
rewrite (shr_fexp_id mr e1 loc_Exact) by lia. cbn [shr_record_of_loc shr_m].
destruct mr as [|p|p] eqn:Emr.
+ left. split; reflexivity.
+ right. exists p, e1. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. reflexivity.
+ exfalso. lia.
-
assert (Emr : mr = (2 ^ prec)%Z) by lia.
rewrite Emr, (shr_fexp_carry e1) by lia. cbn [shr_m].
destruct (2 ^ (prec - 1))%Z as [|p|p] eqn:Ep.
+ exfalso. pose proof (pow2_pos (prec - 1) ltac:(lia)). lia.
+ right. exists p, (e1 + 1)%Z.
split.
{ rewrite pow_prec_split, Ep. unfold F2R, Fnum, Fexp. rewrite mult_IZR, bpow_plus.
change (bpow radix2 1) with 2. change (IZR 2) with 2. ring. }
split; [rewrite pow_prec_split; lia|]. split; [left; lia|]. split; [lia|]. reflexivity.
+ exfalso. pose proof (pow2_pos (prec - 1) ltac:(lia)). lia.
Qed.
Lemma rep_discrete m1 e1 y :
(0 <= m1)%Z -> (emin <= e1)%Z -> ((2 ^ (prec - 1) <= m1)%Z \/ e1 = emin) ->
Rep f y -> ~ (F2R (Float radix2 m1 e1) < y < F2R (Float radix2 (m1 + 1) e1)).
Proof.
intros Hm1 He1 Hcanon (my & ey & -> & Hmy & Hey) [Hlo Hhi]. pose proof prec_pos.
destruct (Z.le_gt_cases e1 ey) as [Hle|Hgt].
- rewrite (F2R_change_exp radix2 e1 my ey) in Hlo, Hhi by exact Hle.
apply lt_F2R in Hlo. apply lt_F2R in Hhi. lia.
- destruct Hcanon as [Hm1n|Heq]; [|lia].
assert (Hy : Rabs (F2R (Float radix2 my ey)) < bpow radix2 (prec + ey)).
{ apply F2R_lt_bpow. cbn [Fnum Fexp]. replace (prec + ey - ey)%Z with (fp_prec f) by lia. exact Hmy. }
assert (Hlo' : bpow radix2 (prec + ey) <= F2R (Float radix2 m1 e1)).
{ apply Rle_trans with (bpow radix2 (prec - 1 + e1)). apply bpow_le; lia.
rewrite bpow_plus. unfold F2R, Fnum, Fexp. apply Rmult_le_compat_r. apply bpow_ge_0.
rewrite <- IZR_Zpower by lia. apply IZR_le. exact Hm1n. }
apply Rabs_lt_inv in Hy. lra.
Qed.
Theorem round_aux_valid md sx mx ex lx x :
(0 <= mx)%Z -> inbetween_float radix2 mx ex x lx -> (ex <= fexp (Zdigits radix2 mx + ex))%Z ->
valid_binary prec emax (fst (round_aux f md sx mx ex lx)) = true /\
fl_nv (snd (round_aux f md sx mx ex lx)) = false /\
fl_dz (snd (round_aux f md sx mx ex lx)) = false.
Proof.
intros Hmx Hin Hex.
destruct (round_aux_cases md sx mx ex lx x Hmx Hin Hex)
as (m1 & e1 & l1 & Hin1 & Hm1 & He1 & Hcanon & _ & Hmr & Hcases).
destruct Hcases as [[Hz ->]|(mz & ez & Hval & Hmz & Hcz & Hez & ->)].
- repeat split; reflexivity.
- destruct (Z.leb_spec ez (emax - prec)) as [Hle|Hgt]; cbn [fst snd].
+ split; [|split; reflexivity]. apply bounded_of_range; auto.
+ split; [apply binary_overflow_valid|split; reflexivity].
Qed.
Lemma canonical_exp_le (mz : positive) ez :
((2 ^ (prec - 1) <= Z.pos mz)%Z \/ ez = emin) -> (emin <= ez)%Z ->
F2R (Float radix2 (Z.pos mz) ez) < bpow radix2 emax -> (ez <= emax - prec)%Z.
Proof.
intros Hcanon Hez Hlt. pose proof prec_pos. pose proof emin_lt.
destruct (Z.le_gt_cases ez (emax - prec)) as [H1|H1]; [exact H1|exfalso].
destruct Hcanon as [Hm|Heq]; [|lia].
assert (bpow radix2 emax <= F2R (Float radix2 (Z.pos mz) ez)); [|lra].
apply Rle_trans with (bpow radix2 (prec - 1 + ez)). apply bpow_le. lia.
rewrite bpow_plus. unfold F2R, Fnum, Fexp. apply Rmult_le_compat_r. apply bpow_ge_0.
rewrite <- IZR_Zpower by lia. apply IZR_le. exact Hm.
Qed.
Theorem round_aux_exact md sx mx ex :
(0 < mx)%Z -> (ex <= fexp (Zdigits radix2 mx + ex))%Z ->
Rep f (F2R (Float radix2 mx ex)) -> F2R (Float radix2 mx ex) < bpow radix2 emax ->
exists (mz : positive) (ez : Z),
round_aux f md sx mx ex loc_Exact = (S754_finite sx mz ez, no_flags) /\
SpecFloat.bounded prec emax mz ez = true /\
F2R (Float radix2 (Z.pos mz) ez) = F2R (Float radix2 mx ex).
Proof.
intros Hmx Hex Hrep Hlt.
set (x := F2R (Float radix2 mx ex)) in *.
assert (Hin : inbetween_float radix2 mx ex x loc_Exact) by (constructor; reflexivity).
destruct (round_aux_cases md sx mx ex loc_Exact x ltac:(lia) Hin Hex)
as (m1 & e1 & l1 & Hin1 & Hm1 & He1 & Hcanon & _ & Hmr & Hcases).
assert (Hl1 : l1 = loc_Exact).
{ destruct l1 as [|ord]; [reflexivity|exfalso].
apply (rep_discrete m1 e1 x); try assumption; try lia.
inversion Hin1. assumption. }
subst l1. rewrite choice_mode_exact in Hmr, Hcases.
assert (Hx1 : x = F2R (Float radix2 m1 e1)) by (inversion Hin1; assumption).
assert (Hxpos : 0 < x) by (unfold x; apply F2R_gt_0; cbn; lia).
destruct Hcases as [[Hz _]|(mz & ez & Hval & Hmz & Hcz & Hez & Hr)].
- exfalso. rewrite Hz in Hx1. rewrite F2R_0 in Hx1. lra.
- rewrite <- Hx1 in Hval.
assert (Hezle : (ez <= emax - prec)%Z).
{ apply (canonical_exp_le mz ez Hcz Hez). rewrite Hval. exact Hlt. }
rewrite (Zle_imp_le_bool _ _ Hezle) in Hr.
exists mz, ez. split; [exact Hr|]. split; [apply bounded_of_range; auto; lia|exact Hval].
Qed.
Theorem round_aux_nearest sx mx ex lx x B :
(0 <= mx)%Z -> inbetween_float radix2 mx ex x lx -> (ex <= fexp (Zdigits radix2 mx + ex))%Z ->
Rep f B -> x <= B -> B < bpow radix2 emax ->
exists v,
Nearest x v /\ 0 <= v <= B /\
SFval (fst (round_aux f RNE sx mx ex lx)) = Some (if sx then - v else v) /\
is_finite_SF (fst (round_aux f RNE sx mx ex lx)) = true.
Proof.
intros Hmx Hin Hex HB HxB HBlt. pose proof prec_pos as Hp.
destruct (round_aux_cases RNE sx mx ex lx x Hmx Hin Hex)
as (m1 & e1 & l1 & Hin1 & Hm1 & He1 & Hcanon & _ & Hmr & Hcases).
cbn [flocq_mode] in Hmr, Hcases.
set (mr := choice_mode mode_NE sx m1 l1) in *.
set (lo := F2R (Float radix2 m1 e1)). set (hi := F2R (Float radix2 (m1 + 1) e1)).
set (v := F2R (Float radix2 mr e1)).
assert (Hlohi : hi - lo = bpow radix2 e1).
{ unfold hi, lo, F2R, Fnum, Fexp. rewrite plus_IZR. simpl (IZR 1). ring. }
assert (Hlo0 : 0 <= lo) by (unfold lo; apply F2R_ge_0; cbn; lia).
assert (Hdist : (lo <= x <= hi) /\ (v = lo \/ v = hi) /\
(forall y, (y <= lo \/ hi <= y) -> Rabs (v - x) <= Rabs (y - x))).
{ unfold v, mr. destruct l1 as [|ord].
- rewrite choice_mode_exact. assert (x = lo) by (inversion Hin1; assumption). subst x.
pose proof (bpow_gt_0 radix2 e1).
split; [lra|]. split; [left; reflexivity|]. intros y Hy.
replace (F2R (Float radix2 m1 e1) - lo) with 0 by (unfold lo; ring). rewrite Rabs_R0. apply Rabs_pos.
- inversion Hin1 as [|ord' Hb Hcmp]. subst ord'. fold lo hi in Hb, Hcmp.
cbn [choice_mode cond_incr round_N].
assert (Hmid : forall y, (y <= lo \/ hi <= y) ->
(Rabs (lo - x) <= Rabs (hi - x) -> Rabs (lo - x) <= Rabs (y - x)) /\
(Rabs (hi - x) <= Rabs (lo - x) -> Rabs (hi - x) <= Rabs (y - x))).
{ intros y Hy. rewrite (Rabs_left (lo - x)) by lra. rewrite (Rabs_right (hi - x)) by lra.
destruct Hy as [Hy|Hy].
- rewrite (Rabs_left1 (y - x)) by lra. split; intros; lra.
- rewrite (Rabs_right (y - x)) by lra. split; intros; lra. }
destruct ord; cbn [round_N negb cond_incr].
+
apply Rcompare_Eq_inv in Hcmp.
assert (Rabs (lo - x) = Rabs (hi - x)).
{ rewrite (Rabs_left (lo - x)), (Rabs_right (hi - x)) by lra. lra. }
destruct (Z.even m1); cbn [negb cond_incr round_N];
first [ solve [split; [lra|]; split; [left; reflexivity|]; intros y Hy; apply (proj1 (Hmid y Hy)); lra]
| solve [split; [lra|]; split; [right; reflexivity|]; intros y Hy; apply (proj2 (Hmid y Hy)); lra] ].
+ apply Rcompare_Lt_inv in Hcmp.
split; [lra|]. split; [left; reflexivity|]. intros y Hy. apply (proj1 (Hmid y Hy)).
rewrite (Rabs_left (lo - x)), (Rabs_right (hi - x)) by lra. lra.
+ apply Rcompare_Gt_inv in Hcmp.
split; [lra|]. split; [right; reflexivity|]. intros y Hy. apply (proj2 (Hmid y Hy)).
rewrite (Rabs_left (lo - x)), (Rabs_right (hi - x)) by lra. lra. }
destruct Hdist as (Hxlohi & Hv & Hmin).
assert (Hrep_lo : Rep f lo) by (unfold lo; apply (Rep_intro f); [rewrite Z.abs_eq by lia; lia|exact He1]).
assert (Hrep_hi : Rep f hi).
{ unfold hi. destruct (Z.eq_dec (m1 + 1) (2 ^ prec)) as [E|NE].
- rewrite E. unfold F2R, Fnum, Fexp. rewrite (IZR_Zpower radix2) by lia. rewrite <- bpow_plus.
apply (Rep_bpow f Hf). lia.
- apply (Rep_intro f); [rewrite Z.abs_eq by lia; lia|exact He1]. }
assert (Hnear : Nearest x v).
{ split.
- destruct Hv as [-> | ->]; assumption.
- intros y Hy. apply Hmin.
destruct (Rle_or_lt y lo) as [|H1]; [left; assumption|].
destruct (Rle_or_lt hi y) as [|H2]; [right; assumption|].
exfalso. apply (rep_discrete m1 e1 y); try assumption; try lia. unfold lo, hi in H1, H2. lra. }
exists v. split; [exact Hnear|].
assert (Hv0 : 0 <= v) by (apply (Nearest_nonneg x v Hnear); lra).
assert (HvB : v <= B) by (apply (Nearest_le x v B Hnear HB HxB)).
split; [lra|].
destruct Hcases as [[Hz ->]|(mz & ez & Hval & Hmz & Hcz & Hez & ->)].
- cbn [fst SFval is_finite_SF]. assert (v = 0) by (unfold v; rewrite Hz; apply F2R_0).
split; [|reflexivity]. f_equal. destruct sx; lra.
- fold v in Hval.
assert (Hezle : (ez <= emax - prec)%Z).
{ apply (canonical_exp_le mz ez Hcz Hez). rewrite Hval. lra. }
rewrite (Zle_imp_le_bool _ _ Hezle). cbn [fst SFval is_finite_SF].
split; [|reflexivity]. f_equal. rewrite F2R_cond_Zopp, Hval. destruct sx; reflexivity.
Qed.
Lemma shl_align_props mx ex :
let '(mz, ez) := shl_align mx ex (fexp (Z.pos (digits2_pos mx) + ex)) in
F2R (Float radix2 (Z.pos mz) ez) = F2R (Float radix2 (Z.pos mx) ex) /\
(ez <= fexp (Zdigits radix2 (Z.pos mz) + ez))%Z.
Proof.
set (e' := fexp (Z.pos (digits2_pos mx) + ex)).
assert (Hez : (snd (shl_align mx ex e') <= ex)%Z).
{ unfold shl_align. destruct (e' - ex)%Z eqn:E; cbn [snd]; lia. }
generalize (shl_align_correct mx ex e').
destruct (shl_align mx ex e') as [mz ez]. cbn [snd] in Hez. intros [Hval Hle].
split; [symmetry; exact Hval|].
unfold e' in Hle. rewrite Zpos_digits2_pos in Hle.
rewrite (F2R_change_exp radix2 ez (Z.pos mx) ex) in Hval by exact Hez.
apply eq_F2R in Hval.
rewrite <- Hval, Zdigits_mult_Zpower by lia.
replace (Zdigits radix2 (Z.pos mx) + (ex - ez) + ez)%Z with (Zdigits radix2 (Z.pos mx) + ex)%Z by lia.
exact Hle.
Qed.
Theorem round_exact_valid md sx mx ex :
valid_binary prec emax (fst (round_exact f md sx mx ex)) = true /\
fl_nv (snd (round_exact f md sx mx ex)) = false /\
fl_dz (snd (round_exact f md sx mx ex)) = false.
Proof.
unfold round_exact. generalize (shl_align_props mx ex).
destruct (shl_align mx ex _) as [mz ez]. intros [Hval Hle].
apply (round_aux_valid md sx (Z.pos mz) ez loc_Exact (F2R (Float radix2 (Z.pos mz) ez))); [lia| |exact Hle].
constructor. reflexivity.
Qed.
Theorem round_exact_exact md sx mx ex :
let x := F2R (Float radix2 (cond_Zopp sx (Z.pos mx)) ex) in
Rep f x -> Rabs x < bpow radix2 emax ->
exists (m : positive) (e : Z),
round_exact f md sx mx ex = (S754_finite sx m e, no_flags) /\
SpecFloat.bounded prec emax m e = true /\
F2R (Float radix2 (cond_Zopp sx (Z.pos m)) e) = x.
Proof.
intros x Hrep Hlt.
assert (Hax : Rabs x = F2R (Float radix2 (Z.pos mx) ex)).
{ unfold x. rewrite <- F2R_Zabs, abs_cond_Zopp. reflexivity. }
unfold round_exact. generalize (shl_align_props mx ex).
destruct (shl_align mx ex _) as [mz ez]. intros [Hval Hle].
destruct (round_aux_exact md sx (Z.pos mz) ez ltac:(lia) Hle) as (m & e & Hr & Hb & Hv).
- rewrite Hval, <- Hax. apply (Rep_abs f). exact Hrep.
- rewrite Hval, <- Hax. exact Hlt.
- exists m, e. split; [exact Hr|]. split; [exact Hb|].
unfold x. rewrite !F2R_cond_Zopp. rewrite Hv, Hval. reflexivity.
Qed.
Theorem round_exact_nearest sx mx ex B :
let ax := F2R (Float radix2 (Z.pos mx) ex) in
Rep f B -> ax <= B -> B < bpow radix2 emax ->
exists v,
Nearest ax v /\ 0 <= v <= B /\
SFval (fst (round_exact f RNE sx mx ex)) = Some (if sx then - v else v) /\
is_finite_SF (fst (round_exact f RNE sx mx ex)) = true.
Proof.
intros ax HB Hle HBlt. unfold round_exact. generalize (shl_align_props mx ex).
destruct (shl_align mx ex _) as [mz ez]. intros [Hval Hez].
unfold ax in *. rewrite <- Hval in Hle |- *.
apply (round_aux_nearest sx (Z.pos mz) ez loc_Exact _ B); try assumption; try lia.
constructor. reflexivity.
Qed.
Theorem round_scaled_valid md sz m e :
valid_binary prec emax (fst (round_scaled f md sz (m, e))) = true /\
fl_nv (snd (round_scaled f md sz (m, e))) = false /\
fl_dz (snd (round_scaled f md sz (m, e))) = false.
Proof.
unfold round_scaled. destruct m as [|p|p]; [repeat split; reflexivity|apply round_exact_valid|apply round_exact_valid].
Qed.
Theorem round_scaled_exact md sz m e :
let x := F2R (Float radix2 m e) in
Rep f x -> Rabs x < bpow radix2 emax ->
snd (round_scaled f md sz (m, e)) = no_flags /\
valid_binary prec emax (fst (round_scaled f md sz (m, e))) = true /\
SFval (fst (round_scaled f md sz (m, e))) = Some x /\
(m = 0%Z -> fst (round_scaled f md sz (m, e)) = S754_zero sz) /\
(m <> 0%Z -> exists mr er, fst (round_scaled f md sz (m, e)) = S754_finite (m <? 0)%Z mr er).
Proof.
intros x Hrep Hlt. unfold round_scaled.
destruct m as [|p|p].
- cbn [fst snd SFval]. split; [reflexivity|]. split; [reflexivity|]. split.
+ unfold x. rewrite F2R_0. reflexivity.
+ split; [reflexivity|]. intros H; exfalso; lia.
- destruct (round_exact_exact md false p e Hrep Hlt) as (m' & e' & Hr & Hb & Hv).
rewrite Hr. cbn [fst snd SFval]. split; [reflexivity|]. split; [exact Hb|]. split.
+ f_equal. exact Hv.
+ split; [intros; exfalso; lia|]. intros _. eexists _, _. reflexivity.
- destruct (round_exact_exact md true p e Hrep Hlt) as (m' & e' & Hr & Hb & Hv).
rewrite Hr. cbn [fst snd SFval]. split; [reflexivity|]. split; [exact Hb|]. split.
+ f_equal. exact Hv.
+ split; [intros; exfalso; lia|]. intros _. eexists _, _. reflexivity.
Qed.
Theorem round_scaled_nearest sz m e B :
let x := F2R (Float radix2 m e) in
Rep f B -> Rabs x <= B -> B < bpow radix2 emax ->
exists v,
Nearest x v /\ Rabs v <= B /\
SFval (fst (round_scaled f RNE sz (m, e))) = Some v /\
is_finite_SF (fst (round_scaled f RNE sz (m, e))) = true.
Proof.
intros x HB Hle HBlt. unfold round_scaled.
destruct m as [|p|p].
- exists 0. cbn [fst SFval is_finite_SF]. unfold x. rewrite F2R_0.
split; [apply Nearest_of_rep, (Rep_0 f Hf)|]. split; [rewrite Rabs_R0; apply Rle_trans with (Rabs x); [apply Rabs_pos|exact Hle]|].
split; reflexivity.
- unfold x in *. rewrite Rabs_pos_eq in Hle by (apply F2R_ge_0; cbn; lia).
destruct (round_exact_nearest false p e B HB Hle HBlt) as (v & Hn & Hv & Hs & Hfin).
exists v. split; [exact Hn|]. split; [rewrite Rabs_pos_eq by lra; lra|]. split; [exact Hs|exact Hfin].
- unfold x in *.
assert (Hax : Rabs (F2R (Float radix2 (Z.neg p) e)) = F2R (Float radix2 (Z.pos p) e)).
{ rewrite <- F2R_Zabs. reflexivity. }
rewrite Hax in Hle.
destruct (round_exact_nearest true p e B HB Hle HBlt) as (v & Hn & Hv & Hs & Hfin).
exists (- v). split.
+ replace (F2R (Float radix2 (Z.neg p) e)) with (- F2R (Float radix2 (Z.pos p) e)).
2:{ rewrite <- F2R_Zopp. reflexivity. }
apply Nearest_opp. exact Hn.
+ split; [rewrite Rabs_Ropp, Rabs_pos_eq by lra; lra|]. split; [exact Hs|exact Hfin].
Qed.
End a.
