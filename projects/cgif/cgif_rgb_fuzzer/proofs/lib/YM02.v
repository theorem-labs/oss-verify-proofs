(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Reals Psatz SpecFloat Bool List.
From Flocq Require Import Core.Core Calc.Bracket Calc.Round Calc.Operations
IEEE754.BinarySingleNaN.
From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM00 YM07 YM05 YM04 YM01.
Unset Lia Cache. Unset Nia Cache.
Local Abbreviation D := fmt_double.
Local Abbreviation S := fmt_single.
Local Open Scope Z_scope.
Local Open Scope R_scope.
Definition C2p52  : Z := 4841369599423283200.
Definition Chalf  : Z := 4602678819172646912.
Definition Cmhalf : Z := 13826050856027422720.
Definition Cone   : Z := 4607182418800017408.
Definition Cm1    : Z := 13830554455654793216.
Definition C256   : Z := 4643211215818981376.
Definition C09    : Z := 4606281698874543309.
Definition S255   : Z := 1132396544.
Definition Slo    : Z := 3472883713.
Definition Shi    : Z := 1325400064.
Definition c09 : R := IZR 8106479329266893 * bpow radix2 (-53).
Ltac val_const :=
unfold is_intd, is_ints, dval, sval, fval;
match goal with
| |- SFval (fp_decode ?f ?x) = Some _ /\ _ => split; [|simpl; lia]
| _ => idtac
end;
match goal with
| |- SFval (fp_decode ?f ?x) = Some _ =>
let d := eval vm_compute in (fp_decode f x) in change (fp_decode f x) with d
end;
simpl SFval; f_equal; unfold F2R, Fnum, Fexp, cond_Zopp; simpl bpow.
Lemma C2p52_val : is_intd C2p52 (2 ^ 52).
Proof. val_const. rewrite <- mult_IZR. reflexivity. Qed.
Lemma Chalf_val : dval Chalf (/ 2).
Proof. val_const. lra. Qed.
Lemma Cmhalf_val : dval Cmhalf (- / 2).
Proof. val_const. lra. Qed.
Lemma Cone_val : is_intd Cone 1.
Proof. val_const. lra. Qed.
Lemma Cm1_val : is_intd Cm1 (-1).
Proof. val_const. lra. Qed.
Lemma C256_val : is_intd C256 256.
Proof. val_const. lra. Qed.

Lemma S255_val : is_ints S255 255.
Proof. val_const. lra. Qed.
Lemma Shi_val : sval Shi (IZR (2 ^ 31)).
Proof. val_const. rewrite <- mult_IZR. reflexivity. Qed.
Lemma Slo_val : sval Slo (IZR (- 2147483904)).
Proof. val_const. rewrite <- mult_IZR. reflexivity. Qed.

Definition RepS : R -> Prop := Rep S.
Definition NearestS : R -> R -> Prop := Nearest S.

Lemma formats_int n : (Z.abs n <= 2 ^ 24)%Z -> RepS (IZR n).
Proof. intros H. apply (Rep_int S fmt_single_ok). exact H. Qed.

Lemma Rabs_int_lt_emax_D n : (Z.abs n <= 2 ^ 53)%Z -> Rabs (IZR n) < bpow radix2 1024.
Proof. intros. apply (int_lt_emax D fmt_double_ok). cbn. lia. Qed.
Lemma IZR_lt_emax_D n : (Z.abs n <= 2 ^ 53)%Z -> IZR n < bpow radix2 1024.
Proof. intros H. eapply Rle_lt_trans; [apply Rle_abs|apply Rabs_int_lt_emax_D, H]. Qed.
Lemma bpow_lt_emax_D e : (e < 1024)%Z -> bpow radix2 e < bpow radix2 (fp_emax D).
Proof. intros. apply bpow_lt. exact H. Qed.
Lemma rounds_to_nearest f x r B :
rounds_to f RNE x r -> Rep f B -> Rabs x <= B -> B < bpow radix2 (fp_emax f) ->
exists v, fval f (fst r) = Some v /\ Nearest f x v /\ Rabs v <= B.
Proof. intros (_ & H & _). apply H. reflexivity. Qed.
Lemma rounds_to_exact_val f md x r :
rounds_to f md x r -> Rep f x -> Rabs x < bpow radix2 (fp_emax f) ->
fval f (fst r) = Some x /\ snd r = no_flags.
Proof. intros (_ & _ & H). exact H. Qed.
Lemma rounds_to_flags f md x r : rounds_to f md x r -> no_nv_dz (snd r).
Proof. intros (H & _). exact H. Qed.


Lemma dexp_field_asm x :
(0 <= x < 2 ^ 64)%Z ->
(((x * 2) mod 2 ^ 64) / 2 ^ 53)%Z = fp_exp_field D x.
Proof.
intros Hx. rewrite (exp_field_eq D fmt_double_ok). change (fp_mw D) with 52%Z. change (fp_ew D) with 11%Z.
apply Z.bits_inj'. intros n Hn.
rewrite Z.div_pow2_bits by lia.
rewrite !Z.testbit_mod_pow2 by lia.
destruct (Z.ltb_spec (n + 53) 64); destruct (Z.ltb_spec n 11); cbn [andb]; try lia.
rewrite Z.div_pow2_bits by lia. rewrite (Z.mul_comm x 2), Z.double_bits. f_equal. lia.
Qed.
Lemma dexp_field_bound x r k :
dval x r -> Rabs r < bpow radix2 k -> (-1022 <= k)%Z -> (fp_exp_field D x <= k + 1022)%Z.
Proof.
intros Hx Hr Hk. unfold dval, fval in Hx.
destruct (fp_decode_cases D fmt_double_ok x) as [(He&_&E)|[(He&_&E)|[(He&_&E)|[(He&_&E)|(He&E)]]]];
try (rewrite He; lia); rewrite E in Hx; cbn [SFval] in Hx; try discriminate.
apply Some_inj in Hx. subst r.
change (fp_mw D) with 52%Z in *. change (fp_ew D) with 11%Z in *. change (fp_emin D) with (-1074)%Z in *.
pose proof (man_field_range D fmt_double_ok x) as HM. change (fp_mw D) with 52%Z in HM.
set (M := fp_man_field D x) in *. set (E0 := fp_exp_field D x) in *.
assert (Hge : bpow radix2 (E0 - 1023) <= Rabs (F2R (Float radix2 (cond_Zopp (fp_sign_bit D x) (Z.pos (Z.to_pos (2 ^ 52 + M)))) (E0 + -1074 - 1)))).
{ rewrite <- F2R_Zabs, abs_cond_Zopp. cbn [Z.abs]. rewrite Z2Pos.id by lia.
unfold F2R, Fnum, Fexp. replace (E0 - 1023)%Z with (52 + (E0 + -1074 - 1))%Z by lia.
rewrite bpow_plus. apply Rmult_le_compat_r. apply bpow_ge_0.
rewrite <- (IZR_Zpower radix2) by lia. apply IZR_le. cbn [radix_val radix2]. lia. }
assert (Hlt : bpow radix2 (E0 - 1023) < bpow radix2 k) by lra.
apply lt_bpow in Hlt. lia.
Qed.
Lemma dexp_field_small_iff x r :
dval x r -> ((fp_exp_field D x <= 1021)%Z <-> Rabs r < / 2).
Proof.
intros Hx. unfold dval, fval in Hx.
change (/ 2) with (bpow radix2 (-1)).
destruct (fp_decode_cases D fmt_double_ok x) as [(He&HM0&E)|[(He&HM0&E)|[(He&HM0&E)|[(He&HM0&E)|(He&E)]]]];
rewrite E in Hx; cbn [SFval] in Hx; try discriminate; apply Some_inj in Hx; subst r.
- rewrite He, Rabs_R0. split; [intros _; apply bpow_gt_0|lia].
- rewrite He. split; [intros _|lia].
pose proof (man_field_range D fmt_double_ok x) as HM. change (fp_mw D) with 52%Z in HM.
change (fp_emin D) with (-1074)%Z.
rewrite <- F2R_Zabs, abs_cond_Zopp. cbn [Z.abs]. rewrite Z2Pos.id by lia.
apply Rlt_trans with (bpow radix2 (52 + -1074)). 2: apply bpow_lt; lia.
rewrite bpow_plus. unfold F2R, Fnum, Fexp. apply Rmult_lt_compat_r. apply bpow_gt_0.
rewrite <- (IZR_Zpower radix2) by lia. apply IZR_lt. cbn [radix_val radix2]. lia.
- change (fp_mw D) with 52%Z in *. change (fp_ew D) with 11%Z in *. change (fp_emin D) with (-1074)%Z in *.
pose proof (man_field_range D fmt_double_ok x) as HM. change (fp_mw D) with 52%Z in HM.
set (M := fp_man_field D x) in *. set (E0 := fp_exp_field D x) in *.
rewrite <- F2R_Zabs, abs_cond_Zopp. cbn [Z.abs]. rewrite Z2Pos.id by lia.
unfold F2R, Fnum, Fexp.
assert (HmLo : bpow radix2 52 <= IZR (2 ^ 52 + M)).
{ rewrite <- (IZR_Zpower radix2) by lia. apply IZR_le. cbn [radix_val radix2]. lia. }
assert (HmHi : IZR (2 ^ 52 + M) < bpow radix2 53).
{ rewrite <- (IZR_Zpower radix2) by lia. apply IZR_lt. cbn [radix_val radix2]. lia. }
pose proof (bpow_gt_0 radix2 (E0 + -1074 - 1)) as Hp.
split.
+ intros Hle. apply Rlt_le_trans with (bpow radix2 53 * bpow radix2 (E0 + -1074 - 1)).
* apply Rmult_lt_compat_r; assumption.
* rewrite <- bpow_plus. apply bpow_le. lia.
+ intros Hlt.
assert (Hge : bpow radix2 (52 + (E0 + -1074 - 1)) <= IZR (2 ^ 52 + M) * bpow radix2 (E0 + -1074 - 1)).
{ rewrite bpow_plus. apply Rmult_le_compat_r. apply bpow_ge_0. exact HmLo. }
assert (H : bpow radix2 (52 + (E0 + -1074 - 1)) < bpow radix2 (-1)) by lra.
apply lt_bpow in H. lia.
Qed.
Lemma dval_pos_bits x r :
dval x r -> 0 < r -> (0 <= x < 2 ^ 64)%Z -> (x < 2 ^ 63)%Z /\ fp_abs D x = x.
Proof.
intros Hx Hr Hrange.
pose proof (fval_sign_bit D fmt_double_ok x r Hx ltac:(lra)) as Hs.
rewrite Rlt_bool_false in Hs by lra.
apply (fp_sign_bit_false_iff D fmt_double_ok x Hrange) in Hs. change (2 ^ (fp_width D - 1))%Z with (2 ^ 63)%Z in Hs.
split; [exact Hs|]. unfold fp_abs. change (fp_width D - 1)%Z with 63%Z. apply Z.mod_small. lia.
Qed.

Lemma fp_abs_D x : fp_abs D x = x mod 2 ^ 63.
Proof. reflexivity. Qed.
Lemma nearest_big_int y v :
bpow radix2 52 <= y < bpow radix2 53 -> NearestD y v ->
exists n : Z, v = IZR n /\ Rabs (IZR n - y) <= / 2.
Proof.
intros Hy Hn.
assert (F52 : RepD (bpow radix2 52)) by (apply bpow_D_format; lia).
assert (F53 : RepD (bpow radix2 53)) by (apply bpow_D_format; lia).
assert (Hv52 : bpow radix2 52 <= v) by (apply (Nearest_ge D _ _ _ Hn F52); lra).
assert (Hv53 : v <= bpow radix2 53) by (apply (Nearest_le D _ _ _ Hn F53); lra).
destruct (Nearest_rep D _ _ Hn) as (m & e & Hv & Hm & He). cbn in Hm, He.
assert (Hint : exists n, v = IZR n).
{ destruct (Z.le_gt_cases 0 e) as [He0|He0].
- exists (m * 2 ^ e)%Z. rewrite Hv. unfold F2R, Fnum, Fexp. rewrite mult_IZR, (IZR_Zpower radix2) by lia. reflexivity.
- exfalso.
assert (Rabs v < bpow radix2 (53 + e)).
{ rewrite Hv. apply F2R_lt_bpow. cbn [Fnum Fexp]. replace (53 + e - e)%Z with 53%Z by lia. exact Hm. }
assert (bpow radix2 (53 + e) <= bpow radix2 52) by (apply bpow_le; lia).
rewrite Rabs_pos_eq in H by (pose proof (bpow_ge_0 radix2 52); lra). lra. }
destruct Hint as [n Hvn]. exists n. split; [exact Hvn|].
set (k := Zfloor y). pose proof (Zfloor_lb y) as L. pose proof (Zfloor_ub y) as U. fold k in L, U.
assert (Hb52 : bpow radix2 52 = IZR (2 ^ 52)) by (symmetry; apply (IZR_Zpower radix2); lia).
assert (Hb53 : bpow radix2 53 = IZR (2 ^ 53)) by (symmetry; apply (IZR_Zpower radix2); lia).
assert (Hk : (2 ^ 52 <= k < 2 ^ 53)%Z).
{ split. apply Zfloor_lub. rewrite <- Hb52. lra. apply lt_IZR. rewrite <- Hb53. lra. }
assert (F1 : RepD (IZR k)) by (apply formatd_int; lia).
assert (F2 : RepD (IZR (k + 1))) by (apply formatd_int; lia).
destruct Hn as [_ Hmin]. rewrite <- Hvn.
destruct (Rle_or_lt (y - IZR k) (/ 2)) as [C|C].
- specialize (Hmin _ F1). rewrite (Rabs_left1 (IZR k - y)) in Hmin by lra. lra.
- specialize (Hmin _ F2). rewrite plus_IZR in Hmin. rewrite (Rabs_right (IZR k + 1 - y)) in Hmin by lra.
rewrite plus_IZR in *. lra.
Qed.
Lemma format_int_minus (n : Z) r :
RepD r -> / 2 <= r < bpow radix2 51 -> Rabs (IZR n - r) <= / 2 -> RepD (IZR n - r).
Proof.
intros (m & e & Hr & Hm & He) Hrange Hn. cbn in Hm, He.
destruct (Z.le_gt_cases 0 e) as [He0|He0].
-
assert (Hri : r = IZR (m * 2 ^ e)).
{ rewrite Hr. unfold F2R, Fnum, Fexp. rewrite mult_IZR, (IZR_Zpower radix2) by lia. reflexivity. }
rewrite Hri, <- minus_IZR in Hn |- *.
assert (Hz : (n - m * 2 ^ e = 0)%Z).
{ apply Rabs_le_inv in Hn. destruct Hn as [H1 H2].
assert (IZR (n - m * 2 ^ e) < 1) by lra. assert (-1 < IZR (n - m * 2 ^ e)) by lra.
apply lt_IZR in H. apply (lt_IZR (-1)) in H0. lia. }
rewrite Hz. apply (Rep_0 D fmt_double_ok).
-
assert (He53 : (-53 <= e)%Z).
{ destruct (Z.le_gt_cases (-53) e) as [H|H]; [exact H|exfalso].
assert (Rabs r < bpow radix2 (53 + e)).
{ rewrite Hr. apply F2R_lt_bpow. cbn [Fnum Fexp]. replace (53 + e - e)%Z with 53%Z by lia. exact Hm. }
assert (bpow radix2 (53 + e) <= bpow radix2 (-1)) by (apply bpow_le; lia).
change (bpow radix2 (-1)) with (/ 2) in H1. rewrite Rabs_pos_eq in H0 by lra. lra. }
assert (Hm0 : (Z.abs (n * 2 ^ (- e) - m) < 2 ^ fp_prec D)%Z).
{ apply lt_IZR. rewrite abs_IZR, minus_IZR, mult_IZR, (IZR_Zpower radix2) by lia.
replace (IZR n * bpow radix2 (- e) - IZR m) with ((IZR n - r) * bpow radix2 (- e)).
2:{ rewrite Hr. unfold F2R, Fnum, Fexp. rewrite Rmult_minus_distr_r, Rmult_assoc, <- bpow_plus.
replace (e + - e)%Z with 0%Z by lia. cbn [bpow]. ring. }
rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 (- e))) by apply bpow_ge_0.
apply Rle_lt_trans with (/ 2 * bpow radix2 (- e)).
* apply Rmult_le_compat_r. apply bpow_ge_0. exact Hn.
* change (/ 2) with (bpow radix2 (-1)). rewrite <- bpow_plus, (IZR_Zpower radix2) by (cbn; lia). apply bpow_lt. change (fp_prec D) with 53%Z. lia. }
exists (n * 2 ^ (- e) - m)%Z, e. split; [|split; [exact Hm0|cbn; lia]].
unfold F2R, Fnum, Fexp. rewrite minus_IZR, mult_IZR, (IZR_Zpower radix2) by lia.
rewrite Rmult_minus_distr_r, Rmult_assoc, <- bpow_plus. replace (- e + e)%Z with 0%Z by lia.
cbn [bpow]. rewrite Rmult_1_r. rewrite Hr. reflexivity.
Qed.
Theorem musl_round_main x r two52 half mhalf one :
dval x r -> / 2 <= r < bpow radix2 51 ->
is_intd two52 (2 ^ 52) -> dval half (/ 2) -> dval mhalf (- / 2) -> is_intd one 1 ->
let t  := fst (fp_add D RNE x two52) in
let t1 := fst (fp_sub D RNE t two52) in
let y  := fst (fp_sub D RNE t1 x) in
let r0 := fst (fp_add D RNE y x) in
exists N : Z,
is_intd t (2 ^ 52 + N) /\
is_intd t1 N /\
dval y (IZR N - r) /\ - / 2 <= IZR N - r <= / 2 /\
fst (fp_lt D half y) = false /\
is_intd r0 N /\
(0 <= N <= Zfloor (r + / 2))%Z /\
(fst (fp_le D y mhalf) = true ->
is_intd (fst (fp_add D RNE r0 one)) (N + 1) /\ (N + 1)%Z = Zfloor (r + / 2)) /\
(fst (fp_le D y mhalf) = false -> N = Zfloor (r + / 2)).
Proof.
intros Hx Hr H52 Hhalf Hmhalf Hone t t1 y r0.
assert (Hb51 : bpow radix2 51 < bpow radix2 52) by (apply bpow_lt; lia).
assert (Hb52 : bpow radix2 52 = IZR (2 ^ 52)) by (symmetry; apply (IZR_Zpower radix2); lia).
assert (Hb5253 : bpow radix2 53 = 2 * bpow radix2 52).
{ change 53%Z with (1 + 52)%Z. rewrite bpow_plus. reflexivity. }
destruct (rounds_to_nearest D _ _ (bpow radix2 53)
(fp_add_finite D fmt_double_ok RNE x two52 _ _ Hx (is_intd_dval _ _ H52)))
as (v & Htv & Hn & _).
{ apply bpow_D_format. lia. }
{ rewrite <- Hb52, Rabs_pos_eq by lra. lra. }
{ apply bpow_lt_emax_D. lia. }
destruct (nearest_big_int (r + IZR (2 ^ 52)) v) as (n & Hvn & Hnr).
{ rewrite <- Hb52. lra. }
{ exact Hn. }
set (N := (n - 2 ^ 52)%Z).
assert (HNr : Rabs (IZR N - r) <= / 2).
{ unfold N. rewrite minus_IZR. replace (IZR n - IZR (2 ^ 52) - r) with (IZR n - (r + IZR (2 ^ 52))) by ring. exact Hnr. }
apply Rabs_le_inv in HNr.
assert (HN0 : (0 <= N)%Z).
{ apply le_IZR. lra. }
assert (HNhi : IZR N <= bpow radix2 51 + 1) by lra.
assert (Hb51' : bpow radix2 51 = IZR (2 ^ 51)) by (symmetry; apply (IZR_Zpower radix2); lia).
assert (HN53 : (Z.abs N <= 2 ^ 51 + 1)%Z).
{ rewrite Z.abs_eq by lia. apply le_IZR. rewrite plus_IZR, <- Hb51'. exact HNhi. }
assert (Ht : is_intd t (2 ^ 52 + N)).
{ split; [|unfold N; clear -HN53; lia]. unfold dval. fold t in Htv. rewrite Htv, Hvn. f_equal. f_equal. unfold N. lia. }
exists N.
assert (Ht1 : is_intd t1 N).
{ replace N with (2 ^ 52 + N - 2 ^ 52)%Z by lia.
apply (is_intd_sub RNE t two52 _ _ Ht H52). clear -HN53; cbn -[Z.add Z.sub Z.pow Z.le Z.abs]; lia. }
assert (Hfmt : RepD (IZR N - r)).
{ apply format_int_minus; try assumption. apply (dval_format x). exact Hx.
apply Rabs_le. lra. }
assert (Hy : dval y (IZR N - r)).
{ destruct (rounds_to_exact_val D _ _ _ (fp_sub_finite D fmt_double_ok RNE t1 x _ _ (is_intd_dval _ _ Ht1) Hx)) as [Hv _].
- exact Hfmt.
- apply Rle_lt_trans with (/ 2). apply Rabs_le; lra. change (/ 2) with (bpow radix2 (-1)). apply bpow_lt. reflexivity.
- exact Hv. }
assert (Hlt : fst (fp_lt D half y) = false).
{ rewrite (fp_lt_fval D fmt_double_ok half y _ _ Hhalf Hy). cbn [fst]. apply Rlt_bool_false. lra. }
assert (Hr0 : is_intd r0 N).
{ destruct (rounds_to_exact_val D _ _ _ (fp_add_finite D fmt_double_ok RNE y x _ _ Hy Hx)) as [Hv _].
- replace (IZR N - r + r) with (IZR N) by ring. apply formatd_int. lia.
- replace (IZR N - r + r) with (IZR N) by ring. apply Rabs_int_lt_emax_D. lia.
- split; [|lia]. unfold dval. fold r0 in Hv. rewrite Hv. f_equal. ring. }
pose proof (Zfloor_lb (r + / 2)) as FL. pose proof (Zfloor_ub (r + / 2)) as FU.
assert (HNle : (N <= Zfloor (r + / 2))%Z) by (apply Zfloor_lub; lra).
repeat match goal with |- _ /\ _ => split end; try assumption; try lra.
- intros Hle. rewrite (fp_le_fval D fmt_double_ok y mhalf _ _ Hy Hmhalf) in Hle. cbn [fst] in Hle.
destruct (Rle_bool_spec (IZR N - r) (- / 2)) as [H|H]; [|discriminate].
split.
+ apply (is_intd_add RNE r0 one _ _ Hr0 Hone). clear -HN53 HNle; cbn -[Z.add Z.sub Z.pow Z.le Z.abs]; lia.
+ symmetry. apply Zfloor_imp. rewrite !plus_IZR. lra.
- intros Hle. rewrite (fp_le_fval D fmt_double_ok y mhalf _ _ Hy Hmhalf) in Hle. cbn [fst] in Hle.
destruct (Rle_bool_spec (IZR N - r) (- / 2)) as [H|H]; [discriminate|].
symmetry. apply Zfloor_imp. rewrite plus_IZR. lra.
Qed.
Theorem musl_round_small x r zero md :
dval x r -> is_intd zero 0 ->
dval (fst (fp_mul D md zero x)) 0 /\ no_nv_dz (snd (fp_mul D md zero x)).
Proof.
intros Hx [Hz _].
pose proof (fp_mul_finite D fmt_double_ok md zero x _ _ Hz Hx) as Hm.
rewrite Rmult_0_l in Hm.
destruct (rounds_to_exact_val D _ _ _ Hm (Rep_0 D fmt_double_ok) ltac:(rewrite Rabs_R0; apply bpow_gt_0)) as [Hv _].
split; [exact Hv|apply (rounds_to_flags D _ _ _ Hm)].
Qed.
Theorem musl_round_branches x r :
dval x r -> 0 <= r <= 255 -> (0 <= x < 2 ^ 64)%Z ->
(fp_exp_field D x <= 1074)%Z /\
((fp_exp_field D x <= 1021)%Z <-> r < / 2) /\
(/ 2 <= r -> (x < 2 ^ 63)%Z /\ fp_abs D x = x /\ r < bpow radix2 51).
Proof.
intros Hx Hr Hrange. split; [|split].
- apply Z.le_trans with (8 + 1022)%Z; [|lia]. apply (dexp_field_bound x r 8 Hx); [|lia].
rewrite Rabs_pos_eq by lra. apply Rle_lt_trans with 255; [lra|].
change (bpow radix2 8) with (IZR 256). lra.
- rewrite (dexp_field_small_iff x r Hx). rewrite Rabs_pos_eq by lra. tauto.
- intros Hhalf. destruct (dval_pos_bits x r Hx ltac:(lra) Hrange) as [H1 H2].
repeat split; try assumption.
apply Rle_lt_trans with 255; [lra|]. apply Rlt_trans with (IZR 256); [lra|].
change (IZR 256) with (bpow radix2 8). apply bpow_lt. lia.
Qed.
Theorem round_result_checks rr n cm1 c256 md :
is_intd rr n -> (0 <= n <= 255)%Z -> is_intd cm1 (-1) -> is_intd c256 256 ->
fp_lt D cm1 rr = (true, no_flags) /\
fp_lt D rr c256 = (true, no_flags) /\
fp_to_int D md false 64 rr = (n, no_flags).
Proof.
intros Hrr Hn Hm1 H256.
rewrite (is_intd_flt cm1 rr _ _ Hm1 Hrr), (is_intd_flt rr c256 _ _ Hrr H256).
rewrite (is_intd_to_lu md rr n Hrr) by lia.
repeat split; f_equal; apply Z.ltb_lt; lia.
Qed.
Lemma dval0_is_intd x : dval x 0 -> is_intd x 0.
Proof. intros H. split; [exact H|simpl; lia]. Qed.

Lemma floor_half_range r : 0 <= r <= 255 -> (0 <= Zfloor (r + / 2) <= 255)%Z.
Proof.
intros Hr. split. apply Zfloor_lub. simpl. lra.
apply Z.lt_succ_r. apply lt_IZR. eapply Rle_lt_trans. apply Zfloor_lb. simpl. lra.
Qed.
Theorem mean_dval_range d m s :
is_quot d m s -> (m <= 255 * s)%Z ->
exists q, dval d q /\ 0 <= q <= 255 /\ NearestD (IZR m / IZR s) q.
Proof.
intros (Hs & Hm & q & Hd & Hn) Hle. exists q. split; [exact Hd|].
destruct (quot_bounds m s q ltac:(lia) ltac:(lia) Hn) as [H0 H255]. split; [split; [exact H0|exact (H255 Hle)]|exact Hn].
Qed.

Definition sfin (v : Z) (B : Z) : Prop := exists r, sval v r /\ Rabs r <= IZR B.
Definition s_in (v lo hi : Z) : Prop := exists r, sval v r /\ IZR lo <= r <= IZR hi.
Definition d_in (v lo hi : Z) : Prop := exists r, dval v r /\ IZR lo <= r <= IZR hi.

Lemma is_ints_s_in v n lo hi : is_ints v n -> (lo <= n <= hi)%Z -> s_in v lo hi.
Proof. intros [H _] Hb. exists (IZR n). split; [exact H|]. split; apply IZR_le; lia. Qed.

Theorem dither_init md b :
(0 <= b < 256)%Z -> is_ints (fst (fp_of_int S md false 32 b)) b /\ s_in (fst (fp_of_int S md false 32 b)) 0 255.
Proof.
intros Hb. destruct (is_ints_of_int_wu md b) as [Hi _]. rewrite Z.mod_small; lia.
rewrite Z.mod_small in Hi by lia. split; [exact Hi|]. apply (is_ints_s_in _ b); [exact Hi|lia].
Qed.

Definition clamp_sel (v c0 c255 : Z) : Z :=
let le255 := fst (fp_le S v c255) in
let le0 := fst (fp_le S v c0) in
if (le0 && le255)%bool then c0
else if (negb le255 || le0)%bool then c255
else v.
Lemma fle_true_cases a b rb :
sval b rb -> fst (fp_le S a b) = true ->
(exists ra, sval a ra /\ ra <= rb) \/ fp_decode S a = S754_infinity true.
Proof.
intros Hb Hle.
destruct (is_finite_SF (fp_decode S a)) eqn:Fa.
- left. pose proof (SFval_of_finite _ Fa) as Ha.
change (sval a (SF2R radix2 (fp_decode S a))) in Ha.
exists (SF2R radix2 (fp_decode S a)). split; [exact Ha|].
rewrite (fp_le_fval S fmt_single_ok a b _ _ Ha Hb) in Hle. cbn [fst] in Hle.
destruct (Rle_bool_spec (SF2R radix2 (fp_decode S a)) rb); [assumption|discriminate].
- unfold fp_le, fp_compare in Hle. cbn [fst] in Hle. unfold sval, fval in Hb.
destruct (fp_decode S a) as [sa|[|]| |sa ma ea]; try discriminate; [right; reflexivity|];
destruct (fp_decode S b); cbn in Hle, Hb; discriminate.
Qed.
Lemma fle_false_cases a b rb :
sval b rb -> fst (fp_le S a b) = false ->
(exists ra, sval a ra /\ rb < ra) \/ fp_decode S a = S754_infinity false \/ fp_is_nan S a = true.
Proof.
intros Hb Hle. rewrite (fp_is_nan_decode S fmt_single_ok).
destruct (is_finite_SF (fp_decode S a)) eqn:Fa.
- left. pose proof (SFval_of_finite _ Fa) as Ha.
change (sval a (SF2R radix2 (fp_decode S a))) in Ha.
exists (SF2R radix2 (fp_decode S a)). split; [exact Ha|].
rewrite (fp_le_fval S fmt_single_ok a b _ _ Ha Hb) in Hle. cbn [fst] in Hle.
destruct (Rle_bool_spec (SF2R radix2 (fp_decode S a)) rb); [discriminate|assumption].
- unfold fp_le, fp_compare in Hle. cbn [fst] in Hle. unfold sval, fval in Hb. right.
destruct (fp_decode S a) as [sa|[|]| |sa ma ea]; try discriminate; [| left; reflexivity | right; reflexivity ].
destruct (fp_decode S b); cbn in Hle, Hb; discriminate.
Qed.
Theorem clamp_mid v c0 c255 :
is_ints c0 0 -> is_ints c255 255 ->
fst (fp_le S v c255) = true -> fst (fp_le S v c0) = false ->
exists r, sval v r /\ 0 < r <= 255.
Proof.
intros [H0 _] [H255 _] Hle Hgt.
destruct (fle_true_cases v c255 _ H255 Hle) as [(r & Hv & Hr)|Hinf].
- destruct (fle_false_cases v c0 _ H0 Hgt) as [(r' & Hv' & Hr')|[Hinf|Hnan]].
+ exists r. split; [exact Hv|]. unfold sval in Hv, Hv'. rewrite Hv in Hv'. apply Some_inj in Hv'. subst r'.
change (IZR 0) with 0 in Hr'. change (IZR 255) with 255 in Hr. lra.
+ exfalso. unfold sval, fval in Hv. rewrite Hinf in Hv. discriminate.
+ exfalso. rewrite (fval_is_nan S fmt_single_ok v r Hv) in Hnan. discriminate.
- exfalso. unfold fp_le, fp_compare in Hgt. rewrite Hinf in Hgt.
unfold sval, fval in H0. destruct (fp_decode S c0); cbn [SFcompare fst] in Hgt; discriminate.
Qed.

Theorem dither_err md v p slo shi :
s_in v 0 255 -> (0 <= p < 256)%Z ->
sval slo (IZR (- 2147483904)) -> sval shi (IZR (2 ^ 31)) ->
let xp := fst (fp_of_int S md false 32 p) in
let diff := fst (fp_sub S RNE v xp) in
exists (rd : R) (e : Z),
sval diff rd /\ Rabs rd <= 255 /\
no_nv_dz (snd (fp_sub S RNE v xp)) /\
fp_lt S slo diff = (true, no_flags) /\
fp_lt S diff shi = (true, no_flags) /\
fst (fp_to_int S RTZ true 32 diff) = int_wrap 32 e /\
fl_nv (snd (fp_to_int S RTZ true 32 diff)) = false /\
(-255 <= e <= 255)%Z /\ e = Ztrunc rd.
Proof.
intros (r & Hv & Hr) Hp Hlo Hhi xp diff.
destruct (dither_init md p Hp) as [[Hxp _] _]. fold xp in Hxp.
pose proof (fp_sub_finite S fmt_single_ok RNE v xp _ _ Hv Hxp) as Hsub.
change (IZR 0) with 0 in Hr. change (IZR 255) with 255 in Hr.
assert (Hpr : 0 <= IZR p <= 255).
{ split. apply (IZR_le 0); lia. apply (IZR_le _ 255); lia. }
assert (Hd : Rabs (r - IZR p) <= 255) by (apply Rabs_le; lra).
assert (H255 : RepS 255) by (apply (formats_int 255); cbn; lia).
destruct (rounds_to_nearest S _ _ 255 Hsub H255 Hd) as (rd & Hrnd & Hnear & Hrd).
{ apply Rlt_trans with (IZR 256). lra. change (IZR 256) with (bpow radix2 8). apply bpow_lt. reflexivity. }
fold diff in Hrnd. change (sval diff rd) in Hrnd.
pose proof Hrd as Hrd'. apply Rabs_le_inv in Hrd.
exists rd, (Ztrunc rd).
assert (Htr : (-255 <= Ztrunc rd <= 255)%Z).
{ unfold Ztrunc. destruct (Rlt_bool_spec rd 0).
- split. 2: { apply Z.le_trans with 0%Z; [|lia]. assert (Zceil rd <= 0)%Z by (apply Zceil_glb; simpl; lra). lia. }
apply Z.le_trans with (Zfloor rd); [|apply le_IZR; rewrite <- (Zceil_IZR (Zfloor rd)); apply IZR_le, Zceil_le, Zfloor_lb].
apply Zfloor_lub. change (IZR (-255)) with (-255). lra.
- split. apply Z.le_trans with 0%Z; [lia|]. apply Zfloor_lub. simpl; lra.
apply Z.lt_succ_r. apply lt_IZR. eapply Rle_lt_trans. apply Zfloor_lb. change (IZR (Z.succ 255)) with 256. lra. }
destruct (fp_to_int_finite S fmt_single_ok RTZ true 32 diff rd Hrnd) as (Hti & Hnv & _).
{ cbn [round_mode flocq_mode]. unfold int_lo, int_hi. change (Z.shiftl 1 (32 - 1)) with (2 ^ 31)%Z. lia. }
cbn [round_mode flocq_mode] in Hti.
rewrite (fp_lt_fval S fmt_single_ok slo diff _ _ Hlo Hrnd).
rewrite (fp_lt_fval S fmt_single_ok diff shi _ _ Hrnd Hhi).
repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity.
- apply (rounds_to_flags S _ _ _ Hsub).
- f_equal. apply Rlt_bool_true. apply Rlt_le_trans with (-255); [|lra]. apply (IZR_lt _ (-255)). lia.
- f_equal. apply Rlt_bool_true. apply Rle_lt_trans with 255; [lra|]. apply (IZR_lt 255). lia.
- lia.
- lia.
Qed.

Lemma format_int_bpow n e :
(Z.abs n < 2 ^ 53)%Z -> (-1074 <= e)%Z -> RepD (IZR n * bpow radix2 e).
Proof. intros Hn He. apply (Rep_int_bpow D); assumption. Qed.
Lemma quot_dist m s p q :
(0 < s <= 2 ^ 32)%Z -> (0 <= m <= 255 * s)%Z -> (p * s <> m)%Z -> NearestD (IZR m / IZR s) q ->
bpow radix2 (-33) <= Rabs (IZR p - q).
Proof.
intros Hs Hm Hne Hn.
assert (H0s : 0 < IZR s) by (apply IZR_lt; lia).
assert (Hb32 : bpow radix2 (-32) = / IZR (2 ^ 32)) by reflexivity.
assert (Hb3233 : bpow radix2 (-32) = 2 * bpow radix2 (-33)).
{ change (-32)%Z with (1 + -33)%Z. rewrite bpow_plus. reflexivity. }
assert (Hinv : bpow radix2 (-32) <= / IZR s).
{ rewrite Hb32. apply Rinv_le_contravar. exact H0s. apply IZR_le. lia. }
destruct (Z.eq_dec m 0) as [Hm0|Hm0].
-
subst m. replace (IZR 0 / IZR s) with 0 in Hn by (unfold Rdiv; ring).
rewrite (Nearest_0 D fmt_double_ok q Hn). rewrite Rminus_0_r.
assert (Hp : (p <> 0)%Z) by lia.
apply Rle_trans with 1.
+ change 1 with (bpow radix2 0). apply bpow_le. lia.
+ rewrite <- abs_IZR. apply (IZR_le 1). lia.
- set (x := IZR m / IZR s) in *.
assert (Hx_lo : / IZR s <= x).
{ unfold x, Rdiv. rewrite <- (Rmult_1_l (/ IZR s)) at 1.
apply Rmult_le_compat_r. left. apply Rinv_0_lt_compat. exact H0s. apply (IZR_le 1). lia. }
assert (Hx_hi : x <= 255).
{ unfold x. apply (Rmult_le_reg_r (IZR s)). exact H0s.
unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
rewrite <- (mult_IZR 255). apply IZR_le. lia. }
assert (Hx_pos : 0 < x) by (pose proof (bpow_gt_0 radix2 (-32)); lra).
assert (Herr : Rabs (q - x) <= bpow radix2 (-45)).
{ eapply Rle_trans. apply (Nearest_error D fmt_double_ok x q (-32) 8 Hn); [cbn; lia|].
{ rewrite Rabs_pos_eq by lra. split; [lra|]. apply Rle_lt_trans with 255; [lra|].
change (bpow radix2 8) with 256. lra. }
rewrite Rabs_pos_eq by lra. change (- fp_prec D)%Z with (-53)%Z. change (-45)%Z with (8 + -53)%Z. rewrite bpow_plus.
apply Rmult_le_compat_r. apply bpow_ge_0. apply Rle_trans with 255; [lra|].
change (bpow radix2 8) with 256. lra. }
assert (Hgap : / IZR s <= Rabs (IZR p - x)).
{ replace (IZR p - x) with (IZR (p * s - m) * / IZR s).
2:{ unfold x. rewrite minus_IZR, mult_IZR. field. lra. }
rewrite Rabs_mult, (Rabs_pos_eq (/ IZR s)) by (left; apply Rinv_0_lt_compat; exact H0s).
rewrite <- (Rmult_1_l (/ IZR s)) at 1. apply Rmult_le_compat_r.
left; apply Rinv_0_lt_compat; exact H0s.
rewrite <- abs_IZR. apply (IZR_le 1). lia. }
assert (H45 : bpow radix2 (-45) <= bpow radix2 (-33)) by (apply bpow_le; lia).
pose proof (Rabs_triang_inv (IZR p - x) (q - x)) as T.
replace (IZR p - x - (q - x)) with (IZR p - q) in T by ring.
lra.
Qed.
Lemma NearestD_away x v b :
RepD b -> 0 < b -> NearestD x v ->
(b <= x -> b <= v) /\ (x <= - b -> v <= - b).
Proof.
intros Hb Hb0 Hn. split; intros Hx.
- apply (Nearest_ge D _ _ _ Hn Hb Hx).
- apply (Nearest_le D _ _ _ Hn). apply (Rep_opp D). exact Hb. exact Hx.
Qed.
Definition vacc (acc : Z) (k : Z) (pos : bool) : Prop :=
exists a, dval acc a /\ 0 <= a <= IZR k * bpow radix2 48 /\
(if pos then bpow radix2 (-66) <= a else a = 0).
Theorem variance_init : vacc 0 0 false.
Proof.
exists 0. split; [exact (is_intd_dval _ _ is_intd_zero)|]. split; [|reflexivity].
rewrite Rmult_0_l. lra.
Qed.

Theorem variance_step xp p mean m s xf f acc k pos :
is_intd xp p -> (0 <= p <= 255)%Z ->
is_quot mean m s -> (m <= 255 * s)%Z ->
is_intd xf f -> (1 <= f <= 2 ^ 32)%Z ->
vacc acc k pos -> (0 <= k)%Z -> (k + 1 < 2 ^ 53)%Z ->
let t1 := fst (fp_sub D RNE xp mean) in
let t2 := fst (fp_mul D RNE t1 xf) in
let acc' := fst (fp_fma D RNE t2 t1 acc) in
vacc acc' (k + 1) (pos || negb (p * s =? m))%bool /\
(exists r1, dval t1 r1 /\ Rabs r1 <= 255 /\ (r1 = 0 <-> (p * s)%Z = m)) /\
(exists r2, dval t2 r2 /\ Rabs r2 <= IZR (255 * 2 ^ 32)) /\
no_nv_dz (snd (fp_sub D RNE xp mean)) /\
no_nv_dz (snd (fp_mul D RNE t1 xf)) /\
no_nv_dz (snd (fp_fma D RNE t2 t1 acc)).
Proof.
intros [Hxp _] Hp Hq Hms [Hxf _] Hf (a & Hacc & Ha & Hpos) Hk0 Hk t1 t2 acc'.
pose proof Hq as Hq'. destruct Hq' as (Hs & Hm & q & Hmean & Hnq).
destruct (quot_bounds m s q ltac:(lia) ltac:(lia) Hnq) as [Hq0 Hq255]. specialize (Hq255 Hms).
assert (HpR : 0 <= IZR p <= 255).
{ split. apply (IZR_le 0); lia. apply (IZR_le _ 255); lia. }
assert (HfR : 1 <= IZR f <= IZR (2 ^ 32)).
{ split. apply (IZR_le 1); lia. apply IZR_le; lia. }
assert (F255 : RepD 255) by (apply (formatd_int 255); cbn; lia).
assert (Fb33 : RepD (bpow radix2 (-33))) by (apply bpow_D_format; lia).
assert (Fb66 : RepD (bpow radix2 (-66))) by (apply bpow_D_format; lia).
assert (Hb33 : 0 < bpow radix2 (-33)) by apply bpow_gt_0.
assert (Hb66 : bpow radix2 (-66) = bpow radix2 (-33) * bpow radix2 (-33)).
{ change (-66)%Z with (-33 + -33)%Z. apply bpow_plus. }
set (B2 := IZR (255 * 2 ^ 32)).
assert (FB2 : RepD B2) by (apply formatd_int; cbn; lia).
assert (HB2 : B2 = 255 * IZR (2 ^ 32)) by (unfold B2; rewrite mult_IZR; reflexivity).
assert (HB2lt : B2 < bpow radix2 (fp_emax D)) by (unfold B2; apply IZR_lt_emax_D; cbn; lia).
set (B3 := IZR (k + 1) * bpow radix2 48).
assert (FB3 : RepD B3) by (apply format_int_bpow; lia).
assert (HB3lt : B3 < bpow radix2 (fp_emax D)).
{ unfold B3. apply Rlt_trans with (bpow radix2 53 * bpow radix2 48).
- apply Rmult_lt_compat_r. apply bpow_gt_0. rewrite <- (IZR_Zpower radix2) by lia. apply IZR_lt. exact Hk.
- rewrite <- bpow_plus. apply bpow_lt. reflexivity. }
assert (Hk1R : 1 <= IZR (k + 1)) by (apply (IZR_le 1); lia).
assert (Hb48 : 0 < bpow radix2 48) by apply bpow_gt_0.
pose proof (fp_sub_finite D fmt_double_ok RNE xp mean _ _ Hxp Hmean) as Hsub.
destruct (rounds_to_nearest D _ _ 255 Hsub F255) as (r1 & Hv1 & Hn1 & Hr1abs).
{ apply Rabs_le. lra. }
{ apply Rlt_trans with (IZR 256); [lra|]. apply IZR_lt_emax_D. cbn; lia. }
fold t1 in Hv1. change (dval t1 r1) in Hv1.
pose proof (fp_mul_finite D fmt_double_ok RNE t1 xf _ _ Hv1 Hxf) as Hmul.
destruct (rounds_to_nearest D _ _ B2 Hmul FB2) as (r2 & Hv2 & Hn2 & Hr2abs).
{ rewrite HB2, Rabs_mult. rewrite (Rabs_pos_eq (IZR f)) by lra.
apply Rmult_le_compat; try apply Rabs_pos; lra. }
{ exact HB2lt. }
fold t2 in Hv2. change (dval t2 r2) in Hv2.
assert (Hprod_hi : r2 * r1 <= bpow radix2 48).
{ apply Rle_trans with (Rabs (r2 * r1)); [apply Rle_abs|]. rewrite Rabs_mult.
apply Rle_trans with (B2 * 255).
- apply Rmult_le_compat; try apply Rabs_pos; assumption.
- unfold B2. rewrite <- (mult_IZR _ 255). change (bpow radix2 48) with (IZR (2 ^ 48)). apply IZR_le.
cbn. lia. }
apply Rabs_le_inv in Hr1abs. apply Rabs_le_inv in Hr2abs.
assert (Hcase : ((p * s)%Z = m /\ r1 = 0 /\ r2 = 0) \/
((p * s)%Z <> m /\ r1 <> 0 /\ bpow radix2 (-66) <= r2 * r1)).
{ destruct (Z.eq_dec (p * s) m) as [E|NE].
- left. split; [exact E|].
assert (Hq_eq : q = IZR p).
{ destruct (quot_gap m s p q Hs Hm Hnq) as (_ & _ & G). apply G. exact E. }
assert (Hr1z : r1 = 0).
{ apply (Nearest_0 D fmt_double_ok). replace 0 with (IZR p - q) by (rewrite Hq_eq; ring). exact Hn1. }
split; [exact Hr1z|].
apply (Nearest_0 D fmt_double_ok). replace 0 with (r1 * IZR f) by (rewrite Hr1z; ring). exact Hn2.
- right. split; [exact NE|].
pose proof (quot_dist m s p q Hs ltac:(lia) NE Hnq) as Hd.
destruct (NearestD_away (IZR p - q) r1 _ Fb33 Hb33 Hn1) as [A1 A2].
destruct (NearestD_away (r1 * IZR f) r2 _ Fb33 Hb33 Hn2) as [B1 B2'].
destruct (Rle_or_lt 0 (IZR p - q)) as [Hdp|Hdn].
+ rewrite Rabs_pos_eq in Hd by lra. specialize (A1 Hd).
assert (Hr2 : bpow radix2 (-33) <= r2).
{ apply B1. rewrite <- (Rmult_1_r (bpow radix2 (-33))). apply Rmult_le_compat; lra. }
split; [lra|]. rewrite Hb66. apply Rmult_le_compat; lra.
+ rewrite Rabs_left in Hd by lra. specialize (A2 ltac:(lra)).
assert (Hr2 : r2 <= - bpow radix2 (-33)).
{ apply B2'. apply Rle_trans with (r1 * 1); [|lra]. apply Rmult_le_compat_neg_l; lra. }
split; [lra|]. rewrite Hb66. replace (r2 * r1) with ((- r2) * (- r1)) by ring.
apply Rmult_le_compat; lra. }
assert (Hprod_lo : 0 <= r2 * r1).
{ destruct Hcase as [(_ & -> & ->)|(_ & _ & H)]. lra. pose proof (bpow_ge_0 radix2 (-66)). lra. }
pose proof (fp_fma_finite D fmt_double_ok RNE t2 t1 acc _ _ _ Hv2 Hv1 Hacc) as Hfma.
destruct (rounds_to_nearest D _ _ B3 Hfma FB3) as (a' & Hv3 & Hn3 & Ha'abs).
{ unfold B3. rewrite Rabs_pos_eq by lra. rewrite plus_IZR, Rmult_plus_distr_r, Rmult_1_l. lra. }
{ exact HB3lt. }
fold acc' in Hv3. change (dval acc' a') in Hv3.
assert (Ha'lo : 0 <= a').
{ apply (Nearest_nonneg D fmt_double_ok _ _ Hn3). lra. }
unfold B3 in Ha'abs. apply Rabs_le_inv in Ha'abs.
split; [|split; [|split; [|split; [|split]]]].
- exists a'. split; [exact Hv3|]. split; [lra|].
destruct Hcase as [(E & Hr1z & Hr2z)|(NE & Hr1nz & Hge)].
+ rewrite (proj2 (Z.eqb_eq _ _) E). cbn [negb]. rewrite Bool.orb_false_r.
assert (Ha' : a' = a).
{ apply (Nearest_id D). apply (dval_format acc). exact Hacc.
replace a with (r2 * r1 + a) at 1 by (rewrite Hr1z; ring). exact Hn3. }
rewrite Ha'. destruct pos; [exact Hpos|exact Hpos].
+ rewrite (proj2 (Z.eqb_neq _ _) NE). cbn [negb]. rewrite Bool.orb_true_r.
apply (Nearest_ge D _ _ _ Hn3 Fb66). lra.
- exists r1. split; [exact Hv1|]. split; [apply Rabs_le; lra|].
destruct Hcase as [(E & Hr1z & _)|(NE & Hr1nz & _)]; split; intros; auto; try lra. exfalso. exact (NE H).
- exists r2. split; [exact Hv2|]. apply Rabs_le. lra.
- apply (rounds_to_flags D _ _ _ Hsub).
- apply (rounds_to_flags D _ _ _ Hmul).
- apply (rounds_to_flags D _ _ _ Hfma).
Qed.
Theorem variance_final acc k pos xs s :
vacc acc k pos -> is_intd xs s -> (1 <= s <= 2 ^ 32)%Z -> (0 <= k < 2 ^ 53)%Z ->
let var := fst (fp_div D RNE acc xs) in
(exists v, dval var v /\ 0 <= v <= IZR k * bpow radix2 48 /\
(if pos then 0 < v else v = 0)) /\
no_nv_dz (snd (fp_div D RNE acc xs)).
Proof.
intros (a & Hacc & Ha & Hpos) [Hxs _] Hs Hk var.
assert (H0s : 0 < IZR s) by (apply (IZR_lt 0); lia).
assert (Hsinv : 0 < / IZR s) by (apply Rinv_0_lt_compat; exact H0s).
assert (Hs1 : / IZR s <= 1).
{ rewrite <- Rinv_1. apply Rinv_le_contravar. lra. apply (IZR_le 1). lia. }
destruct (fp_div_finite D fmt_double_ok RNE acc xs _ _ Hacc Hxs ltac:(lra)) as [Hfl Hv].
assert (Hq : 0 <= a / IZR s <= a).
{ unfold Rdiv. split. apply Rmult_le_pos; lra.
rewrite <- (Rmult_1_r a) at 2. apply Rmult_le_compat_l; lra. }
set (B3 := IZR k * bpow radix2 48) in *.
assert (Hb48 : 0 < bpow radix2 48) by apply bpow_gt_0.
assert (HkR : 0 <= IZR k) by (apply (IZR_le 0); lia).
destruct (Hv eq_refl (Rmax B3 1)) as (v & Hvar & Hn & Hvabs).
{ unfold Rmax. destruct (Rle_dec B3 1). apply (formatd_int 1); cbn; lia. apply format_int_bpow; lia. }
{ rewrite Rabs_pos_eq by lra. apply Rle_trans with a; [lra|]. apply Rle_trans with B3; [lra|apply Rmax_l]. }
{ unfold Rmax. destruct (Rle_dec B3 1). apply (IZR_lt_emax_D 1); cbn; lia.
unfold B3. apply Rle_lt_trans with (bpow radix2 53 * bpow radix2 48).
- apply Rmult_le_compat_r. apply bpow_ge_0. rewrite <- (IZR_Zpower radix2) by lia. apply IZR_le. change (radix_val radix2) with 2%Z. lia.
- rewrite <- bpow_plus. apply bpow_lt. reflexivity. }
fold var in Hvar.
assert (Hv0 : 0 <= v) by (apply (Nearest_nonneg D fmt_double_ok _ _ Hn); lra).
assert (Hvhi : v <= a).
{ apply (Nearest_le D _ _ _ Hn). apply (dval_format acc). exact Hacc. lra. }
split; [|exact Hfl].
exists v. split; [exact Hvar|]. split; [lra|].
destruct pos.
- apply Rlt_le_trans with (bpow radix2 (-98)). apply bpow_gt_0.
apply (Nearest_ge D _ _ _ Hn). apply bpow_D_format. lia.
change (-98)%Z with (-66 + -32)%Z. rewrite bpow_plus. unfold Rdiv.
apply Rmult_le_compat. apply bpow_ge_0. apply bpow_ge_0. exact Hpos.
change (bpow radix2 (-32)) with (/ IZR (2 ^ 32)). apply Rinv_le_contravar. exact H0s. apply IZR_le. lia.
- apply (Nearest_0 D fmt_double_ok). replace 0 with (a / IZR s); [exact Hn|]. rewrite Hpos. unfold Rdiv. apply Rmult_0_l.
Qed.
Theorem dval_flt a b ra rb :
dval a ra -> dval b rb -> fp_lt D a b = (Rlt_bool ra rb, no_flags).
Proof. apply (fp_lt_fval D fmt_double_ok). Qed.


Lemma dval_zero : dval 0 0.
Proof. exact (is_intd_dval _ _ is_intd_zero). Qed.
Definition argmax3 (v0 v1 v2 : R) : nat :=
let '(i1, m1) := if Rlt_bool 0 v0 then (0%nat, v0) else (0%nat, 0) in
let '(i2, m2) := if Rlt_bool m1 v1 then (1%nat, v1) else (i1, m1) in
let '(i3, _)  := if Rlt_bool m2 v2 then (2%nat, v2) else (i2, m2) in
i3.

Local Close Scope R_scope.
Import ListNotations.
Fixpoint wsum (l : list (Z * Z)) : Z :=
match l with [] => 0 | (f, _) :: t => f + wsum t end.
Fixpoint wdot (l : list (Z * Z)) : Z :=
match l with [] => 0 | (f, p) :: t => f * p + wdot t end.
Definition node_ok (l : list (Z * Z)) : Prop :=
Forall (fun fp => 1 <= fst fp /\ 0 <= snd fp <= 255) l.
Lemma wsum_app l1 l2 : wsum (l1 ++ l2) = wsum l1 + wsum l2.
Proof. induction l1 as [|[f p] t IH]; cbn -[Z.add]; [lia|]. rewrite IH. lia. Qed.
Lemma wdot_app l1 l2 : wdot (l1 ++ l2) = wdot l1 + wdot l2.
Proof. induction l1 as [|[f p] t IH]; cbn -[Z.add Z.mul]; [lia|]. rewrite IH. lia. Qed.
Lemma wsum_ge_len l : node_ok l -> Z.of_nat (length l) <= wsum l.
Proof.
induction l as [|[f p] t IH]; intros H; cbn -[Z.add Z.of_nat]; [lia|].
inversion H; subst. cbn [fst snd] in *. specialize (IH ltac:(assumption)).
rewrite Nat2Z.inj_succ. lia.
Qed.
Lemma wsum_pos l : node_ok l -> l <> [] -> 1 <= wsum l.
Proof.
intros H Hne. pose proof (wsum_ge_len l H). destruct l; [congruence|]. cbn [length] in *. lia.
Qed.
Lemma wdot_bounds l : node_ok l -> 0 <= wdot l <= 255 * wsum l /\ 0 <= wsum l.
Proof.
induction l as [|[f p] t IH]; intros H; cbn -[Z.add Z.mul]; [lia|].
inversion H; subst. cbn [fst snd] in *. specialize (IH ltac:(assumption)). nia.
Qed.
Lemma wdot_ge_min c l :
Forall (fun fp => 0 <= fst fp /\ c <= snd fp) l -> c * wsum l <= wdot l.
Proof.
induction l as [|[f p] t IH]; intros H; cbn -[Z.add Z.mul]; [lia|].
inversion H; subst. cbn [fst snd] in *. specialize (IH ltac:(assumption)). nia.
Qed.
Lemma wdot_le_max c l :
Forall (fun fp => 0 <= fst fp /\ snd fp <= c) l -> wdot l <= c * wsum l.
Proof.
induction l as [|[f p] t IH]; intros H; cbn -[Z.add Z.mul]; [lia|].
inversion H; subst. cbn [fst snd] in *. specialize (IH ltac:(assumption)). nia.
Qed.
Lemma wdot_lt_max c l :
Forall (fun fp => 1 <= fst fp /\ snd fp <= c) l -> Exists (fun fp => snd fp < c) l ->
wdot l < c * wsum l.
Proof.
induction l as [|[f p] t IH]; intros H He; [inversion He|]. cbn -[Z.add Z.mul].
inversion H; subst. cbn [fst snd] in *.
assert (Ht : Forall (fun fp : Z * Z => 0 <= fst fp /\ snd fp <= c) t).
{ eapply Forall_impl; [|eassumption]. intros [a b]; cbn; lia. }
pose proof (wdot_le_max c t Ht).
inversion He; subst; cbn [snd] in *.
- nia.
- specialize (IH ltac:(assumption) ltac:(assumption)). nia.
Qed.

Lemma wdot_all_equal c l :
Forall (fun fp => snd fp = c) l -> wdot l = c * wsum l.
Proof.
induction l as [|[f p] t IH]; intros H; cbn -[Z.add Z.mul]; [lia|].
inversion H; subst. cbn [fst snd] in *. specialize (IH ltac:(assumption)). subst. nia.
Qed.
Lemma exists_min_snd (l : list (Z * Z)) :
l <> [] -> exists a, In a l /\ Forall (fun fp => snd a <= snd fp) l.
Proof.
induction l as [|x t IH]; intros Hne; [congruence|].
destruct t as [|y t'].
- exists x. split; [left; reflexivity|]. constructor; [lia|constructor].
- destruct (IH ltac:(discriminate)) as (a & Ha & Hall).
destruct (Z.le_gt_cases (snd x) (snd a)).
+ exists x. split; [left; reflexivity|]. constructor; [lia|].
eapply Forall_impl; [|exact Hall]. cbn; intros; lia.
+ exists a. split; [right; exact Ha|]. constructor; [lia|exact Hall].
Qed.
Lemma exists_max_snd (l : list (Z * Z)) :
l <> [] -> exists a, In a l /\ Forall (fun fp => snd fp <= snd a) l.
Proof.
induction l as [|x t IH]; intros Hne; [congruence|].
destruct t as [|y t'].
- exists x. split; [left; reflexivity|]. constructor; [lia|constructor].
- destruct (IH ltac:(discriminate)) as (a & Ha & Hall).
destruct (Z.le_gt_cases (snd a) (snd x)).
+ exists x. split; [left; reflexivity|]. constructor; [lia|].
eapply Forall_impl; [|exact Hall]. cbn; intros; lia.
+ exists a. split; [right; exact Ha|]. constructor; [lia|exact Hall].
Qed.
Lemma not_all_equal_witness (l : list (Z * Z)) x :
(exists a b, In a l /\ In b l /\ snd a <> snd b) -> In x l ->
exists b, In b l /\ snd b <> snd x.
Proof.
intros (a & b & Ha & Hb & Hne) Hx.
destruct (Z.eq_dec (snd a) (snd x)); [exists b|exists a]; split; auto; lia.
Qed.
Definition neq_meanb (s m : Z) (l : list (Z * Z)) : bool :=
existsb (fun fp => negb (snd fp * s =? m)) l.
Lemma neq_meanb_app s m l1 l2 : neq_meanb s m (l1 ++ l2) = (neq_meanb s m l1 || neq_meanb s m l2)%bool.
Proof. unfold neq_meanb. apply existsb_app. Qed.
Theorem neq_mean_iff l :
node_ok l ->
(neq_meanb (wsum l) (wdot l) l = true <-> exists a b, In a l /\ In b l /\ snd a <> snd b).
Proof.
intros Hok. unfold neq_meanb. rewrite existsb_exists. split.
- intros (x & Hx & Hb). apply Bool.negb_true_iff in Hb. apply Z.eqb_neq in Hb.
destruct (Exists_dec (fun fp => snd fp <> snd x) l) as [He|Hn].
{ intros fp. destruct (Z.eq_dec (snd fp) (snd x)); [right|left]; lia. }
+ apply Exists_exists in He. destruct He as (b & Hbin & Hbne). exists x, b. auto.
+ exfalso. apply Hb. symmetry. apply wdot_all_equal.
apply Forall_Exists_neg in Hn. eapply Forall_impl; [|exact Hn]. cbn. intros a Ha. lia.
- intros (a & b & Ha & Hb & Hne).
pose proof (wsum_pos l Hok ltac:(destruct l; [destruct Ha|discriminate])) as Hs.
destruct (Z.eq_dec (snd a * wsum l) (wdot l)).
+ exists b. split; [exact Hb|]. apply Bool.negb_true_iff, Z.eqb_neq. nia.
+ exists a. split; [exact Ha|]. apply Bool.negb_true_iff, Z.eqb_neq. exact n.
Qed.
Local Open Scope R_scope.
Theorem tree_mean xm xs l :
node_ok l -> l <> [] -> (wsum l <= 2 ^ 32)%Z ->
is_intd xs (wsum l) -> is_intd xm (wdot l) ->
is_quot (fst (fp_div D RNE xm xs)) (wdot l) (wsum l) /\
(wdot l <= 255 * wsum l)%Z /\
no_nv_dz (snd (fp_div D RNE xm xs)).
Proof.
intros Hok Hne Hs Hxs Hxm.
pose proof (wsum_pos l Hok Hne). pose proof (wdot_bounds l Hok).
destruct (is_quot_div xm xs _ _ Hxm Hxs) as [Hq Hfl]; [lia| |].
{ split; [lia|]. apply Z.le_lt_trans with (255 * 2 ^ 32)%Z; [nia|reflexivity]. }
split; [exact Hq|]. split; [lia|exact Hfl].
Qed.




Corollary variance_sign acc xs l :
node_ok l -> l <> [] -> (wsum l <= 2 ^ 32)%Z -> (Z.of_nat (length l) < 2 ^ 53)%Z ->
vacc acc (Z.of_nat (length l)) (neq_meanb (wsum l) (wdot l) l) -> is_intd xs (wsum l) ->
exists v, dval (fst (fp_div D RNE acc xs)) v /\ 0 <= v /\
(0 < v <-> exists a b, In a l /\ In b l /\ snd a <> snd b).
Proof.
intros Hok Hne Hs Hlen Hacc Hxs.
pose proof (wsum_pos l Hok Hne) as Hs1.
destruct (variance_final acc (Z.of_nat (length l)) _ xs (wsum l) Hacc Hxs ltac:(lia) ltac:(lia)) as [(v & Hv & Hvr & Hpos) _].
exists v. split; [exact Hv|]. split; [lra|].
rewrite <- (neq_mean_iff l Hok).
destruct (neq_meanb (wsum l) (wdot l) l); split; intros H; auto; try lra; try discriminate.
Qed.
