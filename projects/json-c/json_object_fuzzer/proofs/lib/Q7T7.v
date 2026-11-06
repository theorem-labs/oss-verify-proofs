(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith Lia Bool.
From Stdlib Require Import Floats.SpecFloat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsjA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B.
Open Scope Z_scope.

Definition dsgn (x : Z) : bool := 2^63 <=? x.
Definition dmag (x : Z) : Z := x mod 2^63.
Definition dexp (x : Z) : Z := dmag x / 2^52.
Definition dman (x : Z) : Z := x mod 2^52.
Definition dkey (x : Z) : Z := if dsgn x then - dmag x else dmag x.
Definition DINF : Z := 2047 * 2^52.
Definition dnan (x : Z) : bool := DINF <? dmag x.

Section Bits.
Variable x : Z.
Hypothesis Hx : 0 <= x < 2^64.

#[using="Hx"] Lemma dmag_range : 0 <= dmag x < 2^63. Proof. unfold dmag. Z.div_mod_to_equations. lia. Qed.
#[using="Hx"] Lemma dman_range : 0 <= dman x < 2^52. Proof. unfold dman. Z.div_mod_to_equations. lia. Qed.
#[using="Hx"] Lemma dexp_range : 0 <= dexp x < 2^11. Proof. unfold dexp, dmag. Z.div_mod_to_equations. lia. Qed.
#[using="Hx"] Lemma dmag_split : dmag x = dexp x * 2^52 + dman x.
Proof. unfold dexp, dman, dmag. Z.div_mod_to_equations. lia. Qed.

#[using="Hx"] Lemma sign_bit_eq : fp_sign_bit fmt_double x = dsgn x.
Proof.
change (fp_sign_bit fmt_double x) with (Z.testbit x 63).
rewrite Z.testbit_odd, Z.shiftr_div_pow2 by lia. unfold dsgn.
destruct (Z.leb_spec (2^63) x).
- replace (x / 2^63) with 1 by (Z.div_mod_to_equations; lia). reflexivity.
- replace (x / 2^63) with 0 by (Z.div_mod_to_equations; lia). reflexivity.
Qed.

#[using="Hx"] Lemma exp_field_eq : fp_exp_field fmt_double x = dexp x.
Proof.
change (fp_exp_field fmt_double x) with (Z.land (Z.shiftr x 52) (Z.ones 11)).
rewrite Z.land_ones by lia. rewrite Z.shiftr_div_pow2 by lia. unfold dexp, dmag. Z.div_mod_to_equations. lia.
Qed.

#[using="Hx"] Lemma man_field_eq : fp_man_field fmt_double x = dman x.
Proof.
change (fp_man_field fmt_double x) with (Z.land x (Z.ones 52)). rewrite Z.land_ones by lia. reflexivity.
Qed.

End Bits.

Definition sf_rank (f : spec_float) : Z :=
match f with
| S754_zero _ => 0
| S754_infinity _ => DINF
| S754_finite _ M E => if Z.pos M <? 2^52 then Z.pos M else (E + 1075) * 2^52 + (Z.pos M - 2^52)
| S754_nan => 0
end.
Definition sf_wf (f : spec_float) : Prop :=
match f with
| S754_finite _ M E => (Z.pos M < 2^52 /\ E = -1074) \/ (2^52 <= Z.pos M < 2^53 /\ -1074 <= E <= 971)
| S754_nan => False
| _ => True
end.
Definition sf_key (f : spec_float) : Z := if sf_sign f then - sf_rank f else sf_rank f.

Lemma sf_rank_range : forall f, sf_wf f -> 0 <= sf_rank f <= DINF /\ (forall s M E, f = S754_finite s M E -> 0 < sf_rank f < DINF).
Proof.
intros f W. unfold sf_wf, sf_rank, DINF in *. destruct f as [s|s| |s M E]; try contradiction.
- split; [lia|]. intros; discriminate.
- split; [lia|]. intros; discriminate.
- destruct (Z.ltb_spec (Z.pos M) (2^52)); (split; [lia | intros; lia]).
Qed.

Lemma poscmp_Z : forall m1 m2, Pos.compare_cont Eq m1 m2 = Z.compare (Z.pos m1) (Z.pos m2).
Proof. intros. reflexivity. Qed.

Ltac norm_cmp t := first [ replace t with Lt by (symmetry; apply Z.compare_lt_iff; lia)
| replace t with Gt by (symmetry; apply Z.compare_gt_iff; lia)
| replace t with Eq by (symmetry; apply Z.compare_eq_iff; lia) ].
Ltac zcmp := cbn [CompOpp]; repeat match goal with |- context [Z.compare ?a ?b] => norm_cmp (Z.compare a b) end; cbn [CompOpp]; reflexivity.

Definition lex (E1 E2 : Z) (M1 M2 : positive) : comparison :=
match Z.compare E1 E2 with Lt => Lt | Gt => Gt | Eq => Pos.compare_cont Eq M1 M2 end.

Lemma lex_rank : forall s1 s2 M1 E1 M2 E2,
sf_wf (S754_finite s1 M1 E1) -> sf_wf (S754_finite s2 M2 E2) ->
lex E1 E2 M1 M2 = Z.compare (sf_rank (S754_finite s1 M1 E1)) (sf_rank (S754_finite s2 M2 E2)).
Proof.
intros s1 s2 M1 E1 M2 E2 W1 W2. unfold lex, sf_wf, sf_rank, DINF in *. rewrite poscmp_Z.
destruct (Z.ltb_spec (Z.pos M1) (2^52)) as [A1|B1]; destruct (Z.ltb_spec (Z.pos M2) (2^52)) as [A2|B2];
destruct (Z.compare_spec E1 E2) as [HE|HE|HE]; first [zcmp | exfalso; lia | idtac].
subst E2. destruct (Z.compare_spec (Z.pos M1) (Z.pos M2)); zcmp.
Qed.

Lemma CompOpp_compare : forall a b, CompOpp (Z.compare a b) = Z.compare (- a) (- b).
Proof. intros a b. destruct (Z.compare_spec a b); zcmp. Qed.

Lemma SFcompare_key : forall f1 f2, sf_wf f1 -> sf_wf f2 -> SFcompare f1 f2 = Some (Z.compare (sf_key f1) (sf_key f2)).
Proof.
intros f1 f2 W1 W2.
pose proof (sf_rank_range f1 W1) as [R1 F1]. pose proof (sf_rank_range f2 W2) as [R2 F2].
unfold sf_key.
destruct f1 as [s1|s1| |s1 M1 E1]; destruct f2 as [s2|s2| |s2 M2 E2]; try contradiction;
try (specialize (F1 _ _ _ eq_refl)); try (specialize (F2 _ _ _ eq_refl)).
all: try (cbn [SFcompare sf_sign]; generalize dependent (sf_rank (S754_finite s1 M1 E1)); intros; destruct s1; destruct s2; f_equal; unfold sf_rank, DINF in *; zcmp).
all: try (cbn [SFcompare sf_sign]; generalize dependent (sf_rank (S754_finite s2 M2 E2)); intros; destruct s1; destruct s2; f_equal; unfold sf_rank, DINF in *; zcmp).
all: try (cbn [SFcompare sf_sign]; destruct s1; destruct s2; f_equal; unfold sf_rank, DINF in *; zcmp).

cbn [SFcompare sf_sign]. destruct s1; destruct s2; f_equal.
- transitivity (CompOpp (lex E1 E2 M1 M2)); [unfold lex; destruct (E1 ?= E2); reflexivity|].
rewrite (lex_rank true true M1 E1 M2 E2 W1 W2). apply CompOpp_compare.
- zcmp.
- zcmp.
- fold (lex E1 E2 M1 M2). apply (lex_rank false false M1 E1 M2 E2 W1 W2).
Qed.

Lemma fp_decode_double : forall x, 0 <= x < 2^64 ->
fp_decode fmt_double x =
(if dexp x =? 0 then match dman x with Zpos p => S754_finite (dsgn x) p (-1074) | _ => S754_zero (dsgn x) end
else if dexp x =? 2047 then (if dman x =? 0 then S754_infinity (dsgn x) else S754_nan)
else match 2^52 + dman x with Zpos p => S754_finite (dsgn x) p (dexp x - 1075) | _ => S754_nan end).
Proof.
intros x Hx. unfold fp_decode. rewrite (sign_bit_eq x Hx), (exp_field_eq x Hx), (man_field_eq x Hx).
change (fp_emin fmt_double) with (-1074). change (Z.ones (fp_ew fmt_double)) with 2047.
change (Z.shiftl 1 (fp_mw fmt_double)) with (2^52).
replace (dexp x + -1074 - 1) with (dexp x - 1075) by lia. reflexivity.
Qed.

Lemma fp_decode_ok : forall x, 0 <= x < 2^64 -> dnan x = false ->
sf_wf (fp_decode fmt_double x) /\ sf_key (fp_decode fmt_double x) = dkey x.
Proof.
intros x Hx Hn. rewrite (fp_decode_double x Hx).
pose proof (dmag_split x Hx) as SP. pose proof (dexp_range x Hx) as ER. pose proof (dman_range x Hx) as MR.
unfold dnan in Hn. apply Z.ltb_ge in Hn. unfold dkey, sf_key, sf_wf, sf_rank, sf_sign.
destruct (Z.eqb_spec (dexp x) 0) as [E0|E0].
- rewrite E0 in SP. destruct (dman x) as [|p|p] eqn:EM.
+ split; [exact I|]. destruct (dsgn x); lia.
+ split; [left; lia|]. replace (Z.pos p <? 2^52) with true by (symmetry; apply Z.ltb_lt; lia).
destruct (dsgn x); lia.
+ lia.
- destruct (Z.eqb_spec (dexp x) 2047) as [E1|E1].
+ destruct (Z.eqb_spec (dman x) 0) as [M0|M0].
* split; [exact I|]. unfold DINF. destruct (dsgn x); lia.
* exfalso. unfold DINF in Hn. lia.
+ destruct (2^52 + dman x) as [|p|p] eqn:EP; [lia| |lia].
split; [right; lia|].
replace (Z.pos p <? 2^52) with false by (symmetry; apply Z.ltb_ge; lia).
destruct (dsgn x); lia.
Qed.

Theorem fp_compare_double : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
dnan x = false -> dnan y = false ->
fp_compare fmt_double x y = Some (dkey x ?= dkey y).
Proof.
intros x y Hx Hy Nx Ny. unfold fp_compare.
destruct (fp_decode_ok x Hx Nx) as [Wx <-]. destruct (fp_decode_ok y Hy Ny) as [Wy <-].
apply SFcompare_key; assumption.
Qed.

Corollary fp_lt_double : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> dnan x = false -> dnan y = false ->
fst (fp_lt fmt_double x y) = (dkey x <? dkey y).
Proof.
intros. unfold fp_lt. cbn [fst]. rewrite fp_compare_double by assumption.
destruct (Z.compare_spec (dkey x) (dkey y)); symmetry; first [apply Z.ltb_lt; lia | apply Z.ltb_ge; lia].
Qed.

Corollary fp_le_double : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> dnan x = false -> dnan y = false ->
fst (fp_le fmt_double x y) = (dkey x <=? dkey y).
Proof.
intros. unfold fp_le. cbn [fst]. rewrite fp_compare_double by assumption.
destruct (Z.compare_spec (dkey x) (dkey y)); symmetry; first [apply Z.leb_le; lia | apply Z.leb_gt; lia].
Qed.

Corollary fp_eq_double : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> dnan x = false -> dnan y = false ->
fst (fp_eq fmt_double x y) = (dkey x =? dkey y).
Proof.
intros. unfold fp_eq. cbn [fst]. rewrite fp_compare_double by assumption.
destruct (Z.compare_spec (dkey x) (dkey y)); symmetry; first [apply Z.eqb_eq; lia | apply Z.eqb_neq; lia].
Qed.

Definition wmag (a : word) : Z := dmag (bv_unsigned a).
Definition wkey (a : word) : Z := dkey (bv_unsigned a).
Definition wnan (a : word) : bool := dnan (bv_unsigned a).

Lemma flt_d_key : forall a b : word, wnan a = false -> wnan b = false -> flt_d a b = (wkey a <? wkey b).
Proof. intros a b Na Nb. unfold flt_d, wkey. apply fp_lt_double; auto using u64_range. Qed.
Lemma fle_d_key : forall a b : word, wnan a = false -> wnan b = false -> fle_d a b = (wkey a <=? wkey b).
Proof. intros a b Na Nb. unfold fle_d, wkey. apply fp_le_double; auto using u64_range. Qed.
Lemma feq_d_key : forall a b : word, wnan a = false -> wnan b = false -> feq_d a b = (wkey a =? wkey b).
Proof. intros a b Na Nb. unfold feq_d, wkey. apply fp_eq_double; auto using u64_range. Qed.

Lemma wmag_range : forall a : word, 0 <= wmag a < 2^63.
Proof. intros a. unfold wmag. apply dmag_range, u64_range. Qed.
Lemma wkey_abs : forall a : word, Z.abs (wkey a) = wmag a.
Proof. intros a. unfold wkey, wmag, dkey. pose proof (dmag_range (bv_unsigned a) (u64_range a)). destruct (dsgn _); lia. Qed.
Lemma wnan_mag : forall a : word, wnan a = (DINF <? wmag a).
Proof. reflexivity. Qed.
Lemma wkey_notnan_range : forall a : word, wnan a = false -> - DINF <= wkey a <= DINF.
Proof.
intros a N. unfold wnan, dnan in N. apply Z.ltb_ge in N. pose proof (wkey_abs a). unfold wmag in *. lia.
Qed.

Lemma shl1_shr1_mag : forall z, 0 <= z < 2^64 -> Z.shiftr ((Z.shiftl z 1) mod 2^64) 1 = z mod 2^63.
Proof.
intros z Hz. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2^1) with 2.
Z.div_mod_to_equations. lia.
Qed.

Lemma v_srli_slli_1 : forall a : word, bv_unsigned (v_srli (v_slli a 1) 1) = wmag a.
Proof.
intros a. unfold v_srli, v_slli, wmag, dmag. rewrite !Z_to_bv_unsigned.
pose proof (u64_range a) as Ha.
change (bv_wrap 64 (Z.shiftl (bv_unsigned a) 1)) with ((Z.shiftl (bv_unsigned a) 1) mod 2^64).
rewrite shl1_shr1_mag by exact Ha.
change (bv_wrap 64 (bv_unsigned a mod 2^63)) with ((bv_unsigned a mod 2^63) mod 2^64).
rewrite Z.mod_small; [reflexivity|]. Z.div_mod_to_equations. lia.
Qed.

Lemma nan_test_ltu : forall a : word,
bv_ltu (v_srli (v_slli a 1) 1) (Z_to_bv 64 0x7FF0000000000001) = negb (wnan a).
Proof.
intros a. unfold bv_ltu. rewrite v_srli_slli_1, Z_to_bv_unsigned.
change (bv_wrap 64 0x7FF0000000000001) with (DINF + 1).
rewrite wnan_mag. pose proof (wmag_range a).
destruct (Z.ltb_spec DINF (wmag a)); cbn [negb]; first [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Ltac fp_lit_keys :=
repeat match goal with
| |- context [wkey (Z_to_bv 64 ?c)] => let v := eval vm_compute in (wkey (Z_to_bv 64 c)) in change (wkey (Z_to_bv 64 c)) with v
| |- context [wnan (Z_to_bv 64 ?c)] => let v := eval vm_compute in (wnan (Z_to_bv 64 c)) in change (wnan (Z_to_bv 64 c)) with v
| |- context [wmag (Z_to_bv 64 ?c)] => let v := eval vm_compute in (wmag (Z_to_bv 64 c)) in change (wmag (Z_to_bv 64 c)) with v
| H : context [wkey (Z_to_bv 64 ?c)] |- _ => let v := eval vm_compute in (wkey (Z_to_bv 64 c)) in change (wkey (Z_to_bv 64 c)) with v in H
| H : context [wnan (Z_to_bv 64 ?c)] |- _ => let v := eval vm_compute in (wnan (Z_to_bv 64 c)) in change (wnan (Z_to_bv 64 c)) with v in H
| H : context [wmag (Z_to_bv 64 ?c)] |- _ => let v := eval vm_compute in (wmag (Z_to_bv 64 c)) in change (wmag (Z_to_bv 64 c)) with v in H
end.

Ltac fp_order_prep :=
repeat match goal with
| |- context [flt_d ?a ?b] => rewrite (flt_d_key a b) by (fp_lit_keys; first [assumption|reflexivity])
| |- context [fle_d ?a ?b] => rewrite (fle_d_key a b) by (fp_lit_keys; first [assumption|reflexivity])
| |- context [feq_d ?a ?b] => rewrite (feq_d_key a b) by (fp_lit_keys; first [assumption|reflexivity])
| H : context [flt_d ?a ?b] |- _ => rewrite (flt_d_key a b) in H by (fp_lit_keys; first [assumption|reflexivity])
| H : context [fle_d ?a ?b] |- _ => rewrite (fle_d_key a b) in H by (fp_lit_keys; first [assumption|reflexivity])
| H : context [feq_d ?a ?b] |- _ => rewrite (feq_d_key a b) in H by (fp_lit_keys; first [assumption|reflexivity])
end;
fp_lit_keys;
repeat match goal with
| H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
| H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
| H : (_ <=? _) = true |- _ => apply Z.leb_le in H
| H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
| H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
| H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
| |- (_ <? _) = true => apply Z.ltb_lt
| |- (_ <? _) = false => apply Z.ltb_ge
| |- (_ <=? _) = true => apply Z.leb_le
| |- (_ <=? _) = false => apply Z.leb_gt
| |- (_ =? _) = true => apply Z.eqb_eq
| |- (_ =? _) = false => apply Z.eqb_neq
end.

Ltac fp_order := fp_order_prep; first [lia | match goal with x : word |- _ => pose proof (wkey_notnan_range x ltac:(assumption)); lia end].

Definition D_m2e31   : word := Z_to_bv 64 0xC1E0000000000000.
Definition D_2e31m1  : word := Z_to_bv 64 0x41DFFFFFFFC00000.
Definition D_m2e31m1 : word := Z_to_bv 64 0xC1E0000000200000.
Definition D_2e31    : word := Z_to_bv 64 0x41E0000000000000.
Definition D_2e63    : word := Z_to_bv 64 0x43E0000000000000.
Definition D_m2e63   : word := Z_to_bv 64 0xC3E0000000000000.
Definition D_m2e63x  : word := Z_to_bv 64 0xC3E0000000000001.
Definition D_2e64    : word := Z_to_bv 64 0x43F0000000000000.
Definition D_m1      : word := Z_to_bv 64 0xBFF0000000000000.
Definition D_0       : word := Z_to_bv 64 0.

Section UbCastFacts.
Variable x : word.
Hypothesis NX : wnan x = false.

#[using="NX"] Lemma ub_int_lo : flt_d x (Z_to_bv 64 0xC1E0000000000000) = false -> flt_d (Z_to_bv 64 0xC1E0000000200000) x = true.
Proof. intros. fp_order. Qed.
#[using="NX"] Lemma ub_int_hi : flt_d (Z_to_bv 64 0x41DFFFFFFFC00000) x = false -> flt_d x (Z_to_bv 64 0x41E0000000000000) = true.
Proof. intros. fp_order. Qed.

#[using="NX"] Lemma ub_int64_lo : flt_d x (Z_to_bv 64 0xC3E0000000000000) = false -> flt_d (Z_to_bv 64 0xC3E0000000000001) x = true.
Proof. intros. fp_order. Qed.
#[using="NX"] Lemma ub_int64_hi : fle_d (Z_to_bv 64 0x43E0000000000000) x = false -> flt_d x (Z_to_bv 64 0x43E0000000000000) = true.
Proof. intros. fp_order. Qed.

#[using="NX"] Lemma ub_uint64_lo : flt_d x (Z_to_bv 64 0) = false -> flt_d (Z_to_bv 64 0xBFF0000000000000) x = true.
Proof. intros. fp_order. Qed.
#[using="NX"] Lemma ub_uint64_hi : fle_d (Z_to_bv 64 0x43F0000000000000) x = false -> flt_d x (Z_to_bv 64 0x43F0000000000000) = true.
Proof. intros. fp_order. Qed.
End UbCastFacts.

Lemma nan_test_false : forall x : word,
bv_ltu (v_srli (v_slli x 1) 1) (Z_to_bv 64 0x7FF0000000000001) = true -> wnan x = false.
Proof. intros x H. rewrite nan_test_ltu in H. destruct (wnan x); [discriminate|reflexivity]. Qed.

