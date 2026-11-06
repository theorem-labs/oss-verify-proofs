(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Reals Psatz SpecFloat Bool.
From Flocq Require Import Core.Core Calc.Bracket Calc.Round Calc.Operations
IEEE754.BinarySingleNaN.
From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM00 YM07 YM05 YM04.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section g.
Variable f : format.
Hypothesis Hf : format_ok f.
Local Abbreviation prec := (fp_prec f).
Local Abbreviation emax := (fp_emax f).
Lemma prec_pos : 0 < prec.
Proof. exact (prec_gt_0_f f Hf). Qed.
Lemma prec_lt_emax : prec < emax.
Proof. exact (fok_prec_emax f Hf). Qed.
Lemma int_format (n : Z) : Z.abs n <= 2 ^ prec -> Rep f (IZR n).
Proof. apply (Rep_int f Hf). Qed.
Lemma int_lt_emax (n : Z) :
Z.abs n <= 2 ^ prec -> (Rabs (IZR n) < bpow radix2 emax)%R.
Proof.
intros Hn. rewrite <- abs_IZR.
apply Rle_lt_trans with (bpow radix2 prec).
- rewrite <- (IZR_Zpower radix2) by (pose proof prec_pos; lia). apply IZR_le. exact Hn.
- apply bpow_lt. exact prec_lt_emax.
Qed.
Definition is_intf (x n : Z) : Prop := fval f x = Some (IZR n) /\ Z.abs n <= 2 ^ prec.
Lemma is_intf_add md a b m n :
is_intf a m -> is_intf b n -> Z.abs (m + n) <= 2 ^ prec ->
is_intf (fst (fp_add f md a b)) (m + n) /\ snd (fp_add f md a b) = no_flags.
Proof.
intros [Ha _] [Hb _] Hmn.
destruct (fp_add_finite f Hf md a b _ _ Ha Hb) as (_ & _ & Hex).
rewrite <- plus_IZR in Hex. destruct (Hex (int_format _ Hmn) (int_lt_emax _ Hmn)) as [Hv Hfl].
repeat split; auto.
Qed.
Lemma is_intf_sub md a b m n :
is_intf a m -> is_intf b n -> Z.abs (m - n) <= 2 ^ prec ->
is_intf (fst (fp_sub f md a b)) (m - n) /\ snd (fp_sub f md a b) = no_flags.
Proof.
intros [Ha _] [Hb _] Hmn.
destruct (fp_sub_finite f Hf md a b _ _ Ha Hb) as (_ & _ & Hex).
rewrite <- minus_IZR in Hex. destruct (Hex (int_format _ Hmn) (int_lt_emax _ Hmn)) as [Hv Hfl].
repeat split; auto.
Qed.


Lemma is_intf_of_int md signed bits v :
Z.abs (int_val signed bits v) <= 2 ^ prec ->
is_intf (fst (fp_of_int f md signed bits v)) (int_val signed bits v) /\
snd (fp_of_int f md signed bits v) = no_flags.
Proof.
intros Hn. destruct (fp_of_int_finite f Hf md signed bits v) as (_ & _ & Hex).
destruct (Hex (int_format _ Hn) (int_lt_emax _ Hn)) as [Hv Hfl]. repeat split; auto.
Qed.

Lemma is_intf_lt a b m n :
is_intf a m -> is_intf b n -> fp_lt f a b = (Z.ltb m n, no_flags).
Proof.
intros [Ha _] [Hb _]. rewrite (fp_lt_fval f Hf a b _ _ Ha Hb). f_equal.
destruct (Z.ltb_spec m n) as [H|H].
- apply Rlt_bool_true. apply IZR_lt. exact H.
- apply Rlt_bool_false. apply IZR_le. exact H.
Qed.

Lemma is_intf_to_int md signed bits a n :
is_intf a n -> int_lo signed bits <= n <= int_hi signed bits ->
fp_to_int f md signed bits a = (int_wrap bits n, no_flags).
Proof.
intros [Ha _] Hr.
assert (Hn : round_mode (flocq_mode md) (IZR n) = n) by (apply Zrnd_IZR, valid_rnd_round_mode).
destruct (fp_to_int_finite f Hf md signed bits a (IZR n) Ha) as (Hv & _ & Hfl); [rewrite Hn; exact Hr|].
rewrite Hn in Hv, Hfl. specialize (Hfl eq_refl).
destruct (fp_to_int f md signed bits a); simpl in *; congruence.
Qed.
End g.
Lemma int_wrap_mod bits v : 0 <= bits -> int_wrap bits v = v mod 2 ^ bits.
Proof. intros. unfold int_wrap. apply Z.land_ones. assumption. Qed.
Lemma int_wrap_id bits v : 0 <= bits -> 0 <= v < 2 ^ bits -> int_wrap bits v = v.
Proof. intros. rewrite int_wrap_mod by assumption. apply Z.mod_small. assumption. Qed.
Lemma int_val_unsigned bits v : 0 <= bits -> int_val false bits v = v mod 2 ^ bits.
Proof. intros. unfold int_val. simpl. apply int_wrap_mod. assumption. Qed.
Definition sint32 (v : Z) : Z :=
let u := v mod 2 ^ 32 in if u <? 2 ^ 31 then u else u - 2 ^ 32.



Local Abbreviation D := fmt_double.
Local Abbreviation S := fmt_single.
Definition dval (x : Z) (r : R) : Prop := fval fmt_double x = Some r.
Definition sval (x : Z) (r : R) : Prop := fval fmt_single x = Some r.
Definition is_intd (x n : Z) : Prop := dval x (IZR n) /\ Z.abs n <= 2 ^ 53.
Definition is_ints (x n : Z) : Prop := sval x (IZR n) /\ Z.abs n <= 2 ^ 24.
Lemma is_intd_intf x n : is_intd x n <-> is_intf D x n.
Proof. unfold is_intd, is_intf, dval. simpl (fp_prec D). tauto. Qed.
Lemma is_ints_intf x n : is_ints x n <-> is_intf S x n.
Proof. unfold is_ints, is_intf, sval. simpl (fp_prec S). tauto. Qed.
Lemma is_intd_dval x n : is_intd x n -> dval x (IZR n).
Proof. intros [H _]; exact H. Qed.

Lemma is_intd_zero : is_intd 0 0.
Proof. split. apply (fval_0 D fmt_double_ok). simpl; lia. Qed.
Lemma is_ints_zero : is_ints 0 0.
Proof. split. apply (fval_0 S fmt_single_ok). simpl; lia. Qed.
Theorem is_intd_of_int_wu md v :
is_intd (fst (fp_of_int D md false 32 v)) (v mod 2 ^ 32) /\
snd (fp_of_int D md false 32 v) = no_flags.
Proof.
rewrite <- (int_val_unsigned 32 v) by lia. rewrite is_intd_intf.
apply (is_intf_of_int D fmt_double_ok). rewrite int_val_unsigned by lia.
pose proof (Z.mod_pos_bound v (2 ^ 32)). simpl (fp_prec D). lia.
Qed.


Theorem is_ints_of_int_wu md v :
v mod 2 ^ 32 <= 2 ^ 24 ->
is_ints (fst (fp_of_int S md false 32 v)) (v mod 2 ^ 32) /\
snd (fp_of_int S md false 32 v) = no_flags.
Proof.
intros Hv. rewrite <- (int_val_unsigned 32 v) by lia. rewrite is_ints_intf.
apply (is_intf_of_int S fmt_single_ok). rewrite int_val_unsigned by lia.
pose proof (Z.mod_pos_bound v (2 ^ 32)). simpl (fp_prec S). lia.
Qed.

Theorem is_intd_add md a b m n :
is_intd a m -> is_intd b n -> Z.abs (m + n) <= 2 ^ 53 ->
is_intd (fst (fp_add D md a b)) (m + n) /\ snd (fp_add D md a b) = no_flags.
Proof. rewrite !is_intd_intf. apply (is_intf_add D fmt_double_ok). Qed.
Theorem is_intd_sub md a b m n :
is_intd a m -> is_intd b n -> Z.abs (m - n) <= 2 ^ 53 ->
is_intd (fst (fp_sub D md a b)) (m - n) /\ snd (fp_sub D md a b) = no_flags.
Proof. rewrite !is_intd_intf. apply (is_intf_sub D fmt_double_ok). Qed.





Theorem is_intd_flt a b m n : is_intd a m -> is_intd b n -> fp_lt D a b = (Z.ltb m n, no_flags).
Proof. rewrite !is_intd_intf. apply (is_intf_lt D fmt_double_ok). Qed.




Theorem is_intd_to_lu md a n :
is_intd a n -> 0 <= n -> fp_to_int D md false 64 a = (n, no_flags).
Proof.
intros Ha Hn. rewrite is_intd_intf in Ha. pose proof (proj2 Ha) as Hb. simpl (fp_prec D) in Hb.
rewrite (is_intf_to_int D fmt_double_ok md false 64 a n Ha).
- rewrite int_wrap_id; [reflexivity|lia|]. split; [lia|].
apply Z.le_lt_trans with (2 ^ 53); [lia|]. apply Z.pow_lt_mono_r; lia.
- unfold int_lo, int_hi. change (Z.shiftl 1 64) with (2 ^ 64).
split; [lia|]. apply Z.le_trans with (2 ^ 53); [lia|].
assert (2 ^ 53 < 2 ^ 64) by (apply Z.pow_lt_mono_r; lia). lia.
Qed.
















Local Open Scope R_scope.
Definition RepD : R -> Prop := Rep D.
Definition NearestD : R -> R -> Prop := Nearest D.
Lemma formatd_int n : (Z.abs n <= 2 ^ 53)%Z -> RepD (IZR n).
Proof. intros H. apply (Rep_int D fmt_double_ok). exact H. Qed.
Lemma dval_format x r : dval x r -> RepD r.
Proof. intros H. apply (fval_rep D fmt_double_ok x r H). Qed.
Lemma bpow_D_format e : (-1074 <= e)%Z -> RepD (bpow radix2 e).
Proof. intros. apply (Rep_bpow D fmt_double_ok). exact H. Qed.
Definition is_quot (d m s : Z) : Prop :=
(0 < s <= 2 ^ 32)%Z /\ (0 <= m < 2 ^ 53)%Z /\
exists q, dval d q /\ NearestD (IZR m / IZR s) q.
Lemma quot_range m s :
(0 < s)%Z -> (0 <= m)%Z -> 0 <= IZR m / IZR s <= IZR m.
Proof.
intros Hs Hm.
assert (H0s : 0 < IZR s) by (apply IZR_lt; lia).
assert (H1s : 1 <= IZR s) by (apply (IZR_le 1); lia).
assert (HmR : 0 <= IZR m) by (apply (IZR_le 0); lia).
split.
- apply Rmult_le_pos; [lra|]. left. apply Rinv_0_lt_compat. exact H0s.
- rewrite <- (Rdiv_1_r (IZR m)) at 2. unfold Rdiv. apply Rmult_le_compat_l; [lra|].
apply Rinv_le_contravar; lra.
Qed.
Theorem is_quot_div xm xs m s :
is_intd xm m -> is_intd xs s -> (0 < s <= 2 ^ 32)%Z -> (0 <= m < 2 ^ 53)%Z ->
is_quot (fst (fp_div D RNE xm xs)) m s /\ no_nv_dz (snd (fp_div D RNE xm xs)).
Proof.
intros [Hm _] [Hs _] Hsr Hmr.
assert (Hsnz : IZR s <> 0) by (apply not_0_IZR; lia).
destruct (fp_div_finite D fmt_double_ok RNE xm xs _ _ Hm Hs Hsnz) as [Hfl Hv].
split; [|exact Hfl]. split; [exact Hsr|]. split; [exact Hmr|].
destruct (quot_range m s ltac:(lia) ltac:(lia)) as [Hq0 Hq1].
destruct (Hv eq_refl (bpow radix2 53)) as (q & Hd & Hn & _).
- apply bpow_D_format. lia.
- rewrite Rabs_pos_eq by lra. apply Rle_trans with (IZR m); [lra|].
rewrite <- (IZR_Zpower radix2) by lia. apply IZR_le. change (radix_val radix2) with 2%Z. lia.
- apply bpow_lt. reflexivity.
- exists q. split; assumption.
Qed.

Theorem quot_bounds m s q :
(0 < s)%Z -> (0 <= m)%Z -> NearestD (IZR m / IZR s) q ->
0 <= q /\ ((m <= 255 * s)%Z -> q <= 255).
Proof.
intros Hs Hm Hn.
assert (H0s : 0 < IZR s) by (apply IZR_lt; lia).
destruct (quot_range m s Hs Hm) as [Hq0 _].
split.
- apply (Nearest_nonneg D fmt_double_ok _ _ Hn). exact Hq0.
- intros Hle. apply (Nearest_le D _ _ 255 Hn). apply (formatd_int 255). cbn; lia.
apply (Rmult_le_reg_r (IZR s)); [exact H0s|].
unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
rewrite <- (mult_IZR 255). apply IZR_le. lia.
Qed.

Lemma quot_gap m s c q :
(0 < s <= 2 ^ 32)%Z -> (0 <= m < 2 ^ 53)%Z -> NearestD (IZR m / IZR s) q ->
((c * s < m)%Z -> IZR c < q) /\
((m < c * s)%Z -> q < IZR c) /\
((c * s = m)%Z -> q = IZR c).
Proof.
intros Hs Hm Hn.
assert (H0s : 0 < IZR s) by (apply IZR_lt; lia).
assert (Hsinv : 0 < / IZR s) by (apply Rinv_0_lt_compat; exact H0s).
destruct (quot_range m s ltac:(lia) ltac:(lia)) as [Hx0 Hx1].
assert (Fc : forall k : Z, (Z.abs k <= 2 ^ 53)%Z -> RepD (IZR k)).
{ intros k Hk. apply formatd_int. exact Hk. }
assert (Key : forall k : Z, (Z.abs k <= 2 ^ 53)%Z -> q = IZR k -> (k * s = m)%Z).
{ intros k Hk Hqk.
destruct (Z.eq_dec (k * s) m) as [|Hne]; [assumption|exfalso].
destruct (Z.eq_dec m 0) as [Hm0|Hm0].
{
assert (q = 0) as Hq0.
{ apply (Nearest_id D). apply (Rep_0 D fmt_double_ok).
replace 0 with (IZR m / IZR s); [exact Hn|]. rewrite Hm0. unfold Rdiv. apply Rmult_0_l. }
rewrite Hq0 in Hqk. apply eq_sym, eq_IZR_R0 in Hqk. subst k. lia. }
assert (Hx : bpow radix2 (-32) <= Rabs (IZR m / IZR s) < bpow radix2 53).
{ rewrite Rabs_pos_eq by lra. split.
- apply Rle_trans with (/ IZR s).
+ change (bpow radix2 (-32)) with (/ IZR (2 ^ 32)).
apply Rinv_le_contravar. exact H0s. apply IZR_le. lia.
+ rewrite <- (Rmult_1_l (/ IZR s)) at 1. unfold Rdiv. apply Rmult_le_compat_r. lra.
apply IZR_le. lia.
- apply Rle_lt_trans with (IZR m); [lra|]. rewrite <- (IZR_Zpower radix2) by lia. apply IZR_lt.
change (radix_val radix2) with 2%Z. lia. }
pose proof (Nearest_error D fmt_double_ok _ _ (-32) 53 Hn ltac:(cbn; lia) Hx) as Herr.
change (bpow radix2 (- fp_prec D)) with (bpow radix2 (-53)) in Herr.
rewrite (Rabs_pos_eq (IZR m / IZR s)) in Herr by lra.
assert (Hb53 : bpow radix2 (-53) = / IZR (2 ^ 53)) by (cbn; reflexivity).
assert (H253 : 0 < IZR (2 ^ 53)) by (apply IZR_lt; reflexivity).
assert (Hm53 : IZR m * / IZR (2 ^ 53) < 1).
{ apply (Rmult_lt_reg_r (IZR (2 ^ 53))); [exact H253|].
rewrite Rmult_assoc, Rinv_l, Rmult_1_r, Rmult_1_l by lra. apply IZR_lt. lia. }
assert (Hlt1 : IZR m / IZR s * bpow radix2 (-53) < / IZR s).
{ rewrite Hb53. unfold Rdiv.
replace (IZR m * / IZR s * / IZR (2 ^ 53)) with ((IZR m * / IZR (2 ^ 53)) * / IZR s) by ring.
rewrite <- (Rmult_1_l (/ IZR s)) at 2. apply Rmult_lt_compat_r; [exact Hsinv|exact Hm53]. }
assert (Hge : / IZR s <= Rabs (IZR k - IZR m / IZR s)).
{ replace (IZR k - IZR m / IZR s) with ((IZR (k * s - m)) * / IZR s).
2:{ rewrite minus_IZR, mult_IZR. field. lra. }
rewrite Rabs_mult, (Rabs_pos_eq (/ IZR s)) by lra.
rewrite <- (Rmult_1_l (/ IZR s)) at 1. apply Rmult_le_compat_r. lra.
rewrite <- abs_IZR. apply (IZR_le 1). lia. }
rewrite <- Hqk in Hge.
pose proof (Rabs_triang_inv q (IZR m / IZR s)). lra. }
assert (Hq0 : 0 <= q).
{ apply (Nearest_nonneg D fmt_double_ok _ _ Hn). lra. }
assert (Hq1 : q <= IZR (2 ^ 53)).
{ apply (Nearest_le D _ _ _ Hn). apply formatd_int. cbn; lia.
apply Rle_trans with (IZR m); [lra|]. apply IZR_le; lia. }
split; [|split].
- intros Hlt.
destruct (Z.le_gt_cases (Z.abs c) (2 ^ 53)) as [Hc|Hc].
+ assert (Hle : IZR c <= q).
{ apply (Nearest_ge D _ _ _ Hn). apply Fc, Hc.
apply Rlt_le. apply (Rmult_lt_reg_r (IZR s)). exact H0s.
unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra. rewrite <- mult_IZR. apply IZR_lt. lia. }
destruct (Req_dec (IZR c) q) as [Heq|Hne]; [|lra].
exfalso. symmetry in Heq. pose proof (Key c Hc Heq). lia.
+
assert (c < 0)%Z by nia. apply Rlt_le_trans with 0; [|exact Hq0]. apply IZR_lt. lia.
- intros Hlt.
destruct (Z.le_gt_cases (Z.abs c) (2 ^ 53)) as [Hc|Hc].
+ assert (Hle : q <= IZR c).
{ apply (Nearest_le D _ _ _ Hn). apply Fc, Hc.
apply Rlt_le. apply (Rmult_lt_reg_r (IZR s)). exact H0s.
unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra. rewrite <- mult_IZR. apply IZR_lt. lia. }
destruct (Req_dec q (IZR c)) as [Heq|Hne]; [|lra].
exfalso. pose proof (Key c Hc Heq). lia.
+ assert (2 ^ 53 < c)%Z by nia. apply Rle_lt_trans with (IZR (2 ^ 53)); [exact Hq1|]. apply IZR_lt. lia.
- intros Heq.
assert (Hx : IZR m / IZR s = IZR c).
{ rewrite <- Heq, mult_IZR. field. lra. }
rewrite Hx in Hn. apply (Nearest_id D); [|exact Hn]. apply Fc. nia.
Qed.
Theorem is_quot_cmp xc c d m s :
is_intd xc c -> is_quot d m s ->
fp_lt D xc d = (Z.ltb (c * s) m, no_flags) /\
fp_le D xc d = (Z.leb (c * s) m, no_flags) /\
fp_lt D d xc = (Z.ltb m (c * s), no_flags) /\
fp_le D d xc = (Z.leb m (c * s), no_flags).
Proof.
intros [Hc Hcb] (Hs & Hm & q & Hd & Hn).
destruct (quot_gap m s c q Hs Hm Hn) as (G1 & G2 & G3).
rewrite (fp_lt_fval D fmt_double_ok xc d _ _ Hc Hd).
rewrite (fp_le_fval D fmt_double_ok xc d _ _ Hc Hd).
rewrite (fp_lt_fval D fmt_double_ok d xc _ _ Hd Hc).
rewrite (fp_le_fval D fmt_double_ok d xc _ _ Hd Hc).
assert (E1 : Rlt_bool (IZR c) q = Z.ltb (c * s) m).
{ destruct (Z.ltb_spec (c * s) m) as [H|H].
- apply Rlt_bool_true. apply G1. exact H.
- apply Rlt_bool_false. destruct (Z.eq_dec (c * s) m) as [H'|H'].
+ rewrite (G3 H'). lra. + apply Rlt_le, G2. lia. }
assert (E2 : Rle_bool (IZR c) q = Z.leb (c * s) m).
{ destruct (Z.leb_spec (c * s) m) as [H|H].
- apply Rle_bool_true. destruct (Z.eq_dec (c * s) m) as [H'|H'].
+ rewrite (G3 H'). lra. + apply Rlt_le, G1. lia.
- apply Rle_bool_false. apply G2. lia. }
assert (E3 : Rlt_bool q (IZR c) = Z.ltb m (c * s)).
{ destruct (Z.ltb_spec m (c * s)) as [H|H].
- apply Rlt_bool_true. apply G2. exact H.
- apply Rlt_bool_false. destruct (Z.eq_dec (c * s) m) as [H'|H'].
+ rewrite (G3 H'). lra. + apply Rlt_le, G1. lia. }
assert (E4 : Rle_bool q (IZR c) = Z.leb m (c * s)).
{ destruct (Z.leb_spec m (c * s)) as [H|H].
- apply Rle_bool_true. destruct (Z.eq_dec (c * s) m) as [H'|H'].
+ rewrite (G3 H'). lra. + apply Rlt_le, G2. lia.
- apply Rle_bool_false. apply G1. lia. }
rewrite E1, E2, E3, E4. repeat split; reflexivity.
Qed.
Corollary crawl_scan_le md (p d m s : Z) :
(0 <= p < 2 ^ 32)%Z -> is_quot d m s ->
fst (fp_le D (fst (fp_of_int D md false 32 p)) d) = Z.leb (p * s) m.
Proof.
intros Hp Hq. destruct (is_intd_of_int_wu md p) as [Hi _].
rewrite Z.mod_small in Hi by lia.
destruct (is_quot_cmp _ _ _ _ _ Hi Hq) as (_ & -> & _). reflexivity.
Qed.
Corollary crawl_scan_gt md (p d m s : Z) :
(0 <= p < 2 ^ 32)%Z -> is_quot d m s ->
fst (fp_lt D d (fst (fp_of_int D md false 32 p))) = Z.ltb m (p * s).
Proof.
intros Hp Hq. destruct (is_intd_of_int_wu md p) as [Hi _].
rewrite Z.mod_small in Hi by lia.
destruct (is_quot_cmp _ _ _ _ _ Hi Hq) as (_ & _ & -> & _). reflexivity.
Qed.
