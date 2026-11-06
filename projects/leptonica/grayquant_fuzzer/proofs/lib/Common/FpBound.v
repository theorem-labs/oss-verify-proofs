(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool SpecFloat.
From Flocq.Core Require Import Zaux Digits.
From Flocq.IEEE754 Require BinarySingleNaN.
From LinuxProcessSemantics.Riscv Require Import Fpu.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zd2_bounds : forall m, 0 < m -> 2 ^ (Zdigits2 m - 1) <= m < 2 ^ Zdigits2 m.
Proof.
  intros m Hm. rewrite Zdigits2_Zdigits. pose proof (Zdigits_correct radix2 m) as H.
  rewrite Z.abs_eq in H by lia. exact H.
Qed.

Lemma zd2_pos : forall m, 0 < m -> 0 < Zdigits2 m.
Proof. intros [|p|p] H; try lia. reflexivity. Qed.

Lemma zd2_nonneg : forall m, 0 <= Zdigits2 m.
Proof. intros [|p|p]; cbn; lia. Qed.

(* [comment removed for export] *)
Lemma zd2_le : forall m k, 0 < m -> 0 <= k -> (Zdigits2 m <= k <-> m < 2 ^ k).
Proof.
  intros m k Hm Hk. pose proof (zd2_bounds m Hm) as [B1 B2]. pose proof (zd2_pos m Hm) as P. split; intros H.
  - apply Z.lt_le_trans with (1 := B2). apply Z.pow_le_mono_r; lia.
  - destruct (Z_le_gt_dec (Zdigits2 m) k) as [L|G]; [exact L | exfalso].
    assert (2 ^ k <= 2 ^ (Zdigits2 m - 1)) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma zd2_ge : forall m k, 0 < m -> 0 <= k -> 2 ^ k <= m -> k + 1 <= Zdigits2 m.
Proof.
  intros m k Hm Hk H. pose proof (zd2_bounds m Hm) as [B1 B2].
  destruct (Z_le_gt_dec (k + 1) (Zdigits2 m)) as [L|G]; [exact L | exfalso].
  assert (2 ^ Zdigits2 m <= 2 ^ k) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma zd2_pow : forall k, 0 <= k -> Zdigits2 (2 ^ k) = k + 1.
Proof.
  intros k Hk. assert (P : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  apply Z.le_antisymm; [| apply zd2_ge; lia].
  apply zd2_le; [exact P | lia |]. apply Z.pow_lt_mono_r; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pos_iter_xO : forall d m, Z.pos (Pos.iter xO m d) = Z.pos m * 2 ^ Z.pos d.
Proof.
  intros d m. induction d as [|d IH] using Pos.peano_ind.
  - cbn [Pos.iter]. rewrite Pos2Z.inj_xO. change (2 ^ 1) with 2. lia.
  - rewrite Pos.iter_succ, Pos2Z.inj_xO, IH, Pos2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma shl_align_Z : forall mx ex e', let '(mz, ez) := shl_align mx ex e' in
  ez = Z.min ex e' /\ Z.pos mz = Z.pos mx * 2 ^ (ex - ez) /\ Zdigits2 (Z.pos mz) + ez = Zdigits2 (Z.pos mx) + ex.
Proof.
  intros mx ex e'. unfold shl_align. destruct (e' - ex) as [|d|d] eqn:E.
  - assert (ex = e') by lia. subst e'. rewrite Z.min_id, Z.sub_diag. cbn. lia.
  - rewrite Z.min_l by lia. rewrite Z.sub_diag. cbn [Z.pow]. lia.
  - rewrite Z.min_r by lia. replace (ex - e') with (Z.pos d) by lia. split; [reflexivity|]. split; [apply pos_iter_xO|].
    rewrite pos_iter_xO. rewrite !Zdigits2_Zdigits. rewrite (Zdigits_mult_Zpower radix2) by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma shr_fexp_Z : forall p em m e l, 0 <= m ->
  let n := fexp p em (Zdigits2 m + e) - e in
  let '(mrs, e') := shr_fexp p em m e l in
  0 <= shr_m mrs /\ (n <= 0 -> shr_m mrs = m /\ e' = e) /\
  (0 < n -> e' = e + n /\ 2 ^ n * shr_m mrs <= m < 2 ^ n * (shr_m mrs + 1)).
Proof.
  intros p em m e l Hm n. unfold shr_fexp. fold n.
  destruct (shr (shr_record_of_loc m l) e n) as [mrs e'] eqn:E.
  pose proof (BinarySingleNaN.shr_m_shr_record_of_loc m l) as M0.
  destruct (Z_le_gt_dec n 0) as [L|G].
  - assert (E' : shr (shr_record_of_loc m l) e n = (shr_record_of_loc m l, e)) by (unfold shr; destruct n; [reflexivity | lia | reflexivity]).
    rewrite E' in E. injection E as <- <-. rewrite M0. repeat split; try lia.
  - pose proof (BinarySingleNaN.le_shr_le (shr_record_of_loc m l) e n ltac:(rewrite M0; lia) ltac:(lia)) as (H0 & H1).
    rewrite E in H0, H1. cbn [fst] in H0, H1. rewrite M0 in H1.
    assert (Es : e' = e + n) by (unfold shr in E; destruct n; [lia | injection E as _ <-; reflexivity | lia]).
    repeat split; try lia.
Qed.

(* [comment removed for export] *)
Definition canon (f : format) (m : positive) (e : Z) : Prop :=
  Zdigits2 (Z.pos m) <= fp_prec f /\ fp_emin f <= e /\ (Zdigits2 (Z.pos m) = fp_prec f \/ e = fp_emin f).

Definition fmt_ok (f : format) : Prop := 1 < fp_prec f /\ fp_prec f < fp_emax f.
Lemma fmt_ok_single : fmt_ok fmt_single. Proof. split; reflexivity. Qed.
Lemma fmt_ok_double : fmt_ok fmt_double. Proof. split; reflexivity. Qed.

Lemma pow2_split : forall a b, 0 <= a <= b -> 2 ^ b = 2 ^ a * 2 ^ (b - a).
Proof. intros a b H. rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.

(* [comment removed for export] *)
Lemma round_aux_struct : forall f md sx mz ez lx, fmt_ok f ->
  let E := Zdigits2 (Z.pos mz) + ez in
  ez <= fexp (fp_prec f) (fp_emax f) E -> Z.max E (fp_emin f) + 1 <= fp_emax f ->
  fst (round_aux f md sx (Z.pos mz) ez lx) = S754_zero sx \/
  exists m' e', fst (round_aux f md sx (Z.pos mz) ez lx) = S754_finite sx m' e' /\ canon f m' e' /\ e' <= fp_emax f - fp_prec f /\
                Zdigits2 (Z.pos m') + e' <= Z.max E (fp_emin f) + 1.
Proof.
  intros f md sx mz ez lx (Hp & Hpe) E Hal Hov. unfold round_aux, canon, fp_emin in *.
  set (p := fp_prec f) in *. set (em := fp_emax f) in *. set (emn := 3 - em - p) in *.
  set (MX := Z.max E emn) in *. assert (MX1 : E <= MX) by apply Z.le_max_l. assert (MX2 : emn <= MX) by apply Z.le_max_r. clearbody MX.
  pose proof (zd2_bounds (Z.pos mz) ltac:(lia)) as [DZ1 DZ2]. pose proof (zd2_pos (Z.pos mz) ltac:(lia)) as DZ0.
  set (dz := Zdigits2 (Z.pos mz)) in *.
  (* [comment removed for export] *)
  pose proof (shr_fexp_Z p em (Z.pos mz) ez lx ltac:(lia)) as S1. cbv zeta in S1. fold dz in S1. fold E in S1.
  assert (FE : fexp p em E = E - p /\ emn <= E - p \/ fexp p em E = emn /\ E - p < emn) by (unfold fexp, SpecFloat.emin; fold emn; lia).
  set (fe := fexp p em E) in *.
  destruct (shr_fexp p em (Z.pos mz) ez lx) as [mrs1 e1]. destruct S1 as (M1 & S1a & S1b).
  set (m1 := shr_m mrs1) in *.
  assert (E1 : e1 = fe) by (destruct (Z_le_gt_dec (fe - ez) 0) as [L|G]; [destruct (S1a L); lia | destruct (S1b ltac:(lia)); lia]).
  subst e1. set (q := E - fe).
  set (q' := Z.max q 0). assert (Q1 : q <= q') by apply Z.le_max_l. assert (Q2 : 0 <= q') by apply Z.le_max_r.
  assert (Q3 : q' = q \/ q' = 0) by (unfold q'; lia). assert (Hq : q' <= p) by (unfold q', q; lia).
  assert (B1 : m1 < 2 ^ q').
  { unfold q'. destruct (Z_le_gt_dec (fe - ez) 0) as [L|G].
    - destruct (S1a L) as [-> _]. assert (q = dz) by (unfold q, E; lia). rewrite Z.max_l by lia. replace q with dz by lia. exact DZ2.
    - destruct (S1b ltac:(lia)) as (_ & LO & _). destruct (Z_le_gt_dec 0 q) as [Q|Q].
      + rewrite Z.max_l by lia. rewrite (pow2_split (fe - ez) dz) in DZ2 by (unfold q, E in Q; lia). replace (dz - (fe - ez)) with q in DZ2 by (unfold q, E; lia).
        assert (P : 0 < 2 ^ (fe - ez)) by (apply Z.pow_pos_nonneg; lia). clear -LO DZ2 P M1. nia.
      + rewrite Z.max_r by lia. change (2 ^ 0) with 1.
        assert (2 ^ dz <= 2 ^ (fe - ez)) by (apply Z.pow_le_mono_r; unfold q, E in Q; lia).
        assert (P : 0 < 2 ^ (fe - ez)) by (apply Z.pow_pos_nonneg; lia). clear -LO DZ2 P M1 H. nia. }
  assert (B2 : q = p -> 2 ^ (p - 1) <= m1).
  { intros Qp. destruct (Z_le_gt_dec (fe - ez) 0) as [L|G].
    - destruct (S1a L) as [-> _]. replace (p - 1) with (dz - 1) by (unfold q, E in Qp; lia). exact DZ1.
    - destruct (S1b ltac:(lia)) as (_ & _ & HI).
      rewrite (pow2_split (fe - ez) (dz - 1)) in DZ1 by (unfold q, E in Qp; lia). replace (dz - 1 - (fe - ez)) with (p - 1) in DZ1 by (unfold q, E in Qp; lia).
      assert (P : 0 < 2 ^ (fe - ez)) by (apply Z.pow_pos_nonneg; lia). clear -HI DZ1 P M1. nia. }
  assert (FEq : fe = E - q) by (unfold q; lia).
  assert (FEm : emn <= fe) by lia.
  assert (FEc : q = p \/ fe = emn) by (unfold q; lia).
  assert (FEo : fe <= em - p) by (clear -FE Hov MX1 MX2 Hp Hpe; subst emn; lia).
  assert (FEo' : q = p -> fe + 1 <= em - p) by (clear -FEq Hov MX1; lia).
  assert (MXq : q' + fe <= MX) by (clear -Q1 Q3 FEq MX1 MX2 FEc Hp; lia).
  clear S1a S1b DZ1 DZ2 DZ0 Hal Hov FE MX1 MX2. clearbody q' q fe dz.
  (* [comment removed for export] *)
  pose proof (BinarySingleNaN.le_choice_mode_le (flocq_mode md) sx m1 (loc_of_shr_record mrs1)) as CM.
  set (m1' := BinarySingleNaN.choice_mode (flocq_mode md) sx m1 (loc_of_shr_record mrs1)) in *.
  (* [comment removed for export] *)
  pose proof (shr_fexp_Z p em m1' fe loc_Exact ltac:(lia)) as S2. cbv zeta in S2.
  destruct (shr_fexp p em m1' fe loc_Exact) as [mrs2 e2]. destruct S2 as (M2 & S2a & S2b).
  assert (En2 : fexp p em (Zdigits2 m1' + fe) - fe = Z.max (Zdigits2 m1' + fe - p) emn - fe) by reflexivity.
  rewrite En2 in S2a, S2b. clear En2.
  set (n2 := Z.max (Zdigits2 m1' + fe - p) emn - fe) in *.
  assert (N2a : Zdigits2 m1' <= p -> n2 <= 0) by (unfold n2; clear -FEm Hp; lia).
  assert (N2b : Zdigits2 m1' = p + 1 -> n2 = 1) by (unfold n2; clear -FEm Hp; lia).
  clearbody n2.
  destruct (Z.eq_dec m1' 0) as [Z0|NZ].
  { (* [comment removed for export] *)
    left. rewrite Z0 in N2a. cbn [Zdigits2] in N2a. destruct (S2a ltac:(lia)) as [-> _]. rewrite Z0. reflexivity. }
  assert (P1 : 0 < m1') by (clear -CM M1 NZ; lia).
  assert (D1 : Zdigits2 m1' <= q' + 1).
  { apply zd2_le; [exact P1 | lia |]. rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. assert (0 < 2 ^ q') by (apply Z.pow_pos_nonneg; lia). lia. }
  pose proof (zd2_pos m1' P1) as D0.
  right. destruct (Z_le_gt_dec (Zdigits2 m1') p) as [DP|DP].
  - (* [comment removed for export] *)
    destruct (S2a (N2a DP)) as [-> ->]. destruct m1' as [|m'|m'] eqn:Em; [lia | | lia].
    exists m', fe. replace (fe <=? em - p) with true by (symmetry; apply Z.leb_le; exact FEo). cbn [fst].
    split; [reflexivity|]. split; [|split; [exact FEo | lia]].
    split; [exact DP|]. split; [exact FEm|].
    destruct FEc as [Qp|Q]; [left | right; exact Q].
    pose proof (B2 Qp). pose proof (zd2_ge (Z.pos m') (p - 1) ltac:(lia) ltac:(lia) ltac:(lia)). lia.
  - (* [comment removed for export] *)
    assert (Qp' : q' = p) by (clear -DP D1 Hq; lia). assert (Qp : q = p) by (clear -Qp' Q3 Hp; lia). rewrite Qp' in B1, D1.
    pose proof (zd2_bounds m1' P1) as [G1 _]. assert (2 ^ p <= 2 ^ (Zdigits2 m1' - 1)) by (apply Z.pow_le_mono_r; lia).
    assert (M2p : m1' = 2 ^ p) by (clear -H G1 CM B1; lia).
    assert (Dp : Zdigits2 m1' = p + 1) by lia.
    rewrite (N2b Dp) in S2b.
    destruct (S2b ltac:(lia)) as (-> & LO & HI). change (2 ^ 1) with 2 in LO, HI.
    rewrite M2p in LO, HI.
    assert (X : 2 ^ p = 2 * 2 ^ (p - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    assert (M2v : shr_m mrs2 = 2 ^ (p - 1)) by lia.
    assert (P2 : 0 < 2 ^ (p - 1)) by (apply Z.pow_pos_nonneg; lia).
    destruct (shr_m mrs2) as [|m'|m'] eqn:Em; [lia | | lia].
    exists m', (fe + 1). replace (fe + 1 <=? em - p) with true by (symmetry; apply Z.leb_le; exact (FEo' Qp)). cbn [fst].
    split; [reflexivity|]. rewrite M2v, zd2_pow by lia. pose proof (FEo' Qp). repeat split; lia.
Qed.

(* [comment removed for export] *)
Lemma round_exact_struct : forall f md sx mx ex, fmt_ok f ->
  let E := Zdigits2 (Z.pos mx) + ex in
  Z.max E (fp_emin f) + 1 <= fp_emax f ->
  fst (round_exact f md sx mx ex) = S754_zero sx \/
  exists m' e', fst (round_exact f md sx mx ex) = S754_finite sx m' e' /\ canon f m' e' /\ e' <= fp_emax f - fp_prec f /\
                Zdigits2 (Z.pos m') + e' <= Z.max E (fp_emin f) + 1.
Proof.
  intros f md sx mx ex OK E Hov. unfold round_exact.
  pose proof (shl_align_Z mx ex (fexp (fp_prec f) (fp_emax f) (Z.pos (digits2_pos mx) + ex))) as SA.
  destruct (shl_align mx ex (fexp (fp_prec f) (fp_emax f) (Z.pos (digits2_pos mx) + ex))) as [mz ez].
  destruct SA as (Ez & _ & Ed). change (Z.pos (digits2_pos mx)) with (Zdigits2 (Z.pos mx)) in Ez. fold E in Ez, Ed.
  pose proof (round_aux_struct f md sx mz ez loc_Exact OK) as R. cbv zeta in R. rewrite Ed in R.
  apply R; [rewrite Ez; apply Z.le_min_r | exact Hov].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fmt_ok2 (f : format) : Prop := fmt_ok f /\ fp_emax f = 2 ^ Z.log2 (fp_emax f).
Lemma fmt_ok2_single : fmt_ok2 fmt_single. Proof. split; [exact fmt_ok_single | reflexivity]. Qed.
Lemma fmt_ok2_double : fmt_ok2 fmt_double. Proof. split; [exact fmt_ok_double | reflexivity]. Qed.

Lemma size_digits2 : forall m, Pos.size m = digits2_pos m.
Proof. induction m as [m IH|m IH|]; cbn; rewrite ?IH; reflexivity. Qed.

(* [comment removed for export] *)
Lemma fields_of_sum : forall mw ew sb ef mf, 0 <= mw -> 0 <= ew -> 0 <= mf < 2 ^ mw -> 0 <= ef < 2 ^ ew -> 0 <= sb <= 1 ->
  let x := sb * 2 ^ (mw + ew) + ef * 2 ^ mw + mf in
  Z.land x (Z.ones mw) = mf /\ Z.land (Z.shiftr x mw) (Z.ones ew) = ef /\ Z.testbit x (mw + ew) = (sb =? 1).
Proof.
  intros mw ew sb ef mf Hmw Hew Hmf Hef Hsb x.
  assert (Pm : 0 < 2 ^ mw) by (apply Z.pow_pos_nonneg; lia). assert (Pe : 0 < 2 ^ ew) by (apply Z.pow_pos_nonneg; lia).
  assert (X1 : x = (sb * 2 ^ ew + ef) * 2 ^ mw + mf) by (unfold x; rewrite Z.pow_add_r by lia; ring).
  assert (D1 : x / 2 ^ mw = sb * 2 ^ ew + ef) by (rewrite X1; rewrite Z.div_add_l by lia; rewrite (Z.div_small mf) by lia; lia).
  split; [|split].
  - rewrite Z.land_ones by lia. rewrite X1. rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. rewrite D1. rewrite Z.land_ones by lia. rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.testbit_eqb by lia.
    assert (D2 : x / 2 ^ (mw + ew) = sb).
    { rewrite Z.pow_add_r by lia. rewrite <- Z.div_div by lia. rewrite D1. rewrite Z.div_add_l by lia. rewrite (Z.div_small ef) by lia. lia. }
    rewrite D2. destruct (Z.eq_dec sb 1) as [S1|N]; [rewrite S1; reflexivity|]. assert (S0 : sb = 0) by lia. rewrite S0. reflexivity.
Qed.

Section Bits.
Variable f : format.
Hypothesis OK : fmt_ok2 f.

Let Hmw : 0 < fp_mw f. Proof. destruct OK as [[H _] _]. unfold fp_mw. lia. Qed.
Let Hew : 0 < fp_ew f. Proof. unfold fp_ew. pose proof (Z.log2_nonneg (fp_emax f)). lia. Qed.
Let Hem : 2 ^ fp_ew f = 2 * fp_emax f.
Proof. destruct OK as [_ H]. unfold fp_ew. rewrite Z.pow_add_r by (pose proof (Z.log2_nonneg (fp_emax f)); lia). rewrite <- H. change (2 ^ 1) with 2. lia. Qed.

Definition sbit (s : bool) : Z := if s then 1 else 0.

Lemma decode_fields : forall s ef mf, 0 <= mf < 2 ^ fp_mw f -> 0 <= ef < 2 ^ fp_ew f ->
  let x := sbit s * 2 ^ (fp_mw f + fp_ew f) + ef * 2 ^ fp_mw f + mf in
  fp_sign_bit f x = s /\ fp_exp_field f x = ef /\ fp_man_field f x = mf.
Proof.
  intros s ef mf Hmf Hef x. unfold fp_sign_bit, fp_exp_field, fp_man_field.
  destruct (fields_of_sum (fp_mw f) (fp_ew f) (sbit s) ef mf ltac:(lia) ltac:(lia) Hmf Hef ltac:(destruct s; cbn; lia)) as (A & B & C).
  fold x in A, B, C. rewrite A, B, C. destruct s; repeat split; reflexivity.
Qed.

Lemma sb_shift : forall s : bool, (if s then Z.shiftl 1 (fp_mw f + fp_ew f) else 0) = sbit s * 2 ^ (fp_mw f + fp_ew f).
Proof. intros [|]; cbn [sbit]; [rewrite Z.shiftl_1_l; lia | lia]. Qed.

Lemma fp_decode_encode_zero : forall s, fp_decode f (fp_encode f (S754_zero s)) = S754_zero s.
Proof.
  intros s. unfold fp_encode. rewrite sb_shift.
  assert (P : 0 < 2 ^ fp_mw f) by (apply Z.pow_pos_nonneg; lia). assert (P' : 0 < 2 ^ fp_ew f) by (apply Z.pow_pos_nonneg; lia).
  destruct (decode_fields s 0 0 ltac:(lia) ltac:(lia)) as (A & B & C). rewrite Z.mul_0_l, !Z.add_0_r in A, B, C.
  unfold fp_decode. rewrite A, B, C. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fp_decode_encode : forall s m e, canon f m e -> e <= fp_emax f - fp_prec f ->
  fp_decode f (fp_encode f (S754_finite s m e)) = S754_finite s m e.
Proof.
  intros s m e (Cd & Ce & Cc) Hhi. unfold fp_encode. rewrite sb_shift, size_digits2.
  change (Z.pos (digits2_pos m)) with (Zdigits2 (Z.pos m)).
  pose proof (zd2_bounds (Z.pos m) ltac:(lia)) as [B1 B2].
  assert (P : 0 < 2 ^ fp_mw f) by (apply Z.pow_pos_nonneg; lia). assert (P' : 0 < 2 ^ fp_ew f) by (apply Z.pow_pos_nonneg; lia).
  destruct OK as [[Hp Hpe] _]. unfold fp_emin in *. unfold fp_mw in *.
  destruct (Z.ltb_spec (Zdigits2 (Z.pos m)) (fp_prec f)) as [SUB|NRM].
  - (* [comment removed for export] *)
    assert (Ee : e = 3 - fp_emax f - fp_prec f) by lia.
    assert (Mf : 0 <= Z.pos m < 2 ^ (fp_prec f - 1)).
    { split; [lia|]. apply Z.lt_le_trans with (1 := B2). apply Z.pow_le_mono_r; lia. }
    destruct (decode_fields s 0 (Z.pos m) Mf ltac:(lia)) as (A & B & C). unfold fp_mw in *. rewrite Z.mul_0_l, Z.add_0_r in A, B, C.
    unfold fp_decode. unfold fp_mw. rewrite A, B, C. cbn [Z.eqb]. unfold fp_emin. rewrite Ee. reflexivity.
  - (* [comment removed for export] *)
    assert (Ed : Zdigits2 (Z.pos m) = fp_prec f) by lia. rewrite Ed in B1, B2.
    rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftl_1_l.
    assert (X2 : 2 ^ fp_prec f = 2 * 2 ^ (fp_prec f - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    set (ef := e - (3 - fp_emax f - fp_prec f) + 1). set (mf := Z.pos m - 2 ^ (fp_prec f - 1)).
    assert (Mf : 0 <= mf < 2 ^ (fp_prec f - 1)) by (unfold mf; lia).
    assert (Ef : 0 <= ef < 2 ^ fp_ew f) by (unfold ef; lia).
    destruct (decode_fields s ef mf Mf Ef) as (A & B & C). unfold fp_mw in *.
    unfold fp_decode. unfold fp_mw. rewrite A, B, C.
    replace (ef =? 0) with false by (symmetry; apply Z.eqb_neq; unfold ef; lia).
    replace (ef =? Z.ones (fp_ew f)) with false by (symmetry; apply Z.eqb_neq; rewrite Z.ones_equiv; unfold ef; lia).
    rewrite Z.shiftl_1_l. replace (2 ^ (fp_prec f - 1) + mf) with (Z.pos m) by (unfold mf; lia).
    unfold fp_emin. replace (ef + (3 - fp_emax f - fp_prec f) - 1) with e by (unfold ef; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Definition fp_width (g : format) : Z := fp_mw g + fp_ew g + 1.

Lemma fp_encode_range_zero : forall s, 0 <= fp_encode f (S754_zero s) < 2 ^ fp_width f.
Proof.
  intros s. unfold fp_encode, fp_width. rewrite sb_shift.
  assert (P : 0 < 2 ^ (fp_mw f + fp_ew f)) by (apply Z.pow_pos_nonneg; lia).
  rewrite (Z.pow_add_r 2 (fp_mw f + fp_ew f) 1) by lia. change (2 ^ 1) with 2. destruct s; cbn [sbit]; lia.
Qed.

Lemma fp_encode_range : forall s m e, canon f m e -> e <= fp_emax f - fp_prec f -> 0 <= fp_encode f (S754_finite s m e) < 2 ^ fp_width f.
Proof.
  intros s m e (Cd & Ce & Cc) Hhi. unfold fp_encode, fp_width. rewrite sb_shift, size_digits2.
  change (Z.pos (digits2_pos m)) with (Zdigits2 (Z.pos m)).
  pose proof (zd2_bounds (Z.pos m) ltac:(lia)) as [B1 B2].
  assert (P : 0 < 2 ^ fp_mw f) by (apply Z.pow_pos_nonneg; lia). assert (P' : 0 < 2 ^ fp_ew f) by (apply Z.pow_pos_nonneg; lia).
  assert (W : 2 ^ (fp_mw f + fp_ew f + 1) = 2 * (2 ^ fp_ew f * 2 ^ fp_mw f)) by (rewrite !Z.pow_add_r by lia; change (2 ^ 1) with 2; ring).
  assert (W' : 2 ^ (fp_mw f + fp_ew f) = 2 ^ fp_ew f * 2 ^ fp_mw f) by (rewrite !Z.pow_add_r by lia; ring).
  rewrite W, W'. destruct OK as [[Hp Hpe] _]. unfold fp_emin in *. unfold fp_mw in *.
  assert (SB : 0 <= sbit s <= 1) by (destruct s; cbn; lia).
  destruct (Z.ltb_spec (Zdigits2 (Z.pos m)) (fp_prec f)) as [SUB|NRM].
  - assert (Mf : Z.pos m < 2 ^ (fp_prec f - 1)) by (apply Z.lt_le_trans with (1 := B2); apply Z.pow_le_mono_r; lia). nia.
  - assert (Ed : Zdigits2 (Z.pos m) = fp_prec f) by lia. rewrite Ed in B1, B2.
    rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftl_1_l.
    assert (X2 : 2 ^ fp_prec f = 2 * 2 ^ (fp_prec f - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    set (ef := e - (3 - fp_emax f - fp_prec f) + 1) in *. assert (Ef : 1 <= ef /\ ef + 1 <= 2 ^ fp_ew f) by (unfold ef; lia). clearbody ef. nia.
Qed.

(* [comment removed for export] *)
Lemma fp_decode_canon : forall x s m e, fp_decode f x = S754_finite s m e -> canon f m e.
Proof.
  intros x s m e. unfold fp_decode, canon.
  destruct OK as [[Hp Hpe] _].
  assert (Mf : 0 <= fp_man_field f x < 2 ^ fp_mw f).
  { unfold fp_man_field. rewrite Z.land_ones by lia. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. }
  assert (Efd : 0 <= fp_exp_field f x).
  { unfold fp_exp_field. rewrite Z.land_ones by lia. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. }
  unfold fp_mw in *.
  destruct (fp_exp_field f x =? 0) eqn:E0.
  - destruct (fp_man_field f x) as [|pm|pm] eqn:Em; intros H; try discriminate H. injection H as _ <- <-.
    assert (Zdigits2 (Z.pos pm) <= fp_prec f - 1) by (apply zd2_le; lia). split; [lia|]. split; [lia|]. right; reflexivity.
  - destruct (fp_exp_field f x =? Z.ones (fp_ew f)); [destruct (fp_man_field f x =? 0); discriminate|].
    rewrite Z.shiftl_1_l.
    destruct (2 ^ (fp_prec f - 1) + fp_man_field f x) as [|pm|pm] eqn:Em; intros H; try discriminate H. injection H as _ <- <-.
    assert (P : 0 < 2 ^ (fp_prec f - 1)) by (apply Z.pow_pos_nonneg; lia).
    assert (X2 : 2 ^ fp_prec f = 2 * 2 ^ (fp_prec f - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    assert (D : Zdigits2 (Z.pos pm) = fp_prec f).
    { apply Z.le_antisymm; [apply zd2_le; lia|]. replace (fp_prec f) with (fp_prec f - 1 + 1) at 1 by lia. apply zd2_ge; lia. }
    apply Z.eqb_neq in E0. unfold fp_emin. split; [lia|]. split; [lia|]. left; exact D.
Qed.

(* [comment removed for export] *)
Lemma fp_decode_not_nan : forall x, match fp_decode f x with S754_zero _ | S754_finite _ _ _ => True | _ => False end -> fp_is_nan f x = false.
Proof.
  intros x. unfold fp_decode, fp_is_nan.
  destruct (fp_exp_field f x =? Z.ones (fp_ew f)) eqn:E1; [|reflexivity].
  apply Z.eqb_eq in E1. assert (N0 : fp_exp_field f x <> 0) by (rewrite E1, Z.ones_equiv; assert (1 < 2 ^ fp_ew f) by (apply Z.pow_gt_1; lia); lia).
  apply Z.eqb_neq in N0. rewrite N0. destruct (fp_man_field f x =? 0); intros []. 
Qed.
End Bits.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition FBd (f : format) (k x : Z) : Prop :=
  match fp_decode f x with
  | S754_zero _ => True
  | S754_finite s m e => s = false /\ Zdigits2 (Z.pos m) + e <= k
  | _ => False
  end.
(* [comment removed for export] *)
Definition FB (f : format) (k x : Z) : Prop := 0 <= x < 2 ^ fp_width f /\ FBd f k x.

Lemma FB_mono : forall f k k' x, k <= k' -> FB f k x -> FB f k' x.
Proof. intros f k k' x H [R D]. split; [exact R|]. unfold FBd in *. destruct (fp_decode f x); try tauto. destruct D as [-> L]. split; [reflexivity | lia]. Qed.

Lemma FB_range : forall f k x, FB f k x -> 0 <= x < 2 ^ fp_width f.
Proof. intros f k x [R _]. exact R. Qed.
Lemma FB_range_single : forall k x, FB fmt_single k x -> 0 <= x < 2 ^ 32.
Proof. intros k x [R _]. exact R. Qed.
Lemma FB_range_double : forall k x, FB fmt_double k x -> 0 <= x < 2 ^ 64.
Proof. intros k x [R _]. exact R. Qed.

Lemma FB_not_nan : forall f k x, fmt_ok2 f -> FB f k x -> fp_is_nan f x = false.
Proof. intros f k x OK [_ H]. apply (fp_decode_not_nan f). unfold FBd in H. destruct (fp_decode f x); tauto. Qed.

(* [comment removed for export] *)
Lemma FB_const : forall f k x,
  ((0 <=? x) && (x <? 2 ^ fp_width f) &&
   match fp_decode f x with S754_zero _ => true | S754_finite s m e => negb s && (Zdigits2 (Z.pos m) + e <=? k) | _ => false end) = true -> FB f k x.
Proof.
  intros f k x H. apply andb_true_iff in H. destruct H as [H0 H]. apply andb_true_iff in H0. destruct H0 as [R1 R2].
  apply Z.leb_le in R1. apply Z.ltb_lt in R2. split; [lia|].
  unfold FBd. destruct (fp_decode f x) as [s| | |s m e]; try discriminate; [tauto|].
  apply andb_true_iff in H. destruct H as [H1 H2]. apply Z.leb_le in H2. destruct s; [discriminate|]. split; [reflexivity | exact H2].
Qed.

Lemma zd2_mul : forall a b, 0 < a -> 0 < b -> Zdigits2 (a * b) <= Zdigits2 a + Zdigits2 b.
Proof. intros a b Ha Hb. rewrite !Zdigits2_Zdigits. apply Zdigits_mult. Qed.

(* [comment removed for export] *)
Lemma scaled_add_bound : forall ma ea mb eb K, 0 <= ma -> 0 <= mb ->
  (ma = 0 \/ Zdigits2 ma + ea <= K) -> (mb = 0 \/ Zdigits2 mb + eb <= K) ->
  0 <= fst (scaled_add (ma, ea) (mb, eb)) /\
  (fst (scaled_add (ma, ea) (mb, eb)) = 0 \/
   Zdigits2 (fst (scaled_add (ma, ea) (mb, eb))) + snd (scaled_add (ma, ea) (mb, eb)) <= K + 1).
Proof.
  intros ma ea mb eb K Ha Hb Ka Kb. unfold scaled_add. cbn [fst snd].
  set (e := Z.min ea eb). rewrite !Z.shiftl_mul_pow2 by (unfold e; lia).
  assert (Pa : 0 < 2 ^ (ea - e)) by (apply Z.pow_pos_nonneg; unfold e; lia).
  assert (Pb : 0 < 2 ^ (eb - e)) by (apply Z.pow_pos_nonneg; unfold e; lia).
  set (M := ma * 2 ^ (ea - e) + mb * 2 ^ (eb - e)).
  assert (M0 : 0 <= M) by (unfold M; nia). split; [exact M0|].
  destruct (Z.eq_dec M 0) as [Z|NZ]; [left; exact Z | right].
  assert (TB : forall m em, 0 <= m -> e <= em -> (m = 0 \/ Zdigits2 m + em <= K) -> 0 <= K - e -> m * 2 ^ (em - e) < 2 ^ (K - e)).
  { intros m em Hm Hem [->|Hk] HK; [rewrite Z.mul_0_l; apply Z.pow_pos_nonneg; lia|].
    destruct (Z.eq_dec m 0) as [->|N]; [rewrite Z.mul_0_l; apply Z.pow_pos_nonneg; lia|].
    pose proof (zd2_bounds m ltac:(lia)) as [_ B]. pose proof (zd2_pos m ltac:(lia)) as D.
    assert (P : 0 < 2 ^ (em - e)) by (apply Z.pow_pos_nonneg; lia).
    apply Z.lt_le_trans with (2 ^ Zdigits2 m * 2 ^ (em - e)); [nia|]. rewrite <- Z.pow_add_r by lia. apply Z.pow_le_mono_r; lia. }
  assert (HK : 0 <= K - e).
  { destruct (Z.eq_dec ma 0) as [Za|Na].
    - destruct (Z.eq_dec mb 0) as [Zb|Nb]; [exfalso; apply NZ; unfold M; rewrite Za, Zb; lia|].
      destruct Kb as [?|Kb]; [lia|]. pose proof (zd2_pos mb ltac:(lia)). unfold e. lia.
    - destruct Ka as [?|Ka]; [lia|]. pose proof (zd2_pos ma ltac:(lia)). unfold e. lia. }
  pose proof (TB ma ea Ha ltac:(unfold e; lia) Ka HK) as T1. pose proof (TB mb eb Hb ltac:(unfold e; lia) Kb HK) as T2.
  assert (LT : M < 2 ^ (K - e + 1)) by (rewrite Z.pow_add_r by lia; change (2 ^ 1) with 2; unfold M; lia).
  apply (zd2_le M (K - e + 1)) in LT; lia.
Qed.

Section Calc.
Variable f : format.
Hypothesis OK : fmt_ok2 f.

Lemma FB_zero : forall s k, FB f k (fp_encode f (S754_zero s)).
Proof. intros s k. split; [exact (fp_encode_range_zero f OK s)|]. unfold FBd. rewrite (fp_decode_encode_zero f OK). exact I. Qed.

(* [comment removed for export] *)
Lemma FB_round : forall md mx ex k, fp_emin f <= k -> k + 1 <= fp_emax f -> Zdigits2 (Z.pos mx) + ex <= k ->
  FB f (k + 1) (fp_encode f (fst (round_exact f md false mx ex))).
Proof.
  intros md mx ex k Hlo Hhi Hk.
  destruct (round_exact_struct f md false mx ex (proj1 OK) ltac:(lia)) as [Z | (m' & e' & R & CN & HI & MG)].
  - rewrite Z. apply FB_zero.
  - rewrite R. split; [exact (fp_encode_range f OK false m' e' CN HI)|]. unfold FBd. rewrite (fp_decode_encode f OK false m' e' CN HI). split; [reflexivity | lia].
Qed.

Lemma FB_round_scaled : forall md sz M e k, fp_emin f <= k -> k + 1 <= fp_emax f -> 0 <= M -> (M = 0 \/ Zdigits2 M + e <= k) ->
  FB f (k + 1) (fp_encode f (fst (round_scaled f md sz (M, e)))).
Proof.
  intros md sz M e k Hlo Hhi HM HK. unfold round_scaled. destruct M as [|p|p]; [| | lia].
  - cbn [fst]. apply FB_zero.
  - destruct HK as [?|HK]; [lia|]. apply FB_round; assumption.
Qed.

(* [comment removed for export] *)
Lemma FB_scaled : forall k x, FB f k x ->
  0 <= fst (sf_scaled (fp_decode f x)) /\
  (fst (sf_scaled (fp_decode f x)) = 0 \/ Zdigits2 (fst (sf_scaled (fp_decode f x))) + snd (sf_scaled (fp_decode f x)) <= k).
Proof.
  intros k x [_ H]. unfold FBd in H. destruct (fp_decode f x) as [s| | |s m e]; cbn [sf_scaled fst snd]; try tauto; try lia.
  destruct H as [-> L]. split; [lia | right; exact L].
Qed.

Lemma fb_mul : forall md ka kb a b, FB f ka a -> FB f kb b -> fp_emin f <= ka + kb -> ka + kb + 1 <= fp_emax f ->
  FB f (ka + kb + 1) (fst (fp_mul f md a b)).
Proof.
  intros md ka kb a b Ha Hb Hlo Hhi. unfold fp_mul, nan_pass2.
  rewrite (FB_not_nan f ka a OK Ha), (FB_not_nan f kb b OK Hb). cbn [orb].
  destruct Ha as [_ Ha]. destruct Hb as [_ Hb]. unfold FBd in Ha, Hb.
  destruct (fp_decode f a) as [sa| | |sa ma ea]; try tauto; destruct (fp_decode f b) as [sb| | |sb mb eb]; try tauto; cbn [fst].
  - apply FB_zero.
  - apply FB_zero.
  - apply FB_zero.
  - destruct Ha as [-> La]. destruct Hb as [-> Lb]. cbn [xorb]. unfold enc. cbn [fst].
    apply FB_round; [exact Hlo | exact Hhi |].
    pose proof (zd2_mul (Z.pos ma) (Z.pos mb) ltac:(lia) ltac:(lia)) as D. rewrite Pos2Z.inj_mul. lia.
Qed.

Lemma fb_add : forall md ka kb a b, FB f ka a -> FB f kb b -> fp_emin f <= Z.max ka kb + 1 -> Z.max ka kb + 2 <= fp_emax f ->
  FB f (Z.max ka kb + 2) (fst (fp_add f md a b)).
Proof.
  intros md ka kb a b Ha Hb Hlo Hhi. unfold fp_add, nan_pass2.
  rewrite (FB_not_nan f ka a OK Ha), (FB_not_nan f kb b OK Hb). cbn [orb].
  pose proof (FB_scaled ka a Ha) as (A0 & A1). pose proof (FB_scaled kb b Hb) as (B0 & B1).
  assert (R : forall sz, FB f (Z.max ka kb + 2) (fp_encode f (fst (round_scaled f md sz (scaled_add (sf_scaled (fp_decode f a)) (sf_scaled (fp_decode f b))))))).
  { intros sz. destruct (sf_scaled (fp_decode f a)) as [ma ea]. destruct (sf_scaled (fp_decode f b)) as [mb eb]. cbn [fst snd] in *.
    pose proof (scaled_add_bound ma ea mb eb (Z.max ka kb) A0 B0 ltac:(lia) ltac:(lia)) as (S0 & S1).
    destruct (scaled_add (ma, ea) (mb, eb)) as [M e]. cbn [fst snd] in *.
    replace (Z.max ka kb + 2) with (Z.max ka kb + 1 + 1) by lia. apply FB_round_scaled; [lia | lia | exact S0 | exact S1]. }
  destruct Ha as [_ Ha]. destruct Hb as [_ Hb]. unfold FBd in Ha, Hb.
  destruct (fp_decode f a) as [sa| | |sa ma ea]; try tauto; destruct (fp_decode f b) as [sb| | |sb mb eb]; try tauto; unfold enc; cbn [fst]; apply R.
Qed.

Lemma fb_fma : forall md ka kb kc a b c, FB f ka a -> FB f kb b -> FB f kc c ->
  fp_emin f <= Z.max (ka + kb) kc + 1 -> Z.max (ka + kb) kc + 2 <= fp_emax f ->
  FB f (Z.max (ka + kb) kc + 2) (fst (fp_fma f md a b c)).
Proof.
  intros md ka kb kc a b c Ha Hb Hc Hlo Hhi. unfold fp_fma, nan_pass3.
  rewrite (FB_not_nan f ka a OK Ha), (FB_not_nan f kb b OK Hb), (FB_not_nan f kc c OK Hc). cbn [orb negb].
  pose proof (FB_scaled kc c Hc) as (C0 & C1).
  set (K := Z.max (ka + kb) kc) in *.
  (* [comment removed for export] *)
  assert (RZ : forall sz, FB f (K + 2) (fp_encode f (fst (round_scaled f md sz (sf_scaled (fp_decode f c)))))).
  { intros sz. destruct (sf_scaled (fp_decode f c)) as [mc ec]. cbn [fst snd] in *.
    replace (K + 2) with (K + 1 + 1) by lia. apply FB_round_scaled; [lia | lia | exact C0 | destruct C1; [left; assumption | right; unfold K; lia]]. }
  (* [comment removed for export] *)
  assert (RF : forall sz ma ea mb eb, Zdigits2 (Z.pos ma) + ea <= ka -> Zdigits2 (Z.pos mb) + eb <= kb ->
             FB f (K + 2) (fp_encode f (fst (round_scaled f md sz (scaled_add (Z.pos (ma * mb), ea + eb) (sf_scaled (fp_decode f c))))))).
  { intros sz ma ea mb eb La Lb. destruct (sf_scaled (fp_decode f c)) as [mc ec]. cbn [fst snd] in *.
    pose proof (zd2_mul (Z.pos ma) (Z.pos mb) ltac:(lia) ltac:(lia)) as D. rewrite <- Pos2Z.inj_mul in D.
    pose proof (scaled_add_bound (Z.pos (ma * mb)) (ea + eb) mc ec K ltac:(lia) C0 ltac:(right; unfold K; lia) ltac:(destruct C1; [left; assumption | right; unfold K; lia])) as (S0 & S1).
    destruct (scaled_add (Z.pos (ma * mb), ea + eb) (mc, ec)) as [M e]. cbn [fst snd] in *.
    replace (K + 2) with (K + 1 + 1) by lia. apply FB_round_scaled; [lia | lia | exact S0 | exact S1]. }
  destruct Ha as [_ Ha]. destruct Hb as [_ Hb]. destruct Hc as [_ Hc]. unfold FBd in Ha, Hb, Hc.
  destruct (fp_decode f a) as [sa| | |sa ma ea] eqn:Da; try tauto; destruct (fp_decode f b) as [sb| | |sb mb eb] eqn:Db; try tauto; cbn [andb];
    destruct (fp_decode f c) as [sc| | |sc mc ec] eqn:Dc; try tauto; unfold enc; cbn [fst sf_sign xorb]; try (apply RZ).
  - destruct Ha as [-> La]. destruct Hb as [-> Lb]. cbn [xorb]. apply (RF _ ma ea mb eb La Lb).
  - destruct Ha as [-> La]. destruct Hb as [-> Lb]. cbn [xorb]. apply (RF _ ma ea mb eb La Lb).
Qed.

Lemma fb_of_int : forall md sg bits n k, 0 <= k -> 0 <= n < 2 ^ k -> k < bits -> fp_emin f <= k -> k + 1 <= fp_emax f ->
  FB f (k + 1) (fst (fp_of_int f md sg bits n)).
Proof.
  intros md sg bits n k Hk Hn Hb Hlo Hhi. unfold fp_of_int, int_wrap.
  assert (P : 2 ^ k <= 2 ^ (bits - 1)) by (apply Z.pow_le_mono_r; lia).
  assert (P' : 2 ^ bits = 2 * 2 ^ (bits - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
  rewrite Z.land_ones by lia. rewrite (Z.mod_small n) by lia.
  assert (T : Z.testbit n (bits - 1) = false) by (rewrite Z.testbit_eqb by lia; rewrite Z.div_small by lia; reflexivity).
  rewrite T, andb_false_r. unfold enc. cbn [fst].
  apply FB_round_scaled; [exact Hlo | exact Hhi | lia |].
  destruct (Z.eq_dec n 0) as [->|N]; [left; reflexivity | right]. rewrite Z.add_0_r. apply zd2_le; lia.
Qed.

(* [comment removed for export] *)
Lemma fb_lt_hi : forall k d c mc ec, FB f k d -> fp_decode f c = S754_finite false mc ec -> Zdigits2 (Z.pos mc) = fp_prec f ->
  k <= fp_prec f + ec - 1 -> fst (fp_lt f d c) = true.
Proof.
  intros k d c mc ec Hd Dc Nc Hk. unfold fp_lt, fp_compare. cbn [fst]. rewrite Dc.
  pose proof (fp_decode_canon f OK c false mc ec Dc) as (_ & Cce & _).
  destruct Hd as [_ Hd]. unfold FBd in Hd. destruct (fp_decode f d) as [sd| | |sd md ed] eqn:Dd; try tauto; try reflexivity.
  destruct Hd as [-> Ld]. pose proof (fp_decode_canon f OK d false md ed Dd) as (Cd & Ce & Cc).
  cbn [SFcompare]. destruct (Z.compare_spec ed ec) as [E|L|G]; [| reflexivity |].
  - (* [comment removed for export] *)
    destruct Cc as [Cn|Cs]; [exfalso; lia|].
    destruct (Z.eq_dec (Zdigits2 (Z.pos md)) (fp_prec f)) as [Q|Q]; [exfalso; lia|].
    assert (LT : (md < mc)%positive).
    { apply Pos2Z.pos_lt_pos. pose proof (zd2_bounds (Z.pos md) ltac:(lia)) as [_ B]. pose proof (zd2_bounds (Z.pos mc) ltac:(lia)) as [B' _].
      rewrite Nc in B'. assert (2 ^ Zdigits2 (Z.pos md) <= 2 ^ (fp_prec f - 1)) by (apply Z.pow_le_mono_r; pose proof (zd2_pos (Z.pos md)); lia). lia. }
    change (Pos.compare_cont Eq md mc) with (Pos.compare md mc). rewrite (proj2 (Pos.compare_lt_iff md mc) LT). reflexivity.
  - exfalso. destruct Cc as [Cn|Cs]; lia.
Qed.

(* [comment removed for export] *)
Lemma fb_lt_lo : forall k d c mc ec, FB f k d -> fp_decode f c = S754_finite true mc ec -> fst (fp_lt f c d) = true.
Proof.
  intros k d c mc ec Hd Dc. unfold fp_lt, fp_compare. cbn [fst]. rewrite Dc.
  destruct Hd as [_ Hd]. unfold FBd in Hd. destruct (fp_decode f d) as [sd| | |sd md ed]; try tauto; try reflexivity. destruct Hd as [-> _]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fb_to_int : forall md sg bits k d, FB f k d -> 0 <= k -> k < bits - 1 -> 0 <= fst (fp_to_int f md sg bits d) <= 2 ^ k.
Proof.
  intros md sg bits k d Hd Hk Hb. unfold fp_to_int. rewrite (FB_not_nan f k d OK Hd).
  assert (Pk : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  destruct Hd as [_ Hd]. unfold FBd in Hd. destruct (fp_decode f d) as [sd| | |sd m e]; try tauto; [cbn [fst]; lia|]. destruct Hd as [-> Ld].
  pose proof (zd2_bounds (Z.pos m) ltac:(lia)) as [_ B]. pose proof (zd2_pos (Z.pos m) ltac:(lia)) as D.
  set (ql := if 0 <=? e then (Z.shiftl (Z.pos m) e, loc_Exact)
             else let d0 := Z.shiftl 1 (- e) in let '(q, r) := Z.div_eucl (Z.pos m) d0 in (q, new_location d0 r)).
  assert (Q : 0 <= fst ql /\ fst ql + 1 <= 2 ^ k).
  { unfold ql. destruct (Z.leb_spec 0 e) as [E|E]; cbn [fst].
    - rewrite Z.shiftl_mul_pow2 by lia. assert (0 < 2 ^ e) by (apply Z.pow_pos_nonneg; lia).
      assert (Z.pos m * 2 ^ e < 2 ^ (Zdigits2 (Z.pos m) + e)) by (rewrite Z.pow_add_r by lia; nia).
      assert (2 ^ (Zdigits2 (Z.pos m) + e) <= 2 ^ k) by (apply Z.pow_le_mono_r; lia). nia.
    - cbv zeta. rewrite Z.shiftl_1_l. assert (P : 0 < 2 ^ (- e)) by (apply Z.pow_pos_nonneg; lia).
      pose proof (Z.div_eucl_eq (Z.pos m) (2 ^ (- e)) ltac:(lia)) as EQ. pose proof (Z.mod_pos_bound (Z.pos m) (2 ^ (- e)) P) as MB.
      unfold Z.modulo in MB. destruct (Z.div_eucl (Z.pos m) (2 ^ (- e))) as [q r]. cbn [fst].
      assert (Q0 : 0 <= q) by nia. split; [exact Q0|].
      destruct (Z_le_gt_dec 0 (Zdigits2 (Z.pos m) + e)) as [G|G].
      + assert (X : 2 ^ Zdigits2 (Z.pos m) = 2 ^ (- e) * 2 ^ (Zdigits2 (Z.pos m) + e)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
        assert (q < 2 ^ (Zdigits2 (Z.pos m) + e)) by nia.
        assert (2 ^ (Zdigits2 (Z.pos m) + e) <= 2 ^ k) by (apply Z.pow_le_mono_r; lia). lia.
      + assert (2 ^ Zdigits2 (Z.pos m) <= 2 ^ (- e)) by (apply Z.pow_le_mono_r; lia). assert (q = 0) by nia. lia. }
  fold ql. destruct ql as [q l]. cbn [fst] in Q.
  pose proof (BinarySingleNaN.le_choice_mode_le (flocq_mode md) false q l) as CM.
  set (q' := BinarySingleNaN.choice_mode (flocq_mode md) false q l) in *.
  assert (HI : 2 ^ k <= int_hi sg bits).
  { unfold int_hi. assert (2 ^ k < 2 ^ (bits - 1)) by (apply Z.pow_lt_mono_r; lia).
    assert (2 ^ bits = 2 * 2 ^ (bits - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    rewrite !Z.shiftl_1_l. destruct sg; lia. }
  assert (LO : int_lo sg bits <= 0) by (unfold int_lo; destruct sg; [rewrite Z.shiftl_1_l; assert (0 < 2 ^ (bits - 1)) by (apply Z.pow_pos_nonneg; lia); lia | lia]).
  replace (q' <? int_lo sg bits) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (int_hi sg bits <? q') with false by (symmetry; apply Z.ltb_ge; lia).
  cbn [orb fst]. unfold int_wrap. rewrite Z.land_ones by lia.
  assert (2 ^ k < 2 ^ bits) by (apply Z.pow_lt_mono_r; lia). rewrite Z.mod_small by lia. lia.
Qed.
End Calc.

(* [comment removed for export] *)
Lemma fb_convert : forall fs fd md k a, fmt_ok2 fs -> fmt_ok2 fd -> FB fs k a -> fp_emin fd <= k -> k + 1 <= fp_emax fd ->
  FB fd (k + 1) (fst (fp_convert fs fd md a)).
Proof.
  intros fs fd md k a OKs OKd Ha Hlo Hhi. unfold fp_convert. rewrite (FB_not_nan fs k a OKs Ha).
  destruct Ha as [_ Ha]. unfold FBd in Ha. destruct (fp_decode fs a) as [s| | |s m e]; try tauto; cbn [fst].
  - apply (FB_zero fd OKd).
  - destruct Ha as [-> L]. unfold enc. cbn [fst]. apply (FB_round fd OKd); assumption.
Qed.
