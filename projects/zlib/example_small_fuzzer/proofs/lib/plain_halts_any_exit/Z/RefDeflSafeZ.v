(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.

Module BoundArith.
From Stdlib Require Import ZArith Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition cdiv8 (v : Z) : Z := (v + 7) / 8.

Lemma cdiv8_nonneg : forall v, 0 <= v -> 0 <= cdiv8 v.
Proof. intros v H. unfold cdiv8. apply Z.div_pos; lia. Qed.
Lemma cdiv8_le : forall a b, a <= b -> cdiv8 a <= cdiv8 b.
Proof. intros a b H. unfold cdiv8. apply Z.div_le_mono; lia. Qed.
Lemma cdiv8_add : forall a b, 0 <= a -> 0 <= b -> cdiv8 (a + b) <= cdiv8 a + cdiv8 b.
Proof. intros a b Ha Hb. unfold cdiv8. Z.to_euclidean_division_equations. lia. Qed.
Lemma cdiv8_mul8 : forall a k, cdiv8 (a + 8 * k) = cdiv8 a + k.
Proof. intros a k. unfold cdiv8. Z.to_euclidean_division_equations. lia. Qed.
Lemma cdiv8_small : forall v, 0 <= v <= 7 -> cdiv8 v <= 1.
Proof. intros v H. unfold cdiv8. Z.to_euclidean_division_equations. lia. Qed.
Lemma cdiv8_shiftr : forall x, 0 <= x -> Z.shiftr (x + 3 + 7) 3 = cdiv8 (x + 3).
Proof. intros x H. rewrite Z.shiftr_div_pow2 by lia. unfold cdiv8. change (2 ^ 3) with 8. f_equal. Qed.

Definition KBLK : Z := 16383.
Definition cb_budget (n : Z) : Z := n + 11 + 5 * (n / KBLK).
Definition cbound (n : Z) : Z := n + Z.shiftr n 12 + Z.shiftr n 14 + Z.shiftr n 25 + 13.

Lemma cbound_range : forall n, 0 <= n <= 2 ^ 20 -> n + 13 <= cbound n <= 2 * n + 13.
Proof.
  intros n H. unfold cbound. rewrite !Z.shiftr_div_pow2 by lia.
  change (2 ^ 12) with 4096; change (2 ^ 14) with 16384; change (2 ^ 25) with 33554432; change (2 ^ 20) with 1048576 in H.
  Z.to_euclidean_division_equations. lia.
Qed.

Lemma cb_budget_le : forall n, 0 <= n <= 2 ^ 20 -> cb_budget n <= cbound n.
Proof.
  intros n H. unfold cb_budget, cbound, KBLK. rewrite !Z.shiftr_div_pow2 by lia.
  change (2 ^ 12) with 4096; change (2 ^ 14) with 16384; change (2 ^ 25) with 33554432; change (2 ^ 20) with 1048576 in H.
  Z.to_euclidean_division_equations. lia.
Qed.

Definition phi0 (a : Z) : Z := a + 5 * (a / KBLK).
Lemma phi0_mono : forall a b, 0 <= a <= b -> phi0 a <= phi0 b.
Proof. intros a b H. unfold phi0, KBLK. pose proof (Z.div_le_mono a b 16383 ltac:(lia) ltac:(lia)). lia. Qed.
Lemma phi0_step : forall a L, 0 <= a -> KBLK <= L -> phi0 a + L + 5 <= phi0 (a + L).
Proof. intros a L Ha HL. unfold phi0, KBLK in *. Z.to_euclidean_division_equations. lia. Qed.
Lemma phi0_budget : forall a n, 0 <= a <= n -> phi0 a + 11 <= cb_budget n.
Proof. intros a n H. pose proof (phi0_mono a n H). unfold phi0, cb_budget in *. lia. Qed.

Lemma static_big_block : forall nl nm L S,
  0 <= nl -> 0 <= nm -> nl + nm <= 16383 -> nl + 3 * nm <= L -> 32507 <= L ->
  S <= 3 * L + 6 * nl + 13 * nm -> S <= 8 * L + 30.
Proof. intros. lia. Qed.
End BoundArith.

Module OverlayHuff1.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Fixpoint lsum (f : Z -> Z) (l : list Z) : Z :=
  match l with [] => 0 | x :: r => f x + lsum f r end.

Lemma lsum_app f l1 l2 : lsum f (l1 ++ l2) = lsum f l1 + lsum f l2.
Proof. induction l1; cbn; lia. Qed.

Lemma lsum_ext f g l : (forall x, In x l -> f x = g x) -> lsum f l = lsum g l.
Proof.
  induction l as [|x r IH]; cbn; intros H; [reflexivity|].
  rewrite (H x) by (left; reflexivity). rewrite IH by (intros; apply H; right; assumption). reflexivity.
Qed.

Lemma lsum_le f g l : (forall x, In x l -> f x <= g x) -> lsum f l <= lsum g l.
Proof.
  induction l as [|x r IH]; cbn; intros H; [lia|].
  pose proof (H x (or_introl eq_refl)). specialize (IH ltac:(intros; apply H; right; assumption)). lia.
Qed.

Lemma lsum_zero l : lsum (fun _ => 0) l = 0.
Proof. induction l; cbn; lia. Qed.

Lemma lsum_nonneg f l : (forall x, In x l -> 0 <= f x) -> 0 <= lsum f l.
Proof. intros H. pose proof (lsum_le (fun _ => 0) f l H). rewrite lsum_zero in H0. exact H0. Qed.

Lemma lsum_add f g l : lsum (fun x => f x + g x) l = lsum f l + lsum g l.
Proof. induction l; cbn; lia. Qed.

Lemma lsum_scale c f l : lsum (fun x => c * f x) l = c * lsum f l.
Proof. induction l; cbn; lia. Qed.

Lemma lsum_in_split (l : list Z) (x : Z) : In x l -> NoDup l ->
  exists l1 l2, l = l1 ++ x :: l2 /\ ~ In x l1 /\ ~ In x l2.
Proof.
  intros I ND. destruct (in_split x l I) as (l1 & l2 & E). subst l.
  pose proof (NoDup_remove_2 _ _ _ ND) as A. exists l1, l2. split; [reflexivity|].
  split; intros C; [apply A, in_or_app; left; exact C | apply A, in_or_app; right; exact C].
Qed.

Lemma lsum_upd f l x v : NoDup l -> In x l ->
  lsum (fun y => if y =? x then v else f y) l = lsum f l - f x + v.
Proof.
  intros ND I. destruct (lsum_in_split l x I ND) as (l1 & l2 & E & N1 & N2). rewrite E.
  rewrite !lsum_app. cbn. rewrite Z.eqb_refl.
  rewrite (lsum_ext (fun y => if y =? x then v else f y) f l1) by (intros y Hy; destruct (Z.eqb_spec y x); [subst; tauto|reflexivity]).
  rewrite (lsum_ext (fun y => if y =? x then v else f y) f l2) by (intros y Hy; destruct (Z.eqb_spec y x); [subst; tauto|reflexivity]).
  lia.
Qed.

Lemma lsum_notin f l x v : ~ In x l -> lsum (fun y => if y =? x then v else f y) l = lsum f l.
Proof. intros N. apply lsum_ext. intros y Hy. destruct (Z.eqb_spec y x); [subst; tauto|reflexivity]. Qed.

Lemma lsum_remove f l x : NoDup l -> In x l -> lsum f (remove Z.eq_dec x l) = lsum f l - f x.
Proof.
  intros ND I. destruct (lsum_in_split l x I ND) as (l1 & l2 & E & N1 & N2). rewrite E.
  rewrite remove_app. cbn. destruct (Z.eq_dec x x); [|congruence].
  rewrite (notin_remove _ _ _ N1), (notin_remove _ _ _ N2). rewrite !lsum_app. cbn. lia.
Qed.

Lemma lsum_ge_member f l x : (forall y, In y l -> 0 <= f y) -> In x l -> f x <= lsum f l.
Proof.
  intros P I. induction l as [|y r IH]; [destruct I|]. cbn. destruct I as [->|I].
  - pose proof (lsum_nonneg f r ltac:(intros; apply P; right; assumption)). lia.
  - specialize (IH ltac:(intros; apply P; right; assumption) I). pose proof (P y (or_introl eq_refl)). lia.
Qed.


Lemma pow2_pos k : 0 <= k -> 0 < 2 ^ k.
Proof. intros. apply Z.pow_pos_nonneg; lia. Qed.

Lemma pow2_split k : 1 <= k -> 2 ^ k = 2 * 2 ^ (k - 1).
Proof. intros. replace k with (Z.succ (k - 1)) at 1 by lia. rewrite Z.pow_succ_r; lia. Qed.

Lemma pow2_le k k' : 0 <= k <= k' -> 2 ^ k <= 2 ^ k'.
Proof. intros. apply Z.pow_le_mono_r; lia. Qed.

Lemma lsum_divide m f l : (forall x, In x l -> (m | f x)) -> (m | lsum f l).
Proof.
  induction l as [|x r IH]; cbn; intros H; [apply Z.divide_0_r|].
  apply Z.divide_add_r; [apply H; left; reflexivity | apply IH; intros; apply H; right; assumption].
Qed.


Section Kraft.
Variable K : Z.
Hypothesis Kpos : 0 <= K.

Definition ksum (sg : Z -> Z) (F : list Z) : Z := lsum (fun x => 2 ^ (K - sg x)) F.
Definition csum (w sg : Z -> Z) (F : list Z) : Z := lsum (fun x => w x * sg x) F.

Definition code_ok (sg : Z -> Z) (F : list Z) : Prop :=
  (forall x, In x F -> 0 <= sg x <= K) /\ ksum sg F <= 2 ^ K.

Lemma code_two_pos sg F a b : code_ok sg F -> NoDup F -> In a F -> In b F -> a <> b -> 1 <= sg a.
Proof.
  intros [R KS] ND Ia Ib NE. destruct (Z_lt_le_dec 0 (sg a)) as [|LE]; [lia|]. exfalso.
  pose proof (R a Ia). assert (sg a = 0) by lia.
  unfold ksum in KS.
  destruct (lsum_in_split F a Ia ND) as (l1 & l2 & E & N1 & N2).
  rewrite E, lsum_app in KS. cbn in KS. rewrite H0, Z.sub_0_r in KS.
  assert (In b (l1 ++ l2)).
  { rewrite E in Ib. apply in_app_or in Ib. destruct Ib as [|[|]]; [apply in_or_app; tauto|congruence|apply in_or_app; tauto]. }
  assert (P : forall y, In y (l1 ++ l2) -> 0 <= 2 ^ (K - sg y)) by (intros; apply Z.pow_nonneg; lia).
  pose proof (lsum_ge_member _ _ _ P H1). rewrite lsum_app in H2.
  pose proof (R b Ib). pose proof (pow2_pos (K - sg b) ltac:(lia)). lia.
Qed.

Fixpoint lmax (sg : Z -> Z) (F : list Z) : Z :=
  match F with [] => 0 | x :: r => Z.max (sg x) (lmax sg r) end.

Lemma lmax_ge sg F x : In x F -> sg x <= lmax sg F.
Proof. induction F as [|y r IH]; cbn; [tauto|]. intros [->|I]; [lia|]. specialize (IH I). lia. Qed.

Lemma lmax_in sg F : F <> [] -> (forall x, In x F -> 0 <= sg x) -> exists x, In x F /\ sg x = lmax sg F.
Proof.
  induction F as [|y r IH]; [congruence|]. intros _ NN. cbn.
  destruct r as [|z r'].
  - exists y. cbn. pose proof (NN y (or_introl eq_refl)). split; [tauto|lia].
  - destruct (IH ltac:(congruence) ltac:(intros; apply NN; right; assumption)) as (x & I & E).
    destruct (Z_le_gt_dec (sg y) (lmax sg (z :: r'))).
    + exists x. split; [right; exact I|]. rewrite E. lia.
    + exists y. split; [left; reflexivity|lia].
Qed.

Lemma lmax_nonneg sg F : (forall x, In x F -> 0 <= sg x) -> 0 <= lmax sg F.
Proof. induction F; cbn; intros; [lia|]. pose proof (H a (or_introl eq_refl)). lia. Qed.

Definition cnt (sg : Z -> Z) (v : Z) (F : list Z) : Z := lsum (fun x => if sg x =? v then 1 else 0) F.

Lemma cnt_nonneg sg v F : 0 <= cnt sg v F.
Proof. unfold cnt. apply lsum_nonneg. intros. destruct (_ =? _); lia. Qed.

Lemma cnt_pos_in sg v F : 0 < cnt sg v F -> exists x, In x F /\ sg x = v.
Proof.
  induction F as [|y r IH]; cbn; [unfold cnt; cbn; lia|]. unfold cnt; cbn. fold (cnt sg v r).
  destruct (Z.eqb_spec (sg y) v).
  - intros _. exists y. tauto.
  - intros H. destruct (IH ltac:(lia)) as (x & I & E). exists x. tauto.
Qed.

Lemma cnt_ge2 sg v F : NoDup F -> 2 <= cnt sg v F -> exists x y, In x F /\ In y F /\ x <> y /\ sg x = v /\ sg y = v.
Proof.
  intros ND C. induction F as [|z r IH]; [unfold cnt in C; cbn in C; lia|].
  unfold cnt in C; cbn in C; fold (cnt sg v r) in C. inversion ND; subst.
  destruct (Z.eqb_spec (sg z) v).
  - destruct (cnt_pos_in sg v r ltac:(lia)) as (x & I & E). exists z, x.
    repeat split; try tauto; [cbn; tauto | cbn; tauto | intros ->; tauto].
  - destruct (IH H2 ltac:(lia)) as (x & y & Ix & Iy & NE & Ex & Ey). exists x, y. cbn. tauto.
Qed.

Lemma ksum_divide sg F M : (forall x, In x F -> 0 <= sg x <= M - 1) -> M - 1 <= K ->
  (2 ^ (K - (M - 1)) | ksum sg F).
Proof.
  intros R HM. unfold ksum. apply lsum_divide. intros x I. pose proof (R x I).
  exists (2 ^ ((M - 1) - sg x)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.


Definition upd (sg : Z -> Z) (x v : Z) : Z -> Z := fun y => if y =? x then v else sg y.

Lemma ksum_upd sg F x v : NoDup F -> In x F -> ksum (upd sg x v) F = ksum sg F - 2 ^ (K - sg x) + 2 ^ (K - v).
Proof.
  intros. unfold ksum, upd.
  rewrite (lsum_ext (fun y => 2 ^ (K - (if y =? x then v else sg y))) (fun y => if y =? x then 2 ^ (K - v) else 2 ^ (K - sg y)))
    by (intros y _; destruct (y =? x); reflexivity).
  rewrite lsum_upd by assumption. lia.
Qed.

Lemma csum_upd w sg F x v : NoDup F -> In x F -> csum w (upd sg x v) F = csum w sg F - w x * sg x + w x * v.
Proof.
  intros. unfold csum, upd.
  rewrite (lsum_ext (fun y => w y * (if y =? x then v else sg y)) (fun y => if y =? x then w x * v else w y * sg y))
    by (intros y _; destruct (Z.eqb_spec y x); [subst; reflexivity|reflexivity]).
  rewrite lsum_upd by assumption. lia.
Qed.

Lemma exch_norm (w : Z -> Z) (F : list Z) (a b : Z) :
  NoDup F -> In a F -> In b F -> a <> b ->
  (forall x, In x F -> 0 <= w x) ->
  (forall x, In x F -> x <> a -> x <> b -> w a <= w x /\ w b <= w x) ->
  forall n sg, code_ok sg F -> lmax sg F <= Z.of_nat n ->
  exists sg', code_ok sg' F /\ csum w sg' F <= csum w sg F /\
              1 <= sg' a /\ sg' a = sg' b /\ (forall x, In x F -> sg' x <= sg' a).
Proof.
  intros ND Ia Ib NE Wnn Wmin.
  induction n as [|n IH]; intros sg OK LM.
  -
    exfalso. pose proof (code_two_pos sg F a b OK ND Ia Ib NE). pose proof (lmax_ge sg F a Ia). lia.
  - destruct OK as [R KS].
    set (M := lmax sg F) in *.
    assert (Mnn : 0 <= M) by (apply lmax_nonneg; intros; apply R; assumption).
    destruct (Z_le_gt_dec M (Z.of_nat n)) as [LE|GT]; [apply IH; [split; assumption|exact LE]|].
    assert (ME : M = Z.of_nat (S n)) by lia.
    destruct (Z_le_gt_dec 2 (cnt sg M F)) as [TWO|ONE].
    +
      destruct (cnt_ge2 sg M F ND TWO) as (c & d & Ic & Id & NEcd & Ec & Ed).
      assert (STEP : forall sg0 x y, code_ok sg0 F -> In x F -> In y F -> x <> y -> sg0 y = lmax sg0 F ->
                     (forall z, In z F -> z <> x -> z <> b \/ x = b -> True) ->
                     w x <= w y \/ x = y ->
                     exists sg1, code_ok sg1 F /\ csum w sg1 F <= csum w sg0 F /\ sg1 x = lmax sg0 F /\ sg1 y = sg0 x
                                 /\ (forall z, In z F -> z <> x -> z <> y -> sg1 z = sg0 z) /\ lmax sg1 F = lmax sg0 F).
      { intros sg0 x y OK0 Ix Iy NExy Ey _ Wxy.
        destruct OK0 as [R0 K0].
        exists (upd (upd sg0 x (sg0 y)) y (sg0 x)).
        assert (E1 : forall z, In z F -> z <> x -> z <> y -> upd (upd sg0 x (sg0 y)) y (sg0 x) z = sg0 z).
        { intros z _ Zx Zy. unfold upd. destruct (Z.eqb_spec z y); [congruence|]. destruct (Z.eqb_spec z x); [congruence|reflexivity]. }
        assert (Ex : upd (upd sg0 x (sg0 y)) y (sg0 x) x = sg0 y).
        { unfold upd. destruct (Z.eqb_spec x y); [congruence|]. rewrite Z.eqb_refl. reflexivity. }
        assert (Ey' : upd (upd sg0 x (sg0 y)) y (sg0 x) y = sg0 x) by (unfold upd; rewrite Z.eqb_refl; reflexivity).
        split; [split|].
        - intros z Iz. destruct (Z.eq_dec z x); [subst; rewrite Ex; apply R0; assumption|].
          destruct (Z.eq_dec z y); [subst; rewrite Ey'; apply R0; assumption|]. rewrite E1 by assumption. apply R0; assumption.
        - rewrite ksum_upd; [| assumption | assumption]. rewrite ksum_upd by assumption.
          unfold upd at 1. destruct (Z.eqb_spec y x); [congruence|]. lia.
        - split; [|split; [rewrite Ex; exact Ey|split; [exact Ey'|split; [exact E1|]]]].
          + rewrite csum_upd; [| assumption | assumption]. rewrite csum_upd by assumption.
            unfold upd. destruct (Z.eqb_spec y x); [congruence|].
            destruct Wxy as [Wxy| ->]; [|congruence].
            pose proof (lmax_ge sg0 F x Ix). rewrite <- Ey in H. nia.
          +
            apply Z.le_antisymm.
            * assert (forall z, In z F -> upd (upd sg0 x (sg0 y)) y (sg0 x) z <= lmax sg0 F).
              { intros z Iz. destruct (Z.eq_dec z x); [subst; rewrite Ex; apply lmax_ge; assumption|].
                destruct (Z.eq_dec z y); [subst; rewrite Ey'; apply lmax_ge; assumption|].
                rewrite E1 by assumption. apply lmax_ge; assumption. }
              destruct (lmax_in (upd (upd sg0 x (sg0 y)) y (sg0 x)) F ltac:(destruct F; [destruct Ix|congruence])) as (z & Iz & Ez).
              { intros z Iz. destruct (Z.eq_dec z x); [subst; rewrite Ex; apply R0; assumption|].
                destruct (Z.eq_dec z y); [subst; rewrite Ey'; apply R0; assumption|]. rewrite E1 by assumption. apply R0; assumption. }
              rewrite <- Ez. apply H; assumption.
            * pose proof (lmax_ge (upd (upd sg0 x (sg0 y)) y (sg0 x)) F x Ix) as LG. rewrite Ex in LG. lia. }
      assert (XA : exists y, In y F /\ sg y = M /\ (w a <= w y \/ a = y)).
      { destruct (Z.eq_dec (sg a) M) as [EA|NA].
        - exists a. repeat split; auto.
        - destruct (Z.eq_dec c b) as [->|NCB].
          + exists d. repeat split; auto. left. destruct (Z.eq_dec d a) as [->|]; [congruence|]. apply (Wmin d Id); congruence.
          + exists c. repeat split; auto. left. destruct (Z.eq_dec c a) as [->|]; [congruence|]. apply (Wmin c Ic); congruence. }
      destruct XA as (y & Iy & Ey & Wy).
      destruct (Z.eq_dec a y) as [<-|NAy].
      *
        assert (XB : exists z, In z F /\ sg z = M /\ (w b <= w z \/ b = z) /\ z <> a).
        { destruct (Z.eq_dec (sg b) M) as [EB|NB]; [exists b; repeat split; auto|].
          destruct (Z.eq_dec c a) as [->|NCA].
          - exists d. repeat split; auto. left. destruct (Z.eq_dec d b) as [->|]; [congruence|]. apply (Wmin d Id); congruence.
          - exists c. repeat split; auto. left. destruct (Z.eq_dec c b) as [->|]; [congruence|]. apply (Wmin c Ic); congruence. }
        destruct XB as (z & Iz & Ez & Wz & NZa).
        destruct (Z.eq_dec b z) as [<-|NBz].
        -- exists sg. split; [split; assumption|]. split; [lia|]. split; [|split]; [ | lia | intros; rewrite Ey; apply lmax_ge; assumption].
           pose proof (code_two_pos sg F a b (conj R KS) ND Ia Ib NE). lia.
        -- destruct (STEP sg b z (conj R KS) Ib Iz NBz ltac:(rewrite Ez; reflexivity) ltac:(intros; exact I) Wz) as (sg1 & OK1 & C1 & B1 & Z1 & E1 & L1).
           exists sg1. split; [exact OK1|]. split; [exact C1|].
           assert (sg1 a = M) by (rewrite E1 by auto; exact Ey).
           split; [pose proof (code_two_pos sg1 F a b OK1 ND Ia Ib NE); lia|].
           split; [rewrite H, B1; reflexivity|]. intros x Ix. rewrite H. unfold M. rewrite <- L1. apply lmax_ge. assumption.
      * destruct (STEP sg a y (conj R KS) Ia Iy NAy ltac:(rewrite Ey; reflexivity) ltac:(intros; exact I) Wy) as (sg1 & OK1 & C1 & A1 & Y1 & E1 & L1).
        assert (XB : exists z, In z F /\ sg1 z = M /\ (w b <= w z \/ b = z) /\ z <> a).
        { destruct (Z.eq_dec (sg1 b) M) as [EB|NB]; [exists b; repeat split; auto|].
          assert (CASE : forall u, In u F -> sg u = M -> u <> a -> u <> y -> sg1 u = M) by (intros; rewrite E1 by auto; assumption).
          assert (PICK : forall u, In u F -> sg u = M -> u <> a -> u <> y ->
                         exists z, In z F /\ sg1 z = M /\ (w b <= w z \/ b = z) /\ z <> a).
          { intros u Iu Eu NUa NUy. exists u. split; [exact Iu|]. split; [apply CASE; auto|]. split; [|exact NUa].
            left. destruct (Z.eq_dec u b) as [EUb|NUb]; [rewrite EUb in *; rewrite (CASE b Iu Eu NUa NUy) in NB; congruence|].
            apply (Wmin u Iu); congruence. }
          destruct (Z.eq_dec c a) as [ECa|NCa]; [|destruct (Z.eq_dec c y) as [ECy|NCy]; [|exact (PICK c Ic Ec NCa NCy)]];
          (destruct (Z.eq_dec d a) as [EDa|NDa]; [|destruct (Z.eq_dec d y) as [EDy|NDy]; [|exact (PICK d Id Ed NDa NDy)]]).
          - congruence.
          - exists y. split; [exact Iy|]. split; [rewrite Y1, <- ECa; exact Ec|]. split; [|congruence].
            destruct (Z.eq_dec y b) as [->|NYb]; [right; reflexivity|left]. apply (Wmin y Iy); congruence.
          - exists y. split; [exact Iy|]. split; [rewrite Y1, <- EDa; exact Ed|]. split; [|congruence].
            destruct (Z.eq_dec y b) as [->|NYb]; [right; reflexivity|left]. apply (Wmin y Iy); congruence.
          - congruence. }
        destruct XB as (z & Iz & Ez & Wz & NZa).
        destruct (Z.eq_dec b z) as [<-|NBz].
        -- exists sg1. split; [exact OK1|]. split; [exact C1|].
           split; [pose proof (code_two_pos sg1 F a b OK1 ND Ia Ib NE); lia|].
           split; [rewrite A1, Ez; reflexivity|]. intros x Ix. rewrite A1. unfold M. rewrite <- L1. apply lmax_ge; assumption.
        -- destruct (STEP sg1 b z OK1 Ib Iz NBz ltac:(rewrite Ez, L1; reflexivity) ltac:(intros; exact I) Wz) as (sg2 & OK2 & C2 & B2 & Z2 & E2 & L2).
           exists sg2. split; [exact OK2|]. split; [lia|].
           assert (sg2 a = M) by (rewrite E2 by auto; exact A1).
           split; [pose proof (code_two_pos sg2 F a b OK2 ND Ia Ib NE); lia|].
           split; [rewrite H, B2, L1; reflexivity|]. intros x Ix. rewrite H. unfold M. rewrite <- L1, <- L2. apply lmax_ge; assumption.
    +
      assert (NN : F <> []) by (destruct F; [destruct Ia|congruence]).
      destruct (lmax_in sg F NN ltac:(intros; apply R; assumption)) as (y & Iy & Ey).
      assert (MY : forall x, In x F -> sg x <= sg y) by (intros; rewrite Ey; apply lmax_ge; assumption).
      assert (M1 : 1 <= sg y) by (pose proof (code_two_pos sg F a b (conj R KS) ND Ia Ib NE); pose proof (MY a Ia); lia).
      assert (MK : sg y <= K) by (apply R; assumption).
      assert (ONE' : cnt sg (sg y) F < 2) by (rewrite Ey; subst M; lia).
      assert (OTH : forall x, In x F -> x <> y -> sg x <= sg y - 1).
      { intros x Ix NExy. pose proof (MY x Ix).
        destruct (Z.eq_dec (sg x) (sg y)) as [Ex|]; [|lia]. exfalso.
        unfold cnt in ONE'.
        destruct (lsum_in_split F y Iy ND) as (l1 & l2 & EF & N1 & N2).
        rewrite EF, lsum_app in ONE'. cbn in ONE'. rewrite Z.eqb_refl in ONE'.
        assert (In x (l1 ++ l2)).
        { rewrite EF in Ix. apply in_app_or in Ix. destruct Ix as [|[|]]; [apply in_or_app; tauto|congruence|apply in_or_app; tauto]. }
        assert (P : forall z, In z (l1 ++ l2) -> 0 <= (if sg z =? sg y then 1 else 0)) by (intros; destruct (_ =? _); lia).
        pose proof (lsum_ge_member _ _ _ P H0). cbn in H1. rewrite Ex, Z.eqb_refl in H1.
        rewrite lsum_app in H1. lia. }
      set (sg1 := upd sg y (sg y - 1)).
      assert (OK1 : code_ok sg1 F).
      { split.
        - intros x Ix. unfold sg1, upd. destruct (Z.eqb_spec x y); [lia|apply R; assumption].
        - unfold sg1. rewrite ksum_upd by assumption.
          assert (DIV : (2 ^ (K - (sg y - 1)) | ksum sg F - 2 ^ (K - sg y))).
          { unfold ksum. destruct (lsum_in_split F y Iy ND) as (l1 & l2 & EF & N1 & N2).
            rewrite EF at 1. rewrite lsum_app. cbn.
            replace (lsum (fun x : Z => 2 ^ (K - sg x)) l1 + (2 ^ (K - sg y) + lsum (fun x : Z => 2 ^ (K - sg x)) l2) - 2 ^ (K - sg y))
              with (lsum (fun x : Z => 2 ^ (K - sg x)) (l1 ++ l2)) by (rewrite lsum_app; lia).
            apply (ksum_divide sg (l1 ++ l2) (sg y)); [|lia].
            intros x Ix. assert (In x F) by (rewrite EF; apply in_app_or in Ix; apply in_or_app; cbn; tauto).
            split; [apply R; assumption|]. apply OTH; [assumption|]. intros ->. apply in_app_or in Ix. tauto. }
          assert (DIV2 : (2 ^ (K - (sg y - 1)) | 2 ^ K)).
          { exists (2 ^ (sg y - 1)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
          destruct DIV as [q Hq]. destruct DIV2 as [r Hr].
          pose proof (pow2_pos (K - sg y) ltac:(lia)) as P1.
          assert (E2 : 2 ^ (K - (sg y - 1)) = 2 * 2 ^ (K - sg y)) by (replace (K - (sg y - 1)) with (Z.succ (K - sg y)) by lia; rewrite Z.pow_succ_r; lia).
          rewrite E2 in Hq, Hr.
          assert (2 * q + 1 <= 2 * r) by nia.
          assert (q + 1 <= r) by lia.
          nia. }
      assert (C1 : csum w sg1 F <= csum w sg F).
      { unfold sg1. rewrite csum_upd by assumption. pose proof (Wnn y Iy). nia. }
      assert (L1 : lmax sg1 F <= Z.of_nat n).
      { destruct (lmax_in sg1 F NN ltac:(intros; apply (proj1 OK1); assumption)) as (z & Iz & Ez). rewrite <- Ez. unfold sg1, upd.
        destruct (Z.eqb_spec z y); [lia|]. pose proof (OTH z Iz n0). lia. }
      destruct (IH sg1 OK1 L1) as (sg' & OK' & C' & A' & AB' & MX'). exists sg'.
      split; [exact OK'|]. split; [lia|]. split; [exact A'|]. split; [exact AB'|exact MX'].
Qed.

Lemma NoDup_remove_elt (x : Z) l : NoDup l -> NoDup (remove Z.eq_dec x l).
Proof.
  induction l as [|y r IH]; cbn; intros ND; [constructor|]. inversion ND; subst.
  destruct (Z.eq_dec x y); [apply IH; assumption|]. constructor; [|apply IH; assumption].
  intros I. apply in_remove in I. tauto.
Qed.

Theorem exch (w : Z -> Z) (F : list Z) (a b p : Z) (sg : Z -> Z) :
  NoDup F -> In a F -> In b F -> a <> b -> ~ In p F ->
  (forall x, In x F -> 0 <= w x) ->
  (forall x, In x F -> x <> a -> x <> b -> w a <= w x /\ w b <= w x) ->
  w p = w a + w b ->
  code_ok sg F ->
  exists sg', code_ok sg' (p :: remove Z.eq_dec a (remove Z.eq_dec b F)) /\
              csum w sg' (p :: remove Z.eq_dec a (remove Z.eq_dec b F)) + w a + w b <= csum w sg F.
Proof.
  intros ND Ia Ib NE NP Wnn Wmin Wp OK.
  assert (LMN : lmax sg F <= Z.of_nat (Z.to_nat (lmax sg F))).
  { rewrite Z2Nat.id; [lia|]. apply lmax_nonneg. intros; apply (proj1 OK); assumption. }
  destruct (exch_norm w F a b ND Ia Ib NE Wnn Wmin _ sg OK LMN) as (sg1 & [R1 K1] & C1 & A1 & AB1 & MX1).
  set (Fb := remove Z.eq_dec b F). set (F' := remove Z.eq_dec a Fb).
  assert (NDb : NoDup Fb) by (apply NoDup_remove_elt; assumption).
  assert (ND' : NoDup F') by (apply NoDup_remove_elt; assumption).
  assert (IaFb : In a Fb) by (apply in_in_remove; [exact NE|exact Ia]).
  assert (SUB : forall x, In x F' -> In x F /\ x <> a /\ x <> b).
  { intros x I. apply in_remove in I. destruct I as [I Na]. apply in_remove in I. tauto. }
  assert (NP' : ~ In p F') by (intros I; apply SUB in I; tauto).
  exists (upd sg1 p (sg1 a - 1)).
  assert (EQ' : forall f, lsum (fun x => f (upd sg1 p (sg1 a - 1) x)) F' = lsum (fun x => f (sg1 x)) F').
  { intros f. apply lsum_ext. intros x I. unfold upd. destruct (Z.eqb_spec x p); [subst; tauto|reflexivity]. }
  split; [split|].
  - intros x [<-|I]; unfold upd; [rewrite Z.eqb_refl; pose proof (R1 a Ia); lia|].
    destruct (Z.eqb_spec x p); [subst; tauto|]. apply R1. apply SUB; assumption.
  - unfold ksum. cbn. unfold upd at 1. rewrite Z.eqb_refl.
    rewrite (EQ' (fun v => 2 ^ (K - v))).
    change (lsum (fun x => 2 ^ (K - sg1 x)) F') with (ksum sg1 F').
    unfold F'. unfold ksum. rewrite lsum_remove by assumption. fold (ksum sg1 Fb). unfold Fb, ksum. rewrite lsum_remove by assumption.
    fold (ksum sg1 F). rewrite <- AB1.
    pose proof (R1 a Ia).
    replace (K - (sg1 a - 1)) with (Z.succ (K - sg1 a)) by lia. rewrite Z.pow_succ_r by lia. lia.
  - unfold csum. cbn. unfold upd at 1. rewrite Z.eqb_refl.
    rewrite (lsum_ext (fun x => w x * upd sg1 p (sg1 a - 1) x) (fun x => w x * sg1 x) F')
      by (intros x I; unfold upd; destruct (Z.eqb_spec x p); [subst; tauto|reflexivity]).
    change (lsum (fun x => w x * sg1 x) F') with (csum w sg1 F').
    unfold F', csum. rewrite lsum_remove by assumption. fold (csum w sg1 Fb). unfold Fb, csum. rewrite lsum_remove by assumption.
    fold (csum w sg1 F). rewrite <- AB1. unfold csum in C1 |- *. nia.
Qed.
End Kraft.
End OverlayHuff1.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Fixpoint zsum (f : Z -> Z) (lo : Z) (n : nat) : Z :=
  match n with
  | O => 0
  | S k => zsum f lo k + f (lo + Z.of_nat k)
  end.

Definition zind (b : bool) : Z := if b then 1 else 0.

Lemma zind_le1 : forall b, 0 <= zind b <= 1.
Proof. intros [|]; cbn; lia. Qed.

Lemma zsum_ext : forall f g lo n, (forall i, lo <= i < lo + Z.of_nat n -> f i = g i) -> zsum f lo n = zsum g lo n.
Proof.
  induction n as [|n IH]; intros Hfg; cbn [zsum]; [reflexivity|].
  rewrite IH by (intros; apply Hfg; lia). rewrite Hfg by lia. reflexivity.
Qed.

Lemma zsum_add : forall f g lo n, zsum (fun i => f i + g i) lo n = zsum f lo n + zsum g lo n.
Proof. induction n as [|n IH]; cbn [zsum]; [reflexivity|]. rewrite IH. lia. Qed.

Lemma zsum_scale : forall c f lo n, zsum (fun i => c * f i) lo n = c * zsum f lo n.
Proof. induction n as [|n IH]; cbn [zsum]; [lia|]. rewrite IH. lia. Qed.

Lemma zsum_0 : forall f lo n, (forall i, lo <= i < lo + Z.of_nat n -> f i = 0) -> zsum f lo n = 0.
Proof. induction n as [|n IH]; intros H; cbn [zsum]; [reflexivity|]. rewrite IH by (intros; apply H; lia). rewrite H by lia. lia. Qed.

Lemma zsum_nonneg : forall f lo n, (forall i, lo <= i < lo + Z.of_nat n -> 0 <= f i) -> 0 <= zsum f lo n.
Proof. induction n as [|n IH]; intros H; cbn [zsum]; [lia|]. pose proof (IH ltac:(intros; apply H; lia)). pose proof (H (lo + Z.of_nat n) ltac:(lia)). lia. Qed.

Lemma zsum_mono : forall f g lo n, (forall i, lo <= i < lo + Z.of_nat n -> f i <= g i) -> zsum f lo n <= zsum g lo n.
Proof. induction n as [|n IH]; intros H; cbn [zsum]; [lia|]. pose proof (IH ltac:(intros; apply H; lia)). pose proof (H (lo + Z.of_nat n) ltac:(lia)). lia. Qed.

Lemma zsum_single : forall f lo n a, lo <= a < lo + Z.of_nat n ->
  (forall i, lo <= i < lo + Z.of_nat n -> i <> a -> f i = 0) -> zsum f lo n = f a.
Proof.
  induction n as [|n IH]; intros a Ha H; cbn [zsum]; [lia|].
  destruct (Z.eq_dec a (lo + Z.of_nat n)) as [->|N].
  - rewrite zsum_0 by (intros; apply H; lia). lia.
  - rewrite (IH a) by (try lia; intros; apply H; lia). rewrite (H (lo + Z.of_nat n)) by lia. lia.
Qed.

Lemma zsum_two : forall f lo n a b, lo <= a < lo + Z.of_nat n -> lo <= b < lo + Z.of_nat n -> a <> b ->
  (forall i, lo <= i < lo + Z.of_nat n -> i <> a -> i <> b -> f i = 0) -> zsum f lo n = f a + f b.
Proof.
  induction n as [|n IH]; intros a b Ha Hb Nab H; cbn [zsum]; [lia|].
  destruct (Z.eq_dec a (lo + Z.of_nat n)) as [->|Na].
  - rewrite (zsum_single f lo n b) by (try lia; intros; apply H; lia). lia.
  - destruct (Z.eq_dec b (lo + Z.of_nat n)) as [->|Nb].
    + rewrite (zsum_single f lo n a) by (try lia; intros; apply H; lia). lia.
    + rewrite (IH a b) by (try lia; intros; apply H; lia). rewrite (H (lo + Z.of_nat n)) by lia. lia.
Qed.

Lemma zsum_ind_ge1 : forall (P : Z -> bool) lo n a, lo <= a < lo + Z.of_nat n -> P a = true ->
  1 <= zsum (fun i => zind (P i)) lo n.
Proof.
  induction n as [|k IHk]; cbn [zsum]; intros a Ha Ea; [lia|].
  pose proof (zsum_nonneg (fun i => zind (P i)) lo k ltac:(intros i0 Hi0; pose proof (zind_le1 (P i0)); lia)).
  destruct (Z.eq_dec a (lo + Z.of_nat k)) as [->|N]; [rewrite Ea; change (zind true) with 1; lia|].
  pose proof (IHk a ltac:(lia) Ea). pose proof (zind_le1 (P (lo + Z.of_nat k))). lia.
Qed.

Lemma zsum_pos_has : forall (P : Z -> bool) lo n, 0 < zsum (fun i => zind (P i)) lo n ->
  exists a, lo <= a < lo + Z.of_nat n /\ P a = true /\ (forall i, lo <= i < a -> P i = false).
Proof.
  induction n as [|n IH]; cbn [zsum]; intros H; [lia|].
  destruct (Z_lt_le_dec 0 (zsum (fun i => zind (P i)) lo n)) as [C|C].
  - destruct (IH C) as (a & A & B & D). exists a. split; [lia|]. split; [exact B | exact D].
  - pose proof (zsum_nonneg (fun i => zind (P i)) lo n ltac:(intros i0 Hi0; pose proof (zind_le1 (P i0)); lia)).
    destruct (P (lo + Z.of_nat n)) eqn:E; [| try rewrite E in H; change (zind false) with 0 in H; lia].
    exists (lo + Z.of_nat n). split; [lia|]. split; [exact E|].
    intros i Hi. destruct (P i) eqn:Ei; [|reflexivity]. exfalso.
    pose proof (zsum_ind_ge1 P lo n i ltac:(lia) Ei). lia.
Qed.



Lemma zsum_snoc : forall f lo n, zsum f lo (S n) = zsum f lo n + f (lo + Z.of_nat n).
Proof. reflexivity. Qed.

Lemma zsum_shift : forall f lo n, zsum f lo (S n) = f lo + zsum f (lo + 1) n.
Proof.
  intros f lo n. induction n as [|n IHn].
  - cbn [zsum Z.of_nat]. rewrite Z.add_0_r. lia.
  - rewrite zsum_snoc, IHn, zsum_snoc. replace (lo + Z.of_nat (S n)) with (lo + 1 + Z.of_nat n) by lia. lia.
Qed.

Lemma zsum_swap : forall (F : Z -> Z -> Z) lo n lo' m,
  zsum (fun b => zsum (F b) lo n) lo' m = zsum (fun p => zsum (fun b => F b p) lo' m) lo n.
Proof.
  intros F lo n lo'. induction m as [|m IH].
  - cbn [zsum]. symmetry. apply zsum_0. intros; reflexivity.
  - rewrite zsum_snoc. rewrite IH. rewrite <- zsum_add. apply zsum_ext. intros; reflexivity.
Qed.

Lemma zsum_split : forall f lo n m, zsum f lo (n + m) = zsum f lo n + zsum f (lo + Z.of_nat n) m.
Proof.
  intros f lo n m. induction m as [|m IH].
  - rewrite Nat.add_0_r. cbn [zsum]. lia.
  - rewrite Nat.add_succ_r. rewrite !zsum_snoc, IH. replace (lo + Z.of_nat (n + m)) with (lo + Z.of_nat n + Z.of_nat m) by lia. lia.
Qed.

Lemma zsum_ge_point : forall f lo n a, (forall i, lo <= i < lo + Z.of_nat n -> 0 <= f i) -> lo <= a < lo + Z.of_nat n ->
  f a <= zsum f lo n.
Proof.
  intros f lo n a Hnn Ha.
  assert (E1 : zsum (fun i => if i =? a then f i else 0) lo n = f a).
  { rewrite (zsum_single (fun i => if i =? a then f i else 0) lo n a); [| exact Ha | intros i Hi Ni; replace (i =? a) with false by (symmetry; apply Z.eqb_neq; exact Ni); reflexivity].
    rewrite Z.eqb_refl. reflexivity. }
  rewrite <- E1. apply zsum_mono. intros i Hi. destruct (Z.eqb_spec i a) as [->|]; [lia | apply Hnn; exact Hi].
Qed.

Lemma zsum_const1 : forall n lo, zsum (fun _ => 1) lo n = Z.of_nat n.
Proof. induction n as [|n IH]; intros lo; [reflexivity|]. rewrite zsum_snoc, IH. lia. Qed.
