(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition countP (p : Z -> bool) (l : list Z) : nat := length (filter p l).

Lemma countP_app : forall p l1 l2, countP p (l1 ++ l2) = (countP p l1 + countP p l2)%nat.
Proof. intros. unfold countP. rewrite filter_app, length_app. reflexivity. Qed.
Lemma countP_cons : forall p a l, countP p (a :: l) = ((if p a then 1 else 0) + countP p l)%nat.
Proof. intros. unfold countP. cbn. destruct (p a); reflexivity. Qed.
(* [comment removed for export] *)
Lemma countP_le_length : forall p l, (countP p l <= length l)%nat.
Proof. intros p l. induction l as [|a l IH]; [reflexivity|]. rewrite countP_cons. cbn [length]. destruct (p a); lia. Qed.
Lemma countP_perm : forall p l1 l2, Permutation l1 l2 -> countP p l1 = countP p l2.
Proof.
  intros p l1 l2 H. induction H.
  - reflexivity.
  - rewrite !countP_cons. lia.
  - rewrite !countP_cons. lia.
  - lia.
Qed.
Lemma countP_all : forall p l, (forall k, (k < length l)%nat -> p (nth k l 0) = true) -> countP p l = length l.
Proof.
  intros p l. induction l as [|a l IH]; intros H; [reflexivity|].
  rewrite countP_cons. pose proof (H 0%nat ltac:(cbn; lia)) as H0. cbn [nth] in H0. rewrite H0. cbn [length]. rewrite IH; [lia|].
  intros k Hk. apply (H (S k)). cbn; lia.
Qed.
Lemma countP_none : forall p l, (forall k, (k < length l)%nat -> p (nth k l 0) = false) -> countP p l = 0%nat.
Proof.
  intros p l. induction l as [|a l IH]; intros H; [reflexivity|].
  rewrite countP_cons. pose proof (H 0%nat ltac:(cbn; lia)) as H0. cbn [nth] in H0. rewrite H0. rewrite IH; [reflexivity|].
  intros k Hk. apply (H (S k)). cbn; lia.
Qed.
(* [comment removed for export] *)
Lemma countP_mono : forall p1 p2 l1 l2, (length l1 <= length l2)%nat ->
  (forall k, (k < length l1)%nat -> p1 (nth k l1 0) = true -> p2 (nth k l2 0) = true) ->
  (countP p1 l1 <= countP p2 l2)%nat.
Proof.
  intros p1 p2 l1. induction l1 as [|a l1 IH]; intros l2 L H; [cbn; lia|].
  destruct l2 as [|b l2]; [cbn in L; lia|]. rewrite !countP_cons. cbn in L.
  assert (IH' : (countP p1 l1 <= countP p2 l2)%nat).
  { apply IH; [lia|]. intros k Hk E. apply (H (S k)); [cbn; lia| exact E]. }
  destruct (p1 a) eqn:E1.
  - pose proof (H 0%nat ltac:(cbn; lia) E1) as H0. cbn [nth] in H0. rewrite H0. lia.
  - destruct (p2 b); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Shell.
  Variable gtb : Z -> Z -> bool.
  Definition leb (x y : Z) : bool := negb (gtb x y).
  Definition le (x y : Z) : Prop := gtb x y = false.
  Hypothesis gt_le : forall x y, gtb x y = true -> le y x.
  Hypothesis le_trans : forall x y z, le x y -> le y z -> le x z.

  Lemma le_refl : forall x, le x x.
  Proof. intros x. unfold le. destruct (gtb x x) eqn:E; [|reflexivity]. pose proof (gt_le _ _ E) as H. unfold le in H. congruence. Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma le_gt : forall x y v, le x y -> gtb x v = true -> gtb y v = true.
  Proof.
    intros x y v H1 H2. destruct (gtb y v) eqn:E; [reflexivity|]. exfalso.
    pose proof (le_trans _ _ _ H1 E) as H3. unfold le in H3. congruence.
  Qed.
  Lemma leb_le : forall x y, leb x y = true <-> le x y.
  Proof. intros. unfold leb, le. destruct (gtb x y); cbn; split; congruence. Qed.

  (* [comment removed for export] *)
  Definition sortedL (l : list Z) : Prop :=
    forall a b, (a <= b)%nat -> (b < length l)%nat -> le (nth a l 0) (nth b l 0).

  (* [comment removed for export] *)
  Lemma countP_split : forall p k l, countP p l = (countP p (firstn k l) + countP p (skipn k l))%nat.
  Proof. intros. rewrite <- countP_app, firstn_skipn. reflexivity. Qed.

  Lemma sorted_count_ge : forall l k, sortedL l -> (k < length l)%nat ->
    (k + 1 <= countP (fun e => leb e (nth k l 0%Z)) l)%nat.
  Proof.
    intros l k SL Hk. set (v := nth k l 0).
    rewrite (countP_split _ (k + 1) l).
    assert (L1 : length (firstn (k + 1) l) = (k + 1)%nat) by (rewrite length_firstn; lia).
    rewrite (countP_all (fun e => leb e v) (firstn (k + 1) l)); [lia|].
    intros j Hj. rewrite L1 in Hj. rewrite nth_firstn.
    replace (j <? k + 1)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    apply (proj2 (leb_le _ _)). subst v. apply SL; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sorted_nth_le : forall l k v, sortedL l -> (k < length l)%nat ->
    (k + 1 <= countP (fun e => leb e v) l)%nat -> le (nth k l 0) v.
  Proof.
    intros l k v SL Hk Hc. destruct (gtb (nth k l 0) v) eqn:E; [|exact E]. exfalso.
    rewrite (countP_split _ k l) in Hc.
    pose proof (countP_le_length (fun e => leb e v) (firstn k l)) as A. rewrite length_firstn in A.
    rewrite (countP_none (fun e => leb e v) (skipn k l)) in Hc; [lia|].
    intros j Hj. rewrite length_skipn in Hj. rewrite nth_skipn.
    unfold leb. rewrite (le_gt (nth k l 0) (nth (k + j) l 0) v); [reflexivity| apply SL; lia| exact E].
  Qed.

  (* [comment removed for export] *)
  Lemma lemma_L : forall (X X' Y Y' : list Z) (m : nat),
    sortedL X' -> sortedL Y' -> Permutation X X' -> Permutation Y Y' ->
    (length X <= m + length Y)%nat ->
    (forall t, (m + t < length X)%nat -> le (nth t Y 0) (nth (m + t) X 0)) ->
    forall t, (m + t < length X)%nat -> le (nth t Y' 0) (nth (m + t) X' 0).
  Proof.
    intros X X' Y Y' m SX SY PX PY LXY PAIR t Ht.
    pose proof (Permutation_length PX) as LX. pose proof (Permutation_length PY) as LY.
    set (v := nth (m + t) X' 0).
    (* [comment removed for export] *)
    pose proof (sorted_count_ge X' (m + t) SX ltac:(lia)) as C1. fold v in C1.
    rewrite <- (countP_perm _ _ _ PX) in C1.
    rewrite (countP_split _ m X) in C1.
    pose proof (countP_le_length (fun e => leb e v) (firstn m X)) as C2. rewrite length_firstn in C2.
    assert (C3 : (t + 1 <= countP (fun e => leb e v) (skipn m X))%nat) by lia.
    (* [comment removed for export] *)
    assert (C4 : (countP (fun e => leb e v) (skipn m X) <= countP (fun e => leb e v) Y)%nat).
    { apply countP_mono; [rewrite length_skipn; lia|].
      intros s Hs E. rewrite length_skipn in Hs. rewrite nth_skipn in E.
      apply (proj2 (leb_le _ _)). apply (le_trans _ (nth (m + s) X 0)); [apply PAIR; lia|]. apply (proj1 (leb_le _ _)). exact E. }
    apply sorted_nth_le; [exact SY| lia|]. rewrite <- (countP_perm _ _ _ PY). lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition hsorted (x : Z -> Z) (lo up h : Z) : Prop :=
    forall p, lo <= p -> p + h < up -> le (x p) (x (p + h)).

  Lemma hsorted_pair : forall x lo up h p q, hsorted x lo up h -> lo <= p -> q = p + h -> q < up -> le (x p) (x q).
  Proof. intros x lo up h p q HS Hp -> Hq. apply HS; lia. Qed.

  Lemma hsorted_chain : forall x lo up h, 0 < h -> hsorted x lo up h ->
    forall p (t : nat), lo <= p -> p + h * Z.of_nat t < up -> le (x p) (x (p + h * Z.of_nat t)).
  Proof.
    intros x lo up h Hh HS p t. induction t as [|t IH]; intros Hp Hu.
    - rewrite Z.mul_0_r, Z.add_0_r. apply le_refl.
    - apply (le_trans _ (x (p + h * Z.of_nat t))).
      + apply IH; [lia| nia].
      + replace (p + h * Z.of_nat (S t)) with (p + h * Z.of_nat t + h) by lia. apply HS; lia.
  Qed.

  (* [comment removed for export] *)
  Fixpoint chain (x : Z -> Z) (c h : Z) (T : nat) : list Z :=
    match T with
    | O => []
    | S T' => x c :: chain x (c + h) h T'
    end.
  Lemma chain_length : forall x c h T, length (chain x c h T) = T.
  Proof. intros x c h T. revert c. induction T; intros; cbn; [reflexivity| now rewrite IHT]. Qed.
  Lemma chain_nth : forall x c h T k, (k < T)%nat -> nth k (chain x c h T) 0 = x (c + h * Z.of_nat k).
  Proof.
    intros x c h T. revert c. induction T as [|T IH]; intros c k Hk; [lia|].
    destruct k as [|k]; cbn [chain nth]; [f_equal; lia|]. rewrite IH by lia. f_equal. lia.
  Qed.
  Lemma chain_ext : forall x y c h T, (forall k, (k < T)%nat -> x (c + h * Z.of_nat k) = y (c + h * Z.of_nat k)) ->
    chain x c h T = chain y c h T.
  Proof.
    intros x y c h T. revert c. induction T as [|T IH]; intros c H; cbn; [reflexivity|].
    f_equal; [pose proof (H 0%nat ltac:(lia)) as E; rewrite Z.mul_0_r, Z.add_0_r in E; exact E|].
    apply IH. intros k Hk. replace (c + h + h * Z.of_nat k) with (c + h * Z.of_nat (S k)) by lia. apply H. lia.
  Qed.
  Lemma chain_app : forall x c h T1 T2, chain x c h (T1 + T2) = chain x c h T1 ++ chain x (c + h * Z.of_nat T1) h T2.
  Proof.
    intros x c h T1. revert c. induction T1 as [|T1 IH]; intros c T2; cbn.
    - f_equal. f_equal. lia.
    - f_equal. rewrite IH. f_equal. f_equal. lia.
  Qed.
  Lemma chain_sorted : forall x lo up h c T, 0 < h -> hsorted x lo up h -> lo <= c -> c + h * (Z.of_nat T - 1) < up ->
    sortedL (chain x c h T).
  Proof.
    intros x lo up h c T Hh HS Hc Hu a b Hab Hb. rewrite chain_length in Hb.
    rewrite !chain_nth by lia.
    replace (c + h * Z.of_nat b) with (c + h * Z.of_nat a + h * Z.of_nat (b - a)) by nia.
    apply (hsorted_chain x lo up h Hh HS); nia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Fixpoint shift (fuel : nat) (x : Z -> Z) (lo h j v : Z) (cnt : nat) : (Z -> Z) * Z * nat :=
    match fuel with
    | O => (x, j, cnt)
    | S f =>
        if gtb (x (j - h)) v then
          let x' := zfupd x j (x (j - h)) in
          let j' := j - h in
          if j' <=? lo + h - 1 then (x', j', S cnt) else shift f x' lo h j' v (S cnt)
        else (x, j, cnt)
    end.
  Definition ins (x : Z -> Z) (lo h i : Z) : (Z -> Z) * nat :=
    let v := x i in
    let '(x1, j, cnt) := shift (S (Z.to_nat (i - lo))) x lo h i v 0 in
    (zfupd x1 j v, cnt).
  (* [comment removed for export] *)
  Fixpoint pass_upto (n : nat) (x : Z -> Z) (lo h i0 : Z) : Z -> Z :=
    match n with
    | O => x
    | S n' => pass_upto n' (fst (ins x lo h i0)) lo h (i0 + 1)
    end.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition shifted (x0 x : Z -> Z) (i h : Z) (s : nat) : Prop :=
    (forall k, (k < s)%nat -> x (i - h * Z.of_nat k) = x0 (i - h * Z.of_nat (S k))) /\
    (forall p, (i < p \/ p < i - h * Z.of_nat s \/ (p <= i /\ (i - p) mod h <> 0)) -> x p = x0 p) /\
    x (i - h * Z.of_nat s) = x0 (i - h * Z.of_nat s).

  Lemma shifted_0 : forall x0 i h, shifted x0 x0 i h 0.
  Proof. intros. split; [intros; lia|]. split; [intros; reflexivity| reflexivity]. Qed.

  Lemma shifted_step : forall x0 x i h s, 0 < h -> shifted x0 x i h s ->
    shifted x0 (zfupd x (i - h * Z.of_nat s) (x (i - h * Z.of_nat s - h))) i h (S s).
  Proof.
    (intros x0 x i h s Hh; cps_intros (A & B & C)).
    assert (E : i - h * Z.of_nat s - h = i - h * Z.of_nat (S s)) by lia.
    split; [|split].
    - intros k Hk. rewrite zfupd_eq. destruct (Z.eqb_spec (i - h * Z.of_nat k) (i - h * Z.of_nat s)) as [Q|Q].
      + assert (k = s) by nia. subst k. rewrite E. apply B. right; left. nia.
      + apply A. assert (k <> s) by (intros ->; lia). lia.
    - intros p Hp. rewrite zfupd_eq. destruct (Z.eqb_spec p (i - h * Z.of_nat s)) as [Q|Q].
      + exfalso. subst p. destruct Hp as [Hp|[Hp|[Hp1 Hp2]]]; [nia| nia|].
        apply Hp2. replace (i - (i - h * Z.of_nat s)) with (Z.of_nat s * h) by lia. apply Z_mod_mult.
      + apply B. destruct Hp as [Hp|[Hp|Hp]]; [left; exact Hp| |right; right; exact Hp].
        (* [comment removed for export] *)
        destruct (Z.eq_dec ((i - p) mod h) 0) as [M|M]; [|right; right; split; [nia| exact M]].
        right; left. apply Z.mod_divide in M; [|lia]. destruct M as [q M].
        assert (q > Z.of_nat s) by nia. nia.
    - rewrite zfupd_eq. destruct (Z.eqb_spec (i - h * Z.of_nat (S s)) (i - h * Z.of_nat s)) as [Q|Q]; [nia|].
      apply B. right; left. nia.
  Qed.

  (* [comment removed for export] *)
  Lemma shift_inv : forall fuel x0 x lo h i v (s0 : nat) cnt,
    0 < h -> let j := i - h * Z.of_nat s0 in
    lo + h <= j -> j - lo < h * Z.of_nat fuel ->
    shifted x0 x i h s0 ->
    (forall k, (k < s0)%nat -> gtb (x0 (i - h * Z.of_nat (S k))) v = true) ->
    let '(x', j', cnt') := shift fuel x lo h j v cnt in
    exists s : nat, (s0 <= s)%nat /\ j' = i - h * Z.of_nat s /\ cnt' = (cnt + (s - s0))%nat /\ lo <= j' /\
      shifted x0 x' i h s /\
      (forall k, (k < s)%nat -> gtb (x0 (i - h * Z.of_nat (S k))) v = true) /\
      (j' - h < lo \/ le (x0 (j' - h)) v).
  Proof.
    intros fuel. induction fuel as [|fuel IH]; intros x0 x lo h i v s0 cnt Hh j Hj Hf SH GT; subst j.
    - exfalso. cbn in Hf. lia.
    - cbn [shift].
      assert (XJ : x (i - h * Z.of_nat s0 - h) = x0 (i - h * Z.of_nat (S s0))).
      { replace (i - h * Z.of_nat s0 - h) with (i - h * Z.of_nat (S s0)) by lia.
        cps_destruct SH as (A & B & C). apply B. right; left. nia. }
      rewrite XJ. destruct (gtb (x0 (i - h * Z.of_nat (S s0))) v) eqn:G.
      + assert (GT' : forall k, (k < S s0)%nat -> gtb (x0 (i - h * Z.of_nat (S k))) v = true).
        { intros k Hk. destruct (Nat.eq_dec k s0) as [->|NE]; [exact G| apply GT; lia]. }
        pose proof (shifted_step x0 x i h s0 Hh SH) as SH'. rewrite XJ in SH'.
        replace (i - h * Z.of_nat s0 - h) with (i - h * Z.of_nat (S s0)) in * by lia.
        destruct (Z.leb_spec (i - h * Z.of_nat (S s0)) (lo + h - 1)) as [L|L].
        * exists (S s0). split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact SH'|]. split; [exact GT'| left; lia].
        * specialize (IH x0 (zfupd x (i - h * Z.of_nat s0) (x0 (i - h * Z.of_nat (S s0)))) lo h i v (S s0) (S cnt) Hh).
          cbv zeta in IH.
          destruct (shift fuel _ lo h (i - h * Z.of_nat (S s0)) v (S cnt)) as [[x' j'] cnt'] eqn:SHF.
          cps_destruct (IH ltac:(lia) ltac:(nia) SH' GT') as (s & S1 & S2 & S3 & S4 & S5 & S6 & S7).
          exists s. split; [lia|]. split; [exact S2|]. split; [lia|]. split; [exact S4|]. split; [exact S5|]. split; [exact S6| exact S7].
      + exists s0. split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact SH|]. split; [exact GT|].
        right. replace (i - h * Z.of_nat s0 - h) with (i - h * Z.of_nat (S s0)) by lia. exact G.
  Qed.

  (* [comment removed for export] *)
  Lemma ins_result : forall x lo h i, 0 < h -> lo + h <= i ->
    let '(x2, s) := ins x lo h i in
    lo <= i - h * Z.of_nat s /\
    (forall p, (i < p \/ p < i - h * Z.of_nat s \/ (p <= i /\ (i - p) mod h <> 0)) -> x2 p = x p) /\
    (forall k, (k < s)%nat -> x2 (i - h * Z.of_nat k) = x (i - h * Z.of_nat (S k))) /\
    x2 (i - h * Z.of_nat s) = x i /\
    (forall k, (k < s)%nat -> gtb (x (i - h * Z.of_nat (S k))) (x i) = true) /\
    (i - h * Z.of_nat (S s) < lo \/ le (x (i - h * Z.of_nat (S s))) (x i)).
  Proof.
    intros x lo h i Hh Hi. unfold ins.
    pose proof (shift_inv (S (Z.to_nat (i - lo))) x x lo h i (x i) 0 0 Hh) as SI. cbv zeta in SI.
    replace (i - h * Z.of_nat 0) with i in SI by lia.
    destruct (shift (S (Z.to_nat (i - lo))) x lo h i (x i) 0) as [[x1 j1] cnt1] eqn:SH.
    cps_destruct (SI ltac:(lia) ltac:(nia) (shifted_0 x i h) ltac:(intros; lia)) as (s & _ & J & C & LO & (A & B & D) & GT & TERM).
    cbn [fst snd]. subst j1. replace cnt1 with s by lia.
    split; [exact LO|]. split; [|split; [|split; [|split; [exact GT|]]]].
    - intros p Hp. rewrite zfupd_eq. destruct (Z.eqb_spec p (i - h * Z.of_nat s)) as [->|NE].
      + exfalso. destruct Hp as [Hp|[Hp|[Hp1 Hp2]]]; [nia| lia|]. apply Hp2.
        replace (i - (i - h * Z.of_nat s)) with (Z.of_nat s * h) by lia. apply Z_mod_mult.
      + apply B. exact Hp.
    - intros k Hk. rewrite zfupd_eq. destruct (Z.eqb_spec (i - h * Z.of_nat k) (i - h * Z.of_nat s)) as [E|NE]; [nia|]. apply A. exact Hk.
    - rewrite zfupd_same. reflexivity.
    - replace (i - h * Z.of_nat (S s)) with (i - h * Z.of_nat s - h) by lia. exact TERM.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition pass_inv (x0 x : Z -> Z) (lo h i : Z) : Prop :=
    (forall p, (p < lo \/ i <= p) -> x p = x0 p) /\
    hsorted x lo i h /\
    (forall c (T : nat), lo <= c < lo + h -> c + h * (Z.of_nat T - 1) < i -> i <= c + h * Z.of_nat T ->
        Permutation (chain x c h T) (chain x0 c h T)).

  Lemma pass_inv_init : forall x0 lo h, 0 < h -> pass_inv x0 x0 lo h (lo + h).
  Proof.
    intros x0 lo h Hh. split; [intros; reflexivity|]. split.
    - intros p Hp Hq. lia.
    - intros c T Hc H1 H2. apply Permutation_refl.
  Qed.

  Lemma mod_off_chain : forall i p h, 0 < h -> (i - p) mod h <> 0 -> (i - (p + h)) mod h <> 0.
  Proof.
    intros i p h Hh H. replace (i - (p + h)) with (i - p + (-1) * h) by lia. rewrite Z_mod_plus_full. exact H.
  Qed.
  Lemma on_chain : forall i p h, 0 < h -> (i - p) mod h = 0 -> p <= i -> exists q : nat, p = i - h * Z.of_nat q.
  Proof.
    intros i p h Hh H Hp. apply Z.mod_divide in H; [|lia]. destruct H as [z H].
    assert (0 <= z) by nia. exists (Z.to_nat z). rewrite Z2Nat.id by lia. lia.
  Qed.
  (* [comment removed for export] *)

  Lemma ins_preserves : forall x0 x lo h i, 0 < h -> lo + h <= i ->
    pass_inv x0 x lo h i -> pass_inv x0 (fst (ins x lo h i)) lo h (i + 1).
  Proof.
    (intros x0 x lo h i Hh Hi; cps_intros (U & SRT & PERM)).
    pose proof (ins_result x lo h i Hh Hi) as IR.
    destruct (ins x lo h i) as [x2 s] eqn:INS. cbn [fst].
    cps_destruct IR as (LO & R1 & R2 & R3 & GT & TERM).
    split; [|split].
    - (* [comment removed for export] *)
      intros p Hp. rewrite R1 by lia. apply U. lia.
    - (* [comment removed for export] *)
      intros p Hp Hq.
      destruct (Z.eq_dec ((i - p) mod h) 0) as [M|M].
      + destruct (on_chain i p h Hh M ltac:(lia)) as [q Hpq].
        assert (1 <= Z.of_nat q) by nia.
        destruct q as [|k]; [cbn in *; lia|].
        replace (p + h) with (i - h * Z.of_nat k) by lia. rewrite Hpq.
        destruct (lt_dec (S k) s) as [C1|C1].
        * rewrite (R2 (S k) C1), (R2 k ltac:(lia)). apply (hsorted_pair x lo i h); [exact SRT| nia| lia| lia].
        * destruct (Nat.eq_dec (S k) s) as [C2|C2].
          -- rewrite C2. rewrite R3. rewrite (R2 k ltac:(lia)). apply gt_le. apply GT. lia.
          -- destruct (Nat.eq_dec k s) as [C3|C3].
             ++ subst k. rewrite R3. rewrite R1 by (right; left; nia).
                destruct TERM as [T|T]; [exfalso; nia| exact T].
             ++ rewrite !R1 by (right; left; nia). apply (hsorted_pair x lo i h); [exact SRT| nia| lia| nia].
      + pose proof (mod_off_chain i p h Hh M) as M2.
        assert (p + h <> i) by (intros E; apply M; replace (i - p) with (1 * h) by lia; apply Z_mod_mult).
        rewrite !R1 by (right; right; split; [lia| assumption]). apply (hsorted_pair x lo i h); [exact SRT| lia| lia| lia].
    - (* [comment removed for export] *)
      intros c T Hc HT1 HT2.
      set (K := (i - lo) / h).
      assert (KB : h * K <= i - lo < h * (K + 1)).
      { subst K. split; [apply Z.mul_div_le; lia|]. rewrite Z.mul_add_distr_l, Z.mul_1_r.
        pose proof (Z.mod_pos_bound (i - lo) h Hh). pose proof (Z.div_mod (i - lo) h ltac:(lia)). lia. }
      assert (K1 : 1 <= K) by (subst K; apply Z.div_le_lower_bound; lia).
      destruct (Z.eq_dec c (i - h * K)) as [Ec|Nc].
      + (* [comment removed for export] *)
        assert (ET : Z.of_nat T = K + 1) by nia.
        assert (SK : Z.of_nat s <= K) by nia.
        set (L := chain x c h (Z.to_nat K)).
        assert (LL : length L = Z.to_nat K) by (subst L; apply chain_length).
        assert (EQ : chain x2 c h T = firstn (Z.to_nat K - s) L ++ x i :: skipn (Z.to_nat K - s) L).
        { apply (nth_ext _ _ 0 0).
          - rewrite chain_length, length_app. cbn [length]. rewrite length_firstn, length_skipn, LL. lia.
          - intros n Hn. rewrite chain_length in Hn. rewrite chain_nth by exact Hn.
            destruct (lt_dec n (Z.to_nat K - s)) as [A|A].
            + rewrite app_nth1 by (rewrite length_firstn, LL; lia). rewrite nth_firstn.
              replace (n <? Z.to_nat K - s)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
              subst L. rewrite chain_nth by lia. apply R1. right; left. nia.
            + rewrite app_nth2 by (rewrite length_firstn, LL; lia). rewrite length_firstn, LL.
              replace (Init.Nat.min (Z.to_nat K - s) (Z.to_nat K)) with (Z.to_nat K - s)%nat by lia.
              destruct (Nat.eq_dec n (Z.to_nat K - s)) as [B|B].
              * rewrite B, Nat.sub_diag. cbn [nth]. replace (c + h * Z.of_nat (Z.to_nat K - s)) with (i - h * Z.of_nat s) by nia. exact R3.
              * replace (n - (Z.to_nat K - s))%nat with (S (n - (Z.to_nat K - s) - 1)) by lia. cbn [nth].
                rewrite nth_skipn. subst L. rewrite chain_nth by lia.
                replace (c + h * Z.of_nat n) with (i - h * Z.of_nat (Z.to_nat K - n)) by nia.
                rewrite R2 by lia. f_equal. nia. }
        rewrite EQ.
        replace T with (Z.to_nat K + 1)%nat by lia. rewrite chain_app. cbn [chain].
        replace (c + h * Z.of_nat (Z.to_nat K)) with i by nia. rewrite <- (U i) by lia.
        apply (Permutation_trans (l' := x i :: firstn (Z.to_nat K - s) L ++ skipn (Z.to_nat K - s) L)); [apply Permutation_sym; apply Permutation_middle|].
        rewrite firstn_skipn.
        apply (Permutation_trans (l' := x i :: chain x0 c h (Z.to_nat K))).
        * apply Permutation_cons; [reflexivity|]. subst L. apply PERM; [lia| nia| nia].
        * apply Permutation_cons_append.
      + (* [comment removed for export] *)
        assert (NCM : (i - c) mod h <> 0).
        { intros M. apply Z.mod_divide in M; [|lia]. destruct M as [z M]. assert (z = K) by nia. nia. }
        assert (HT1' : c + h * (Z.of_nat T - 1) < i).
        { destruct (Z.eq_dec (c + h * (Z.of_nat T - 1)) i) as [E|E]; [|lia]. exfalso. apply NCM.
          replace (i - c) with ((Z.of_nat T - 1) * h) by lia. apply Z_mod_mult. }
        rewrite (chain_ext x2 x c h T); [apply PERM; lia|].
        intros k Hk. apply R1. right; right. split; [nia|].
        intros M. apply NCM. apply Z.mod_divide in M; [|lia]. destruct M as [z M].
        apply Z.mod_divide; [lia|]. exists (z + Z.of_nat k). nia.
  Qed.

  Lemma pass_upto_inv : forall n x0 x lo h i, 0 < h -> lo + h <= i ->
    pass_inv x0 x lo h i -> pass_inv x0 (pass_upto n x lo h i) lo h (i + Z.of_nat n).
  Proof.
    induction n as [|n IH]; intros x0 x lo h i Hh Hi PI; cbn [pass_upto].
    - replace (i + Z.of_nat 0) with i by lia. exact PI.
    - replace (i + Z.of_nat (S n)) with (i + 1 + Z.of_nat n) by lia.
      apply IH; [exact Hh| lia|]. apply ins_preserves; assumption.
  Qed.

  (* [comment removed for export] *)
  Definition hpass (x : Z -> Z) (lo h up : Z) : Z -> Z :=
    pass_upto (Z.to_nat (up - (lo + h))) x lo h (lo + h).

  Lemma hpass_inv : forall x lo h up, 0 < h -> lo + h <= up -> pass_inv x (hpass x lo h up) lo h up.
  Proof.
    intros x lo h up Hh Hup. unfold hpass.
    replace up with (lo + h + Z.of_nat (Z.to_nat (up - (lo + h)))) at 2 by lia.
    apply pass_upto_inv; [exact Hh| lia| apply pass_inv_init; exact Hh].
  Qed.

  Lemma hpass_hsorted : forall x lo h up, 0 < h -> lo + h <= up -> hsorted (hpass x lo h up) lo up h.
  Proof. intros. cps_destruct (hpass_inv x lo h up) as (_ & S & _); assumption. Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Theorem hpass_keeps_ksorted : forall x lo h up k, 0 < h -> 0 < k -> lo + h <= up ->
    hsorted x lo up k -> hsorted (hpass x lo h up) lo up k.
  Proof.
    intros x lo h up k Hh Hk Hup KS.
    cps_destruct (hpass_inv x lo h up Hh Hup) as (U & SRT & PERM). set (x' := hpass x lo h up) in *.
    intros p Hp Hpk.
    destruct (Z.eq_dec (k mod h) 0) as [M|M].
    - (* [comment removed for export] *)
      apply Z.mod_divide in M; [|lia]. destruct M as [q M]. assert (0 < q) by nia.
      replace (p + k) with (p + h * Z.of_nat (Z.to_nat q)) by nia.
      apply (hsorted_chain x' lo up h Hh SRT); nia.
    - (* [comment removed for export] *)
      set (sY := (p - lo) / h). set (cY := p - h * sY).
      set (sX := (p + k - lo) / h). set (cX := p + k - h * sX).
      assert (BY : h * sY <= p - lo < h * (sY + 1)).
      { subst sY. split; [apply Z.mul_div_le; lia|]. rewrite Z.mul_add_distr_l, Z.mul_1_r.
        pose proof (Z.mod_pos_bound (p - lo) h Hh). pose proof (Z.div_mod (p - lo) h ltac:(lia)). lia. }
      assert (BX : h * sX <= p + k - lo < h * (sX + 1)).
      { subst sX. split; [apply Z.mul_div_le; lia|]. rewrite Z.mul_add_distr_l, Z.mul_1_r.
        pose proof (Z.mod_pos_bound (p + k - lo) h Hh). pose proof (Z.div_mod (p + k - lo) h ltac:(lia)). lia. }
      assert (SY0 : 0 <= sY) by nia. assert (SX0 : 0 <= sX) by nia.
      set (m := sX - sY). assert (M0 : 0 <= m) by nia.
      assert (CXm : cX + h * m = cY + k) by (subst m cX cY; lia).
      (* [comment removed for export] *)
      set (TY := Z.to_nat ((up - 1 - cY) / h + 1)). set (TX := Z.to_nat ((up - 1 - cX) / h + 1)).
      assert (BTY : h * ((up - 1 - cY) / h) <= up - 1 - cY < h * ((up - 1 - cY) / h + 1)).
      { split; [apply Z.mul_div_le; lia|]. rewrite Z.mul_add_distr_l, Z.mul_1_r.
        pose proof (Z.mod_pos_bound (up - 1 - cY) h Hh). pose proof (Z.div_mod (up - 1 - cY) h ltac:(lia)). lia. }
      assert (BTX : h * ((up - 1 - cX) / h) <= up - 1 - cX < h * ((up - 1 - cX) / h + 1)).
      { split; [apply Z.mul_div_le; lia|]. rewrite Z.mul_add_distr_l, Z.mul_1_r.
        pose proof (Z.mod_pos_bound (up - 1 - cX) h Hh). pose proof (Z.div_mod (up - 1 - cX) h ltac:(lia)). lia. }
      assert (DY0 : 0 <= (up - 1 - cY) / h) by (apply Z.div_pos; lia).
      assert (DX0 : 0 <= (up - 1 - cX) / h) by (apply Z.div_pos; lia).
      assert (ETY : Z.of_nat TY = (up - 1 - cY) / h + 1) by (subst TY; lia).
      assert (ETX : Z.of_nat TX = (up - 1 - cX) / h + 1) by (subst TX; lia).
      assert (SYT : sY < Z.of_nat TY) by nia.
      assert (SXT : sX < Z.of_nat TX) by nia.
      assert (LEN : Z.of_nat TX <= m + Z.of_nat TY) by nia.
      pose proof (lemma_L (chain x cX h TX) (chain x' cX h TX) (chain x cY h TY) (chain x' cY h TY) (Z.to_nat m)) as L.
      assert (CL := chain_length). 
      specialize (L ltac:(apply (chain_sorted x' lo up h); [exact Hh| exact SRT| nia| nia])
                    ltac:(apply (chain_sorted x' lo up h); [exact Hh| exact SRT| nia| nia])
                    ltac:(apply Permutation_sym; apply PERM; nia)
                    ltac:(apply Permutation_sym; apply PERM; nia)
                    ltac:(rewrite !chain_length; lia)).
      assert (PAIRS : forall t : nat, (Z.to_nat m + t < length (chain x cX h TX))%nat ->
                le (nth t (chain x cY h TY) 0) (nth (Z.to_nat m + t) (chain x cX h TX) 0)).
      { intros t Ht. rewrite chain_length in Ht. rewrite !chain_nth by lia.
        replace (cX + h * Z.of_nat (Z.to_nat m + t)) with (cY + h * Z.of_nat t + k) by nia.
        apply KS; nia. }
      specialize (L PAIRS (Z.to_nat sY) ltac:(rewrite chain_length; lia)).
      rewrite !chain_nth in L by lia.
      replace (cY + h * Z.of_nat (Z.to_nat sY)) with p in L by nia.
      replace (cX + h * Z.of_nat (Z.to_nat m + Z.to_nat sY)) with (p + k) in L by nia.
      exact L.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma frob_3a1 : forall a m, 0 < a -> (a - 1) * (3 * a) <= m ->
    exists u v, 0 <= u /\ 0 <= v /\ m = u * a + v * (3 * a + 1).
  Proof.
    intros a m Ha Hm. exists (m / a - 3 * (m mod a)), (m mod a).
    pose proof (Z.mod_pos_bound m a Ha) as MB. pose proof (Z.div_mod m a ltac:(lia)) as DM.
    assert (3 * a - 3 <= m / a) by (apply Z.div_le_lower_bound; lia).
    nia.
  Qed.

  Lemma far_apart_le : forall x lo up h p m, 0 < h ->
    hsorted x lo up (3 * h + 1) -> hsorted x lo up (9 * h + 4) ->
    lo <= p -> 27 * h * h + 9 * h <= m -> p + m < up -> le (x p) (x (p + m)).
  Proof.
    intros x lo up h p m Hh SA SB Hp Hm Hu.
    cps_destruct (frob_3a1 (3 * h + 1) m ltac:(lia) ltac:(nia)) as (u & v & Hu0 & Hv0 & E).
    replace (3 * (3 * h + 1) + 1) with (9 * h + 4) in E by lia.
    apply (le_trans _ (x (p + (3 * h + 1) * Z.of_nat (Z.to_nat u)))).
    - apply (hsorted_chain x lo up (3 * h + 1)); [lia| exact SA| lia| nia].
    - replace (p + m) with (p + (3 * h + 1) * Z.of_nat (Z.to_nat u) + (9 * h + 4) * Z.of_nat (Z.to_nat v)) by nia.
      apply (hsorted_chain x lo up (9 * h + 4)); [lia| exact SB| nia| nia].
  Qed.

  (* [comment removed for export] *)
  Theorem ins_shift_bound : forall x0 x lo h i up, 0 < h -> lo + h <= i -> i < up ->
    pass_inv x0 x lo h i ->
    hsorted x0 lo up (3 * h + 1) -> hsorted x0 lo up (9 * h + 4) ->
    Z.of_nat (snd (ins x lo h i)) <= 27 * h + 8.
  Proof.
    (intros x0 x lo h i up Hh Hi Hup; cps_intros (U & SRT & PERM); intros SA SB).
    pose proof (ins_result x lo h i Hh Hi) as IR. destruct (ins x lo h i) as [x2 s] eqn:INS. cbn [snd].
    cps_destruct IR as (LO & R1 & R2 & R3 & GT & TERM).
    set (K := (i - lo) / h).
    assert (KB : h * K <= i - lo < h * (K + 1)).
    { subst K. split; [apply Z.mul_div_le; lia|]. rewrite Z.mul_add_distr_l, Z.mul_1_r.
      pose proof (Z.mod_pos_bound (i - lo) h Hh). pose proof (Z.div_mod (i - lo) h ltac:(lia)). lia. }
    assert (K0 : 1 <= K) by (subst K; apply Z.div_le_lower_bound; lia).
    assert (SK : Z.of_nat s <= K) by nia.
    destruct (Z_lt_le_dec (27 * h + 8) (Z.of_nat s)) as [BAD|OK]; [|exact OK]. exfalso.
    set (c := i - h * K).
    set (L := chain x c h (Z.to_nat K)). set (L0 := chain x0 c h (Z.to_nat K)).
    set (P := fun e => gtb e (x i)).
    (* [comment removed for export] *)
    assert (C1 : (s <= countP P L)%nat).
    { rewrite (countP_split P (Z.to_nat K - s) L).
      rewrite (countP_all P (skipn (Z.to_nat K - s) L)); [rewrite length_skipn; subst L; rewrite chain_length; lia|].
      intros n Hn. rewrite length_skipn in Hn. subst L. rewrite chain_length in Hn. rewrite nth_skipn, chain_nth by lia.
      replace (c + h * Z.of_nat (Z.to_nat K - s + n)) with (i - h * Z.of_nat (S (s - 1 - n))) by (subst c; nia).
      apply GT. lia. }
    (* [comment removed for export] *)
    assert (C2 : countP P L = countP P L0) by (apply countP_perm; subst L L0; apply PERM; subst c; nia).
    (* [comment removed for export] *)
    assert (C3 : (countP P L0 <= Z.to_nat (27 * h + 8))%nat).
    { rewrite (countP_split P (Z.to_nat K - Z.to_nat (27 * h + 8)) L0).
      rewrite (countP_none P (firstn (Z.to_nat K - Z.to_nat (27 * h + 8)) L0)).
      - pose proof (countP_le_length P (skipn (Z.to_nat K - Z.to_nat (27 * h + 8)) L0)) as A.
        rewrite length_skipn in A. subst L0. rewrite chain_length in A. lia.
      - intros n Hn. rewrite length_firstn in Hn. subst L0. rewrite chain_length in Hn. rewrite nth_firstn.
        replace (n <? Z.to_nat K - Z.to_nat (27 * h + 8))%nat with true by (symmetry; apply Nat.ltb_lt; lia).
        rewrite chain_nth by lia. subst P. cbn beta.
        rewrite (U i) by lia.
        replace (x0 i) with (x0 (c + h * Z.of_nat n + h * (K - Z.of_nat n))) by (f_equal; subst c; lia).
        apply (far_apart_le x0 lo up h); [exact Hh| exact SA| exact SB| subst c; nia| nia| subst c; nia]. }
    lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma hsorted_ext : forall x y lo up h, (forall p, x p = y p) -> hsorted x lo up h -> hsorted y lo up h.
  Proof. intros x y lo up h E HS p Hp Hq. rewrite <- !E. apply HS; assumption. Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma pass_upto_app : forall a b x lo h i, pass_upto (a + b) x lo h i = pass_upto b (pass_upto a x lo h i) lo h (i + Z.of_nat a).
  Proof.
    induction a as [|a IH]; intros b x lo h i; cbn [pass_upto Nat.add].
    - f_equal. lia.
    - rewrite IH. f_equal. lia.
  Qed.
End Shell.
