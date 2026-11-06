(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith List Bool Lia.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module DF.

Definition TT : Z := 18446744073709551616.
Definition QT : Z := 1844674407370955161.

Fixpoint dval_acc (acc : Z) (cs : list Z) : Z :=
  match cs with [] => acc | c :: t => dval_acc (acc * 10 + (c - 48)) t end.
Definition dval (cs : list Z) : Z := dval_acc 0 cs.

Fixpoint leading_zeros (b : list Z) : nat :=
  match b with
  | c :: r => if Z.eqb c 48 then S (leading_zeros r) else 0%nat
  | [] => 0%nat
  end.
Definition sigd (b : list Z) : list Z := skipn (leading_zeros b) b.
Definition nsig (b : list Z) : nat := length (sigd b).
Definition P19 (b : list Z) : Z := dval (firstn 19 (sigd b)).
Definition P20 (b : list Z) : Z := dval (firstn 20 (sigd b)).
Definition D20 (b : list Z) : Z := nth 19 (sigd b) 48.

Definition pfam_cond (f : nat) (b : list Z) : Prop :=
  match f with
  | 0%nat => (nsig b <= 19)%nat \/ (nsig b = 20%nat /\ P20 b < TT)
  | 1%nat => (20 <= nsig b)%nat /\ QT + 1 <= P19 b
  | 2%nat => (21 <= nsig b)%nat /\ P19 b = QT /\ 54 <= D20 b
  | 3%nat => (21 <= nsig b)%nat /\ P20 b < TT
  | 4%nat => nsig b = 20%nat /\ P19 b = QT /\ 54 <= D20 b
  | _ => False
  end.

Definition pfam (b : list Z) : nat :=
  let n := nsig b in
  if Nat.leb 39 (length b) then 0%nat
  else if Nat.leb n 19 then 0%nat
  else if Nat.eqb n 20 then
    (if Z.ltb (P20 b) TT then 0%nat
     else if Z.leb (QT + 1) (P19 b) then 1%nat
     else 4%nat)
  else
    if Z.leb (QT + 1) (P19 b) then 1%nat
    else if (Z.eqb (P19 b) QT && Z.leb 54 (D20 b))%bool then 2%nat
    else 3%nat.

Definition all_digits (cs : list Z) : bool := forallb (fun c => Z.leb 48 c && Z.leb c 57)%bool cs.

Lemma dval_acc_app : forall a u v, dval_acc a (u ++ v) = dval_acc (dval_acc a u) v.
Proof. intros a u; revert a; induction u as [|c u IH]; intros a v; [reflexivity|]. cbn. apply IH. Qed.

Lemma dval_acc_bound : forall acc cs, 0 <= acc -> all_digits cs = true ->
  acc * 10 ^ Z.of_nat (length cs) <= dval_acc acc cs < (acc + 1) * 10 ^ Z.of_nat (length cs).
Proof.
  intros acc cs; revert acc; induction cs as [|c t IH]; intros acc Hacc Hd; cbn [dval_acc length].
  - cbn. lia.
  - cbn in Hd. apply andb_prop in Hd as [Hc Ht]. apply andb_prop in Hc as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2.
    specialize (IH (acc * 10 + (c - 48)) ltac:(lia) Ht). rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    pose proof (Z.pow_pos_nonneg 10 (Z.of_nat (length t))). nia.
Qed.
Lemma dval_bound : forall cs, all_digits cs = true -> 0 <= dval cs < 10 ^ Z.of_nat (length cs).
Proof. intros cs H. unfold dval. pose proof (dval_acc_bound 0 cs ltac:(lia) H). lia. Qed.

Lemma all_digits_app : forall u v, all_digits (u ++ v) = (all_digits u && all_digits v)%bool.
Proof. intros u v. unfold all_digits. rewrite forallb_app. reflexivity. Qed.
Lemma all_digits_firstn : forall k u, all_digits u = true -> all_digits (firstn k u) = true.
Proof.
  intros k u H. rewrite <- (firstn_skipn k u) in H. rewrite all_digits_app in H. apply andb_prop in H as [H _]. exact H.
Qed.
Lemma all_digits_skipn : forall k u, all_digits u = true -> all_digits (skipn k u) = true.
Proof.
  intros k u H. rewrite <- (firstn_skipn k u) in H. rewrite all_digits_app in H. apply andb_prop in H as [_ H]. exact H.
Qed.
Lemma leading_zeros_le : forall b, (leading_zeros b <= length b)%nat.
Proof. induction b as [|c r IH]; cbn; [lia|]. destruct (Z.eqb c 48); cbn; lia. Qed.
Lemma all_digits_sigd : forall b, all_digits b = true -> all_digits (sigd b) = true.
Proof. intros b H. unfold sigd. apply all_digits_skipn. exact H. Qed.

Lemma leading_zeros_spec : forall b,
  (forall i, (i < leading_zeros b)%nat -> nth i b 0 = 48)
  /\ ((leading_zeros b < length b)%nat -> nth (leading_zeros b) b 0 <> 48).
Proof.
  induction b as [|c r IH]; cbn [leading_zeros length].
  - split; [intros i Hi; lia | intros H; lia].
  - destruct (Z.eqb_spec c 48) as [->|Hc].
    + destruct IH as [IH1 IH2]. split.
      * intros [|i] Hi; cbn; [reflexivity | apply IH1; lia].
      * intros H. cbn. apply IH2. lia.
    + split; [intros i Hi; lia | intros _; exact Hc].
Qed.

Lemma dval_prefix_le : forall k s, all_digits s = true -> (k <= length s)%nat ->
  dval (firstn k s) * 10 ^ Z.of_nat (length s - k) <= dval s < (dval (firstn k s) + 1) * 10 ^ Z.of_nat (length s - k).
Proof.
  intros k s Hd Hk. unfold dval. rewrite <- (firstn_skipn k s) at 3. rewrite <- (firstn_skipn k s) at 5.
  rewrite !dval_acc_app.
  pose proof (dval_acc_bound (dval_acc 0 (firstn k s)) (skipn k s)) as B.
  rewrite length_skipn in B.
  assert (H0 : 0 <= dval_acc 0 (firstn k s)) by (pose proof (dval_bound (firstn k s) (all_digits_firstn k s Hd)) as X; unfold dval in X; lia).
  specialize (B H0 (all_digits_skipn k s Hd)). lia.
Qed.

Lemma P20_split : forall b, all_digits b = true -> (20 <= nsig b)%nat ->
  P20 b = P19 b * 10 + (D20 b - 48) /\ 48 <= D20 b <= 57.
Proof.
  intros b Hd Hn. unfold P20, P19, D20, nsig in *. pose proof (all_digits_sigd b Hd) as Hs. set (s := sigd b) in *.
  assert (E : firstn 20 s = firstn 19 s ++ [nth 19 s 48]).
  { rewrite <- (firstn_skipn 19 (firstn 20 s)). rewrite firstn_firstn by lia. f_equal.
    rewrite skipn_firstn_comm. replace (20 - 19)%nat with 1%nat by lia.
    destruct (skipn 19 s) as [|x r] eqn:Hsk.
    - exfalso. pose proof (f_equal (@length Z) Hsk) as X. rewrite length_skipn in X. cbn in X. lia.
    - cbn. f_equal. change (nth 19 s 48) with (nth (19 + 0) s 48). rewrite <- nth_skipn, Hsk. reflexivity. }
  split.
  - unfold dval. rewrite E, dval_acc_app. cbn [dval_acc]. reflexivity.
  - pose proof (all_digits_skipn 19 s Hs) as X. destruct (skipn 19 s) as [|x r] eqn:Hsk.
    + exfalso. pose proof (f_equal (@length Z) Hsk) as Y. rewrite length_skipn in Y. cbn in Y. lia.
    + cbn in X. apply andb_prop in X as [X _]. apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2.
      change (nth 19 s 48) with (nth (19 + 0) s 48). rewrite <- nth_skipn, Hsk. cbn. lia.
Qed.

Lemma pfam_cond_sound : forall b, all_digits b = true -> (length b <= 38)%nat -> pfam_cond (pfam b) b.
Proof.
  intros b Hd H38. pose proof (all_digits_sigd b Hd) as Hs. unfold pfam.
  destruct (Nat.leb 39 (length b)) eqn:E39; [apply Nat.leb_le in E39; lia|].
  set (n := nsig b).
  destruct (Nat.leb n 19) eqn:E19.
  { apply Nat.leb_le in E19. cbn [pfam_cond]. left. exact E19. }
  apply Nat.leb_gt in E19.
  pose proof (P20_split b Hd ltac:(unfold n in E19; lia)) as [SP R20].
  destruct (Nat.eqb n 20) eqn:E20.
  - apply Nat.eqb_eq in E20.
    destruct (Z.ltb (P20 b) TT) eqn:Ef.
    + apply Z.ltb_lt in Ef. cbn [pfam_cond]. right. split; [exact E20 | exact Ef].
    + apply Z.ltb_ge in Ef. destruct (Z.leb (QT + 1) (P19 b)) eqn:E1.
      * apply Z.leb_le in E1. cbn [pfam_cond]. split; [unfold n in E20; lia | exact E1].
      * apply Z.leb_gt in E1. cbn [pfam_cond]. unfold TT, QT in *.

        split; [exact E20|]. split; lia.
  - apply Nat.eqb_neq in E20. assert (N21 : (21 <= n)%nat) by lia.
    destruct (Z.leb (QT + 1) (P19 b)) eqn:E1.
    + apply Z.leb_le in E1. cbn [pfam_cond]. split; [lia | exact E1].
    + apply Z.leb_gt in E1. destruct (Z.eqb (P19 b) QT && Z.leb 54 (D20 b))%bool eqn:E2.
      * apply andb_prop in E2 as [Ea Eb]. apply Z.eqb_eq in Ea. apply Z.leb_le in Eb.
        cbn [pfam_cond]. split; [lia|]. split; [exact Ea | exact Eb].
      * cbn [pfam_cond]. split; [lia|]. unfold TT, QT in *.
        destruct (Z.eqb (P19 b) 1844674407370955161) eqn:Ea.
        -- apply Z.eqb_eq in Ea. cbn [andb] in E2. apply Z.leb_gt in E2. lia.
        -- apply Z.eqb_neq in Ea. lia.
Qed.

Lemma pfam_range : forall b, (pfam b <= 4)%nat.
Proof.
  intros b. unfold pfam.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia.
Qed.

End DF.
