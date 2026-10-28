(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Sorted.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition blen (bs : list Z) : Z := Z.of_nat (length bs).
Definition B (bs : list Z) (i : Z) : Z := nth (Z.to_nat i) bs 0.
Definition bytes_ok (bs : list Z) : Prop := Forall (fun b => 0 <= b < 256) bs.

Fixpoint str_close (fuel : nat) (bs : list Z) (k : Z) : option Z :=
  match fuel with
  | O => None
  | S f => if blen bs <=? k then None
           else if B bs k =? 34 then Some k
           else if B bs k =? 92 then str_close f bs (k + 2)
           else str_close f bs (k + 1)
  end.

Record S1OUT (bs : list Z) (idxs : list Z) : Prop := {
  s1_nonempty : idxs <> [];
  s1_sorted   : StronglySorted Z.lt idxs;
  s1_range    : Forall (fun i => 0 <= i < blen bs) idxs;
  s1_nonspace : Forall (fun i => B bs i <> 32 /\ B bs i <> 9 /\ B bs i <> 10 /\ B bs i <> 13) idxs;
  s1_strings  : forall k i, nth_error idxs k = Some i -> B bs i = 34 ->
                  exists j, str_close (length bs) bs (i + 1) = Some j /\ i < j < blen bs /\ B bs j = 34 /\
                            (forall i', nth_error idxs (S k) = Some i' -> j < i');
}.

Lemma blen_nonneg : forall bs, 0 <= blen bs.
Proof. intros; unfold blen; lia. Qed.

Lemma B_pad : forall bs i, blen bs <= i -> B bs i = 0.
Proof.
  intros bs i H. unfold B, blen in *. apply nth_overflow. lia.
Qed.

Lemma B_range : forall bs i, bytes_ok bs -> 0 <= B bs i < 256.
Proof.
  intros bs i H. unfold B.
  destruct (Nat.lt_ge_cases (Z.to_nat i) (length bs)) as [Hl|Hl].
  - unfold bytes_ok in H. rewrite Forall_forall in H. apply H. apply nth_In; exact Hl.
  - rewrite nth_overflow by exact Hl. lia.
Qed.

Definition padded (bs : list Z) : list Z := bs ++ repeat 0 64.

Lemma nth_padded : forall bs i, nth i (padded bs) 0 = nth i bs 0.
Proof.
  intros bs i. unfold padded.
  destruct (Nat.lt_ge_cases i (length bs)) as [Hl|Hl].
  - apply app_nth1; exact Hl.
  - rewrite app_nth2 by exact Hl. rewrite (nth_overflow bs) by exact Hl.
    destruct (Nat.lt_ge_cases (i - length bs) 64) as [H6|H6].
    + apply nth_repeat.
    + apply nth_overflow. rewrite repeat_length. exact H6.
Qed.

Lemma B_padded : forall bs i, B (padded bs) i = B bs i.
Proof. intros; unfold B; apply nth_padded. Qed.

Lemma length_padded : forall bs, length (padded bs) = (length bs + 64)%nat.
Proof. intros; unfold padded; rewrite length_app, repeat_length; reflexivity. Qed.

Inductive closes (bs : list Z) : Z -> Z -> Prop :=
| closes_here : forall p, 0 <= p < blen bs -> B bs p = 34 -> closes bs p p
| closes_esc  : forall p j, 0 <= p < blen bs -> B bs p = 92 -> closes bs (p + 2) j -> closes bs p j
| closes_ord  : forall p j, 0 <= p < blen bs -> B bs p <> 34 -> B bs p <> 92 -> closes bs (p + 1) j -> closes bs p j.

Lemma closes_bounds : forall bs p j, closes bs p j -> 0 <= p /\ p <= j /\ j < blen bs /\ B bs j = 34.
Proof. induction 1; intuition lia. Qed.

Lemma closes_pos : forall bs p j, closes bs p j -> 0 <= p < blen bs.
Proof. destruct 1; assumption. Qed.

Lemma closes_det : forall bs p j, closes bs p j -> forall j', closes bs p j' -> j = j'.
Proof.
  induction 1; intros j' H'; inversion H'; subst; try congruence; try lia; auto.
Qed.

Lemma closes_quote_inv : forall bs p j, closes bs p j -> B bs p = 34 -> j = p.
Proof. intros bs p j H Hq; inversion H; subst; congruence. Qed.

Lemma closes_esc_inv : forall bs p j, closes bs p j -> B bs p = 92 -> closes bs (p + 2) j.
Proof. intros bs p j H Hq; inversion H; subst; try congruence; assumption. Qed.

Lemma closes_ord_inv : forall bs p j, closes bs p j -> B bs p <> 34 -> B bs p <> 92 -> closes bs (p + 1) j.
Proof. intros bs p j H H1 H2; inversion H; subst; try congruence; assumption. Qed.

Lemma closes_skip : forall bs n p j, closes bs p j ->
  (forall t, 0 <= t < Z.of_nat n -> B bs (p + t) <> 34 /\ B bs (p + t) <> 92) -> closes bs (p + Z.of_nat n) j.
Proof.
  induction n as [|n IH]; intros p j H Hb.
  - replace (p + Z.of_nat 0) with p by lia. exact H.
  - replace (p + Z.of_nat (S n)) with ((p + 1) + Z.of_nat n) by lia.
    apply IH.
    + destruct (Hb 0) as [Ha Hc]; [lia|]. replace (p + 0) with p in * by lia. apply closes_ord_inv; assumption.
    + intros t Ht. replace (p + 1 + t) with (p + (t + 1)) by lia. apply Hb. lia.
Qed.

Lemma closes_u_inv : forall bs p j, closes bs p j -> B bs p = 92 ->
  (forall t, 2 <= t < 6 -> B bs (p + t) <> 34 /\ B bs (p + t) <> 92) -> closes bs (p + 6) j.
Proof.
  intros bs p j H Hq Hb. apply closes_esc_inv in H; [|exact Hq].
  replace (p + 6) with ((p + 2) + Z.of_nat 4) by lia. apply closes_skip; [exact H|].
  intros t Ht. replace (p + 2 + t) with (p + (t + 2)) by lia. apply Hb. lia.
Qed.

Lemma closes_esc_le : forall bs p j, closes bs p j -> B bs p = 92 -> p + 2 <= j.
Proof. intros bs p j H Hq. apply closes_esc_inv in H; [|exact Hq]. apply closes_bounds in H. lia. Qed.

Lemma closes_ord_le : forall bs p j, closes bs p j -> B bs p <> 34 -> p + 1 <= j.
Proof.
  intros bs p j H Hq. inversion H; subst; try congruence.
  - match goal with Hc : closes _ (p + 2) _ |- _ => apply closes_bounds in Hc; lia end.
  - match goal with Hc : closes _ (p + 1) _ |- _ => apply closes_bounds in Hc; lia end.
Qed.

Lemma closes_u_le : forall bs p j, closes bs p j -> B bs p = 92 ->
  (forall t, 2 <= t < 6 -> B bs (p + t) <> 34 /\ B bs (p + t) <> 92) -> p + 6 <= j.
Proof. intros bs p j H Hq Hb. pose proof (closes_u_inv _ _ _ H Hq Hb) as H6. apply closes_bounds in H6. lia. Qed.

Lemma str_close_closes : forall fuel bs p j, 0 <= p -> str_close fuel bs p = Some j -> closes bs p j.
Proof.
  induction fuel as [|f IH]; intros bs p j Hp H; simpl in H; [discriminate|].
  destruct (blen bs <=? p) eqn:El; [discriminate|]. apply Z.leb_gt in El.
  destruct (B bs p =? 34) eqn:E34.
  - apply Z.eqb_eq in E34. inversion H; subst. apply closes_here; [lia|exact E34].
  - apply Z.eqb_neq in E34. destruct (B bs p =? 92) eqn:E92.
    + apply Z.eqb_eq in E92. apply closes_esc; [lia|exact E92|]. apply IH; [lia|exact H].
    + apply Z.eqb_neq in E92. apply closes_ord; [lia|exact E34|exact E92|]. apply IH; [lia|exact H].
Qed.

Lemma closes_str_close : forall bs p j, closes bs p j ->
  forall fuel, (Z.to_nat (j - p) < fuel)%nat -> str_close fuel bs p = Some j.
Proof.
  induction 1 as [p Hp Hq | p j Hp Hq Hc IH | p j Hp H1 H2 Hc IH]; intros fuel Hf.
  - destruct fuel as [|f]; [lia|]. simpl.
    destruct (blen bs <=? p) eqn:El; [apply Z.leb_le in El; lia|].
    rewrite Hq. reflexivity.
  - pose proof (closes_bounds _ _ _ Hc) as Hb.
    destruct fuel as [|f]; [lia|]. simpl.
    destruct (blen bs <=? p) eqn:El; [apply Z.leb_le in El; lia|].
    rewrite Hq. simpl. apply IH. lia.
  - pose proof (closes_bounds _ _ _ Hc) as Hb.
    destruct fuel as [|f]; [lia|]. simpl.
    destruct (blen bs <=? p) eqn:El; [apply Z.leb_le in El; lia|].
    destruct (B bs p =? 34) eqn:E34; [apply Z.eqb_eq in E34; congruence|].
    destruct (B bs p =? 92) eqn:E92; [apply Z.eqb_eq in E92; congruence|].
    apply IH. lia.
Qed.

Lemma closes_str_close_len : forall bs p j, closes bs p j -> str_close (length bs) bs p = Some j.
Proof.
  intros bs p j H. apply closes_str_close; [exact H|].
  pose proof (closes_bounds _ _ _ H) as Hb. unfold blen in Hb. lia.
Qed.

Lemma StronglySorted_nth_lt : forall (l : list Z) a b x y,
  StronglySorted Z.lt l -> (a < b)%nat -> nth_error l a = Some x -> nth_error l b = Some y -> x < y.
Proof.
  induction l as [|h t IH]; intros a b x y Hs Hab Ha Hb.
  - destruct a; discriminate.
  - inversion Hs as [|? ? Hs' Hall]; subst.
    destruct a as [|a]; destruct b as [|b]; try lia; simpl in *.
    + inversion Ha; subst. rewrite Forall_forall in Hall. apply Hall. eapply nth_error_In; eauto.
    + apply (IH a b x y Hs'); [lia|exact Ha|exact Hb].
Qed.

Lemma StronglySorted_nth_ge_from : forall (l : list Z) lo k x,
  StronglySorted Z.lt l -> Forall (fun i => lo <= i) l -> nth_error l k = Some x -> lo + Z.of_nat k <= x.
Proof.
  induction l as [|h t IH]; intros lo k x Hs Hr Hk.
  - destruct k; discriminate.
  - inversion Hs as [|? ? Hs' Hall]; subst. inversion Hr as [|? ? Hh Hr']; subst.
    destruct k as [|k]; simpl in Hk.
    + inversion Hk; subst. lia.
    + assert (Hr1 : Forall (fun i => lo + 1 <= i) t).
      { rewrite Forall_forall in *. intros y Hy. specialize (Hall y Hy). lia. }
      pose proof (IH (lo + 1) k x Hs' Hr1 Hk). lia.
Qed.

Lemma StronglySorted_nth_ge : forall (l : list Z) k x,
  StronglySorted Z.lt l -> Forall (fun i => 0 <= i) l -> nth_error l k = Some x -> Z.of_nat k <= x.
Proof. intros l k x Hs Hr Hk. pose proof (StronglySorted_nth_ge_from l 0 k x Hs Hr Hk). lia. Qed.

Section S1OUT_facts.
  Variables (bs idxs : list Z).
  Hypothesis HS : S1OUT bs idxs.

  Lemma S1OUT_nth_range : forall k i, nth_error idxs k = Some i -> 0 <= i < blen bs.
  Proof.
    intros k i Hk. pose proof (s1_range _ _ HS) as Hr. rewrite Forall_forall in Hr.
    apply Hr. eapply nth_error_In; eauto.
  Qed.

  Lemma S1OUT_nth_lt : forall a b x y, (a < b)%nat -> nth_error idxs a = Some x -> nth_error idxs b = Some y -> x < y.
  Proof. intros; eapply StronglySorted_nth_lt; eauto using s1_sorted. Qed.

  Lemma S1OUT_nth_ge : forall k i, nth_error idxs k = Some i -> Z.of_nat k <= i.
  Proof.
    intros k i Hk. eapply StronglySorted_nth_ge; eauto using s1_sorted.
    pose proof (s1_range _ _ HS) as Hr. rewrite Forall_forall in *. intros x Hx. specialize (Hr x Hx). lia.
  Qed.

  Lemma S1OUT_length_le : Z.of_nat (length idxs) <= blen bs.
  Proof.
    destruct (length idxs) as [|n] eqn:En; [pose proof (blen_nonneg bs); lia|].
    assert (Hn : (n < length idxs)%nat) by lia.
    destruct (nth_error idxs n) as [i|] eqn:Ei; [|apply nth_error_None in Ei; lia].
    pose proof (S1OUT_nth_ge _ _ Ei). pose proof (S1OUT_nth_range _ _ Ei). lia.
  Qed.

  Lemma S1OUT_length_pos : (0 < length idxs)%nat.
  Proof. pose proof (s1_nonempty _ _ HS). destruct idxs; [congruence|simpl; lia]. Qed.

  Lemma S1OUT_string : forall k i, nth_error idxs k = Some i -> B bs i = 34 ->
    exists j, closes bs (i + 1) j /\ i < j < blen bs /\
              (forall i', nth_error idxs (S k) = Some i' -> j < i').
  Proof.
    intros k i Hk Hq. destruct (s1_strings _ _ HS k i Hk Hq) as (j & Hc & Hj & _ & Hn).
    exists j. split; [|split; assumption].
    eapply str_close_closes; [|exact Hc]. pose proof (S1OUT_nth_range _ _ Hk). lia.
  Qed.
End S1OUT_facts.
