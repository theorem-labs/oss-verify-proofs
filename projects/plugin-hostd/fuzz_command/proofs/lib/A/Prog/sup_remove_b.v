(* The block bookkeeping of sup_remove's post-condition (sup_remove_c.v:95-99),
   derived from the callees' block facts: rec_calls_free (spill arm only),
   arg_i, answer. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
Import ListNotations.
Local Open Scope Z_scope.

Lemma sr_b_pair_dec : forall (x y : Z * Z), {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Qed.

Lemma sr_b_in_or : forall (pn : Z * Z) (X : list (Z * Z)), In pn X \/ ~ In pn X.
Proof. intros pn X. destruct (in_dec sr_b_pair_dec pn X); auto. Qed.

Lemma sr_blocks : forall (B0 B1 B2 B3 O O1 O2 O3 F : list (Z * Z)) (p k p1 p2 n old : Z),
  (* rec_calls_free freed F (the spill's arguments, the recorder's) ; on the table arm F = [] and B1 = B0 *)
  Permutation B0 (B1 ++ F) -> NoDup B0 ->
  (forall pn, In pn F -> In pn O) ->
  (forall pn, In pn O1 <-> In pn O /\ ~ In pn F) ->
  (* arg_i made (p, k) *)
  Permutation B2 ((p, k) :: B1) -> ~ In (p, k) B1 ->
  (forall pn, In pn O2 <-> In pn O1 \/ pn = (p, k)) ->
  (forall pn, In pn O2 -> In pn B2) ->
  (* answer freed the block at old (the recorder's) and made (p1, n) and (p2, n); no block of B2 but the one at old
     is one of them (answer_c.v:121) *)
  (forall pn, In pn B3 <-> (In pn B2 /\ fst pn <> old) \/ pn = (p1, n) \/ pn = (p2, n)) ->
  (forall pn, In pn B2 -> fst pn <> old -> pn <> (p1, n) /\ pn <> (p2, n)) -> p1 <> p2 ->
  (forall pn, In pn O3 <-> (In pn O2 /\ fst pn <> old) \/ pn = (p1, n)) ->
  (forall pn, In pn B2 -> fst pn = old -> In pn O) ->
  (forall pn, In pn O3 -> In pn B3) ->
  (forall x y, In x B3 -> In y B3 -> fst x = fst y -> x = y) ->
  (forall pn, In pn O3 -> In pn O \/ ~ In pn B0) /\
  (forall pn, In pn B3 -> (In pn B0 /\ ~ In pn O) \/ In pn O3 \/ pn = (p2, n)) /\
  (forall pn, In pn B0 -> ~ In pn O -> In pn B3) /\
  In (p2, n) B3 /\
  (In (p2, n) B0 -> In (p2, n) O) /\
  ~ In p2 (map fst O3).
Proof.
  intros B0 B1 B2 B3 O O1 O2 O3 F p k p1 p2 n old
    HP0 HND HFO HO1 HP2 HpkB1 HO2 HO2B2 HB3 Hfr Hp12 HO3 HB2old HO3B3 Hfst.
  assert (HB0 : forall pn, In pn B0 -> In pn B1 \/ In pn F).
  { intros pn H. apply in_app_or. exact (Permutation_in _ HP0 H). }
  assert (HB1 : forall pn, In pn B1 -> In pn B0).
  { intros pn H. apply (Permutation_in _ (Permutation_sym HP0)).
    apply in_or_app. left. exact H. }
  assert (Hdisj : forall pn, In pn B1 -> ~ In pn F).
  { intros pn H1 H2.
    assert (HND' : NoDup (B1 ++ F)) by exact (Permutation_NoDup HP0 HND).
    destruct (in_split pn F H2) as (F1 & F2 & HF).
    rewrite HF, app_assoc in HND'.
    apply NoDup_remove_2 in HND'. apply HND'.
    apply in_or_app. left. apply in_or_app. left. exact H1. }
  assert (HB2 : forall pn, In pn B2 -> pn = (p, k) \/ In pn B1).
  { intros pn H. apply (Permutation_in _ HP2) in H.
    destruct H as [H | H]; [left; congruence | right; exact H]. }
  assert (HB1B2 : forall pn, In pn B1 -> In pn B2).
  { intros pn H. apply (Permutation_in _ (Permutation_sym HP2)). right. exact H. }
  split.
  { intros pn H. apply HO3 in H. destruct H as [[H _] | H].
    - apply HO2 in H. destruct H as [H | H].
      + left. apply HO1 in H. exact (proj1 H).
      + subst pn. destruct (sr_b_in_or (p, k) O) as [Ho | Ho]; [left; exact Ho | right].
        intro Hb. destruct (HB0 _ Hb) as [Hb1 | Hf];
          [exact (HpkB1 Hb1) | exact (Ho (HFO _ Hf))].
    - subst pn. destruct (sr_b_in_or (p1, n) O) as [Ho | Ho]; [left; exact Ho | right].
      intro Hb. destruct (HB0 _ Hb) as [Hb1 | Hf]; [| exact (Ho (HFO _ Hf))].
      destruct (Z.eq_dec p1 old) as [E | E];
        [exact (Ho (HB2old _ (HB1B2 _ Hb1) E)) | exact (proj1 (Hfr _ (HB1B2 _ Hb1) E) eq_refl)]. }
  split.
  { intros pn H. apply HB3 in H. destruct H as [[H Hold] | [H | H]].
    - destruct (HB2 _ H) as [Hpk | Hb1].
      + right; left. apply HO3. left. split; [apply HO2; right; exact Hpk | exact Hold].
      + destruct (sr_b_in_or pn O) as [Ho | Ho].
        * right; left. apply HO3. left. split; [| exact Hold].
          apply HO2. left. apply HO1. split; [exact Ho | exact (Hdisj _ Hb1)].
        * left. split; [exact (HB1 _ Hb1) | exact Ho].
    - right; left. apply HO3. right. exact H.
    - right; right. exact H. }
  split.
  { intros pn Hb Ho. apply HB3. left.
    destruct (HB0 _ Hb) as [Hb1 | Hf]; [| exfalso; exact (Ho (HFO _ Hf))].
    split; [exact (HB1B2 _ Hb1) |].
    intro Hold. exact (Ho (HB2old _ (HB1B2 _ Hb1) Hold)). }
  assert (H23 : In (p2, n) B3) by (apply HB3; right; right; reflexivity).
  split; [exact H23 |].
  split.
  { intro Hb. destruct (HB0 _ Hb) as [Hb1 | Hf]; [| exact (HFO _ Hf)].
    destruct (Z.eq_dec p2 old) as [E | E];
      [exact (HB2old _ (HB1B2 _ Hb1) E) | exfalso; exact (proj2 (Hfr _ (HB1B2 _ Hb1) E) eq_refl)]. }
  intro Hin. apply in_map_iff in Hin. destruct Hin as [x [Hx Hxo]].
  assert (Hxe : x = (p2, n)).
  { apply Hfst; [exact (HO3B3 _ Hxo) | exact H23 | simpl; exact Hx]. }
  subst x. apply HO3 in Hxo. destruct Hxo as [[Ho2 Hne] | He].
  - exact (proj2 (Hfr _ (HO2B2 _ Ho2) Hne) eq_refl).
  - apply Hp12. congruence.
Qed.
