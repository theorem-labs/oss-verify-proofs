(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia List Bool Uint63.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Open Scope uint63_scope.

Inductive itrie (A : Type) : Type :=
| IEmpty
| ILeaf (k : int) (v : A)
| INode (l r : itrie A).
Arguments IEmpty {A}.
Arguments ILeaf {A} k v.
Arguments INode {A} l r.

Definition iempty {A} : itrie A := IEmpty.

Fixpoint iget {A} (k : int) (t : itrie A) : option A :=
  match t with
  | IEmpty => None
  | ILeaf k' v => if k =? k' then Some v else None
  | INode l r =>
      if (k land 1) =? 0 then iget (k >> 1) l else iget (k >> 1) r
  end.

Fixpoint ijoin {A} (n : nat) (k1 : int) (v1 : A) (k2 : int) (v2 : A)
  : itrie A :=
  match n with
  | O => ILeaf k1 v1
  | S n =>
      if (k1 land 1) =? 0 then
        if (k2 land 1) =? 0
        then INode (ijoin n (k1 >> 1) v1 (k2 >> 1) v2) IEmpty
        else INode (ILeaf (k1 >> 1) v1) (ILeaf (k2 >> 1) v2)
      else
        if (k2 land 1) =? 0
        then INode (ILeaf (k2 >> 1) v2) (ILeaf (k1 >> 1) v1)
        else INode IEmpty (ijoin n (k1 >> 1) v1 (k2 >> 1) v2)
  end.

Definition ifuel : nat := 63.

Fixpoint iset {A} (k : int) (x : A) (t : itrie A) : itrie A :=
  match t with
  | IEmpty => ILeaf k x
  | ILeaf k' v => if k =? k' then ILeaf k x else ijoin ifuel k x k' v
  | INode l r =>
      if (k land 1) =? 0 then INode (iset (k >> 1) x l) r
      else INode l (iset (k >> 1) x r)
  end.

Fixpoint iupd {A} (k : int) (f : option A -> A) (t : itrie A) : itrie A :=
  match t with
  | IEmpty => ILeaf k (f None)
  | ILeaf k' v =>
      if k =? k' then ILeaf k (f (Some v)) else ijoin ifuel k (f None) k' v
  | INode l r =>
      if (k land 1) =? 0 then INode (iupd (k >> 1) f l) r
      else INode l (iupd (k >> 1) f r)
  end.

Definition inode {A} (l r : itrie A) : itrie A :=
  match l, r with
  | IEmpty, IEmpty => IEmpty
  | _, _ => INode l r
  end.

Fixpoint iremove {A} (k : int) (t : itrie A) : itrie A :=
  match t with
  | IEmpty => IEmpty
  | ILeaf k' v => if k =? k' then IEmpty else t
  | INode l r =>
      if (k land 1) =? 0 then inode (iremove (k >> 1) l) r
      else inode l (iremove (k >> 1) r)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wB_eq : wB = (2^63)%Z.
Proof. reflexivity. Qed.

Lemma to_Z_lsr1 k : to_Z (k >> 1) = (to_Z k / 2)%Z.
Proof. rewrite lsr_spec. change (2 ^ to_Z 1)%Z with 2%Z. reflexivity. Qed.

Lemma to_Z_land1 k : to_Z (k land 1) = (to_Z k mod 2)%Z.
Proof.
  rewrite land_spec'. change (to_Z 1) with (Z.ones 1).
  rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma ieven_spec k : ((k land 1) =? 0) = (to_Z k mod 2 =? 0)%Z.
Proof.
  rewrite <- to_Z_land1.
  destruct (eqbP (k land 1) 0) as [H|H]; rewrite to_Z_0 in H;
    symmetry; [apply Z.eqb_eq | apply Z.eqb_neq]; exact H.
Qed.

Lemma int_split_eq k k' :
  k = k' <->
  (((k land 1) =? 0) = ((k' land 1) =? 0) /\ k >> 1 = k' >> 1).
Proof.
  split; [intros ->; split; reflexivity|].
  intros [Hb Hs]. apply to_Z_inj.
  apply (f_equal to_Z) in Hs. rewrite !to_Z_lsr1 in Hs.
  rewrite !ieven_spec in Hb.
  pose proof (Z.mod_pos_bound (to_Z k) 2 ltac:(lia)).
  pose proof (Z.mod_pos_bound (to_Z k') 2 ltac:(lia)).
  rewrite (Z.div_mod (to_Z k) 2), (Z.div_mod (to_Z k') 2) by lia.
  rewrite Hs. f_equal.
  destruct (Z.eqb_spec (to_Z k mod 2) 0), (Z.eqb_spec (to_Z k' mod 2) 0);
    try discriminate; lia.
Qed.

Lemma int_neq_split k k' :
  k <> k' -> ((k land 1) =? 0) = ((k' land 1) =? 0) -> k >> 1 <> k' >> 1.
Proof. intros Hne Hb Hs. apply Hne, int_split_eq. split; assumption. Qed.

Lemma eqb_sym (a b : int) : (a =? b) = (b =? a).
Proof.
  destruct (eqbP a b) as [H|H], (eqbP b a) as [H'|H']; try reflexivity;
    exfalso; apply H' || apply H; symmetry; assumption.
Qed.

Lemma eqb_neq_false (a b : int) : a <> b -> (a =? b) = false.
Proof. intros H. apply eqb_false_complete, H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma to_Z_lsr1_lt k n :
  (to_Z k < 2 ^ Z.of_nat (S n))%Z -> (to_Z (k >> 1) < 2 ^ Z.of_nat n)%Z.
Proof.
  intros H. rewrite to_Z_lsr1.
  rewrite Nat2Z.inj_succ, Z.pow_succ_r in H by lia.
  apply Z.div_lt_upper_bound; lia.
Qed.

Lemma iget_ijoin {A} n : forall k k1 (v1 : A) k2 v2,
  k1 <> k2 ->
  (to_Z k1 < 2 ^ Z.of_nat n)%Z -> (to_Z k2 < 2 ^ Z.of_nat n)%Z ->
  iget k (ijoin n k1 v1 k2 v2) =
  if k =? k1 then Some v1 else if k =? k2 then Some v2 else None.
Proof.
  induction n as [|n IH]; intros k k1 v1 k2 v2 Hne H1 H2.
  - exfalso. apply Hne, to_Z_inj.
    pose proof (to_Z_bounded k1). pose proof (to_Z_bounded k2).
    change (2 ^ Z.of_nat 0)%Z with 1%Z in *. lia.
  - cbn [ijoin].
    destruct ((k1 land 1) =? 0) eqn:E1, ((k2 land 1) =? 0) eqn:E2;
      cbn [iget]; destruct ((k land 1) =? 0) eqn:E.
    all: try (rewrite IH by
      (first [ apply int_neq_split; [assumption | congruence]
             | apply to_Z_lsr1_lt; assumption ])).
    all: cbn [iget].
    all: repeat match goal with
         | |- context [?a =? ?b] =>
             lazymatch a with
             | (_ >> _) => fail
             | _ => destruct (eqbP a b) as [Hq|Hq];
                    [apply to_Z_inj in Hq; subst a|]
             end
         end.
    all: try rewrite !Uint63.eqb_refl.
    all: try congruence.
    all: try reflexivity.
    all: repeat match goal with
         | |- context [?a =? ?b] =>
             let Hq := fresh "Hq" in
             destruct (eqbP a b) as [Hq|Hq];
             [apply to_Z_inj in Hq|]
         end.
    all: try reflexivity.
    all: try congruence.
    all: exfalso.
    all: repeat match goal with
         | H : to_Z ?a <> to_Z ?b |- _ =>
             assert (a <> b) by (intros ->; apply H; reflexivity); clear H
         end.
    all: match goal with
         | H : ?a <> ?b |- _ =>
             apply H, int_split_eq; split; congruence
         end.
Qed.

Lemma to_Z_lt_fuel (k : int) : (to_Z k < 2 ^ Z.of_nat ifuel)%Z.
Proof. pose proof (to_Z_bounded k) as H. rewrite wB_eq in H. exact (proj2 H). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma iget_iempty {A} k : iget k (@iempty A) = None.
Proof. reflexivity. Qed.

Lemma iget_iupd_same {A} : forall (t : itrie A) k f,
  iget k (iupd k f t) = Some (f (iget k t)).
Proof.
  induction t as [|k' v|l IHl r IHr]; intros k f; cbn [iupd iget].
  - rewrite Uint63.eqb_refl. reflexivity.
  - destruct (eqbP k k') as [H|H].
    + cbn [iget]. rewrite Uint63.eqb_refl. reflexivity.
    + rewrite iget_ijoin; try apply to_Z_lt_fuel.
      * rewrite Uint63.eqb_refl. reflexivity.
      * intros ->. apply H. reflexivity.
  - destruct ((k land 1) =? 0) eqn:E; cbn [iget]; rewrite E; auto.
Qed.

Lemma iget_iupd_other {A} : forall (t : itrie A) k k' f,
  k <> k' -> iget k' (iupd k f t) = iget k' t.
Proof.
  induction t as [|k0 v|l IHl r IHr]; intros k k' f Hne; cbn [iupd iget].
  - rewrite eqb_neq_false by congruence. reflexivity.
  - destruct (eqbP k k0) as [H|H].
    + apply to_Z_inj in H. subst k0. cbn [iget].
      rewrite eqb_neq_false by congruence. reflexivity.
    + rewrite iget_ijoin; try apply to_Z_lt_fuel.
      * rewrite (eqb_neq_false k' k) by congruence. reflexivity.
      * intros ->. apply H. reflexivity.
  - destruct ((k land 1) =? 0) eqn:E; cbn [iget];
      destruct ((k' land 1) =? 0) eqn:E'; try reflexivity.
    + apply IHl. apply int_neq_split; congruence.
    + apply IHr. apply int_neq_split; congruence.
Qed.

Lemma iset_iupd {A} : forall (t : itrie A) k x,
  iset k x t = iupd k (fun _ => x) t.
Proof.
  induction t as [|k' v|l IHl r IHr]; intros k x; cbn [iset iupd];
    try reflexivity.
  rewrite IHl, IHr. reflexivity.
Qed.

Lemma iget_iset_same {A} (t : itrie A) k x : iget k (iset k x t) = Some x.
Proof. rewrite iset_iupd. apply iget_iupd_same. Qed.

Lemma iget_iset_other {A} (t : itrie A) k k' x :
  k <> k' -> iget k' (iset k x t) = iget k' t.
Proof. rewrite iset_iupd. apply iget_iupd_other. Qed.

Lemma iget_iset {A} (t : itrie A) k k' x :
  iget k' (iset k x t) = if k' =? k then Some x else iget k' t.
Proof.
  destruct (eqbP k' k) as [H|H].
  - apply to_Z_inj in H. subst. apply iget_iset_same.
  - apply iget_iset_other. intros ->. apply H. reflexivity.
Qed.

Lemma iget_iupd {A} (t : itrie A) k k' f :
  iget k' (iupd k f t) = if k' =? k then Some (f (iget k t)) else iget k' t.
Proof.
  destruct (eqbP k' k) as [H|H].
  - apply to_Z_inj in H. subst. apply iget_iupd_same.
  - apply iget_iupd_other. intros ->. apply H. reflexivity.
Qed.

Lemma iget_inode {A} (l r : itrie A) k :
  iget k (inode l r) = iget k (INode l r).
Proof.
  destruct l, r; try reflexivity. cbn.
  destruct ((k land 1) =? 0); reflexivity.
Qed.

Lemma iget_iremove_same {A} : forall (t : itrie A) k,
  iget k (iremove k t) = None.
Proof.
  induction t as [|k' v|l IHl r IHr]; intros k; cbn [iremove].
  - reflexivity.
  - destruct (k =? k') eqn:E; cbn [iget]; [reflexivity | rewrite E; reflexivity].
  - destruct ((k land 1) =? 0) eqn:E; rewrite iget_inode; cbn [iget]; rewrite E; auto.
Qed.

Lemma iget_iremove_other {A} : forall (t : itrie A) k k',
  k <> k' -> iget k' (iremove k t) = iget k' t.
Proof.
  induction t as [|k0 v|l IHl r IHr]; intros k k' Hne; cbn [iremove].
  - reflexivity.
  - destruct (eqbP k k0) as [H|H]; [|reflexivity].
    apply to_Z_inj in H. subst k0. cbn [iget].
    rewrite eqb_neq_false by congruence. reflexivity.
  - destruct ((k land 1) =? 0) eqn:E; rewrite iget_inode; cbn [iget];
      destruct ((k' land 1) =? 0) eqn:E'; try reflexivity.
    + apply IHl. apply int_neq_split; congruence.
    + apply IHr. apply int_neq_split; congruence.
Qed.

Lemma iget_iremove {A} (t : itrie A) k k' :
  iget k' (iremove k t) = if k' =? k then None else iget k' t.
Proof.
  destruct (eqbP k' k) as [H|H].
  - apply to_Z_inj in H. subst. apply iget_iremove_same.
  - apply iget_iremove_other. intros ->. apply H. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint ielements_aux {A} (n : nat) (sh p : int) (t : itrie A)
    (acc : list (int * A)) : list (int * A) :=
  match n with
  | O => match iget 0 t with Some v => (p, v) :: acc | None => acc end
  | S n' =>
      match t with
      | IEmpty => acc
      | ILeaf k v =>
          if ((k << sh) >> sh) =? k then (p + (k << sh), v) :: acc else acc
      | INode l r =>
          ielements_aux n' (sh + 1) p l
            (ielements_aux n' (sh + 1) (p + (1 << sh)) r acc)
      end
  end.

Definition ielements {A} (t : itrie A) : list (int * A) :=
  ielements_aux ifuel 0 0 t [].

Lemma lsl_lsr_mod a s :
  (0 <= s < 63)%Z -> (0 <= a)%Z ->
  (((a * 2 ^ s) mod 2 ^ 63) / 2 ^ s = a mod 2 ^ (63 - s))%Z.
Proof.
  intros Hs Ha.
  replace (2 ^ 63)%Z with (2 ^ (63 - s) * 2 ^ s)%Z
    by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (0 < 2 ^ s)%Z by (apply Z.pow_pos_nonneg; lia).
  assert (0 < 2 ^ (63 - s))%Z by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.mul_mod_distr_r by lia.
  apply Z.div_mul. lia.
Qed.

Lemma ielements_aux_spec {A} : forall n sh p (t : itrie A) acc k v,
  (Z.of_nat n + to_Z sh = 63)%Z -> (to_Z p < 2 ^ to_Z sh)%Z ->
  In (k, v) (ielements_aux n sh p t acc) <->
  (In (k, v) acc \/
   exists r, (to_Z r < 2 ^ Z.of_nat n)%Z /\
             (to_Z k = to_Z p + to_Z r * 2 ^ to_Z sh)%Z /\
             iget r t = Some v).
Proof.
  induction n as [|n IH]; intros sh p t acc k v Hn Hp.
  - cbn [ielements_aux]. change (2 ^ Z.of_nat 0)%Z with 1%Z.
    assert (Hr0 : forall r, (to_Z r < 1)%Z -> r = 0).
    { intros r Hr. apply to_Z_inj. rewrite to_Z_0.
      pose proof (to_Z_bounded r). lia. }
    split.
    + destruct (iget 0 t) as [v'|] eqn:E.
      * intros [H|H]; [|left; exact H]. inversion H; subst. right.
        exists 0. rewrite to_Z_0. split; [lia|]. split; [lia|]. exact E.
      * intros H. left. exact H.
    + intros [H|(r & Hr & Hk & Hg)].
      * destruct (iget 0 t); [right|]; exact H.
      * rewrite (Hr0 r Hr) in *. rewrite to_Z_0 in Hk. rewrite Hg.
        left. f_equal. apply to_Z_inj. lia.
  - rewrite Nat2Z.inj_succ in Hn.
    pose proof (to_Z_bounded sh) as Hsh.
    pose proof (to_Z_bounded p) as Hpb.
    assert (HX : (0 < 2 ^ to_Z sh)%Z) by (apply Z.pow_pos_nonneg; lia).
    assert (HXn : (2 ^ Z.of_nat (S n) * 2 ^ to_Z sh = 2 ^ 63)%Z).
    { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    destruct t as [|k0 v0|l r]; cbn [ielements_aux].
    + split; [intros H; left; exact H|].
      intros [H|(r & _ & _ & Hg)]; [exact H|discriminate].
    + (* [comment removed for export] *)
      assert (Hcond : (((k0 << sh) >> sh) =? k0) = true <->
                      (to_Z k0 < 2 ^ Z.of_nat (S n))%Z).
      { pose proof (to_Z_bounded k0) as Hk0.
        rewrite eqb_spec. split.
        - intros H. apply (f_equal to_Z) in H.
          rewrite lsr_spec, lsl_spec, wB_eq, lsl_lsr_mod in H by lia.
          replace (63 - to_Z sh)%Z with (Z.of_nat (S n)) in H by lia.
          rewrite <- H. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
        - intros H. apply to_Z_inj.
          rewrite lsr_spec, lsl_spec, wB_eq, lsl_lsr_mod by lia.
          replace (63 - to_Z sh)%Z with (Z.of_nat (S n)) by lia.
          apply Z.mod_small. lia. }
      destruct (((k0 << sh) >> sh) =? k0) eqn:Ec.
      * assert (Hk0 : (to_Z k0 < 2 ^ Z.of_nat (S n))%Z) by (apply Hcond; reflexivity).
        pose proof (to_Z_bounded k0) as Hk0b.
        assert (Hkey : (to_Z (p + (k0 << sh)) = to_Z p + to_Z k0 * 2 ^ to_Z sh)%Z).
        { rewrite add_spec, lsl_spec, wB_eq.
          rewrite (Z.mod_small (to_Z k0 * 2 ^ to_Z sh)) by nia.
          apply Z.mod_small. nia. }
        cbn [In]. split.
        -- intros [H|H]; [|left; exact H]. inversion H; subst. right.
           exists k0. split; [exact Hk0|]. split; [exact Hkey|].
           cbn [iget]. rewrite Uint63.eqb_refl. reflexivity.
        -- intros [H|(r & Hr & Hk & Hg)]; [right; exact H|].
           cbn [iget] in Hg. destruct (eqbP r k0) as [E|E]; [|discriminate].
           apply to_Z_inj in E. subst r. inversion Hg; subst. left.
           f_equal. apply to_Z_inj. lia.
      * split; [intros H; left; exact H|].
        intros [H|(r & Hr & Hk & Hg)]; [exact H|]. exfalso.
        cbn [iget] in Hg. destruct (eqbP r k0) as [E|E]; [|discriminate].
        apply to_Z_inj in E. subst r.
        apply Hcond in Hr. discriminate.
    + (* [comment removed for export] *)
      assert (Hsh1 : to_Z (sh + 1) = (to_Z sh + 1)%Z).
      { rewrite add_spec, to_Z_1, wB_eq. apply Z.mod_small. lia. }
      assert (HX1 : (2 ^ to_Z (sh + 1) = 2 * 2 ^ to_Z sh)%Z).
      { rewrite Hsh1, Z.pow_add_r by lia. change (2 ^ 1)%Z with 2%Z. lia. }
      assert (HXlt : (2 * 2 ^ to_Z sh <= 2 ^ 63)%Z).
      { rewrite <- HXn. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
        assert (0 < 2 ^ Z.of_nat n)%Z by (apply Z.pow_pos_nonneg; lia). nia. }
      assert (Hp' : to_Z (p + (1 << sh)) = (to_Z p + 2 ^ to_Z sh)%Z).
      { rewrite add_spec, lsl_spec, to_Z_1, wB_eq, Z.mul_1_l.
        rewrite (Z.mod_small (2 ^ to_Z sh)) by lia.
        apply Z.mod_small. lia. }
      assert (Hn2 : (2 ^ Z.of_nat (S n) = 2 * 2 ^ Z.of_nat n)%Z).
      { rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. reflexivity. }
      assert (HYpos : (0 < 2 ^ Z.of_nat n)%Z) by (apply Z.pow_pos_nonneg; lia).
      assert (HY : (2 ^ Z.of_nat n <= 2 ^ 62)%Z).
      { apply Z.pow_le_mono_r; lia. }
      rewrite IH by lia. rewrite IH by lia.
      rewrite HX1, Hp'.
      split.
      * intros [[H|(r2 & Hr2 & Hk & Hg)]|(r1 & Hr1 & Hk & Hg)].
        -- left; exact H.
        -- right. exists ((r2 << 1) + 1).
           pose proof (to_Z_bounded r2) as Hr2b.
           assert (E : to_Z ((r2 << 1) + 1) = (2 * to_Z r2 + 1)%Z).
           { rewrite add_spec, lsl_spec, to_Z_1, wB_eq.
             change (2 ^ 1)%Z with 2%Z.
             rewrite (Z.mod_small (to_Z r2 * 2)) by lia.
             rewrite Z.mod_small by lia. lia. }
           split; [lia|]. split; [rewrite E; lia|].
           cbn [iget]. rewrite ieven_spec, E.
           replace ((2 * to_Z r2 + 1) mod 2)%Z with 1%Z
             by (rewrite Z.add_comm, Z.mul_comm, Z.mod_add by lia; reflexivity).
           cbn. rewrite <- Hg. f_equal. apply to_Z_inj.
           rewrite to_Z_lsr1, E.
           rewrite Z.add_comm, Z.mul_comm, Z.div_add by lia. reflexivity.
        -- right. exists (r1 << 1).
           pose proof (to_Z_bounded r1) as Hr1b.
           assert (E : to_Z (r1 << 1) = (2 * to_Z r1)%Z).
           { rewrite lsl_spec, to_Z_1, wB_eq.
             change (2 ^ 1)%Z with 2%Z.
             rewrite Z.mod_small by lia. lia. }
           split; [lia|]. split; [rewrite E; lia|].
           cbn [iget]. rewrite ieven_spec, E.
           replace ((2 * to_Z r1) mod 2)%Z with 0%Z
             by (rewrite Z.mul_comm, Z.mod_mul by lia; reflexivity).
           cbn. rewrite <- Hg. f_equal. apply to_Z_inj.
           rewrite to_Z_lsr1, E.
           rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
      * intros [H|(r0 & Hr0 & Hk & Hg)]; [left; left; exact H|].
        cbn [iget] in Hg. rewrite ieven_spec in Hg.
        pose proof (to_Z_bounded r0) as Hr0b.
        pose proof (Z.div_mod (to_Z r0) 2 ltac:(lia)) as Hdm.
        pose proof (Z.mod_pos_bound (to_Z r0) 2 ltac:(lia)) as Hmb.
        destruct (Z.eqb_spec (to_Z r0 mod 2) 0) as [E|E].
        -- right. exists (r0 >> 1). rewrite to_Z_lsr1.
           split; [lia|]. split; [|exact Hg]. nia.
        -- left. right. exists (r0 >> 1). rewrite to_Z_lsr1.
           split; [lia|]. split; [|exact Hg]. nia.
Qed.

Lemma ielements_spec {A} (t : itrie A) k v :
  In (k, v) (ielements t) <-> iget k t = Some v.
Proof.
  unfold ielements. rewrite ielements_aux_spec.
  - split.
    + intros [[]|(r & _ & Hk & Hg)].
      rewrite to_Z_0, Z.pow_0_r, Z.mul_1_r, Z.add_0_l in Hk.
      apply to_Z_inj in Hk. subst. exact Hg.
    + intros H. right. exists k. split; [apply to_Z_lt_fuel|].
      split; [|exact H]. rewrite to_Z_0. cbn. lia.
  - rewrite to_Z_0. reflexivity.
  - rewrite to_Z_0. cbn. lia.
Qed.

(* [comment removed for export] *)

Definition inblock (n : nat) (sh p k : int) : Prop :=
  exists r : Z, (0 <= r < 2 ^ Z.of_nat n)%Z /\
                (to_Z k = to_Z p + r * 2 ^ to_Z sh)%Z.

Lemma ielements_aux_keys {A} n sh p (t : itrie A) acc k :
  (Z.of_nat n + to_Z sh = 63)%Z -> (to_Z p < 2 ^ to_Z sh)%Z ->
  In k (map fst (ielements_aux n sh p t acc)) ->
  In k (map fst acc) \/ inblock n sh p k.
Proof.
  intros Hn Hp H. apply in_map_iff in H. destruct H as ([k' v] & Hk & Hin).
  cbn in Hk. subst k'. apply ielements_aux_spec in Hin; try assumption.
  destruct Hin as [Hin|(r & Hr & Hk & _)].
  - left. apply in_map_iff. exists (k, v). split; [reflexivity|exact Hin].
  - right. exists (to_Z r). pose proof (to_Z_bounded r). split; [lia|exact Hk].
Qed.

Lemma ielements_aux_nodup {A} : forall n sh p (t : itrie A) acc,
  (Z.of_nat n + to_Z sh = 63)%Z -> (to_Z p < 2 ^ to_Z sh)%Z ->
  NoDup (map fst acc) ->
  (forall k, In k (map fst acc) -> ~ inblock n sh p k) ->
  NoDup (map fst (ielements_aux n sh p t acc)).
Proof.
  induction n as [|n IH]; intros sh p t acc Hn Hp Hnd Hdisj.
  - cbn [ielements_aux]. destruct (iget 0 t); [|exact Hnd].
    cbn [map fst]. constructor; [|exact Hnd].
    intros Hin. apply (Hdisj p Hin). exists 0%Z.
    change (2 ^ Z.of_nat 0)%Z with 1%Z. split; lia.
  - rewrite Nat2Z.inj_succ in Hn.
    pose proof (to_Z_bounded sh) as Hsh.
    pose proof (to_Z_bounded p) as Hpb.
    assert (HX : (0 < 2 ^ to_Z sh)%Z) by (apply Z.pow_pos_nonneg; lia).
    assert (HXn : (2 ^ Z.of_nat (S n) * 2 ^ to_Z sh = 2 ^ 63)%Z).
    { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    destruct t as [|k0 v0|l r]; cbn [ielements_aux].
    + exact Hnd.
    + destruct (((k0 << sh) >> sh) =? k0) eqn:Ec; [|exact Hnd].
      cbn [map fst]. constructor; [|exact Hnd].
      intros Hin. apply (Hdisj _ Hin).
      pose proof (to_Z_bounded k0) as Hk0b.
      assert (Hk0 : (to_Z k0 < 2 ^ Z.of_nat (S n))%Z).
      { apply eqb_spec in Ec. apply (f_equal to_Z) in Ec.
        rewrite lsr_spec, lsl_spec, wB_eq, lsl_lsr_mod in Ec by lia.
        replace (63 - to_Z sh)%Z with (Z.of_nat (S n)) in Ec by lia.
        rewrite <- Ec. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. }
      exists (to_Z k0). split; [lia|].
      rewrite add_spec, lsl_spec, wB_eq.
      rewrite (Z.mod_small (to_Z k0 * 2 ^ to_Z sh)) by nia.
      apply Z.mod_small. nia.
    + assert (Hsh1 : to_Z (sh + 1) = (to_Z sh + 1)%Z).
      { rewrite add_spec, to_Z_1, wB_eq. apply Z.mod_small. lia. }
      assert (HX1 : (2 ^ to_Z (sh + 1) = 2 * 2 ^ to_Z sh)%Z).
      { rewrite Hsh1, Z.pow_add_r by lia. change (2 ^ 1)%Z with 2%Z. lia. }
      assert (Hn2 : (2 ^ Z.of_nat (S n) = 2 * 2 ^ Z.of_nat n)%Z).
      { rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. reflexivity. }
      assert (HYpos : (0 < 2 ^ Z.of_nat n)%Z) by (apply Z.pow_pos_nonneg; lia).
      assert (HXlt : (2 * 2 ^ to_Z sh <= 2 ^ 63)%Z) by nia.
      assert (Hp' : to_Z (p + (1 << sh)) = (to_Z p + 2 ^ to_Z sh)%Z).
      { rewrite add_spec, lsl_spec, to_Z_1, wB_eq, Z.mul_1_l.
        rewrite (Z.mod_small (2 ^ to_Z sh)) by lia.
        apply Z.mod_small. lia. }
      apply IH; try lia.
      * apply IH; try lia; [exact Hnd|].
        intros k Hin (r2 & Hr2 & Hk). apply (Hdisj k Hin).
        exists (2 * r2 + 1)%Z. split; [lia|]. rewrite Hk, Hp', HX1. ring.
      * intros k Hin (r1 & Hr1 & Hk).
        apply ielements_aux_keys in Hin; try lia.
        destruct Hin as [Hin|(r2 & Hr2 & Hk2)].
        -- apply (Hdisj k Hin). exists (2 * r1)%Z. split; [lia|].
           rewrite Hk, HX1. ring.
        -- rewrite Hk2, Hp', HX1 in Hk.
           assert ((1 + 2 * r2 - 2 * r1) * 2 ^ to_Z sh = 0)%Z by lia.
           assert (1 + 2 * r2 - 2 * r1 = 0)%Z by nia. lia.
Qed.

Lemma ielements_nodup {A} (t : itrie A) : NoDup (map fst (ielements t)).
Proof.
  unfold ielements. apply ielements_aux_nodup.
  - rewrite to_Z_0. reflexivity.
  - rewrite to_Z_0. cbn. lia.
  - constructor.
  - intros k [].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ifold {A B} (f : int -> A -> B -> B) (t : itrie A) (b : B) : B :=
  fold_right (fun kv acc => f (fst kv) (snd kv) acc) b (ielements t).

Lemma ifold_spec {A B} (f : int -> A -> B -> B) (t : itrie A) (b : B) :
  ifold f t b =
  fold_right (fun kv acc => f (fst kv) (snd kv) acc) b (ielements t).
Proof. reflexivity. Qed.

Definition iall {A} (f : int -> A -> bool) (t : itrie A) : bool :=
  forallb (fun kv => f (fst kv) (snd kv)) (ielements t).

Lemma iall_spec {A} (f : int -> A -> bool) (t : itrie A) :
  iall f t = true <-> (forall k v, iget k t = Some v -> f k v = true).
Proof.
  unfold iall. rewrite forallb_forall. split.
  - intros H k v Hg. apply (H (k, v)). apply (proj2 (ielements_spec t k v)). exact Hg.
  - intros H [k v] Hin. cbn [fst snd]. apply H. apply (proj1 (ielements_spec t k v)). exact Hin.
Qed.

Definition iexists {A} (f : int -> A -> bool) (t : itrie A) : bool :=
  existsb (fun kv => f (fst kv) (snd kv)) (ielements t).

Lemma iexists_spec {A} (f : int -> A -> bool) (t : itrie A) :
  iexists f t = true <-> (exists k v, iget k t = Some v /\ f k v = true).
Proof.
  unfold iexists. rewrite existsb_exists. split.
  - intros ([k v] & Hin & Hf). exists k, v. split; [|exact Hf].
    apply (proj1 (ielements_spec t k v)). exact Hin.
  - intros (k & v & Hg & Hf). exists (k, v). split; [|exact Hf].
    apply (proj2 (ielements_spec t k v)). exact Hg.
Qed.

(* [comment removed for export] *)
Definition iof_list {A} (l : list (int * A)) : itrie A :=
  fold_left (fun t kv => iset (fst kv) (snd kv) t) l IEmpty.

Lemma iget_fold_iset {A} : forall (l : list (int * A)) (t : itrie A) k,
  iget k (fold_left (fun t kv => iset (fst kv) (snd kv) t) l t) =
  match find (fun kv => k =? fst kv) (rev l) with
  | Some kv => Some (snd kv)
  | None => iget k t
  end.
Proof.
  induction l as [|[k0 v0] l IH]; intros t k; cbn [fold_left rev].
  - reflexivity.
  - rewrite IH. cbn [fst snd].
    assert (Hfind : forall l1 l2 : list (int * A),
      find (fun kv => k =? fst kv) (l1 ++ l2) =
      match find (fun kv => k =? fst kv) l1 with
      | Some x => Some x
      | None => find (fun kv => k =? fst kv) l2
      end).
    { induction l1 as [|x l1 IH1]; intros l2; cbn; [reflexivity|].
      destruct (k =? fst x); [reflexivity|apply IH1]. }
    rewrite Hfind. destruct (find _ (rev l)); [reflexivity|].
    cbn [find fst snd]. rewrite iget_iset. destruct (k =? k0); reflexivity.
Qed.

Lemma iget_iof_list {A} (l : list (int * A)) k :
  iget k (iof_list l) =
  match find (fun kv => k =? fst kv) (rev l) with
  | Some kv => Some (snd kv)
  | None => None
  end.
Proof. unfold iof_list. rewrite iget_fold_iset. reflexivity. Qed.

#[global] Opaque ielements ifold iall iexists.

(* [comment removed for export] *)
(* [comment removed for export] *)

Module ITrieTests.
  Definition t0 : itrie int :=
    iset 0 100 (iset 1 101 (iset 0x4000000000000000 102
      (iset 0x7FFFFFFFFFFFFFFF 103 (iset 5 104 (iset 13 105 IEmpty))))).

  Goal iget 0 t0 = Some 100. Proof. vm_compute. reflexivity. Qed.
  Goal iget 1 t0 = Some 101. Proof. vm_compute. reflexivity. Qed.
  Goal iget 0x4000000000000000 t0 = Some 102. Proof. vm_compute. reflexivity. Qed.
  Goal iget 0x7FFFFFFFFFFFFFFF t0 = Some 103. Proof. vm_compute. reflexivity. Qed.
  Goal iget 5 t0 = Some 104. Proof. vm_compute. reflexivity. Qed.
  Goal iget 13 t0 = Some 105. Proof. vm_compute. reflexivity. Qed.
  Goal iget 21 t0 = None. Proof. vm_compute. reflexivity. Qed.
  Goal iget 0x3FFFFFFFFFFFFFFF t0 = None. Proof. vm_compute. reflexivity. Qed.
  Goal iget 5 (iset 5 7 t0) = Some 7. Proof. vm_compute. reflexivity. Qed.
  Goal iget 5 (iremove 5 t0) = None. Proof. vm_compute. reflexivity. Qed.
  Goal iget 13 (iremove 5 t0) = Some 105. Proof. vm_compute. reflexivity. Qed.
  Goal iget 5 (iupd 5 (fun o => match o with Some v => v + 1 | None => 0 end) t0)
       = Some 105.
  Proof. vm_compute. reflexivity. Qed.
  Goal iget 6 (iupd 6 (fun o => match o with Some v => v + 1 | None => 0 end) t0)
       = Some 0.
  Proof. vm_compute. reflexivity. Qed.
  Goal length (ielements t0) = 6%nat. Proof. vm_compute. reflexivity. Qed.
  Goal ifold (fun k v acc => k + v + acc) t0 0
       = 0 + 100 + (1 + 101) + (0x4000000000000000 + 102)
         + (0x7FFFFFFFFFFFFFFF + 103) + (5 + 104) + (13 + 105).
  Proof. vm_compute. reflexivity. Qed.
  Goal iall (fun k v => 100 <=? v) t0 = true. Proof. vm_compute. reflexivity. Qed.
  Goal iexists (fun k v => (k =? 13) && (v =? 105)) t0 = true.
  Proof. vm_compute. reflexivity. Qed.
  Goal iget 2 (iof_list [(1, 10); (2, 20); (2, 21); (3, 30)]) = Some 21.
  Proof. vm_compute. reflexivity. Qed.
End ITrieTests.
