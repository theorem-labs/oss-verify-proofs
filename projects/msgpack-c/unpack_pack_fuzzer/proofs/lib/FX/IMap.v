(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith List Bool Lia Sorted.
From Stdlib Require Import PrimInt63 Uint63.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Module IMap.

Inductive t (A : Type) : Type :=
| Leaf
| Node (h : int) (l : t A) (k : int) (v : A) (r : t A).
Arguments Leaf {A}.
Arguments Node {A} h l k v r.

Section WithA.
Context {A : Type}.
Local Notation t := (t A).

Definition empty : t := Leaf.

Definition ht (m : t) : int := match m with Leaf => 0%uint63 | Node h _ _ _ _ => h end.

Definition mk (l : t) (k : int) (v : A) (r : t) : t :=
  let hl := ht l in let hr := ht r in
  Node (PrimInt63.add (if PrimInt63.ltb hl hr then hr else hl) 1%uint63) l k v r.

Definition bal (l : t) (k : int) (v : A) (r : t) : t :=
  let hl := ht l in let hr := ht r in
  if PrimInt63.ltb (PrimInt63.add hr 1%uint63) hl then
    match l with
    | Node _ ll lk lv lr =>
        if PrimInt63.ltb (ht ll) (ht lr) then
          match lr with
          | Node _ lrl lrk lrv lrr => mk (mk ll lk lv lrl) lrk lrv (mk lrr k v r)
          | Leaf => mk l k v r
          end
        else mk ll lk lv (mk lr k v r)
    | Leaf => mk l k v r
    end
  else if PrimInt63.ltb (PrimInt63.add hl 1%uint63) hr then
    match r with
    | Node _ rl rk rv rr =>
        if PrimInt63.ltb (ht rr) (ht rl) then
          match rl with
          | Node _ rll rlk rlv rlr => mk (mk l k v rll) rlk rlv (mk rlr rk rv rr)
          | Leaf => mk l k v r
          end
        else mk (mk l k v rl) rk rv rr
    | Leaf => mk l k v r
    end
  else mk l k v r.

Fixpoint add (k : int) (v : A) (m : t) : t :=
  match m with
  | Leaf => Node 1%uint63 Leaf k v Leaf
  | Node h l k' v' r =>
      if PrimInt63.ltb k k' then bal (add k v l) k' v' r
      else if PrimInt63.ltb k' k then bal l k' v' (add k v r)
      else Node h l k v r
  end.

Fixpoint find (k : int) (m : t) : option A :=
  match m with
  | Leaf => None
  | Node _ l k' v r =>
      if PrimInt63.ltb k k' then find k l
      else if PrimInt63.ltb k' k then find k r
      else Some v
  end.

Definition mem (k : int) (m : t) : bool :=
  match find k m with Some _ => true | None => false end.

Fixpoint remove_min (l : t) (k : int) (v : A) (r : t) : t * (int * A) :=
  match l with
  | Leaf => (r, (k, v))
  | Node _ ll lk lv lr => let '(l', m) := remove_min ll lk lv lr in (bal l' k v r, m)
  end.

Definition merge (l r : t) : t :=
  match l, r with
  | Leaf, _ => r
  | _, Leaf => l
  | _, Node _ rl rk rv rr => let '(r', m) := remove_min rl rk rv rr in bal l (fst m) (snd m) r'
  end.

Fixpoint remove (k : int) (m : t) : t :=
  match m with
  | Leaf => Leaf
  | Node _ l k' v r =>
      if PrimInt63.ltb k k' then bal (remove k l) k' v r
      else if PrimInt63.ltb k' k then bal l k' v (remove k r)
      else merge l r
  end.

Fixpoint fold {B : Type} (f : int -> A -> B -> B) (m : t) (acc : B) : B :=
  match m with
  | Leaf => acc
  | Node _ l k v r => fold f r (f k v (fold f l acc))
  end.

Fixpoint elements_aux (m : t) (acc : list (int * A)) : list (int * A) :=
  match m with
  | Leaf => acc
  | Node _ l k v r => elements_aux l ((k, v) :: elements_aux r acc)
  end.
Definition elements (m : t) : list (int * A) := elements_aux m [].

Fixpoint forallb (p : int -> A -> bool) (m : t) : bool :=
  match m with
  | Leaf => true
  | Node _ l k v r => p k v && forallb p l && forallb p r
  end.

Fixpoint cardinal (m : t) : nat :=
  match m with Leaf => O | Node _ l _ _ r => S (cardinal l + cardinal r) end.

Fixpoint find_range_aux (lo hi : int) (m : t) (acc : list (int * A)) : list (int * A) :=
  match m with
  | Leaf => acc
  | Node _ l k v r =>
      if PrimInt63.ltb k lo then find_range_aux lo hi r acc
      else if PrimInt63.leb hi k then find_range_aux lo hi l acc
      else find_range_aux lo hi l ((k, v) :: find_range_aux lo hi r acc)
  end.
Definition find_range (lo hi : int) (m : t) : list (int * A) := find_range_aux lo hi m [].

Fixpoint remove_range (lo hi : int) (m : t) : t :=
  match m with
  | Leaf => Leaf
  | Node _ l k v r =>
      if PrimInt63.ltb k lo then bal l k v (remove_range lo hi r)
      else if PrimInt63.leb hi k then bal (remove_range lo hi l) k v r
      else merge (remove_range lo hi l) (remove_range lo hi r)
  end.

End WithA.

Fixpoint map {A B : Type} (f : A -> B) (m : t A) : t B :=
  match m with
  | Leaf => Leaf
  | Node h l k v r => Node h (map f l) k (f v) (map f r)
  end.

Fixpoint keys_in {A} (p : int -> Prop) (m : t A) : Prop :=
  match m with
  | Leaf => True
  | Node _ l k _ r => p k /\ keys_in p l /\ keys_in p r
  end.
Fixpoint bst {A} (m : t A) : Prop :=
  match m with
  | Leaf => True
  | Node _ l k _ r =>
      keys_in (fun k' => to_Z k' < to_Z k) l /\ keys_in (fun k' => to_Z k < to_Z k') r /\ bst l /\ bst r
  end.

Section Theory.
Context {A : Type}.
Implicit Types (m l r : t A) (k x : int) (v w : A).

Fixpoint inb (x : int) (w : A) (m : t A) : Prop :=
  match m with
  | Leaf => False
  | Node _ l k v r => inb x w l \/ (k = x /\ v = w) \/ inb x w r
  end.

Lemma keys_in_inb : forall (p : int -> Prop) m x w, keys_in p m -> inb x w m -> p x.
Proof.
  induction m as [|h l IHl k v r IHr]; cbn -[to_Z elements]; intros x w Hk Hi; [tauto|].
  destruct Hk as (Pk & Kl & Kr). destruct Hi as [Hi|[[<- _]|Hi]]; eauto.
Qed.

Lemma keys_in_mono : forall (p q : int -> Prop) m, (forall k, p k -> q k) -> keys_in p m -> keys_in q m.
Proof. induction m; cbn -[to_Z elements]; intuition. Qed.

Lemma option_ext : forall (o1 o2 : option A), (forall w, o1 = Some w <-> o2 = Some w) -> o1 = o2.
Proof.
  intros [a|] [b|] H; try reflexivity.
  - f_equal. apply (proj1 (H a)) in H || idtac. assert (Some b = Some a) by (apply H; reflexivity). congruence.
  - symmetry. apply H. reflexivity.
  - apply H. reflexivity.
Qed.

Lemma find_inb : forall x w m, bst m -> (find x m = Some w <-> inb x w m).
Proof.
  induction m as [|h l IHl k v r IHr]; cbn -[to_Z elements].
  - split; [discriminate|tauto].
  - intros (Kl & Kr & Bl & Br). destruct (ltbP x k) as [L|L].
    + rewrite IHl by assumption. split; [tauto|].
      intros [H|[[E _]|H]]; [assumption| subst; exfalso; exact (Z.lt_irrefl _ L) |].
      exfalso. pose proof (keys_in_inb _ _ _ _ Kr H) as P. cbn -[to_Z elements] in P. exact (Z.lt_asymm _ _ L P).
    + destruct (ltbP k x) as [L'|L'].
      * rewrite IHr by assumption. split; [tauto|].
        intros [H|[[E _]|H]]; [| subst; exfalso; exact (Z.lt_irrefl _ L') | assumption].
        exfalso. pose proof (keys_in_inb _ _ _ _ Kl H) as P. cbn -[to_Z elements] in P. exact (Z.lt_asymm _ _ L' P).
      * assert (E : k = x) by (apply to_Z_inj; apply Z.le_antisymm; apply Z.nlt_ge; assumption).
        subst k. split.
        -- intros E. injection E as ->. tauto.
        -- intros [H|[[_ ->]|H]]; [| reflexivity |]; exfalso.
           ++ pose proof (keys_in_inb _ _ _ _ Kl H) as P. cbn -[to_Z elements] in P. exact (Z.lt_irrefl _ P).
           ++ pose proof (keys_in_inb _ _ _ _ Kr H) as P. cbn -[to_Z elements] in P. exact (Z.lt_irrefl _ P).
Qed.

Lemma find_none_inb : forall x m, bst m -> (find x m = None <-> forall w, ~ inb x w m).
Proof.
  intros x m B. split.
  - intros E w H. apply (find_inb x w m B) in H. congruence.
  - intros H. destruct (find x m) eqn:E; [|reflexivity]. exfalso. apply (H a). apply find_inb; assumption.
Qed.

Lemma find_ext : forall x m1 m2, bst m1 -> bst m2 ->
  (forall w, inb x w m1 <-> inb x w m2) -> find x m1 = find x m2.
Proof.
  intros x m1 m2 B1 B2 H. apply option_ext. intros w. rewrite !find_inb by assumption. apply H.
Qed.

Lemma elements_aux_in : forall m acc kv,
  In kv (elements_aux m acc) <-> (inb (fst kv) (snd kv) m \/ In kv acc).
Proof.
  induction m as [|h l IHl k v r IHr]; cbn -[to_Z elements]; intros acc kv; [tauto|].
  rewrite IHl. cbn -[to_Z elements]. rewrite IHr. destruct kv as [x w]; cbn -[to_Z elements].
  split.
  - intros [H|[E|[H|H]]]; [tauto| injection E as -> ->; tauto |tauto|tauto].
  - intros [[H|[[-> ->]|H]]|H]; tauto.
Qed.

Lemma elements_in : forall m x w, In (x, w) (elements m) <-> inb x w m.
Proof. intros. unfold elements. rewrite elements_aux_in. cbn -[to_Z elements]. tauto. Qed.

Lemma elements_aux_app : forall m acc, elements_aux m acc = elements_aux m [] ++ acc.
Proof.
  induction m as [|h l IHl k v r IHr]; cbn -[to_Z elements]; intros acc; [reflexivity|].
  rewrite (IHl ((k, v) :: elements_aux r acc)), (IHl ((k, v) :: elements_aux r [])), (IHr acc), <- app_assoc.
  reflexivity.
Qed.

Lemma elements_node : forall h l k v r,
  elements (Node h l k v r) = elements l ++ (k, v) :: elements r.
Proof. intros. unfold elements. cbn -[to_Z elements]. rewrite elements_aux_app. reflexivity. Qed.

Lemma fold_elements : forall {B} (f : int -> A -> B -> B) m (b : B),
  fold f m b = List.fold_left (fun acc kv => f (fst kv) (snd kv) acc) (elements m) b.
Proof.
  induction m as [|h l IHl k v r IHr]; intros b; [reflexivity|].
  rewrite elements_node, fold_left_app. cbn [fold fold_left fst snd]. rewrite IHr, IHl. reflexivity.
Qed.

Lemma elements_aux_keys : forall (p : int -> Prop) m acc,
  keys_in p m -> Forall (fun kv => p (fst kv)) acc -> Forall (fun kv => p (fst kv)) (elements_aux m acc).
Proof.
  induction m as [|h l IHl k v r IHr]; cbn -[to_Z elements]; intros acc Hm Hacc; [exact Hacc|].
  destruct Hm as (Pk & Pl & Pr). apply IHl; [exact Pl|]. constructor; [exact Pk|]. apply IHr; assumption.
Qed.

Lemma elements_aux_sorted : forall m acc, bst m ->
  Sorted.StronglySorted (fun a b => to_Z (fst a) < to_Z (fst b)) acc ->
  keys_in (fun k => Forall (fun kv => to_Z k < to_Z (fst kv)) acc) m ->
  Sorted.StronglySorted (fun a b => to_Z (fst a) < to_Z (fst b)) (elements_aux m acc).
Proof.
  induction m as [|h l IHl k v r IHr]; cbn -[to_Z elements]; intros acc Bm Sacc Hacc; [exact Sacc|].
  destruct Bm as (Kl & Kr & Bl & Br). destruct Hacc as (Ak & Al & Ar).
  apply IHl; [exact Bl| |].
  - constructor.
    + apply IHr; assumption.
    + apply (elements_aux_keys (fun x => to_Z k < to_Z x)); assumption.
  -
    clear IHl IHr.
    induction l as [|lh ll IHll lk lv lr IHlr]; cbn -[to_Z elements]; [exact I|].
    cbn -[to_Z elements] in Kl, Bl, Al. destruct Kl as (K1 & K2 & K3). destruct Al as (A1 & A2 & A3). destruct Bl as (B1 & B2 & B3 & B4).
    split; [|split; [apply IHll; assumption| apply IHlr; assumption]].
    constructor; [cbn -[to_Z elements]; exact K1|].
    apply (elements_aux_keys (fun x => to_Z lk < to_Z x)).
    + refine (keys_in_mono _ _ _ _ Kr). cbn -[to_Z elements]. intros; lia.
    + eapply Forall_impl; [|exact Ak]. cbn -[to_Z elements]. intros; lia.
Qed.

Lemma elements_sorted : forall m, bst m ->
  Sorted.StronglySorted (fun a b => to_Z (fst a) < to_Z (fst b)) (elements m).
Proof.
  intros m B. unfold elements. apply elements_aux_sorted; [exact B|constructor|].
  clear B. induction m; cbn -[to_Z elements]; auto.
Qed.

Lemma keys_in_iff : forall (p : int -> Prop) m, keys_in p m <-> (forall x w, inb x w m -> p x).
Proof.
  induction m as [|h l IHl k v r IHr]; cbn -[to_Z elements].
  - split; [intros _ x w F; destruct F| intros; exact I].
  - rewrite IHl, IHr. split.
    + intros (Pk & Pl & Pr) x w [H|[[<- _]|H]]; eauto.
    + intros H. split; [|split]; intros; eapply H; eauto.
Qed.

Lemma keys_in_forall : forall (p : int -> Prop) m, keys_in p m <-> Forall (fun kv => p (fst kv)) (elements m).
Proof.
  intros p m. rewrite keys_in_iff, Forall_forall. split.
  - intros H [x w] I. cbn -[to_Z elements]. apply elements_in in I. eauto.
  - intros H x w I. apply (H (x, w)). apply elements_in. exact I.
Qed.

Lemma sorted_app_inv : forall {T} (R : T -> T -> Prop) (xs ys : list T),
  StronglySorted R (xs ++ ys) ->
  StronglySorted R xs /\ StronglySorted R ys /\ (forall a b, In a xs -> In b ys -> R a b).
Proof.
  intros T R xs ys. induction xs as [|x xs IH]; cbn -[to_Z elements]; intros S.
  - split; [constructor|]. split; [exact S|]. intros a b F; destruct F.
  - inversion S as [|x' l' S1 F1]; subst.
    destruct (IH S1) as (Sx & Sy & Hr). apply Forall_app in F1. destruct F1 as [Fx Fy].
    split; [constructor; assumption|]. split; [exact Sy|].
    intros a b [<-|Ia] Ib.
    + exact (proj1 (Forall_forall _ _) Fy b Ib).
    + apply Hr; assumption.
Qed.

Lemma bst_of_sorted : forall m,
  StronglySorted (fun a b => to_Z (fst a) < to_Z (fst b)) (elements m) -> bst m.
Proof.
  induction m as [|h l IHl k v r IHr]; cbn -[to_Z elements]; intros S; [exact I|].
  rewrite elements_node in S.
  destruct (sorted_app_inv _ _ _ S) as (Sl & Skr & Hlr).
  inversion Skr as [|x' l' Sr Fr]; subst.
  split; [|split; [|split; [apply IHl, Sl| apply IHr, Sr]]].
  - apply keys_in_forall. apply Forall_forall. intros [x w] I. exact (Hlr _ _ I (or_introl eq_refl)).
  - apply keys_in_forall. exact Fr.
Qed.

Lemma bst_iff_sorted : forall m,
  bst m <-> StronglySorted (fun a b => to_Z (fst a) < to_Z (fst b)) (elements m).
Proof. intros m; split; [apply elements_sorted | apply bst_of_sorted]. Qed.

Local Ltac bal_cases :=
  unfold bal, mk;
  repeat match goal with
    | |- context [if ?c then _ else _] => destruct c
    | |- context [match ?m with Leaf => _ | Node _ _ _ _ _ => _ end] => destruct m
    end.

Lemma bal_elements : forall l k v r, elements (bal l k v r) = elements l ++ (k, v) :: elements r.
Proof.
  intros. bal_cases; rewrite !elements_node; cbn -[to_Z elements]; repeat (rewrite <- !app_assoc; cbn -[to_Z elements]); reflexivity.
Qed.

Lemma bal_inb : forall l k v r x w,
  inb x w (bal l k v r) <-> (inb x w l \/ (k = x /\ v = w) \/ inb x w r).
Proof.
  intros. rewrite <- !elements_in, bal_elements, in_app_iff. cbn -[to_Z elements].
  assert ((k, v) = (x, w) <-> (k = x /\ v = w)).
  { split; [intros E; injection E; auto| intros [-> ->]; reflexivity]. }
  tauto.
Qed.

Lemma bal_keys : forall (p : int -> Prop) l k v r,
  keys_in p (bal l k v r) <-> (p k /\ keys_in p l /\ keys_in p r).
Proof.
  intros. rewrite !keys_in_forall, bal_elements, Forall_app. cbn -[to_Z elements].
  rewrite Forall_cons_iff. cbn -[to_Z elements]. tauto.
Qed.

Lemma bal_bst : forall l k v r,
  bst l -> bst r -> keys_in (fun x => to_Z x < to_Z k) l -> keys_in (fun x => to_Z k < to_Z x) r ->
  bst (bal l k v r).
Proof.
  intros l k v r Bl Br Kl Kr. apply bst_of_sorted. rewrite bal_elements, <- (elements_node 1%uint63).
  apply (elements_sorted (Node 1%uint63 l k v r)). cbn -[to_Z elements]. auto.
Qed.

Lemma add_keys : forall (p : int -> Prop) k v m, keys_in p (add k v m) <-> (p k /\ keys_in p m).
Proof.
  induction m as [|h l IHl k' v' r IHr]; cbn -[to_Z elements]; [tauto|].
  destruct (ltbP k k'); [rewrite bal_keys, IHl; tauto|].
  destruct (ltbP k' k); [rewrite bal_keys, IHr; tauto|].
  cbn -[to_Z elements]. assert (k' = k); [|subst; tauto].
  apply to_Z_inj. apply Z.le_antisymm; apply Z.nlt_ge; assumption.
Qed.

Lemma add_bst : forall k v m, bst m -> bst (add k v m).
Proof.
  induction m as [|h l IHl k' v' r IHr]; cbn -[to_Z elements]; [repeat split; exact I|].
  intros (Kl & Kr & Bl & Br).
  destruct (ltbP k k') as [L|L].
  - apply bal_bst; auto. apply add_keys. cbn -[to_Z elements]. auto.
  - destruct (ltbP k' k) as [L'|L'].
    + apply bal_bst; auto. apply add_keys. cbn -[to_Z elements]. auto.
    + assert (k' = k) as -> by (apply to_Z_inj; apply Z.le_antisymm; apply Z.nlt_ge; assumption).
      cbn -[to_Z elements]. auto.
Qed.

Lemma add_inb : forall k v m x w, bst m ->
  (inb x w (add k v m) <-> ((k = x /\ v = w) \/ (to_Z x <> to_Z k /\ inb x w m))).
Proof.
  intros k v m; induction m as [|h l IHl k' v' r IHr]; intros x w; cbn -[to_Z elements].
  - intros _. split; [|intuition]. intros [F|[E|F]]; [destruct F|left; exact E|destruct F].
  - intros (Kl & Kr & Bl & Br).
    destruct (ltbP k k') as [L|L].
    + rewrite bal_inb, IHl by assumption. split.
      * intros [[E|[N H]]|[[<- E]|H]]; [tauto|tauto| right; split; [lia|tauto] |].
        right. split; [|tauto]. pose proof (keys_in_inb _ _ _ _ Kr H). cbn -[to_Z elements] in *. lia.
      * intros [E|[N [H|[E|H]]]]; tauto.
    + destruct (ltbP k' k) as [L'|L'].
      * rewrite bal_inb, IHr by assumption. split.
        -- intros [H|[[<- E]|[E|[N H]]]]; [| right; split; [lia|tauto] | tauto | tauto].
           right. split; [|tauto]. pose proof (keys_in_inb _ _ _ _ Kl H). cbn -[to_Z elements] in *. lia.
        -- intros [E|[N [H|[E|H]]]]; tauto.
      * assert (k' = k) as -> by (apply to_Z_inj; apply Z.le_antisymm; apply Z.nlt_ge; assumption).
        cbn -[to_Z elements]. split.
        -- intros [H|[E|H]]; [| tauto |].
           ++ right. split; [|tauto]. pose proof (keys_in_inb _ _ _ _ Kl H). cbn -[to_Z elements] in *. lia.
           ++ right. split; [|tauto]. pose proof (keys_in_inb _ _ _ _ Kr H). cbn -[to_Z elements] in *. lia.
        -- intros [E|[N [H|[[E _]|H]]]]; [tauto|tauto| subst; lia |tauto].
Qed.

Lemma remove_min_spec : forall l k v r,
  let res := remove_min l k v r in
  (forall x w, (inb x w l \/ (k = x /\ v = w) \/ inb x w r) <-> (inb x w (fst res) \/ (fst (snd res) = x /\ snd (snd res) = w)))
  /\ (forall p : int -> Prop, p k -> keys_in p l -> keys_in p r -> keys_in p (fst res) /\ p (fst (snd res)))
  /\ (bst l -> bst r -> keys_in (fun x => to_Z x < to_Z k) l -> keys_in (fun x => to_Z k < to_Z x) r ->
      bst (fst res) /\ keys_in (fun x => to_Z (fst (snd res)) < to_Z x) (fst res)).
Proof.
  induction l as [|h ll IHl lk lv lr _]; intros k v r; cbn -[to_Z elements].
  - repeat split; try tauto.
  - specialize (IHl lk lv lr). destruct (remove_min ll lk lv lr) as [l' [mk' mv]]. cbn -[to_Z elements] in *.
    destruct IHl as (IH1 & IH2 & IH3).
    split; [|split].
    + intros x w. rewrite bal_inb. specialize (IH1 x w). tauto.
    + intros p Pk (Plk & Pll & Plr) Pr. destruct (IH2 p Plk Pll Plr) as [P1 P2].
      rewrite bal_keys. tauto.
    + intros (Kll & Klr & Bll & Blr) Br (Lk & Ll & Lr) Rk.
      destruct (IH3 Bll Blr Kll Klr) as [B' M'].
      destruct (IH2 (fun x => to_Z x < to_Z k) Lk Ll Lr) as [K' Mk]. cbn -[to_Z elements] in Mk.
      split.
      * apply bal_bst; assumption.
      * rewrite bal_keys. split; [exact Mk|]. split; [exact M'|].
        refine (keys_in_mono _ _ _ _ Rk). cbn -[to_Z elements]. intros; lia.
Qed.

Lemma merge_inb : forall l r x w, inb x w (merge l r) <-> (inb x w l \/ inb x w r).
Proof.
  intros l r x w. unfold merge. destruct l as [|lh ll lk lv lr]; [cbn -[to_Z elements]; tauto|].
  destruct r as [|rh rl rk rv rr]; [cbn -[to_Z elements]; tauto|].
  pose proof (proj1 (remove_min_spec rl rk rv rr)) as IH1.
  destruct (remove_min rl rk rv rr) as [r' [mk' mv]]. cbn [fst snd] in *.
  rewrite bal_inb. specialize (IH1 x w). cbn -[to_Z elements]. tauto.
Qed.

Lemma merge_keys : forall (p : int -> Prop) l r, keys_in p l -> keys_in p r -> keys_in p (merge l r).
Proof.
  intros p l r Hl Hr. unfold merge. destruct l as [|lh ll lk lv lr]; [exact Hr|].
  destruct r as [|rh rl rk rv rr]; [exact Hl|].
  pose proof (proj1 (proj2 (remove_min_spec rl rk rv rr))) as IH2.
  destruct (remove_min rl rk rv rr) as [r' [mk' mv]]. cbn [fst snd] in *.
  destruct Hr as (Pk & Pl & Pr). destruct (IH2 p Pk Pl Pr) as [K1 K2].
  rewrite bal_keys. cbn -[to_Z elements] in *. tauto.
Qed.

Lemma merge_bst : forall l r k, bst l -> bst r ->
  keys_in (fun x => to_Z x < to_Z k) l -> keys_in (fun x => to_Z k < to_Z x) r -> bst (merge l r).
Proof.
  intros l r k Bl Br Kl Kr. unfold merge. destruct l as [|lh ll lk lv lr]; [exact Br|].
  destruct r as [|rh rl rk rv rr]; [exact Bl|].
  pose proof (proj2 (remove_min_spec rl rk rv rr)) as [IH2 IH3].
  destruct (remove_min rl rk rv rr) as [r' [mk' mv]]. cbn [fst snd] in *.
  destruct Br as (Krl & Krr & Brl & Brr). destruct Kr as (Lk & Ll & Lr).
  destruct (IH3 Brl Brr Krl Krr) as [B' M'].
  destruct (IH2 (fun x => to_Z k < to_Z x) Lk Ll Lr) as [_ Mk]. cbn -[to_Z elements] in Mk.
  apply bal_bst; [exact Bl | exact B' | | exact M'].
  refine (keys_in_mono _ _ _ _ Kl). cbn beta. intros; lia.
Qed.

Lemma remove_keys : forall (p : int -> Prop) k m, keys_in p m -> keys_in p (remove k m).
Proof.
  induction m as [|h l IHl k' v' r IHr]; cbn -[to_Z elements]; [tauto|].
  intros (Pk & Pl & Pr).
  destruct (PrimInt63.ltb k k'); [rewrite bal_keys; auto|].
  destruct (PrimInt63.ltb k' k); [rewrite bal_keys; auto|].
  apply merge_keys; assumption.
Qed.

Lemma remove_bst : forall k m, bst m -> bst (remove k m).
Proof.
  induction m as [|h l IHl k' v' r IHr]; cbn -[to_Z elements]; [tauto|].
  intros (Kl & Kr & Bl & Br).
  destruct (PrimInt63.ltb k k'); [apply bal_bst; auto using remove_keys|].
  destruct (PrimInt63.ltb k' k); [apply bal_bst; auto using remove_keys|].
  apply (merge_bst l r k'); assumption.
Qed.

Lemma remove_inb : forall k m x w, bst m ->
  (inb x w (remove k m) <-> (inb x w m /\ to_Z x <> to_Z k)).
Proof.
  intros k m; induction m as [|h l IHl k' v' r IHr]; intros x w; cbn -[to_Z elements]; [tauto|].
  intros (Kl & Kr & Bl & Br).
  destruct (ltbP k k') as [L|L].
  - rewrite bal_inb, IHl by assumption. split.
    + intros [[H N]|[[<- E]|H]]; [tauto| split; [tauto|lia] |].
      split; [tauto|]. pose proof (keys_in_inb _ _ _ _ Kr H). cbn -[to_Z elements] in *. lia.
    + tauto.
  - destruct (ltbP k' k) as [L'|L'].
    + rewrite bal_inb, IHr by assumption. split.
      * intros [H|[[<- E]|[H N]]]; [| split; [tauto|lia] | tauto].
        split; [tauto|]. pose proof (keys_in_inb _ _ _ _ Kl H). cbn -[to_Z elements] in *. lia.
      * tauto.
    + assert (k' = k) as -> by (apply to_Z_inj; apply Z.le_antisymm; apply Z.nlt_ge; assumption).
      rewrite merge_inb. split.
      * intros [H|H]; split; try tauto.
        -- pose proof (keys_in_inb _ _ _ _ Kl H). cbn -[to_Z elements] in *. lia.
        -- pose proof (keys_in_inb _ _ _ _ Kr H). cbn -[to_Z elements] in *. lia.
      * intros [[H|[[E _]|H]] N]; [tauto| subst; lia |tauto].
Qed.

Lemma remove_range_keys : forall (p : int -> Prop) lo hi m, keys_in p m -> keys_in p (remove_range lo hi m).
Proof.
  induction m as [|h l IHl k' v' r IHr]; cbn -[to_Z elements]; [tauto|].
  intros (Pk & Pl & Pr).
  destruct (PrimInt63.ltb k' lo); [rewrite bal_keys; auto|].
  destruct (PrimInt63.leb hi k'); [rewrite bal_keys; auto|].
  apply merge_keys; auto.
Qed.

Lemma remove_range_bst : forall lo hi m, bst m -> bst (remove_range lo hi m).
Proof.
  induction m as [|h l IHl k' v' r IHr]; cbn -[to_Z elements]; [tauto|].
  intros (Kl & Kr & Bl & Br).
  destruct (PrimInt63.ltb k' lo); [apply bal_bst; auto using remove_range_keys|].
  destruct (PrimInt63.leb hi k'); [apply bal_bst; auto using remove_range_keys|].
  apply (merge_bst _ _ k'); auto using remove_range_keys.
Qed.

Lemma remove_range_inb : forall lo hi m x w, bst m ->
  (inb x w (remove_range lo hi m) <-> (inb x w m /\ ~ (to_Z lo <= to_Z x < to_Z hi))).
Proof.
  intros lo hi m; induction m as [|h l IHl k' v' r IHr]; intros x w; cbn -[to_Z elements]; [tauto|].
  intros (Kl & Kr & Bl & Br).
  destruct (ltbP k' lo) as [L|L].
  - rewrite bal_inb, IHr by assumption. split.
    + intros [H|[[<- E]|[H N]]]; [| split; [tauto|lia] | tauto].
      split; [tauto|]. pose proof (keys_in_inb _ _ _ _ Kl H). cbn -[to_Z elements] in *. lia.
    + set (R := _ <= _ < _) in *. clearbody R. tauto.
  - destruct (lebP hi k') as [L'|L'].
    + rewrite bal_inb, IHl by assumption. split.
      * intros [[H N]|[[<- E]|H]]; [tauto| split; [tauto|lia] |].
        split; [tauto|]. pose proof (keys_in_inb _ _ _ _ Kr H). cbn -[to_Z elements] in *. lia.
      * set (R := _ <= _ < _) in *. clearbody R. tauto.
    + rewrite merge_inb, IHl, IHr by auto using remove_range_bst.
      split.
      * intros [[H N]|[H N]]; tauto.
      * intros [[H|[[<- <-]|H]] N]; [tauto| exfalso; apply N; lia |tauto].
Qed.

Lemma forallb_inb : forall (p : int -> A -> bool) m,
  forallb p m = true <-> (forall x w, inb x w m -> p x w = true).
Proof.
  induction m as [|h l IHl k v r IHr]; cbn -[to_Z elements].
  - split; [intros _ x w F; destruct F | reflexivity].
  - rewrite !andb_true_iff, IHl, IHr. split.
    + intros ((Pk & Pl) & Pr) x w [H|[[<- <-]|H]]; eauto.
    + intros H. repeat split; intros; eauto.
Qed.

Lemma find_range_aux_in : forall lo hi m acc x w, bst m ->
  (In (x, w) (find_range_aux lo hi m acc) <->
   ((inb x w m /\ to_Z lo <= to_Z x < to_Z hi) \/ In (x, w) acc)).
Proof.
  induction m as [|h l IHl k v r IHr]; cbn -[to_Z elements]; intros acc x w; [tauto|].
  intros (Kl & Kr & Bl & Br).
  destruct (ltbP k lo) as [L|L].
  - rewrite IHr by assumption. split; [tauto|].
    intros [[[H|[[<- _]|H]] R]|H]; [| lia | tauto | tauto].
    pose proof (keys_in_inb _ _ _ _ Kl H). cbn -[to_Z elements] in *. lia.
  - destruct (lebP hi k) as [L'|L'].
    + rewrite IHl by assumption. split; [tauto|].
      intros [[[H|[[<- _]|H]] R]|H]; [tauto| lia | | tauto].
      pose proof (keys_in_inb _ _ _ _ Kr H). cbn -[to_Z elements] in *. lia.
    + rewrite IHl by assumption. cbn -[to_Z elements]. rewrite IHr by assumption. split.
      * intros [H|[E|[H|H]]]; [tauto| injection E as -> ->; left; split; [tauto|lia] | tauto | tauto].
      * intros [[[H|[[-> ->]|H]] R]|H]; tauto.
Qed.

End Theory.

Section Spec.
Context {A : Type}.
Implicit Types (m : t A) (k : int) (v : A).
Lemma bst_empty : bst (@empty A). Proof. exact I. Qed.
Lemma find_empty : forall k, find k (@empty A) = None. Proof. reflexivity. Qed.
Lemma bst_add : forall k v m, bst m -> bst (add k v m).
Proof. exact add_bst. Qed.
Lemma bst_remove : forall k m, bst m -> bst (remove k m).
Proof. exact remove_bst. Qed.
Lemma bst_remove_range : forall lo hi m, bst m -> bst (remove_range lo hi m).
Proof. exact remove_range_bst. Qed.
Lemma find_add_same : forall k v m, bst m -> find k (add k v m) = Some v.
Proof. intros k v m B. apply find_inb; [apply add_bst, B|]. apply add_inb; [exact B|]. tauto. Qed.
Lemma find_add_other : forall k k' v m, bst m -> k <> k' -> find k' (add k v m) = find k' m.
Proof.
  intros k k' v m B N. apply find_ext; [apply add_bst, B| exact B|]. intros w.
  rewrite add_inb by exact B. assert (to_Z k' <> to_Z k) by (intros E; apply N; symmetry; apply to_Z_inj, E).
  tauto.
Qed.
Lemma find_add_other_eqb : forall k k' v m, bst m -> PrimInt63.eqb k k' = false -> find k' (add k v m) = find k' m.
Proof. intros k k' v m B E. apply find_add_other; [exact B|]. apply eqb_false_spec. exact E. Qed.
Lemma find_remove_same : forall k m, bst m -> find k (remove k m) = None.
Proof.
  intros k m B. apply find_none_inb; [apply remove_bst, B|]. intros w H.
  apply remove_inb in H; [|exact B]. tauto.
Qed.
Lemma find_remove_other : forall k k' m, bst m -> k <> k' -> find k' (remove k m) = find k' m.
Proof.
  intros k k' m B N. apply find_ext; [apply remove_bst, B| exact B|]. intros w.
  rewrite remove_inb by exact B. assert (to_Z k' <> to_Z k) by (intros E; apply N; symmetry; apply to_Z_inj, E).
  tauto.
Qed.
Lemma find_remove_range : forall lo hi k m, bst m ->
  find k (remove_range lo hi m) =
  if (PrimInt63.leb lo k && PrimInt63.ltb k hi)%bool then None else find k m.
Proof.
  intros lo hi k m B.
  destruct (lebP lo k) as [L1|L1]; [destruct (ltbP k hi) as [L2|L2]|]; cbn -[to_Z elements].
  - apply find_none_inb; [apply remove_range_bst, B|]. intros w H.
    apply remove_range_inb in H; [|exact B]. tauto.
  - apply find_ext; [apply remove_range_bst, B| exact B|]. intros w.
    rewrite remove_range_inb by exact B. split; [tauto|]. intros H; split; [exact H|lia].
  - apply find_ext; [apply remove_range_bst, B| exact B|]. intros w.
    rewrite remove_range_inb by exact B. split; [tauto|]. intros H; split; [exact H|lia].
Qed.
Lemma find_range_spec : forall lo hi k v m, bst m ->
  In (k, v) (find_range lo hi m) <-> (find k m = Some v /\ to_Z lo <= to_Z k < to_Z hi).
Proof.
  intros lo hi k v m B. unfold find_range. rewrite find_range_aux_in, find_inb by exact B. cbn -[to_Z elements]. tauto.
Qed.
Lemma elements_spec : forall k v m, bst m -> In (k, v) (elements m) <-> find k m = Some v.
Proof. intros k v m B. rewrite elements_in, find_inb by exact B. tauto. Qed.
Lemma forallb_spec : forall (p : int -> A -> bool) m, bst m ->
  forallb p m = true <-> (forall k v, find k m = Some v -> p k v = true).
Proof.
  intros p m B. rewrite forallb_inb. split; intros H k v H'; apply H; apply find_inb; assumption.
Qed.
Lemma fold_spec : forall {B} (f : int -> A -> B -> B) m (b : B),
  fold f m b = List.fold_left (fun acc kv => f (fst kv) (snd kv) acc) (elements m) b.
Proof. intros. apply fold_elements. Qed.
Lemma find_map : forall {B} (f : A -> B) k m, find k (map f m) = option_map f (find k m).
Proof.
  intros B f k m. induction m as [|h l IHl k' v' r IHr]; cbn -[to_Z elements]; [reflexivity|].
  destruct (PrimInt63.ltb k k'); [exact IHl|]. destruct (PrimInt63.ltb k' k); [exact IHr|]. reflexivity.
Qed.
Lemma keys_in_map : forall {B} (p : int -> Prop) (f : A -> B) m, keys_in p (map f m) <-> keys_in p m.
Proof. intros B p f m. induction m; cbn -[to_Z elements]; tauto. Qed.
Lemma bst_map : forall {B} (f : A -> B) m, bst m -> bst (map f m).
Proof.
  intros B f m. induction m as [|h l IHl k v r IHr]; cbn -[to_Z elements]; [tauto|].
  rewrite !keys_in_map. tauto.
Qed.

Lemma filter_all_false : forall {T} (P : T -> bool) (xs : list T),
  Forall (fun a => P a = false) xs -> filter P xs = [].
Proof. intros T P xs F. induction F as [|a xs E F IH]; cbn; [reflexivity|]. rewrite E. exact IH. Qed.

Lemma find_range_aux_elements : forall lo hi m acc, bst m ->
  find_range_aux lo hi m acc =
  filter (fun kv => (PrimInt63.leb lo (fst kv) && PrimInt63.ltb (fst kv) hi)%bool) (elements m) ++ acc.
Proof.
  induction m as [|h l IHl k v r IHr]; intros acc B; [reflexivity|].
  destruct B as (Kl & Kr & Bl & Br). cbn [find_range_aux]. rewrite elements_node, filter_app. cbn [filter fst].
  destruct (ltbP k lo) as [L|L].
  - destruct (lebP lo k); [lia|]. cbn [andb].
    rewrite IHr by exact Br. rewrite (filter_all_false _ (elements l)); [reflexivity|].
    apply (proj1 (keys_in_forall (fun x => (PrimInt63.leb lo x && PrimInt63.ltb x hi)%bool = false) l)).
    refine (keys_in_mono _ _ _ _ Kl). cbn beta. intros x Hx.
    destruct (lebP lo x); [lia|]. reflexivity.
  - destruct (lebP lo k); [|lia]. cbn [andb].
    destruct (lebP hi k) as [L'|L'].
    + destruct (ltbP k hi); [lia|].
      rewrite IHl by exact Bl. rewrite (filter_all_false _ (elements r)); [rewrite app_nil_r; reflexivity|].
      apply (proj1 (keys_in_forall (fun x => (PrimInt63.leb lo x && PrimInt63.ltb x hi)%bool = false) r)).
      refine (keys_in_mono _ _ _ _ Kr). cbn beta. intros x Hx.
      destruct (ltbP x hi); [lia|]. apply andb_false_r.
    + destruct (ltbP k hi); [|lia].
      rewrite IHl, IHr by assumption. rewrite <- app_assoc. reflexivity.
Qed.

Lemma find_range_elements : forall lo hi m, bst m ->
  find_range lo hi m =
  filter (fun kv => (PrimInt63.leb lo (fst kv) && PrimInt63.ltb (fst kv) hi)%bool) (elements m).
Proof. intros. unfold find_range. rewrite find_range_aux_elements, app_nil_r by assumption. reflexivity. Qed.

Lemma sorted_filter : forall {T} (R : T -> T -> Prop) (P : T -> bool) (xs : list T),
  StronglySorted R xs -> StronglySorted R (filter P xs).
Proof.
  intros T R P xs S. induction S as [|a xs S IH F]; cbn; [constructor|].
  destruct (P a); [|exact IH]. constructor; [exact IH|].
  apply incl_Forall with (l1 := xs); [|exact F]. apply incl_filter.
Qed.

Lemma find_range_sorted : forall lo hi m, bst m ->
  StronglySorted (fun a b => to_Z (fst a) < to_Z (fst b)) (find_range lo hi m).
Proof.
  intros lo hi m B. rewrite find_range_elements by exact B. apply sorted_filter. apply elements_sorted. exact B.
Qed.

Lemma elements_empty : elements (@empty A) = [].
Proof. reflexivity. Qed.

Lemma cardinal_elements : forall m, cardinal m = length (elements m).
Proof.
  induction m as [|h l IHl k v r IHr]; [reflexivity|]. cbn [cardinal]. rewrite elements_node, length_app. cbn [length]. lia.
Qed.
End Spec.
End IMap.
