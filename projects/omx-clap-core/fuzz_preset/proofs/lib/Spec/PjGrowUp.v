From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
Import ListNotations.
Open Scope Z_scope.

Definition grow_up (t : list ev) : Prop := forall m n, In (EGrow m n) t -> (m < n)%nat.

Lemma grow_up_nil : grow_up [].
Proof. intros m n H. destruct H. Qed.

Lemma grow_up_app : forall a b, grow_up a -> grow_up b -> grow_up (a ++ b).
Proof.
  intros a b Ha Hb m n H. apply in_app_or in H. destruct H as [H|H]; [exact (Ha m n H)|exact (Hb m n H)].
Qed.

Definition gup {A : Type} (m : M A) : Prop := forall ok, grow_up (snd (fst (m ok))).

Lemma gup_ret : forall A (a : A), gup (jret a).
Proof. intros A a ok. exact grow_up_nil. Qed.

Lemma gup_refuse : forall A, gup (@jrefuse A).
Proof. intros A ok. exact grow_up_nil. Qed.

Lemma gup_alloc : forall n, gup (jalloc n).
Proof.
  intros n ok. unfold jalloc. destruct (take ok) as [b ok1].
  destruct b; cbn [fst snd]; intros m' n' H; destruct H as [H|H]; try discriminate; destruct H.
Qed.

Lemma gup_free : forall n, gup (jfree n).
Proof. intros n ok m' n' H. destruct H as [H|H]; [discriminate|destruct H]. Qed.

Lemma gup_realloc : forall m n, (m < n)%nat -> gup (jrealloc m n).
Proof.
  intros m n Hmn ok. unfold jrealloc. destruct (take ok) as [b ok1].
  destruct b; cbn [fst snd]; intros m' n' H.
  - destruct H as [H|H]; [injection H as <- <-; exact Hmn|destruct H].
  - destruct H as [H|H]; [discriminate|destruct H].
Qed.

Lemma gup_bind : forall A B (m : M A) (k : A -> M B), gup m -> (forall a, gup (k a)) -> gup (jbind m k).
Proof.
  intros A B m k Hm Hk ok. unfold jbind. specialize (Hm ok).
  destruct (m ok) as [[[a|] t] ok1]; cbn [fst snd] in Hm.
  - specialize (Hk a ok1). destruct (k a ok1) as [[r t'] ok2]. cbn [fst snd] in *.
    exact (grow_up_app t t' Hm Hk).
  - exact Hm.
Qed.

Lemma gup_grow : forall o n cap, gup (grow o n cap).
Proof.
  intros o n cap. unfold grow. destruct (Nat.ltb n cap); [apply gup_ret|]. cbv zeta.
  apply gup_bind; [apply gup_realloc; destruct cap; cbn [Nat.eqb]; lia|]. intros _.
  destruct o; [|apply gup_ret].
  apply gup_bind; [apply gup_realloc; destruct cap; cbn [Nat.eqb]; lia|]. intros _. apply gup_ret.
Qed.

Ltac gu := repeat (cbv beta iota zeta; match goal with
  | |- gup (jbind _ _) => apply gup_bind
  | |- forall p : (_ * _), _ => intros [? ?]
  | |- forall _, _ => intros ?
  | |- gup (jret _) => apply gup_ret
  | |- gup jrefuse => apply gup_refuse
  | |- gup (jalloc _) => apply gup_alloc
  | |- gup (jfree _) => apply gup_free
  | |- gup (grow _ _ _) => apply gup_grow
  | |- gup (jr_cont _ _ _ _) => unfold jr_cont
  | H : forall d x, gup (jrv _ _ d x) |- gup (jrv _ _ _ _) => apply H
  | H : forall d o n cap acc y, gup (jrl _ _ d o n cap acc y) |- gup (jrl _ _ _ _ _ _ _ _) => apply H
  | H : forall z, gup (jr_string z) |- gup (jr_string _) => apply H
  | |- gup (match ?t with _ => _ end) => destruct t
  end).

Lemma gup_jr_string : forall z, gup (jr_string z).
Proof. intros z. unfold jr_string. gu. Qed.

Lemma gup_jr_name : forall o y, gup (jr_name o y).
Proof. pose proof gup_jr_string. intros o y. unfold jr_name. gu. Qed.

Lemma gup_lit : forall w v x, gup (lit w v x).
Proof. intros w v x. unfold lit. gu. Qed.

Section GrowUp.

Variable strtod_model : list Z -> Z * Z.

Lemma gup_jr_number : forall x, gup (jr_number strtod_model x).
Proof. intros x. unfold jr_number. gu. Qed.

Lemma gup_fuel : forall f,
  (forall d x, gup (jrv strtod_model f d x)) /\
  (forall d o n cap acc y, gup (jrl strtod_model f d o n cap acc y)).
Proof.
  pose proof gup_jr_string.
  induction f as [|f [IHv IHl]].
  - split; intros; apply gup_refuse.
  - split.
    + intros d x. cbn [jrv]. gu; first [apply gup_lit | apply gup_jr_number].
    + intros d o n cap acc y. cbn [jrl]. gu; apply gup_jr_name.
Qed.

Theorem jr_value_grow_up : forall d x ok, grow_up (snd (fst (jr_value strtod_model d x ok))).
Proof. intros d x ok. unfold jr_value. apply (proj1 (gup_fuel _)). Qed.

Theorem jr_items_grow_up : forall d o x ok, grow_up (snd (fst (jr_items strtod_model d o x ok))).
Proof.
  intros d o x ok. pose proof (proj2 (gup_fuel (2 * length x + 2))) as H.
  revert ok. change (gup (jr_items strtod_model d o x)). unfold jr_items. gu.
Qed.

Theorem jr_grow_up : forall x ok, grow_up (snd (jr_run strtod_model x ok)).
Proof.
  intros x ok. rewrite jr_run_eq. cbn [snd]. apply jr_value_grow_up.
Qed.

End GrowUp.
