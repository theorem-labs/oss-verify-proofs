(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require ZArith.
From Stdlib Require Bool.
From Stdlib Require List.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Prelim.
From Stdlib Require Import ZArith. From Stdlib Require Import Bool. From Stdlib Require Import List. From Stdlib Require Import Lia.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.

Definition u8  (x : Z) : Z := x mod 2^8.
Definition u16 (x : Z) : Z := x mod 2^16.
Definition u32 (x : Z) : Z := x mod 2^32.
Definition u64 (x : Z) : Z := x mod 2^64.
Definition s32 (x : Z) : Z := (x + 2^31) mod 2^32 - 2^31.
Definition s64 (x : Z) : Z := (x + 2^63) mod 2^64 - 2^63.

Definition zlength {A} (l : list A) : Z := Z.of_nat (length l).

Definition znth (l : list Z) (i : Z) : Z :=
  if i <? 0 then 0 else nth (Z.to_nat i) l 0.

Fixpoint upd_nat (l : list Z) (i : nat) (v : Z) : list Z :=
  match l, i with
  | [], _ => []
  | _ :: t, O => v :: t
  | h :: t, S i' => h :: upd_nat t i' v
  end.

Definition zupd (l : list Z) (i : Z) (v : Z) : list Z :=
  if i <? 0 then l else upd_nat l (Z.to_nat i) v.

Lemma upd_nat_length : forall l i v, length (upd_nat l i v) = length l.
Proof. induction l; intros [|i] v; cbn; auto. Qed.

Lemma zupd_length : forall l i v, length (zupd l i v) = length l.
Proof. intros. unfold zupd. destruct (i <? 0); auto using upd_nat_length. Qed.

Lemma zlength_zupd : forall l i v, zlength (zupd l i v) = zlength l.
Proof. intros. unfold zlength. rewrite zupd_length. reflexivity. Qed.

Lemma nth_upd_nat_same : forall l i v, (i < length l)%nat -> nth i (upd_nat l i v) 0 = v.
Proof. induction l; intros [|i] v H; cbn in *; try lia; auto. apply IHl. lia. Qed.

Lemma nth_upd_nat_other : forall l i j v, i <> j -> nth j (upd_nat l i v) 0 = nth j l 0.
Proof. induction l; intros [|i] [|j] v H; cbn; auto; try congruence. Qed.

Lemma znth_zupd_eq : forall l i v, 0 <= i < zlength l -> znth (zupd l i v) i = v.
Proof.
  intros l i v H. unfold znth, zupd, zlength in *.
  destruct (Z.ltb_spec i 0); [lia|]. apply nth_upd_nat_same. lia.
Qed.

Lemma znth_zupd_neq : forall l i j v, i <> j -> znth (zupd l i v) j = znth l j.
Proof.
  intros l i j v H. unfold znth, zupd.
  destruct (Z.ltb_spec j 0); [reflexivity|]. destruct (Z.ltb_spec i 0); [reflexivity|].
  apply nth_upd_nat_other. intros E. apply H. lia.
Qed.

Lemma znth_range : forall l i, 0 <= i < zlength l -> In (znth l i) l.
Proof.
  intros l i H. unfold znth, zlength in *. destruct (Z.ltb_spec i 0); [lia|].
  apply nth_In. lia.
Qed.

Definition zrepeat (v : Z) (n : Z) : list Z := repeat v (Z.to_nat n).
Lemma zlength_zrepeat : forall v n, 0 <= n -> zlength (zrepeat v n) = n.
Proof. intros. unfold zlength, zrepeat. rewrite repeat_length. lia. Qed.
End Prelim.

Module STree.

From Stdlib Require Import List.
Set Implicit Arguments.

Section STREE.
Variable E : Type.
Variable A : Type.

Inductive stree (R : Type) : Type :=
| SRet (r : R)
| SVis (e : E) (k : A -> stree R).

Arguments SRet {R} r.
Arguments SVis {R} e k.

Fixpoint sbind (R S : Type) (t : stree R) (f : R -> stree S) {struct t} : stree S :=
  match t with
  | SRet r => f r
  | SVis e k => SVis e (fun a => sbind (k a) f)
  end.

Lemma sbind_ret_l : forall R S (r : R) (f : R -> stree S), sbind (SRet r) f = f r.
Proof. reflexivity. Qed.

Lemma sbind_vis : forall R S e (k : A -> stree R) (f : R -> stree S),
  sbind (SVis e k) f = SVis e (fun a => sbind (k a) f).
Proof. reflexivity. Qed.

Inductive steq (R : Type) : stree R -> stree R -> Prop :=
| steq_ret : forall r, steq (SRet r) (SRet r)
| steq_vis : forall e k1 k2, (forall a, steq (k1 a) (k2 a)) -> steq (SVis e k1) (SVis e k2).

Lemma steq_refl : forall R (t : stree R), steq t t.
Proof. induction t; constructor; auto. Qed.

Lemma sbind_ret_r : forall R (t : stree R), steq (sbind t (fun r => SRet r)) t.
Proof. induction t; simpl; constructor; auto. Qed.

Lemma sbind_assoc : forall R S T (t : stree R) (f : R -> stree S) (g : S -> stree T),
  steq (sbind (sbind t f) g) (sbind t (fun r => sbind (f r) g)).
Proof. induction t; intros; simpl. apply steq_refl. constructor; auto. Qed.

Definition smap (R S : Type) (f : R -> S) (t : stree R) : stree S := sbind t (fun r => SRet (f r)).

Inductive strel (R1 R2 : Type) (RR : R1 -> R2 -> Prop) : stree R1 -> stree R2 -> Prop :=
| strel_ret : forall r1 r2, RR r1 r2 -> strel RR (SRet r1) (SRet r2)
| strel_vis : forall e k1 k2, (forall a, strel RR (k1 a) (k2 a)) -> strel RR (SVis e k1) (SVis e k2).

Lemma strel_eq_steq : forall R (t1 t2 : stree R), strel eq t1 t2 <-> steq t1 t2.
Proof.
  split.
  - induction 1; subst; constructor; auto.
  - induction 1; constructor; auto.
Qed.

Lemma strel_mono : forall R1 R2 (RR RR' : R1 -> R2 -> Prop) t1 t2,
  (forall a b, RR a b -> RR' a b) -> strel RR t1 t2 -> strel RR' t1 t2.
Proof. induction 2; constructor; auto. Qed.

Lemma strel_sbind : forall R1 R2 S1 S2 (RR : R1 -> R2 -> Prop) (SS : S1 -> S2 -> Prop)
  t1 t2 (f1 : R1 -> stree S1) (f2 : R2 -> stree S2),
  strel RR t1 t2 -> (forall r1 r2, RR r1 r2 -> strel SS (f1 r1) (f2 r2)) ->
  strel SS (sbind t1 f1) (sbind t2 f2).
Proof. induction 1; intros; simpl; auto. constructor; auto. Qed.

Lemma strel_smap : forall R1 R2 S1 S2 (RR : R1 -> R2 -> Prop) (SS : S1 -> S2 -> Prop)
  t1 t2 (f1 : R1 -> S1) (f2 : R2 -> S2),
  strel RR t1 t2 -> (forall r1 r2, RR r1 r2 -> SS (f1 r1) (f2 r2)) ->
  strel SS (smap f1 t1) (smap f2 t2).
Proof. intros. unfold smap. eapply strel_sbind; eauto. intros; constructor; auto. Qed.

Lemma strel_trans_eq : forall R1 R2 (RR : R1 -> R2 -> Prop) t1 t2 t3,
  strel RR t1 t2 -> strel eq t2 t3 -> strel RR t1 t3.
Proof.
  intros R1 R2 RR t1 t2 t3 H; revert t3; induction H; intros t3 Ht; inversion Ht; subst.
  - constructor; auto.
  - constructor; eauto.
Qed.

Section ERUNS.
Variable O : Type.
Variable sel : O -> E -> option A.
Variable upd : O -> E -> A -> O.

Fixpoint eruns (R : Type) (o : O) (t : stree R) {struct t} : stree (O * R) :=
  match t with
  | SRet r => SRet (o, r)
  | SVis e k =>
      match sel o e with
      | Some a => eruns (upd o e a) (k a)
      | None => SVis e (fun a => eruns (upd o e a) (k a))
      end
  end.

Lemma eruns_ret : forall R o (r : R), eruns o (SRet r) = SRet (o, r).
Proof. reflexivity. Qed.

Lemma eruns_vis_keep : forall R o e (k : A -> stree R),
  sel o e = None -> eruns o (SVis e k) = SVis e (fun a => eruns (upd o e a) (k a)).
Proof. intros. simpl. rewrite H. reflexivity. Qed.

Lemma eruns_vis_sel : forall R o e a (k : A -> stree R),
  sel o e = Some a -> eruns o (SVis e k) = eruns (upd o e a) (k a).
Proof. intros. simpl. rewrite H. reflexivity. Qed.

Lemma eruns_sbind : forall R S o (t : stree R) (g : R -> stree S),
  steq (eruns o (sbind t g)) (sbind (eruns o t) (fun x => eruns (fst x) (g (snd x)))).
Proof.
  intros R S o t; revert o; induction t; intros; simpl.
  - apply steq_refl.
  - destruct (sel o e); simpl; auto. constructor; auto.
Qed.
End ERUNS.

Section RUN.
Variable O : Type.
Variable oracle : O -> E -> A * O.

Fixpoint srun (R : Type) (o : O) (t : stree R) {struct t} : list (E * A) * O * R :=
  match t with
  | SRet r => (nil, o, r)
  | SVis e k =>
      let (a, o1) := oracle o e in
      let '(tr, o2, r) := srun o1 (k a) in
      ((e, a) :: tr, o2, r)
  end.
End RUN.

Definition srun0 (f : E -> A) (R : Type) (t : stree R) : list (E * A) * R :=
  let '(tr, _, r) := srun (fun (_ : unit) e => (f e, tt)) tt t in (tr, r).

End STREE.

Arguments SRet {E A R} r.
Arguments SVis {E A R} e k.
Arguments sbind {E A R S} t f.
Arguments smap {E A R S} f t.
Arguments steq {E A R} _ _.
Arguments strel {E A R1 R2} RR _ _.
Arguments eruns {E A O} sel upd {R} o t.
Arguments srun {E A O} oracle {R} o t.
Arguments srun0 {E A} f {R} t.

Declare Scope stree_scope.
Notation "x <-- c1 ;; c2" := (sbind c1 (fun x => c2))
  (at level 65, c1 at next level, right associativity) : stree_scope.
Notation "' pat <-- c1 ;; c2" := (sbind c1 (fun x__ => match x__ with pat => c2 end))
  (at level 65, pat pattern, c1 at next level, right associativity) : stree_scope.
End STree.
