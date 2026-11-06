(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
