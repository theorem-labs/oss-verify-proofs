(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)

From Stdlib Require ZArith List Lia Bool.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section AProg.
Context {ptr : Type}.

Inductive aprog (A : Type) : Type :=
| ARet (a : A)
| AUnr
| AMalloc (n : Z) (k : option ptr -> aprog A)
| AFree (p : ptr) (k : aprog A).
Arguments ARet {A} a.
Arguments AUnr {A}.
Arguments AMalloc {A} n k.
Arguments AFree {A} p k.

Fixpoint apbind {A B} (t : aprog A) (f : A -> aprog B) : aprog B :=
match t with
| ARet a => f a
| AUnr => AUnr
| AMalloc n k => AMalloc n (fun r => apbind (k r) f)
| AFree p k => AFree p (apbind k f)
end.

Inductive ateq {A} : aprog A -> aprog A -> Prop :=
| ateq_ret a : ateq (ARet a) (ARet a)
| ateq_unr : ateq AUnr AUnr
| ateq_malloc n k k' : (forall r, ateq (k r) (k' r)) -> ateq (AMalloc n k) (AMalloc n k')
| ateq_free p k k' : ateq k k' -> ateq (AFree p k) (AFree p k').

Lemma ateq_refl {A} (t : aprog A) : ateq t t.
Proof. induction t; constructor; auto. Qed.

Lemma apbind_assoc {A B C} (t : aprog A) (f : A -> aprog B) (g : B -> aprog C) :
ateq (apbind (apbind t f) g) (apbind t (fun a => apbind (f a) g)).
Proof. induction t; cbn; try constructor; auto using ateq_refl. Qed.

Section AM.
Context {St : Type}.

Definition AM (A : Type) : Type := St -> aprog (A * St).

Definition aret {A} (a : A) : AM A := fun s => ARet (a, s).
Definition abind {A B} (m : AM A) (f : A -> AM B) : AM B :=
fun s => apbind (m s) (fun p => f (fst p) (snd p)).
Definition aunr {A} : AM A := fun _ => AUnr.
Definition aget : AM St := fun s => ARet (s, s).
Definition aput (s : St) : AM unit := fun _ => ARet (tt, s).
Definition aupd (f : St -> St) : AM unit := fun s => ARet (tt, f s).
Definition aassert (b : bool) : AM unit := if b then aret tt else aunr.
Definition awhen (b : bool) (m : AM unit) : AM unit := if b then m else aret tt.

Definition amalloc (n : Z) : AM (option ptr) := fun s => AMalloc n (fun r => ARet (r, s)).

Definition afree (p : ptr) : AM unit := fun s => AFree p (ARet (tt, s)).

Definition calloc_overflows (m n : Z) : bool := negb (n =? 0) && ((2^64 - 1) / n <? m).
Definition acalloc (m n : Z) : AM (option ptr) :=
if calloc_overflows m n then aret None else amalloc (m * n).

Fixpoint aloop {X R} (fuel : nat) (body : X -> AM (X + R)) (x : X) : AM R :=
match fuel with
| O => aunr
| S fuel' => abind (body x) (fun s => match s with
| inl x' => aloop fuel' body x'
| inr r => aret r
end)
end.

End AM.
Arguments AM St A : clear implicits.

Definition owned := list (ptr * Z).

Fixpoint xremove (peq : ptr -> ptr -> bool) (p : ptr) (X : owned) : owned :=
match X with
| [] => []
| x :: X' => if peq (fst x) p then X' else x :: xremove peq p X'
end.

Section Safe.
Variable peq : ptr -> ptr -> bool.
Hypothesis peq_spec : forall p q, peq p q = true <-> p = q.

Fixpoint asafe {A} (X : owned) (t : aprog A) (Q : A -> owned -> Prop) : Prop :=
match t with
| ARet a => Q a X
| AUnr => False
| AMalloc n k =>
0 <= n
/\ (forall p, ~ In p (map fst X) -> n < 2^63 -> asafe ((p, n) :: X) (k (Some p)) Q)
/\ asafe X (k None) Q
| AFree p k => In p (map fst X) /\ asafe (xremove peq p X) k Q
end.

Section AMSpec.
Context {St : Type}.

Definition aassn : Type := owned -> St -> Prop.

Definition aspec {A} (P : aassn) (m : AM St A) (Q : A -> aassn) : Prop :=
forall X s, P X s -> asafe X (m s) (fun r X' => Q (fst r) X' (snd r)).

End AMSpec.
End Safe.
End AProg.

Arguments aprog ptr A : clear implicits.
Arguments ARet {ptr A} a.
Arguments AUnr {ptr A}.
Arguments AMalloc {ptr A} n k.
Arguments AFree {ptr A} p k.
Arguments AM ptr St A : clear implicits.
Arguments owned ptr : clear implicits.
Arguments aassn ptr St : clear implicits.
Arguments asafe {ptr} peq {A} X t Q.
Arguments aspec {ptr} peq {St A} P m Q.

Declare Scope aprog_scope.
Notation "x <- m ;; k" := (abind m (fun x => k)) (at level 100, m at next level, right associativity) : aprog_scope.
Notation "m ;;; k" := (abind m (fun _ => k)) (at level 100, right associativity) : aprog_scope.
Notation "' p <- m ;; k" := (abind m (fun x => let 'p := x in k)) (at level 100, p pattern, m at next level, right associativity) : aprog_scope.
Delimit Scope aprog_scope with aprog.
End Mq0.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Bool.Bool Stdlib.Lists.List Stdlib.micromega.Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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

Definition zrepeat (v : Z) (n : Z) : list Z := repeat v (Z.to_nat n).
Lemma zlength_zrepeat : forall v n, 0 <= n -> zlength (zrepeat v n) = n.
Proof. intros. unfold zlength, zrepeat. rewrite repeat_length. lia. Qed.
End Mq1.

From Stdlib Require Import List.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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

Inductive steq (R : Type) : stree R -> stree R -> Prop :=
| steq_ret : forall r, steq (SRet r) (SRet r)
| steq_vis : forall e k1 k2, (forall a, steq (k1 a) (k2 a)) -> steq (SVis e k1) (SVis e k2).

Definition smap (R S : Type) (f : R -> S) (t : stree R) : stree S := sbind t (fun r => SRet (f r)).

Inductive strel (R1 R2 : Type) (RR : R1 -> R2 -> Prop) : stree R1 -> stree R2 -> Prop :=
| strel_ret : forall r1 r2, RR r1 r2 -> strel RR (SRet r1) (SRet r2)
| strel_vis : forall e k1 k2, (forall a, strel RR (k1 a) (k2 a)) -> strel RR (SVis e k1) (SVis e k2).

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
