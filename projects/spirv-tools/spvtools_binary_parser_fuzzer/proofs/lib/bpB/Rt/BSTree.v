(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import List.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
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
