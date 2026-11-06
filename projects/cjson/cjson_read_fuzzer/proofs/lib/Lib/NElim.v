(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
Unset Lia Cache.

(* [comment removed for export] *)
Inductive ntele : Type := ntnil | ntcons (T : Type) (ts : ntele).
Inductive nlist (A : Type) : Type := nlnil | nlcons (a : A) (l : nlist A).
Arguments nlnil {A}. Arguments nlcons {A} a l.
Fixpoint narr (ts : ntele) (R : Type) : Type := match ts with ntnil => R | ntcons T ts' => T -> narr ts' R end.
Fixpoint nexk (ts : ntele) : narr ts Prop -> Prop :=
  match ts with ntnil => fun B => B | ntcons T ts' => fun B => exists x : T, nexk ts' (B x) end.
Fixpoint nallk (ts : ntele) : narr ts Prop -> Prop :=
  match ts with ntnil => fun B => B | ntcons T ts' => fun B => forall x : T, nallk ts' (B x) end.
Fixpoint npand (ts : ntele) : narr ts Prop -> narr ts Prop -> narr ts Prop :=
  match ts with ntnil => fun A B => A /\ B | ntcons T ts' => fun A B x => npand ts' (A x) (B x) end.
Fixpoint npimp (ts : ntele) : narr ts Prop -> narr ts Prop -> narr ts Prop :=
  match ts with ntnil => fun A B => A -> B | ntcons T ts' => fun A B x => npimp ts' (A x) (B x) end.
Fixpoint npconst (ts : ntele) (G : Prop) : narr ts Prop := match ts with ntnil => G | ntcons T ts' => fun _ => npconst ts' G end.
Fixpoint nimps (ts : ntele) (As : nlist (narr ts Prop)) (G : Prop) : narr ts Prop :=
  match As with nlnil => npconst ts G | nlcons A As' => npimp ts A (nimps ts As' G) end.
Fixpoint nands (ts : ntele) (As : nlist (narr ts Prop)) : narr ts Prop :=
  match As with nlnil => npconst ts True | nlcons A As' => match As' with nlnil => A | nlcons _ _ => npand ts A (nands ts As') end end.
Fixpoint nallT (k : nat) : (ntele -> Prop) -> Prop :=
  match k with O => fun P => P ntnil | S k' => fun P => forall T : Type, nallT k' (fun ts => P (ntcons T ts)) end.
Fixpoint nallP (m : nat) (ts : ntele) : (nlist (narr ts Prop) -> Prop) -> Prop :=
  match m with O => fun P => P nlnil | S m' => fun P => forall A : narr ts Prop, nallP m' ts (fun As => P (nlcons A As)) end.
Definition NSTMT (k m : nat) : Prop :=
  nallT k (fun ts => nallP m ts (fun As => forall G : Prop, nallk ts (nimps ts As G) -> nexk ts (nands ts As) -> G)).
Ltac nel_stmt k m :=
  let t := eval cbv beta iota delta [NSTMT nallT nallP nallk nexk nimps nands npand npimp npconst narr] in (NSTMT k m) in exact t.
(* [comment removed for export] *)
Tactic Notation "nel_prove_ex" uconstr(e) := intros until 2; lazymatch goal with K : _, H : ex _ |- ?G => let x := fresh "x" in let H' := fresh "H" in destruct H as [x H']; exact (e G (K x) H') end.
Tactic Notation "nel_prove_comp" uconstr(ek) uconstr(em) := intros until 2; lazymatch goal with K : _, H : ex _ |- ?G =>
  refine (ek G _ H); intros; lazymatch goal with Hb : _ /\ _ |- _ => refine (em G _ Hb); intros; eapply K; eassumption end end.
Tactic Notation "nel_prove_and" uconstr(e) := intros until 2; lazymatch goal with K : _, H : _ /\ _ |- ?G => let a := fresh "a" in let H' := fresh "H" in destruct H as [a H']; exact (e G (K a) H') end.

Lemma e0_2 : ltac:(nel_stmt 0%nat 2%nat).
Proof. intros until 2; lazymatch goal with K : _, H : _ /\ _ |- _ => destruct H as [a b]; exact (K a b) end. Qed.
Arguments e0_2 {_ _} G _ _.
Lemma e0_3 : ltac:(nel_stmt 0%nat 3%nat).
Proof. nel_prove_and e0_2. Qed.
Arguments e0_3 {_ _ _} G _ _.
Lemma e0_4 : ltac:(nel_stmt 0%nat 4%nat).
Proof. nel_prove_and e0_3. Qed.
Arguments e0_4 {_ _ _ _} G _ _.
Lemma e0_5 : ltac:(nel_stmt 0%nat 5%nat).
Proof. nel_prove_and e0_4. Qed.
Arguments e0_5 {_ _ _ _ _} G _ _.
Lemma e0_6 : ltac:(nel_stmt 0%nat 6%nat).
Proof. nel_prove_and e0_5. Qed.
Arguments e0_6 {_ _ _ _ _ _} G _ _.
Lemma e0_7 : ltac:(nel_stmt 0%nat 7%nat).
Proof. nel_prove_and e0_6. Qed.
Arguments e0_7 {_ _ _ _ _ _ _} G _ _.
Lemma e0_8 : ltac:(nel_stmt 0%nat 8%nat).
Proof. nel_prove_and e0_7. Qed.
Arguments e0_8 {_ _ _ _ _ _ _ _} G _ _.
Lemma e0_9 : ltac:(nel_stmt 0%nat 9%nat).
Proof. nel_prove_and e0_8. Qed.
Arguments e0_9 {_ _ _ _ _ _ _ _ _} G _ _.
Lemma e0_10 : ltac:(nel_stmt 0%nat 10%nat).
Proof. nel_prove_and e0_9. Qed.
Arguments e0_10 {_ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e0_11 : ltac:(nel_stmt 0%nat 11%nat).
Proof. nel_prove_and e0_10. Qed.
Arguments e0_11 {_ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e0_12 : ltac:(nel_stmt 0%nat 12%nat).
Proof. nel_prove_and e0_11. Qed.
Arguments e0_12 {_ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e0_13 : ltac:(nel_stmt 0%nat 13%nat).
Proof. nel_prove_and e0_12. Qed.
Arguments e0_13 {_ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e0_14 : ltac:(nel_stmt 0%nat 14%nat).
Proof. nel_prove_and e0_13. Qed.
Arguments e0_14 {_ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e0_15 : ltac:(nel_stmt 0%nat 15%nat).
Proof. nel_prove_and e0_14. Qed.
Arguments e0_15 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e0_16 : ltac:(nel_stmt 0%nat 16%nat).
Proof. nel_prove_and e0_15. Qed.
Arguments e0_16 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e0_17 : ltac:(nel_stmt 0%nat 17%nat).
Proof. nel_prove_and e0_16. Qed.
Arguments e0_17 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e0_18 : ltac:(nel_stmt 0%nat 18%nat).
Proof. nel_prove_and e0_17. Qed.
Arguments e0_18 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e0_19 : ltac:(nel_stmt 0%nat 19%nat).
Proof. nel_prove_and e0_18. Qed.
Arguments e0_19 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e0_20 : ltac:(nel_stmt 0%nat 20%nat).
Proof. nel_prove_and e0_19. Qed.
Arguments e0_20 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e0_21 : ltac:(nel_stmt 0%nat 21%nat).
Proof. nel_prove_and e0_20. Qed.
Arguments e0_21 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e0_22 : ltac:(nel_stmt 0%nat 22%nat).
Proof. nel_prove_and e0_21. Qed.
Arguments e0_22 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e0_23 : ltac:(nel_stmt 0%nat 23%nat).
Proof. nel_prove_and e0_22. Qed.
Arguments e0_23 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e0_24 : ltac:(nel_stmt 0%nat 24%nat).
Proof. nel_prove_and e0_23. Qed.
Arguments e0_24 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e1_1 : ltac:(nel_stmt 1%nat 1%nat).
Proof. intros until 2; lazymatch goal with K : _, H : ex _ |- _ => destruct H as [x a]; exact (K x a) end. Qed.
Arguments e1_1 {_ _} G _ _.
Lemma e1_2 : ltac:(nel_stmt 1%nat 2%nat).
Proof. nel_prove_comp e1_1 e0_2. Qed.
Arguments e1_2 {_ _ _} G _ _.
Lemma e1_3 : ltac:(nel_stmt 1%nat 3%nat).
Proof. nel_prove_comp e1_1 e0_3. Qed.
Arguments e1_3 {_ _ _ _} G _ _.
Lemma e1_4 : ltac:(nel_stmt 1%nat 4%nat).
Proof. nel_prove_comp e1_1 e0_4. Qed.
Arguments e1_4 {_ _ _ _ _} G _ _.
Lemma e1_5 : ltac:(nel_stmt 1%nat 5%nat).
Proof. nel_prove_comp e1_1 e0_5. Qed.
Arguments e1_5 {_ _ _ _ _ _} G _ _.
Lemma e1_6 : ltac:(nel_stmt 1%nat 6%nat).
Proof. nel_prove_comp e1_1 e0_6. Qed.
Arguments e1_6 {_ _ _ _ _ _ _} G _ _.
Lemma e2_1 : ltac:(nel_stmt 2%nat 1%nat).
Proof. nel_prove_ex e1_1. Qed.
Arguments e2_1 {_ _ _} G _ _.
Lemma e2_2 : ltac:(nel_stmt 2%nat 2%nat).
Proof. nel_prove_comp e2_1 e0_2. Qed.
Arguments e2_2 {_ _ _ _} G _ _.
Lemma e2_3 : ltac:(nel_stmt 2%nat 3%nat).
Proof. nel_prove_comp e2_1 e0_3. Qed.
Arguments e2_3 {_ _ _ _ _} G _ _.
Lemma e2_4 : ltac:(nel_stmt 2%nat 4%nat).
Proof. nel_prove_comp e2_1 e0_4. Qed.
Arguments e2_4 {_ _ _ _ _ _} G _ _.
Lemma e2_5 : ltac:(nel_stmt 2%nat 5%nat).
Proof. nel_prove_comp e2_1 e0_5. Qed.
Arguments e2_5 {_ _ _ _ _ _ _} G _ _.
Lemma e2_6 : ltac:(nel_stmt 2%nat 6%nat).
Proof. nel_prove_comp e2_1 e0_6. Qed.
Arguments e2_6 {_ _ _ _ _ _ _ _} G _ _.
Lemma e2_7 : ltac:(nel_stmt 2%nat 7%nat).
Proof. nel_prove_comp e2_1 e0_7. Qed.
Arguments e2_7 {_ _ _ _ _ _ _ _ _} G _ _.
Lemma e2_8 : ltac:(nel_stmt 2%nat 8%nat).
Proof. nel_prove_comp e2_1 e0_8. Qed.
Arguments e2_8 {_ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e2_9 : ltac:(nel_stmt 2%nat 9%nat).
Proof. nel_prove_comp e2_1 e0_9. Qed.
Arguments e2_9 {_ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e2_10 : ltac:(nel_stmt 2%nat 10%nat).
Proof. nel_prove_comp e2_1 e0_10. Qed.
Arguments e2_10 {_ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e2_11 : ltac:(nel_stmt 2%nat 11%nat).
Proof. nel_prove_comp e2_1 e0_11. Qed.
Arguments e2_11 {_ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e3_1 : ltac:(nel_stmt 3%nat 1%nat).
Proof. nel_prove_ex e2_1. Qed.
Arguments e3_1 {_ _ _ _} G _ _.
Lemma e3_2 : ltac:(nel_stmt 3%nat 2%nat).
Proof. nel_prove_comp e3_1 e0_2. Qed.
Arguments e3_2 {_ _ _ _ _} G _ _.
Lemma e3_3 : ltac:(nel_stmt 3%nat 3%nat).
Proof. nel_prove_comp e3_1 e0_3. Qed.
Arguments e3_3 {_ _ _ _ _ _} G _ _.
Lemma e3_4 : ltac:(nel_stmt 3%nat 4%nat).
Proof. nel_prove_comp e3_1 e0_4. Qed.
Arguments e3_4 {_ _ _ _ _ _ _} G _ _.
Lemma e3_6 : ltac:(nel_stmt 3%nat 6%nat).
Proof. nel_prove_comp e3_1 e0_6. Qed.
Arguments e3_6 {_ _ _ _ _ _ _ _ _} G _ _.
Lemma e4_1 : ltac:(nel_stmt 4%nat 1%nat).
Proof. nel_prove_ex e3_1. Qed.
Arguments e4_1 {_ _ _ _ _} G _ _.
Lemma e4_6 : ltac:(nel_stmt 4%nat 6%nat).
Proof. nel_prove_comp e4_1 e0_6. Qed.
Arguments e4_6 {_ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e4_7 : ltac:(nel_stmt 4%nat 7%nat).
Proof. nel_prove_comp e4_1 e0_7. Qed.
Arguments e4_7 {_ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e5_1 : ltac:(nel_stmt 5%nat 1%nat).
Proof. nel_prove_ex e4_1. Qed.
Arguments e5_1 {_ _ _ _ _ _} G _ _.
Lemma e5_23 : ltac:(nel_stmt 5%nat 23%nat).
Proof. nel_prove_comp e5_1 e0_23. Qed.
Arguments e5_23 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e6_1 : ltac:(nel_stmt 6%nat 1%nat).
Proof. nel_prove_ex e5_1. Qed.
Arguments e6_1 {_ _ _ _ _ _ _} G _ _.
Lemma e7_1 : ltac:(nel_stmt 7%nat 1%nat).
Proof. nel_prove_ex e6_1. Qed.
Arguments e7_1 {_ _ _ _ _ _ _ _} G _ _.
Lemma e7_2 : ltac:(nel_stmt 7%nat 2%nat).
Proof. nel_prove_comp e7_1 e0_2. Qed.
Arguments e7_2 {_ _ _ _ _ _ _ _ _} G _ _.
Lemma e7_4 : ltac:(nel_stmt 7%nat 4%nat).
Proof. nel_prove_comp e7_1 e0_4. Qed.
Arguments e7_4 {_ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e7_6 : ltac:(nel_stmt 7%nat 6%nat).
Proof. nel_prove_comp e7_1 e0_6. Qed.
Arguments e7_6 {_ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e8_1 : ltac:(nel_stmt 8%nat 1%nat).
Proof. nel_prove_ex e7_1. Qed.
Arguments e8_1 {_ _ _ _ _ _ _ _ _} G _ _.
Lemma e8_10 : ltac:(nel_stmt 8%nat 10%nat).
Proof. nel_prove_comp e8_1 e0_10. Qed.
Arguments e8_10 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e9_1 : ltac:(nel_stmt 9%nat 1%nat).
Proof. nel_prove_ex e8_1. Qed.
Arguments e9_1 {_ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e10_1 : ltac:(nel_stmt 10%nat 1%nat).
Proof. nel_prove_ex e9_1. Qed.
Arguments e10_1 {_ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e10_5 : ltac:(nel_stmt 10%nat 5%nat).
Proof. nel_prove_comp e10_1 e0_5. Qed.
Arguments e10_5 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e11_1 : ltac:(nel_stmt 11%nat 1%nat).
Proof. nel_prove_ex e10_1. Qed.
Arguments e11_1 {_ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e12_1 : ltac:(nel_stmt 12%nat 1%nat).
Proof. nel_prove_ex e11_1. Qed.
Arguments e12_1 {_ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e12_5 : ltac:(nel_stmt 12%nat 5%nat).
Proof. nel_prove_comp e12_1 e0_5. Qed.
Arguments e12_5 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e13_1 : ltac:(nel_stmt 13%nat 1%nat).
Proof. nel_prove_ex e12_1. Qed.
Arguments e13_1 {_ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e14_1 : ltac:(nel_stmt 14%nat 1%nat).
Proof. nel_prove_ex e13_1. Qed.
Arguments e14_1 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e15_1 : ltac:(nel_stmt 15%nat 1%nat).
Proof. nel_prove_ex e14_1. Qed.
Arguments e15_1 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e15_4 : ltac:(nel_stmt 15%nat 4%nat).
Proof. nel_prove_comp e15_1 e0_4. Qed.
Arguments e15_4 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e15_5 : ltac:(nel_stmt 15%nat 5%nat).
Proof. nel_prove_comp e15_1 e0_5. Qed.
Arguments e15_5 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e15_6 : ltac:(nel_stmt 15%nat 6%nat).
Proof. nel_prove_comp e15_1 e0_6. Qed.
Arguments e15_6 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e15_8 : ltac:(nel_stmt 15%nat 8%nat).
Proof. nel_prove_comp e15_1 e0_8. Qed.
Arguments e15_8 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e15_9 : ltac:(nel_stmt 15%nat 9%nat).
Proof. nel_prove_comp e15_1 e0_9. Qed.
Arguments e15_9 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e16_1 : ltac:(nel_stmt 16%nat 1%nat).
Proof. nel_prove_ex e15_1. Qed.
Arguments e16_1 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e16_5 : ltac:(nel_stmt 16%nat 5%nat).
Proof. nel_prove_comp e16_1 e0_5. Qed.
Arguments e16_5 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e16_6 : ltac:(nel_stmt 16%nat 6%nat).
Proof. nel_prove_comp e16_1 e0_6. Qed.
Arguments e16_6 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e16_7 : ltac:(nel_stmt 16%nat 7%nat).
Proof. nel_prove_comp e16_1 e0_7. Qed.
Arguments e16_7 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e17_1 : ltac:(nel_stmt 17%nat 1%nat).
Proof. nel_prove_ex e16_1. Qed.
Arguments e17_1 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e17_5 : ltac:(nel_stmt 17%nat 5%nat).
Proof. nel_prove_comp e17_1 e0_5. Qed.
Arguments e17_5 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e17_6 : ltac:(nel_stmt 17%nat 6%nat).
Proof. nel_prove_comp e17_1 e0_6. Qed.
Arguments e17_6 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e17_8 : ltac:(nel_stmt 17%nat 8%nat).
Proof. nel_prove_comp e17_1 e0_8. Qed.
Arguments e17_8 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e17_9 : ltac:(nel_stmt 17%nat 9%nat).
Proof. nel_prove_comp e17_1 e0_9. Qed.
Arguments e17_9 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e18_1 : ltac:(nel_stmt 18%nat 1%nat).
Proof. nel_prove_ex e17_1. Qed.
Arguments e18_1 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e18_2 : ltac:(nel_stmt 18%nat 2%nat).
Proof. nel_prove_comp e18_1 e0_2. Qed.
Arguments e18_2 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e18_7 : ltac:(nel_stmt 18%nat 7%nat).
Proof. nel_prove_comp e18_1 e0_7. Qed.
Arguments e18_7 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e18_9 : ltac:(nel_stmt 18%nat 9%nat).
Proof. nel_prove_comp e18_1 e0_9. Qed.
Arguments e18_9 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e18_11 : ltac:(nel_stmt 18%nat 11%nat).
Proof. nel_prove_comp e18_1 e0_11. Qed.
Arguments e18_11 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e19_1 : ltac:(nel_stmt 19%nat 1%nat).
Proof. nel_prove_ex e18_1. Qed.
Arguments e19_1 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e19_3 : ltac:(nel_stmt 19%nat 3%nat).
Proof. nel_prove_comp e19_1 e0_3. Qed.
Arguments e19_3 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e19_4 : ltac:(nel_stmt 19%nat 4%nat).
Proof. nel_prove_comp e19_1 e0_4. Qed.
Arguments e19_4 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e19_8 : ltac:(nel_stmt 19%nat 8%nat).
Proof. nel_prove_comp e19_1 e0_8. Qed.
Arguments e19_8 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e19_10 : ltac:(nel_stmt 19%nat 10%nat).
Proof. nel_prove_comp e19_1 e0_10. Qed.
Arguments e19_10 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e20_1 : ltac:(nel_stmt 20%nat 1%nat).
Proof. nel_prove_ex e19_1. Qed.
Arguments e20_1 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e20_4 : ltac:(nel_stmt 20%nat 4%nat).
Proof. nel_prove_comp e20_1 e0_4. Qed.
Arguments e20_4 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e20_5 : ltac:(nel_stmt 20%nat 5%nat).
Proof. nel_prove_comp e20_1 e0_5. Qed.
Arguments e20_5 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e20_7 : ltac:(nel_stmt 20%nat 7%nat).
Proof. nel_prove_comp e20_1 e0_7. Qed.
Arguments e20_7 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e20_9 : ltac:(nel_stmt 20%nat 9%nat).
Proof. nel_prove_comp e20_1 e0_9. Qed.
Arguments e20_9 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e20_10 : ltac:(nel_stmt 20%nat 10%nat).
Proof. nel_prove_comp e20_1 e0_10. Qed.
Arguments e20_10 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e20_11 : ltac:(nel_stmt 20%nat 11%nat).
Proof. nel_prove_comp e20_1 e0_11. Qed.
Arguments e20_11 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e20_12 : ltac:(nel_stmt 20%nat 12%nat).
Proof. nel_prove_comp e20_1 e0_12. Qed.
Arguments e20_12 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e21_1 : ltac:(nel_stmt 21%nat 1%nat).
Proof. nel_prove_ex e20_1. Qed.
Arguments e21_1 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e21_11 : ltac:(nel_stmt 21%nat 11%nat).
Proof. nel_prove_comp e21_1 e0_11. Qed.
Arguments e21_11 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e21_12 : ltac:(nel_stmt 21%nat 12%nat).
Proof. nel_prove_comp e21_1 e0_12. Qed.
Arguments e21_12 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e22_1 : ltac:(nel_stmt 22%nat 1%nat).
Proof. nel_prove_ex e21_1. Qed.
Arguments e22_1 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e23_1 : ltac:(nel_stmt 23%nat 1%nat).
Proof. nel_prove_ex e22_1. Qed.
Arguments e23_1 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e23_4 : ltac:(nel_stmt 23%nat 4%nat).
Proof. nel_prove_comp e23_1 e0_4. Qed.
Arguments e23_4 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e24_1 : ltac:(nel_stmt 24%nat 1%nat).
Proof. nel_prove_ex e23_1. Qed.
Arguments e24_1 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e24_8 : ltac:(nel_stmt 24%nat 8%nat).
Proof. nel_prove_comp e24_1 e0_8. Qed.
Arguments e24_8 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e25_1 : ltac:(nel_stmt 25%nat 1%nat).
Proof. nel_prove_ex e24_1. Qed.
Arguments e25_1 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.
Lemma e26_1 : ltac:(nel_stmt 26%nat 1%nat).
Proof. nel_prove_ex e25_1. Qed.
Arguments e26_1 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} G _ _.

(* [comment removed for export] *)
Ltac nelim_lemma k m :=
  lazymatch constr:((k, m)) with
  | (0%nat, 2%nat) => constr:(@e0_2)
  | (0%nat, 3%nat) => constr:(@e0_3)
  | (0%nat, 4%nat) => constr:(@e0_4)
  | (0%nat, 5%nat) => constr:(@e0_5)
  | (0%nat, 6%nat) => constr:(@e0_6)
  | (0%nat, 7%nat) => constr:(@e0_7)
  | (0%nat, 8%nat) => constr:(@e0_8)
  | (0%nat, 9%nat) => constr:(@e0_9)
  | (0%nat, 10%nat) => constr:(@e0_10)
  | (0%nat, 11%nat) => constr:(@e0_11)
  | (0%nat, 12%nat) => constr:(@e0_12)
  | (0%nat, 13%nat) => constr:(@e0_13)
  | (0%nat, 14%nat) => constr:(@e0_14)
  | (0%nat, 15%nat) => constr:(@e0_15)
  | (0%nat, 16%nat) => constr:(@e0_16)
  | (0%nat, 17%nat) => constr:(@e0_17)
  | (0%nat, 18%nat) => constr:(@e0_18)
  | (0%nat, 19%nat) => constr:(@e0_19)
  | (0%nat, 20%nat) => constr:(@e0_20)
  | (0%nat, 21%nat) => constr:(@e0_21)
  | (0%nat, 22%nat) => constr:(@e0_22)
  | (0%nat, 23%nat) => constr:(@e0_23)
  | (0%nat, 24%nat) => constr:(@e0_24)
  | (1%nat, 1%nat) => constr:(@e1_1)
  | (1%nat, 2%nat) => constr:(@e1_2)
  | (1%nat, 3%nat) => constr:(@e1_3)
  | (1%nat, 4%nat) => constr:(@e1_4)
  | (1%nat, 5%nat) => constr:(@e1_5)
  | (1%nat, 6%nat) => constr:(@e1_6)
  | (2%nat, 1%nat) => constr:(@e2_1)
  | (2%nat, 2%nat) => constr:(@e2_2)
  | (2%nat, 3%nat) => constr:(@e2_3)
  | (2%nat, 4%nat) => constr:(@e2_4)
  | (2%nat, 5%nat) => constr:(@e2_5)
  | (2%nat, 6%nat) => constr:(@e2_6)
  | (2%nat, 7%nat) => constr:(@e2_7)
  | (2%nat, 8%nat) => constr:(@e2_8)
  | (2%nat, 9%nat) => constr:(@e2_9)
  | (2%nat, 10%nat) => constr:(@e2_10)
  | (2%nat, 11%nat) => constr:(@e2_11)
  | (3%nat, 1%nat) => constr:(@e3_1)
  | (3%nat, 2%nat) => constr:(@e3_2)
  | (3%nat, 3%nat) => constr:(@e3_3)
  | (3%nat, 4%nat) => constr:(@e3_4)
  | (3%nat, 6%nat) => constr:(@e3_6)
  | (4%nat, 1%nat) => constr:(@e4_1)
  | (4%nat, 6%nat) => constr:(@e4_6)
  | (4%nat, 7%nat) => constr:(@e4_7)
  | (5%nat, 1%nat) => constr:(@e5_1)
  | (5%nat, 23%nat) => constr:(@e5_23)
  | (6%nat, 1%nat) => constr:(@e6_1)
  | (7%nat, 1%nat) => constr:(@e7_1)
  | (7%nat, 2%nat) => constr:(@e7_2)
  | (7%nat, 4%nat) => constr:(@e7_4)
  | (7%nat, 6%nat) => constr:(@e7_6)
  | (8%nat, 1%nat) => constr:(@e8_1)
  | (8%nat, 10%nat) => constr:(@e8_10)
  | (9%nat, 1%nat) => constr:(@e9_1)
  | (10%nat, 1%nat) => constr:(@e10_1)
  | (10%nat, 5%nat) => constr:(@e10_5)
  | (11%nat, 1%nat) => constr:(@e11_1)
  | (12%nat, 1%nat) => constr:(@e12_1)
  | (12%nat, 5%nat) => constr:(@e12_5)
  | (13%nat, 1%nat) => constr:(@e13_1)
  | (14%nat, 1%nat) => constr:(@e14_1)
  | (15%nat, 1%nat) => constr:(@e15_1)
  | (15%nat, 4%nat) => constr:(@e15_4)
  | (15%nat, 5%nat) => constr:(@e15_5)
  | (15%nat, 6%nat) => constr:(@e15_6)
  | (15%nat, 8%nat) => constr:(@e15_8)
  | (15%nat, 9%nat) => constr:(@e15_9)
  | (16%nat, 1%nat) => constr:(@e16_1)
  | (16%nat, 5%nat) => constr:(@e16_5)
  | (16%nat, 6%nat) => constr:(@e16_6)
  | (16%nat, 7%nat) => constr:(@e16_7)
  | (17%nat, 1%nat) => constr:(@e17_1)
  | (17%nat, 5%nat) => constr:(@e17_5)
  | (17%nat, 6%nat) => constr:(@e17_6)
  | (17%nat, 8%nat) => constr:(@e17_8)
  | (17%nat, 9%nat) => constr:(@e17_9)
  | (18%nat, 1%nat) => constr:(@e18_1)
  | (18%nat, 2%nat) => constr:(@e18_2)
  | (18%nat, 7%nat) => constr:(@e18_7)
  | (18%nat, 9%nat) => constr:(@e18_9)
  | (18%nat, 11%nat) => constr:(@e18_11)
  | (19%nat, 1%nat) => constr:(@e19_1)
  | (19%nat, 3%nat) => constr:(@e19_3)
  | (19%nat, 4%nat) => constr:(@e19_4)
  | (19%nat, 8%nat) => constr:(@e19_8)
  | (19%nat, 10%nat) => constr:(@e19_10)
  | (20%nat, 1%nat) => constr:(@e20_1)
  | (20%nat, 4%nat) => constr:(@e20_4)
  | (20%nat, 5%nat) => constr:(@e20_5)
  | (20%nat, 7%nat) => constr:(@e20_7)
  | (20%nat, 9%nat) => constr:(@e20_9)
  | (20%nat, 10%nat) => constr:(@e20_10)
  | (20%nat, 11%nat) => constr:(@e20_11)
  | (20%nat, 12%nat) => constr:(@e20_12)
  | (21%nat, 1%nat) => constr:(@e21_1)
  | (21%nat, 11%nat) => constr:(@e21_11)
  | (21%nat, 12%nat) => constr:(@e21_12)
  | (22%nat, 1%nat) => constr:(@e22_1)
  | (23%nat, 1%nat) => constr:(@e23_1)
  | (23%nat, 4%nat) => constr:(@e23_4)
  | (24%nat, 1%nat) => constr:(@e24_1)
  | (24%nat, 8%nat) => constr:(@e24_8)
  | (25%nat, 1%nat) => constr:(@e25_1)
  | (26%nat, 1%nat) => constr:(@e26_1)
  end.
Ltac npeel_0 m B t :=
  lazymatch m with
  | 1%nat => constr:(t B)
  | S ?m' => lazymatch B with and ?A ?R => let t' := constr:(t A) in npeel_0 m' R t' end
  end.
Ltac nfl_0 m G H T := let lem := nelim_lemma 0%nat m in let t := npeel_0 m T lem in refine (t G _ H).
Ltac npeel_1 m B t :=
  lazymatch m with
  | 1%nat => constr:(t B)
  | S ?m' => lazymatch B with (fun x1 => and (@?A x1) (@?R x1)) => let t' := constr:(t A) in npeel_1 m' R t' end
  end.
Ltac nfl_1 m G H T := lazymatch T with (@ex ?T1 (fun x1 => (@?B x1))) => let lem := nelim_lemma 1%nat m in let t0 := constr:(lem T1) in let t := npeel_1 m B t0 in refine (t G _ H) end.
Ltac npeel_2 m B t :=
  lazymatch m with
  | 1%nat => constr:(t B)
  | S ?m' => lazymatch B with (fun x1 x2 => and (@?A x1 x2) (@?R x1 x2)) => let t' := constr:(t A) in npeel_2 m' R t' end
  end.
Ltac nfl_2 m G H T := lazymatch T with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@?B x1 x2))))) => let lem := nelim_lemma 2%nat m in let t0 := constr:(lem T1 T2) in let t := npeel_2 m B t0 in refine (t G _ H) end.
Ltac npeel_3 m B t :=
  lazymatch m with
  | 1%nat => constr:(t B)
  | S ?m' => lazymatch B with (fun x1 x2 x3 => and (@?A x1 x2 x3) (@?R x1 x2 x3)) => let t' := constr:(t A) in npeel_3 m' R t' end
  end.
Ltac nfl_3 m G H T := lazymatch T with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@?B x1 x2 x3))))))) => let lem := nelim_lemma 3%nat m in let t0 := constr:(lem T1 T2 T3) in let t := npeel_3 m B t0 in refine (t G _ H) end.
Ltac npeel_4 m B t :=
  lazymatch m with
  | 1%nat => constr:(t B)
  | S ?m' => lazymatch B with (fun x1 x2 x3 x4 => and (@?A x1 x2 x3 x4) (@?R x1 x2 x3 x4)) => let t' := constr:(t A) in npeel_4 m' R t' end
  end.
Ltac nfl_4 m G H T := lazymatch T with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@?B x1 x2 x3 x4))))))))) => let lem := nelim_lemma 4%nat m in let t0 := constr:(lem T1 T2 T3 T4) in let t := npeel_4 m B t0 in refine (t G _ H) end.
Ltac npeel_5 m B t :=
  lazymatch m with
  | 1%nat => constr:(t B)
  | S ?m' => lazymatch B with (fun x1 x2 x3 x4 x5 => and (@?A x1 x2 x3 x4 x5) (@?R x1 x2 x3 x4 x5)) => let t' := constr:(t A) in npeel_5 m' R t' end
  end.
Ltac nfl_5 m G H T := lazymatch T with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@?B x1 x2 x3 x4 x5))))))))))) => let lem := nelim_lemma 5%nat m in let t0 := constr:(lem T1 T2 T3 T4 T5) in let t := npeel_5 m B t0 in refine (t G _ H) end.
Ltac npeel_6 m B t :=
  lazymatch m with
  | 1%nat => constr:(t B)
  | S ?m' => lazymatch B with (fun x1 x2 x3 x4 x5 x6 => and (@?A x1 x2 x3 x4 x5 x6) (@?R x1 x2 x3 x4 x5 x6)) => let t' := constr:(t A) in npeel_6 m' R t' end
  end.
Ltac nfl_6 m G H T := lazymatch T with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@?B x1 x2 x3 x4 x5 x6))))))))))))) => let lem := nelim_lemma 6%nat m in let t0 := constr:(lem T1 T2 T3 T4 T5 T6) in let t := npeel_6 m B t0 in refine (t G _ H) end.
Ltac npeel_7 m B t :=
  lazymatch m with
  | 1%nat => constr:(t B)
  | S ?m' => lazymatch B with (fun x1 x2 x3 x4 x5 x6 x7 => and (@?A x1 x2 x3 x4 x5 x6 x7) (@?R x1 x2 x3 x4 x5 x6 x7)) => let t' := constr:(t A) in npeel_7 m' R t' end
  end.
Ltac nfl_7 m G H T := lazymatch T with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@?B x1 x2 x3 x4 x5 x6 x7))))))))))))))) => let lem := nelim_lemma 7%nat m in let t0 := constr:(lem T1 T2 T3 T4 T5 T6 T7) in let t := npeel_7 m B t0 in refine (t G _ H) end.
Ltac npeel_8 m B t :=
  lazymatch m with
  | 1%nat => constr:(t B)
  | S ?m' => lazymatch B with (fun x1 x2 x3 x4 x5 x6 x7 x8 => and (@?A x1 x2 x3 x4 x5 x6 x7 x8) (@?R x1 x2 x3 x4 x5 x6 x7 x8)) => let t' := constr:(t A) in npeel_8 m' R t' end
  end.
Ltac nfl_8 m G H T := lazymatch T with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@?B x1 x2 x3 x4 x5 x6 x7 x8))))))))))))))))) => let lem := nelim_lemma 8%nat m in let t0 := constr:(lem T1 T2 T3 T4 T5 T6 T7 T8) in let t := npeel_8 m B t0 in refine (t G _ H) end.
Ltac npeel_9 m B t :=
  lazymatch m with
  | 1%nat => constr:(t B)
  | S ?m' => lazymatch B with (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 => and (@?A x1 x2 x3 x4 x5 x6 x7 x8 x9) (@?R x1 x2 x3 x4 x5 x6 x7 x8 x9)) => let t' := constr:(t A) in npeel_9 m' R t' end
  end.
Ltac nfl_9 m G H T := lazymatch T with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@ex ?T9 (fun x9 => (@?B x1 x2 x3 x4 x5 x6 x7 x8 x9))))))))))))))))))) => let lem := nelim_lemma 9%nat m in let t0 := constr:(lem T1 T2 T3 T4 T5 T6 T7 T8 T9) in let t := npeel_9 m B t0 in refine (t G _ H) end.
Ltac npeel_10 m B t :=
  lazymatch m with
  | 1%nat => constr:(t B)
  | S ?m' => lazymatch B with (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 => and (@?A x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (@?R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)) => let t' := constr:(t A) in npeel_10 m' R t' end
  end.
Ltac nfl_10 m G H T := lazymatch T with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@ex ?T9 (fun x9 => (@ex ?T10 (fun x10 => (@?B x1 x2 x3 x4 x5 x6 x7 x8 x9 x10))))))))))))))))))))) => let lem := nelim_lemma 10%nat m in let t0 := constr:(lem T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) in let t := npeel_10 m B t0 in refine (t G _ H) end.
Ltac npeel_11 m B t :=
  lazymatch m with
  | 1%nat => constr:(t B)
  | S ?m' => lazymatch B with (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 => and (@?A x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (@?R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)) => let t' := constr:(t A) in npeel_11 m' R t' end
  end.
Ltac nfl_11 m G H T := lazymatch T with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@ex ?T9 (fun x9 => (@ex ?T10 (fun x10 => (@ex ?T11 (fun x11 => (@?B x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11))))))))))))))))))))))) => let lem := nelim_lemma 11%nat m in let t0 := constr:(lem T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) in let t := npeel_11 m B t0 in refine (t G _ H) end.
Ltac npeel_12 m B t :=
  lazymatch m with
  | 1%nat => constr:(t B)
  | S ?m' => lazymatch B with (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 => and (@?A x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) (@?R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)) => let t' := constr:(t A) in npeel_12 m' R t' end
  end.
Ltac nfl_12 m G H T := lazymatch T with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@ex ?T9 (fun x9 => (@ex ?T10 (fun x10 => (@ex ?T11 (fun x11 => (@ex ?T12 (fun x12 => (@?B x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12))))))))))))))))))))))))) => let lem := nelim_lemma 12%nat m in let t0 := constr:(lem T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) in let t := npeel_12 m B t0 in refine (t G _ H) end.
Ltac npeel_13 m B t :=
  lazymatch m with
  | 1%nat => constr:(t B)
  | S ?m' => lazymatch B with (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 => and (@?A x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) (@?R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)) => let t' := constr:(t A) in npeel_13 m' R t' end
  end.
Ltac nfl_13 m G H T := lazymatch T with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@ex ?T9 (fun x9 => (@ex ?T10 (fun x10 => (@ex ?T11 (fun x11 => (@ex ?T12 (fun x12 => (@ex ?T13 (fun x13 => (@?B x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13))))))))))))))))))))))))))) => let lem := nelim_lemma 13%nat m in let t0 := constr:(lem T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) in let t := npeel_13 m B t0 in refine (t G _ H) end.
Ltac npeel_14 m B t :=
  lazymatch m with
  | 1%nat => constr:(t B)
  | S ?m' => lazymatch B with (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 => and (@?A x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) (@?R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14)) => let t' := constr:(t A) in npeel_14 m' R t' end
  end.
Ltac nfl_14 m G H T := lazymatch T with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@ex ?T9 (fun x9 => (@ex ?T10 (fun x10 => (@ex ?T11 (fun x11 => (@ex ?T12 (fun x12 => (@ex ?T13 (fun x13 => (@ex ?T14 (fun x14 => (@?B x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14))))))))))))))))))))))))))))) => let lem := nelim_lemma 14%nat m in let t0 := constr:(lem T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) in let t := npeel_14 m B t0 in refine (t G _ H) end.
Ltac npeel_15 m B t :=
  lazymatch m with
  | 1%nat => constr:(t B)
  | S ?m' => lazymatch B with (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 => and (@?A x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) (@?R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15)) => let t' := constr:(t A) in npeel_15 m' R t' end
  end.
Ltac nfl_15 m G H T := lazymatch T with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@ex ?T9 (fun x9 => (@ex ?T10 (fun x10 => (@ex ?T11 (fun x11 => (@ex ?T12 (fun x12 => (@ex ?T13 (fun x13 => (@ex ?T14 (fun x14 => (@ex ?T15 (fun x15 => (@?B x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15))))))))))))))))))))))))))))))) => let lem := nelim_lemma 15%nat m in let t0 := constr:(lem T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15) in let t := npeel_15 m B t0 in refine (t G _ H) end.
Ltac npeel_16 m B t :=
  lazymatch m with
  | 1%nat => constr:(t B)
  | S ?m' => lazymatch B with (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 => and (@?A x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) (@?R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16)) => let t' := constr:(t A) in npeel_16 m' R t' end
  end.
Ltac nfl_16 m G H T := lazymatch T with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@ex ?T9 (fun x9 => (@ex ?T10 (fun x10 => (@ex ?T11 (fun x11 => (@ex ?T12 (fun x12 => (@ex ?T13 (fun x13 => (@ex ?T14 (fun x14 => (@ex ?T15 (fun x15 => (@ex ?T16 (fun x16 => (@?B x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16))))))))))))))))))))))))))))))))) => let lem := nelim_lemma 16%nat m in let t0 := constr:(lem T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16) in let t := npeel_16 m B t0 in refine (t G _ H) end.
Ltac npeel_17 m B t :=
  lazymatch m with
  | 1%nat => constr:(t B)
  | S ?m' => lazymatch B with (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 => and (@?A x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17) (@?R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17)) => let t' := constr:(t A) in npeel_17 m' R t' end
  end.
Ltac nfl_17 m G H T := lazymatch T with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@ex ?T9 (fun x9 => (@ex ?T10 (fun x10 => (@ex ?T11 (fun x11 => (@ex ?T12 (fun x12 => (@ex ?T13 (fun x13 => (@ex ?T14 (fun x14 => (@ex ?T15 (fun x15 => (@ex ?T16 (fun x16 => (@ex ?T17 (fun x17 => (@?B x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17))))))))))))))))))))))))))))))))))) => let lem := nelim_lemma 17%nat m in let t0 := constr:(lem T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17) in let t := npeel_17 m B t0 in refine (t G _ H) end.
Ltac npeel_18 m B t :=
  lazymatch m with
  | 1%nat => constr:(t B)
  | S ?m' => lazymatch B with (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 => and (@?A x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18) (@?R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18)) => let t' := constr:(t A) in npeel_18 m' R t' end
  end.
Ltac nfl_18 m G H T := lazymatch T with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@ex ?T9 (fun x9 => (@ex ?T10 (fun x10 => (@ex ?T11 (fun x11 => (@ex ?T12 (fun x12 => (@ex ?T13 (fun x13 => (@ex ?T14 (fun x14 => (@ex ?T15 (fun x15 => (@ex ?T16 (fun x16 => (@ex ?T17 (fun x17 => (@ex ?T18 (fun x18 => (@?B x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18))))))))))))))))))))))))))))))))))))) => let lem := nelim_lemma 18%nat m in let t0 := constr:(lem T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18) in let t := npeel_18 m B t0 in refine (t G _ H) end.
Ltac npeel_19 m B t :=
  lazymatch m with
  | 1%nat => constr:(t B)
  | S ?m' => lazymatch B with (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 => and (@?A x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19) (@?R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19)) => let t' := constr:(t A) in npeel_19 m' R t' end
  end.
Ltac nfl_19 m G H T := lazymatch T with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@ex ?T9 (fun x9 => (@ex ?T10 (fun x10 => (@ex ?T11 (fun x11 => (@ex ?T12 (fun x12 => (@ex ?T13 (fun x13 => (@ex ?T14 (fun x14 => (@ex ?T15 (fun x15 => (@ex ?T16 (fun x16 => (@ex ?T17 (fun x17 => (@ex ?T18 (fun x18 => (@ex ?T19 (fun x19 => (@?B x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19))))))))))))))))))))))))))))))))))))))) => let lem := nelim_lemma 19%nat m in let t0 := constr:(lem T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19) in let t := npeel_19 m B t0 in refine (t G _ H) end.
Ltac npeel_20 m B t :=
  lazymatch m with
  | 1%nat => constr:(t B)
  | S ?m' => lazymatch B with (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 => and (@?A x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20) (@?R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20)) => let t' := constr:(t A) in npeel_20 m' R t' end
  end.
Ltac nfl_20 m G H T := lazymatch T with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@ex ?T9 (fun x9 => (@ex ?T10 (fun x10 => (@ex ?T11 (fun x11 => (@ex ?T12 (fun x12 => (@ex ?T13 (fun x13 => (@ex ?T14 (fun x14 => (@ex ?T15 (fun x15 => (@ex ?T16 (fun x16 => (@ex ?T17 (fun x17 => (@ex ?T18 (fun x18 => (@ex ?T19 (fun x19 => (@ex ?T20 (fun x20 => (@?B x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20))))))))))))))))))))))))))))))))))))))))) => let lem := nelim_lemma 20%nat m in let t0 := constr:(lem T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20) in let t := npeel_20 m B t0 in refine (t G _ H) end.
Ltac npeel_21 m B t :=
  lazymatch m with
  | 1%nat => constr:(t B)
  | S ?m' => lazymatch B with (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 => and (@?A x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21) (@?R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21)) => let t' := constr:(t A) in npeel_21 m' R t' end
  end.
Ltac nfl_21 m G H T := lazymatch T with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@ex ?T9 (fun x9 => (@ex ?T10 (fun x10 => (@ex ?T11 (fun x11 => (@ex ?T12 (fun x12 => (@ex ?T13 (fun x13 => (@ex ?T14 (fun x14 => (@ex ?T15 (fun x15 => (@ex ?T16 (fun x16 => (@ex ?T17 (fun x17 => (@ex ?T18 (fun x18 => (@ex ?T19 (fun x19 => (@ex ?T20 (fun x20 => (@ex ?T21 (fun x21 => (@?B x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21))))))))))))))))))))))))))))))))))))))))))) => let lem := nelim_lemma 21%nat m in let t0 := constr:(lem T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21) in let t := npeel_21 m B t0 in refine (t G _ H) end.
Ltac npeel_22 m B t :=
  lazymatch m with
  | 1%nat => constr:(t B)
  | S ?m' => lazymatch B with (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 => and (@?A x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22) (@?R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22)) => let t' := constr:(t A) in npeel_22 m' R t' end
  end.
Ltac nfl_22 m G H T := lazymatch T with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@ex ?T9 (fun x9 => (@ex ?T10 (fun x10 => (@ex ?T11 (fun x11 => (@ex ?T12 (fun x12 => (@ex ?T13 (fun x13 => (@ex ?T14 (fun x14 => (@ex ?T15 (fun x15 => (@ex ?T16 (fun x16 => (@ex ?T17 (fun x17 => (@ex ?T18 (fun x18 => (@ex ?T19 (fun x19 => (@ex ?T20 (fun x20 => (@ex ?T21 (fun x21 => (@ex ?T22 (fun x22 => (@?B x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22))))))))))))))))))))))))))))))))))))))))))))) => let lem := nelim_lemma 22%nat m in let t0 := constr:(lem T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22) in let t := npeel_22 m B t0 in refine (t G _ H) end.
Ltac npeel_23 m B t :=
  lazymatch m with
  | 1%nat => constr:(t B)
  | S ?m' => lazymatch B with (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 => and (@?A x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23) (@?R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23)) => let t' := constr:(t A) in npeel_23 m' R t' end
  end.
Ltac nfl_23 m G H T := lazymatch T with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@ex ?T9 (fun x9 => (@ex ?T10 (fun x10 => (@ex ?T11 (fun x11 => (@ex ?T12 (fun x12 => (@ex ?T13 (fun x13 => (@ex ?T14 (fun x14 => (@ex ?T15 (fun x15 => (@ex ?T16 (fun x16 => (@ex ?T17 (fun x17 => (@ex ?T18 (fun x18 => (@ex ?T19 (fun x19 => (@ex ?T20 (fun x20 => (@ex ?T21 (fun x21 => (@ex ?T22 (fun x22 => (@ex ?T23 (fun x23 => (@?B x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23))))))))))))))))))))))))))))))))))))))))))))))) => let lem := nelim_lemma 23%nat m in let t0 := constr:(lem T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23) in let t := npeel_23 m B t0 in refine (t G _ H) end.
Ltac npeel_24 m B t :=
  lazymatch m with
  | 1%nat => constr:(t B)
  | S ?m' => lazymatch B with (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 => and (@?A x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24) (@?R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24)) => let t' := constr:(t A) in npeel_24 m' R t' end
  end.
Ltac nfl_24 m G H T := lazymatch T with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@ex ?T9 (fun x9 => (@ex ?T10 (fun x10 => (@ex ?T11 (fun x11 => (@ex ?T12 (fun x12 => (@ex ?T13 (fun x13 => (@ex ?T14 (fun x14 => (@ex ?T15 (fun x15 => (@ex ?T16 (fun x16 => (@ex ?T17 (fun x17 => (@ex ?T18 (fun x18 => (@ex ?T19 (fun x19 => (@ex ?T20 (fun x20 => (@ex ?T21 (fun x21 => (@ex ?T22 (fun x22 => (@ex ?T23 (fun x23 => (@ex ?T24 (fun x24 => (@?B x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24))))))))))))))))))))))))))))))))))))))))))))))))) => let lem := nelim_lemma 24%nat m in let t0 := constr:(lem T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24) in let t := npeel_24 m B t0 in refine (t G _ H) end.
Ltac npeel_25 m B t :=
  lazymatch m with
  | 1%nat => constr:(t B)
  | S ?m' => lazymatch B with (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 => and (@?A x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25) (@?R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25)) => let t' := constr:(t A) in npeel_25 m' R t' end
  end.
Ltac nfl_25 m G H T := lazymatch T with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@ex ?T9 (fun x9 => (@ex ?T10 (fun x10 => (@ex ?T11 (fun x11 => (@ex ?T12 (fun x12 => (@ex ?T13 (fun x13 => (@ex ?T14 (fun x14 => (@ex ?T15 (fun x15 => (@ex ?T16 (fun x16 => (@ex ?T17 (fun x17 => (@ex ?T18 (fun x18 => (@ex ?T19 (fun x19 => (@ex ?T20 (fun x20 => (@ex ?T21 (fun x21 => (@ex ?T22 (fun x22 => (@ex ?T23 (fun x23 => (@ex ?T24 (fun x24 => (@ex ?T25 (fun x25 => (@?B x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25))))))))))))))))))))))))))))))))))))))))))))))))))) => let lem := nelim_lemma 25%nat m in let t0 := constr:(lem T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25) in let t := npeel_25 m B t0 in refine (t G _ H) end.
Ltac npeel_26 m B t :=
  lazymatch m with
  | 1%nat => constr:(t B)
  | S ?m' => lazymatch B with (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 => and (@?A x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26) (@?R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26)) => let t' := constr:(t A) in npeel_26 m' R t' end
  end.
Ltac nfl_26 m G H T := lazymatch T with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@ex ?T9 (fun x9 => (@ex ?T10 (fun x10 => (@ex ?T11 (fun x11 => (@ex ?T12 (fun x12 => (@ex ?T13 (fun x13 => (@ex ?T14 (fun x14 => (@ex ?T15 (fun x15 => (@ex ?T16 (fun x16 => (@ex ?T17 (fun x17 => (@ex ?T18 (fun x18 => (@ex ?T19 (fun x19 => (@ex ?T20 (fun x20 => (@ex ?T21 (fun x21 => (@ex ?T22 (fun x22 => (@ex ?T23 (fun x23 => (@ex ?T24 (fun x24 => (@ex ?T25 (fun x25 => (@ex ?T26 (fun x26 => (@?B x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26))))))))))))))))))))))))))))))))))))))))))))))))))))) => let lem := nelim_lemma 26%nat m in let t0 := constr:(lem T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26) in let t := npeel_26 m B t0 in refine (t G _ H) end.
Ltac nelim_fast_km k m G H T :=
  lazymatch k with
  | 0%nat => nfl_0 m G H T
  | 1%nat => nfl_1 m G H T
  | 2%nat => nfl_2 m G H T
  | 3%nat => nfl_3 m G H T
  | 4%nat => nfl_4 m G H T
  | 5%nat => nfl_5 m G H T
  | 6%nat => nfl_6 m G H T
  | 7%nat => nfl_7 m G H T
  | 8%nat => nfl_8 m G H T
  | 9%nat => nfl_9 m G H T
  | 10%nat => nfl_10 m G H T
  | 11%nat => nfl_11 m G H T
  | 12%nat => nfl_12 m G H T
  | 13%nat => nfl_13 m G H T
  | 14%nat => nfl_14 m G H T
  | 15%nat => nfl_15 m G H T
  | 16%nat => nfl_16 m G H T
  | 17%nat => nfl_17 m G H T
  | 18%nat => nfl_18 m G H T
  | 19%nat => nfl_19 m G H T
  | 20%nat => nfl_20 m G H T
  | 21%nat => nfl_21 m G H T
  | 22%nat => nfl_22 m G H T
  | 23%nat => nfl_23 m G H T
  | 24%nat => nfl_24 m G H T
  | 25%nat => nfl_25 m G H T
  | 26%nat => nfl_26 m G H T
  end.
Ltac nelim_fast_n n G H T :=
  lazymatch n with
  | 2%nat => first [ nfl_1 1%nat G H T | nfl_0 2%nat G H T ]
  | 3%nat => first [ nfl_2 1%nat G H T | nfl_1 2%nat G H T | nfl_0 3%nat G H T ]
  | 4%nat => first [ nfl_3 1%nat G H T | nfl_2 2%nat G H T | nfl_1 3%nat G H T | nfl_0 4%nat G H T ]
  | 5%nat => first [ nfl_4 1%nat G H T | nfl_3 2%nat G H T | nfl_2 3%nat G H T | nfl_1 4%nat G H T | nfl_0 5%nat G H T ]
  | 6%nat => first [ nfl_5 1%nat G H T | nfl_3 3%nat G H T | nfl_2 4%nat G H T | nfl_1 5%nat G H T | nfl_0 6%nat G H T ]
  | 7%nat => first [ nfl_6 1%nat G H T | nfl_3 4%nat G H T | nfl_2 5%nat G H T | nfl_1 6%nat G H T | nfl_0 7%nat G H T ]
  | 8%nat => first [ nfl_7 1%nat G H T | nfl_2 6%nat G H T | nfl_0 8%nat G H T ]
  | 9%nat => first [ nfl_8 1%nat G H T | nfl_7 2%nat G H T | nfl_3 6%nat G H T | nfl_2 7%nat G H T | nfl_0 9%nat G H T ]
  | 10%nat => first [ nfl_9 1%nat G H T | nfl_4 6%nat G H T | nfl_2 8%nat G H T | nfl_0 10%nat G H T ]
  | 11%nat => first [ nfl_10 1%nat G H T | nfl_7 4%nat G H T | nfl_4 7%nat G H T | nfl_2 9%nat G H T | nfl_0 11%nat G H T ]
  | 12%nat => first [ nfl_11 1%nat G H T | nfl_2 10%nat G H T | nfl_0 12%nat G H T ]
  | 13%nat => first [ nfl_12 1%nat G H T | nfl_7 6%nat G H T | nfl_2 11%nat G H T | nfl_0 13%nat G H T ]
  | 14%nat => first [ nfl_13 1%nat G H T | nfl_0 14%nat G H T ]
  | 15%nat => first [ nfl_14 1%nat G H T | nfl_10 5%nat G H T | nfl_0 15%nat G H T ]
  | 16%nat => first [ nfl_15 1%nat G H T | nfl_0 16%nat G H T ]
  | 17%nat => first [ nfl_16 1%nat G H T | nfl_12 5%nat G H T | nfl_0 17%nat G H T ]
  | 18%nat => first [ nfl_17 1%nat G H T | nfl_8 10%nat G H T | nfl_0 18%nat G H T ]
  | 19%nat => first [ nfl_18 1%nat G H T | nfl_15 4%nat G H T | nfl_0 19%nat G H T ]
  | 20%nat => first [ nfl_19 1%nat G H T | nfl_18 2%nat G H T | nfl_15 5%nat G H T | nfl_0 20%nat G H T ]
  | 21%nat => first [ nfl_20 1%nat G H T | nfl_16 5%nat G H T | nfl_15 6%nat G H T | nfl_0 21%nat G H T ]
  | 22%nat => first [ nfl_21 1%nat G H T | nfl_19 3%nat G H T | nfl_17 5%nat G H T | nfl_16 6%nat G H T | nfl_0 22%nat G H T ]
  | 23%nat => first [ nfl_22 1%nat G H T | nfl_19 4%nat G H T | nfl_17 6%nat G H T | nfl_16 7%nat G H T | nfl_15 8%nat G H T | nfl_0 23%nat G H T ]
  | 24%nat => first [ nfl_23 1%nat G H T | nfl_20 4%nat G H T | nfl_15 9%nat G H T | nfl_0 24%nat G H T ]
  | 25%nat => first [ nfl_24 1%nat G H T | nfl_20 5%nat G H T | nfl_18 7%nat G H T | nfl_17 8%nat G H T ]
  | 26%nat => first [ nfl_25 1%nat G H T | nfl_17 9%nat G H T ]
  | 27%nat => first [ nfl_26 1%nat G H T | nfl_23 4%nat G H T | nfl_20 7%nat G H T | nfl_19 8%nat G H T | nfl_18 9%nat G H T ]
  | 28%nat => first [ nfl_5 23%nat G H T ]
  | 29%nat => first [ nfl_20 9%nat G H T | nfl_19 10%nat G H T | nfl_18 11%nat G H T ]
  | 30%nat => first [ nfl_20 10%nat G H T ]
  | 31%nat => first [ nfl_20 11%nat G H T ]
  | 32%nat => first [ nfl_24 8%nat G H T | nfl_21 11%nat G H T | nfl_20 12%nat G H T ]
  | 33%nat => first [ nfl_21 12%nat G H T ]
  end.

(* [comment removed for export] *)
Ltac nelim_direct k m G H :=
  lazymatch constr:((k, m)) with
  | (0%nat, 2%nat) => refine (e0_2 G _ H)
  | (0%nat, 3%nat) => refine (e0_3 G _ H)
  | (0%nat, 4%nat) => refine (e0_4 G _ H)
  | (0%nat, 5%nat) => refine (e0_5 G _ H)
  | (0%nat, 6%nat) => refine (e0_6 G _ H)
  | (0%nat, 7%nat) => refine (e0_7 G _ H)
  | (0%nat, 8%nat) => refine (e0_8 G _ H)
  | (0%nat, 9%nat) => refine (e0_9 G _ H)
  | (0%nat, 10%nat) => refine (e0_10 G _ H)
  | (0%nat, 11%nat) => refine (e0_11 G _ H)
  | (0%nat, 12%nat) => refine (e0_12 G _ H)
  | (0%nat, 13%nat) => refine (e0_13 G _ H)
  | (0%nat, 14%nat) => refine (e0_14 G _ H)
  | (0%nat, 15%nat) => refine (e0_15 G _ H)
  | (0%nat, 16%nat) => refine (e0_16 G _ H)
  | (0%nat, 17%nat) => refine (e0_17 G _ H)
  | (0%nat, 18%nat) => refine (e0_18 G _ H)
  | (0%nat, 19%nat) => refine (e0_19 G _ H)
  | (0%nat, 20%nat) => refine (e0_20 G _ H)
  | (0%nat, 21%nat) => refine (e0_21 G _ H)
  | (0%nat, 22%nat) => refine (e0_22 G _ H)
  | (0%nat, 23%nat) => refine (e0_23 G _ H)
  | (0%nat, 24%nat) => refine (e0_24 G _ H)
  | (1%nat, 1%nat) => refine (e1_1 G _ H)
  | (1%nat, 2%nat) => refine (e1_2 G _ H)
  | (1%nat, 3%nat) => refine (e1_3 G _ H)
  | (1%nat, 4%nat) => refine (e1_4 G _ H)
  | (1%nat, 5%nat) => refine (e1_5 G _ H)
  | (1%nat, 6%nat) => refine (e1_6 G _ H)
  | (2%nat, 1%nat) => refine (e2_1 G _ H)
  | (2%nat, 2%nat) => refine (e2_2 G _ H)
  | (2%nat, 3%nat) => refine (e2_3 G _ H)
  | (2%nat, 4%nat) => refine (e2_4 G _ H)
  | (2%nat, 5%nat) => refine (e2_5 G _ H)
  | (2%nat, 6%nat) => refine (e2_6 G _ H)
  | (2%nat, 7%nat) => refine (e2_7 G _ H)
  | (2%nat, 8%nat) => refine (e2_8 G _ H)
  | (2%nat, 9%nat) => refine (e2_9 G _ H)
  | (2%nat, 10%nat) => refine (e2_10 G _ H)
  | (2%nat, 11%nat) => refine (e2_11 G _ H)
  | (3%nat, 1%nat) => refine (e3_1 G _ H)
  | (3%nat, 2%nat) => refine (e3_2 G _ H)
  | (3%nat, 3%nat) => refine (e3_3 G _ H)
  | (3%nat, 4%nat) => refine (e3_4 G _ H)
  | (3%nat, 6%nat) => refine (e3_6 G _ H)
  | (4%nat, 1%nat) => refine (e4_1 G _ H)
  | (4%nat, 6%nat) => refine (e4_6 G _ H)
  | (4%nat, 7%nat) => refine (e4_7 G _ H)
  | (5%nat, 1%nat) => refine (e5_1 G _ H)
  | (5%nat, 23%nat) => refine (e5_23 G _ H)
  | (6%nat, 1%nat) => refine (e6_1 G _ H)
  | (7%nat, 1%nat) => refine (e7_1 G _ H)
  | (7%nat, 2%nat) => refine (e7_2 G _ H)
  | (7%nat, 4%nat) => refine (e7_4 G _ H)
  | (7%nat, 6%nat) => refine (e7_6 G _ H)
  | (8%nat, 1%nat) => refine (e8_1 G _ H)
  | (8%nat, 10%nat) => refine (e8_10 G _ H)
  | (9%nat, 1%nat) => refine (e9_1 G _ H)
  | (10%nat, 1%nat) => refine (e10_1 G _ H)
  | (10%nat, 5%nat) => refine (e10_5 G _ H)
  | (11%nat, 1%nat) => refine (e11_1 G _ H)
  | (12%nat, 1%nat) => refine (e12_1 G _ H)
  | (12%nat, 5%nat) => refine (e12_5 G _ H)
  | (13%nat, 1%nat) => refine (e13_1 G _ H)
  | (14%nat, 1%nat) => refine (e14_1 G _ H)
  | (15%nat, 1%nat) => refine (e15_1 G _ H)
  | (15%nat, 4%nat) => refine (e15_4 G _ H)
  | (15%nat, 5%nat) => refine (e15_5 G _ H)
  | (15%nat, 6%nat) => refine (e15_6 G _ H)
  | (15%nat, 8%nat) => refine (e15_8 G _ H)
  | (15%nat, 9%nat) => refine (e15_9 G _ H)
  | (16%nat, 1%nat) => refine (e16_1 G _ H)
  | (16%nat, 5%nat) => refine (e16_5 G _ H)
  | (16%nat, 6%nat) => refine (e16_6 G _ H)
  | (16%nat, 7%nat) => refine (e16_7 G _ H)
  | (17%nat, 1%nat) => refine (e17_1 G _ H)
  | (17%nat, 5%nat) => refine (e17_5 G _ H)
  | (17%nat, 6%nat) => refine (e17_6 G _ H)
  | (17%nat, 8%nat) => refine (e17_8 G _ H)
  | (17%nat, 9%nat) => refine (e17_9 G _ H)
  | (18%nat, 1%nat) => refine (e18_1 G _ H)
  | (18%nat, 2%nat) => refine (e18_2 G _ H)
  | (18%nat, 7%nat) => refine (e18_7 G _ H)
  | (18%nat, 9%nat) => refine (e18_9 G _ H)
  | (18%nat, 11%nat) => refine (e18_11 G _ H)
  | (19%nat, 1%nat) => refine (e19_1 G _ H)
  | (19%nat, 3%nat) => refine (e19_3 G _ H)
  | (19%nat, 4%nat) => refine (e19_4 G _ H)
  | (19%nat, 8%nat) => refine (e19_8 G _ H)
  | (19%nat, 10%nat) => refine (e19_10 G _ H)
  | (20%nat, 1%nat) => refine (e20_1 G _ H)
  | (20%nat, 4%nat) => refine (e20_4 G _ H)
  | (20%nat, 5%nat) => refine (e20_5 G _ H)
  | (20%nat, 7%nat) => refine (e20_7 G _ H)
  | (20%nat, 9%nat) => refine (e20_9 G _ H)
  | (20%nat, 10%nat) => refine (e20_10 G _ H)
  | (20%nat, 11%nat) => refine (e20_11 G _ H)
  | (20%nat, 12%nat) => refine (e20_12 G _ H)
  | (21%nat, 1%nat) => refine (e21_1 G _ H)
  | (21%nat, 11%nat) => refine (e21_11 G _ H)
  | (21%nat, 12%nat) => refine (e21_12 G _ H)
  | (22%nat, 1%nat) => refine (e22_1 G _ H)
  | (23%nat, 1%nat) => refine (e23_1 G _ H)
  | (23%nat, 4%nat) => refine (e23_4 G _ H)
  | (24%nat, 1%nat) => refine (e24_1 G _ H)
  | (24%nat, 8%nat) => refine (e24_8 G _ H)
  | (25%nat, 1%nat) => refine (e25_1 G _ H)
  | (26%nat, 1%nat) => refine (e26_1 G _ H)
  end.


(* [comment removed for export] *)
Ltac nel_conj T n :=
  lazymatch n with
  | 1%nat => constr:((1%nat, 1%nat))
  | S ?n' =>
      let T' := eval hnf in T in
      lazymatch T' with
      | and _ ?B => let res := nel_conj B n' in lazymatch res with (?m, ?r) => constr:((S m, r)) end
      | _ => constr:((1%nat, n))
      end
  end.

Ltac nel_ex T n :=
  lazymatch n with
  | 1%nat => constr:((0%nat, 1%nat, 1%nat))
  | S ?n' =>
      let T' := eval hnf in T in
      lazymatch T' with
      | @ex ?A ?P =>
          let res := constr:(fun x : A => ltac:(let B := eval cbv beta in (P x) in let r := nel_ex B n' in exact r)) in
          lazymatch res with (fun _ => (?k, ?m, ?r)) => constr:((S k, m, r)) end
      | and _ _ => let res := nel_conj T' n in lazymatch res with (?m, ?r) => constr:((0%nat, m, r)) end
      end
  end.

Ltac nel_intros cnt tac :=
  lazymatch cnt with
  | O => tac ()
  | S ?c => let x := fresh "nelx" in intro x; nel_intros c tac; revert x
  end.

Ltac nel_log k m r := idtac.   (* [comment removed for export] *)
Ltac nelim_slow H n T :=
  let res := nel_ex T n in
  lazymatch res with
  | (?k, ?m, ?r) =>
      nel_log k m r;
      lazymatch goal with |- ?G =>
        first [ nelim_fast_km k m G H T
              | nelim_direct k m G H
              | (* [comment removed for export] *)
                nelim_direct k 1%nat G H;
                nel_intros k ltac:(fun _ => let Hb := fresh "nelH" in intro Hb;
                                    lazymatch goal with |- ?G2 => nelim_direct 0%nat m G2 Hb end; clear Hb) ];
        lazymatch r with
        | 1%nat => idtac
        | _ => let c := eval cbv in (pred (k + m))%nat in
               nel_intros c ltac:(fun _ => let H2 := fresh "nelH" in intro H2; nelim_term H2 r; clear H2)
        end
      end
  end
with nelim_term H n :=
  let T0 := type of H in
  let T := eval hnf in T0 in
  first [ lazymatch goal with |- ?G => nelim_fast_n n G H T end | nelim_slow H n T ].

(* [comment removed for export] *)
Ltac nelim H n := nelim_term H n; try (is_var H; clear H).
Ltac nelimp H n := nelim_term H n.

Ltac do_nat k tac := lazymatch k with O => idtac | S ?k' => tac (); do_nat k' tac end.

(* [comment removed for export] *)
Ltac nel_conj_syn T := lazymatch T with and _ ?B => let m := nel_conj_syn B in constr:(S m) | _ => constr:(1%nat) end.
Ltac nel_ex_syn T :=
  lazymatch T with
  | @ex ?A ?P => let res := constr:(fun x : A => ltac:(let B := eval cbv beta in (P x) in let r := nel_ex_syn B in exact r)) in
                 lazymatch res with (fun _ => (?k, ?m)) => constr:((S k, m)) end
  | _ => let m := nel_conj_syn T in constr:((0%nat, m))
  end.
Ltac nelim_all H :=
  let T := type of H in
  let res := nel_ex_syn T in
  lazymatch res with
  | (?k, ?m) => let n := eval cbv in (k + m)%nat in
                lazymatch n with
                | 1%nat => fail "nelim_all: nothing to eliminate"
                | _ => nelim H n; do_nat n ltac:(fun _ => intro)
                end
  end.

(* [comment removed for export] *)
Fixpoint nintro (ts : ntele) : narr ts Prop -> Prop -> Prop :=
  match ts with ntnil => fun B C => B -> C | ntcons T ts' => fun B C => forall x : T, nintro ts' (B x) C end.
Definition NISTMT (k : nat) : Prop := nallT k (fun ts => forall B : narr ts Prop, nintro ts B (nexk ts B)).

Ltac nel_istmt k := let t := eval cbv beta iota delta [NISTMT nallT nintro nexk narr] in (NISTMT k) in exact t.
Lemma i1 : ltac:(nel_istmt 1%nat).
Proof. intros; repeat eexists; eassumption. Qed.
Lemma i2 : ltac:(nel_istmt 2%nat).
Proof. intros; repeat eexists; eassumption. Qed.
Lemma i3 : ltac:(nel_istmt 3%nat).
Proof. intros; repeat eexists; eassumption. Qed.
Lemma i4 : ltac:(nel_istmt 4%nat).
Proof. intros; repeat eexists; eassumption. Qed.
Lemma i5 : ltac:(nel_istmt 5%nat).
Proof. intros; repeat eexists; eassumption. Qed.
Lemma i6 : ltac:(nel_istmt 6%nat).
Proof. intros; repeat eexists; eassumption. Qed.
Lemma i7 : ltac:(nel_istmt 7%nat).
Proof. intros; repeat eexists; eassumption. Qed.
Lemma i8 : ltac:(nel_istmt 8%nat).
Proof. intros; repeat eexists; eassumption. Qed.
Lemma i9 : ltac:(nel_istmt 9%nat).
Proof. intros; repeat eexists; eassumption. Qed.
Lemma i10 : ltac:(nel_istmt 10%nat).
Proof. intros; repeat eexists; eassumption. Qed.
Lemma i11 : ltac:(nel_istmt 11%nat).
Proof. intros; repeat eexists; eassumption. Qed.
Lemma i12 : ltac:(nel_istmt 12%nat).
Proof. intros; repeat eexists; eassumption. Qed.
Lemma i13 : ltac:(nel_istmt 13%nat).
Proof. intros; repeat eexists; eassumption. Qed.
Lemma i14 : ltac:(nel_istmt 14%nat).
Proof. intros; repeat eexists; eassumption. Qed.
Lemma i15 : ltac:(nel_istmt 15%nat).
Proof. intros; repeat eexists; eassumption. Qed.
Lemma i16 : ltac:(nel_istmt 16%nat).
Proof. intros; repeat eexists; eassumption. Qed.
Lemma i17 : ltac:(nel_istmt 17%nat).
Proof. intros; repeat eexists; eassumption. Qed.
Lemma i18 : ltac:(nel_istmt 18%nat).
Proof. intros; repeat eexists; eassumption. Qed.
Lemma i19 : ltac:(nel_istmt 19%nat).
Proof. intros; repeat eexists; eassumption. Qed.
Lemma i20 : ltac:(nel_istmt 20%nat).
Proof. intros; repeat eexists; eassumption. Qed.
Lemma i21 : ltac:(nel_istmt 21%nat).
Proof. intros; repeat eexists; eassumption. Qed.
Lemma i22 : ltac:(nel_istmt 22%nat).
Proof. intros; repeat eexists; eassumption. Qed.
Lemma i23 : ltac:(nel_istmt 23%nat).
Proof. intros; repeat eexists; eassumption. Qed.
Lemma i24 : ltac:(nel_istmt 24%nat).
Proof. intros; repeat eexists; eassumption. Qed.
Lemma i25 : ltac:(nel_istmt 25%nat).
Proof. intros; repeat eexists; eassumption. Qed.
Lemma i26 : ltac:(nel_istmt 26%nat).
Proof. intros; repeat eexists; eassumption. Qed.
Ltac nexists_fast k G :=
  lazymatch k with
  | 2%nat => lazymatch G with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@?B x1 x2))))) => refine (@i2 T1 T2 B _ _ _) end
  | 3%nat => lazymatch G with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@?B x1 x2 x3))))))) => refine (@i3 T1 T2 T3 B _ _ _ _) end
  | 4%nat => lazymatch G with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@?B x1 x2 x3 x4))))))))) => refine (@i4 T1 T2 T3 T4 B _ _ _ _ _) end
  | 5%nat => lazymatch G with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@?B x1 x2 x3 x4 x5))))))))))) => refine (@i5 T1 T2 T3 T4 T5 B _ _ _ _ _ _) end
  | 6%nat => lazymatch G with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@?B x1 x2 x3 x4 x5 x6))))))))))))) => refine (@i6 T1 T2 T3 T4 T5 T6 B _ _ _ _ _ _ _) end
  | 7%nat => lazymatch G with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@?B x1 x2 x3 x4 x5 x6 x7))))))))))))))) => refine (@i7 T1 T2 T3 T4 T5 T6 T7 B _ _ _ _ _ _ _ _) end
  | 8%nat => lazymatch G with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@?B x1 x2 x3 x4 x5 x6 x7 x8))))))))))))))))) => refine (@i8 T1 T2 T3 T4 T5 T6 T7 T8 B _ _ _ _ _ _ _ _ _) end
  | 9%nat => lazymatch G with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@ex ?T9 (fun x9 => (@?B x1 x2 x3 x4 x5 x6 x7 x8 x9))))))))))))))))))) => refine (@i9 T1 T2 T3 T4 T5 T6 T7 T8 T9 B _ _ _ _ _ _ _ _ _ _) end
  | 10%nat => lazymatch G with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@ex ?T9 (fun x9 => (@ex ?T10 (fun x10 => (@?B x1 x2 x3 x4 x5 x6 x7 x8 x9 x10))))))))))))))))))))) => refine (@i10 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 B _ _ _ _ _ _ _ _ _ _ _) end
  | 11%nat => lazymatch G with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@ex ?T9 (fun x9 => (@ex ?T10 (fun x10 => (@ex ?T11 (fun x11 => (@?B x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11))))))))))))))))))))))) => refine (@i11 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 B _ _ _ _ _ _ _ _ _ _ _ _) end
  | 12%nat => lazymatch G with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@ex ?T9 (fun x9 => (@ex ?T10 (fun x10 => (@ex ?T11 (fun x11 => (@ex ?T12 (fun x12 => (@?B x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12))))))))))))))))))))))))) => refine (@i12 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 B _ _ _ _ _ _ _ _ _ _ _ _ _) end
  | 13%nat => lazymatch G with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@ex ?T9 (fun x9 => (@ex ?T10 (fun x10 => (@ex ?T11 (fun x11 => (@ex ?T12 (fun x12 => (@ex ?T13 (fun x13 => (@?B x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13))))))))))))))))))))))))))) => refine (@i13 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 B _ _ _ _ _ _ _ _ _ _ _ _ _ _) end
  | 14%nat => lazymatch G with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@ex ?T9 (fun x9 => (@ex ?T10 (fun x10 => (@ex ?T11 (fun x11 => (@ex ?T12 (fun x12 => (@ex ?T13 (fun x13 => (@ex ?T14 (fun x14 => (@?B x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14))))))))))))))))))))))))))))) => refine (@i14 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end
  | 15%nat => lazymatch G with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@ex ?T9 (fun x9 => (@ex ?T10 (fun x10 => (@ex ?T11 (fun x11 => (@ex ?T12 (fun x12 => (@ex ?T13 (fun x13 => (@ex ?T14 (fun x14 => (@ex ?T15 (fun x15 => (@?B x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15))))))))))))))))))))))))))))))) => refine (@i15 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end
  | 16%nat => lazymatch G with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@ex ?T9 (fun x9 => (@ex ?T10 (fun x10 => (@ex ?T11 (fun x11 => (@ex ?T12 (fun x12 => (@ex ?T13 (fun x13 => (@ex ?T14 (fun x14 => (@ex ?T15 (fun x15 => (@ex ?T16 (fun x16 => (@?B x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16))))))))))))))))))))))))))))))))) => refine (@i16 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end
  | 17%nat => lazymatch G with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@ex ?T9 (fun x9 => (@ex ?T10 (fun x10 => (@ex ?T11 (fun x11 => (@ex ?T12 (fun x12 => (@ex ?T13 (fun x13 => (@ex ?T14 (fun x14 => (@ex ?T15 (fun x15 => (@ex ?T16 (fun x16 => (@ex ?T17 (fun x17 => (@?B x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17))))))))))))))))))))))))))))))))))) => refine (@i17 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end
  | 18%nat => lazymatch G with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@ex ?T9 (fun x9 => (@ex ?T10 (fun x10 => (@ex ?T11 (fun x11 => (@ex ?T12 (fun x12 => (@ex ?T13 (fun x13 => (@ex ?T14 (fun x14 => (@ex ?T15 (fun x15 => (@ex ?T16 (fun x16 => (@ex ?T17 (fun x17 => (@ex ?T18 (fun x18 => (@?B x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18))))))))))))))))))))))))))))))))))))) => refine (@i18 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end
  | 19%nat => lazymatch G with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@ex ?T9 (fun x9 => (@ex ?T10 (fun x10 => (@ex ?T11 (fun x11 => (@ex ?T12 (fun x12 => (@ex ?T13 (fun x13 => (@ex ?T14 (fun x14 => (@ex ?T15 (fun x15 => (@ex ?T16 (fun x16 => (@ex ?T17 (fun x17 => (@ex ?T18 (fun x18 => (@ex ?T19 (fun x19 => (@?B x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19))))))))))))))))))))))))))))))))))))))) => refine (@i19 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end
  | 20%nat => lazymatch G with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@ex ?T9 (fun x9 => (@ex ?T10 (fun x10 => (@ex ?T11 (fun x11 => (@ex ?T12 (fun x12 => (@ex ?T13 (fun x13 => (@ex ?T14 (fun x14 => (@ex ?T15 (fun x15 => (@ex ?T16 (fun x16 => (@ex ?T17 (fun x17 => (@ex ?T18 (fun x18 => (@ex ?T19 (fun x19 => (@ex ?T20 (fun x20 => (@?B x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20))))))))))))))))))))))))))))))))))))))))) => refine (@i20 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end
  | 21%nat => lazymatch G with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@ex ?T9 (fun x9 => (@ex ?T10 (fun x10 => (@ex ?T11 (fun x11 => (@ex ?T12 (fun x12 => (@ex ?T13 (fun x13 => (@ex ?T14 (fun x14 => (@ex ?T15 (fun x15 => (@ex ?T16 (fun x16 => (@ex ?T17 (fun x17 => (@ex ?T18 (fun x18 => (@ex ?T19 (fun x19 => (@ex ?T20 (fun x20 => (@ex ?T21 (fun x21 => (@?B x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21))))))))))))))))))))))))))))))))))))))))))) => refine (@i21 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end
  | 22%nat => lazymatch G with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@ex ?T9 (fun x9 => (@ex ?T10 (fun x10 => (@ex ?T11 (fun x11 => (@ex ?T12 (fun x12 => (@ex ?T13 (fun x13 => (@ex ?T14 (fun x14 => (@ex ?T15 (fun x15 => (@ex ?T16 (fun x16 => (@ex ?T17 (fun x17 => (@ex ?T18 (fun x18 => (@ex ?T19 (fun x19 => (@ex ?T20 (fun x20 => (@ex ?T21 (fun x21 => (@ex ?T22 (fun x22 => (@?B x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22))))))))))))))))))))))))))))))))))))))))))))) => refine (@i22 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end
  | 23%nat => lazymatch G with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@ex ?T9 (fun x9 => (@ex ?T10 (fun x10 => (@ex ?T11 (fun x11 => (@ex ?T12 (fun x12 => (@ex ?T13 (fun x13 => (@ex ?T14 (fun x14 => (@ex ?T15 (fun x15 => (@ex ?T16 (fun x16 => (@ex ?T17 (fun x17 => (@ex ?T18 (fun x18 => (@ex ?T19 (fun x19 => (@ex ?T20 (fun x20 => (@ex ?T21 (fun x21 => (@ex ?T22 (fun x22 => (@ex ?T23 (fun x23 => (@?B x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23))))))))))))))))))))))))))))))))))))))))))))))) => refine (@i23 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end
  | 24%nat => lazymatch G with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@ex ?T9 (fun x9 => (@ex ?T10 (fun x10 => (@ex ?T11 (fun x11 => (@ex ?T12 (fun x12 => (@ex ?T13 (fun x13 => (@ex ?T14 (fun x14 => (@ex ?T15 (fun x15 => (@ex ?T16 (fun x16 => (@ex ?T17 (fun x17 => (@ex ?T18 (fun x18 => (@ex ?T19 (fun x19 => (@ex ?T20 (fun x20 => (@ex ?T21 (fun x21 => (@ex ?T22 (fun x22 => (@ex ?T23 (fun x23 => (@ex ?T24 (fun x24 => (@?B x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24))))))))))))))))))))))))))))))))))))))))))))))))) => refine (@i24 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end
  | 25%nat => lazymatch G with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@ex ?T9 (fun x9 => (@ex ?T10 (fun x10 => (@ex ?T11 (fun x11 => (@ex ?T12 (fun x12 => (@ex ?T13 (fun x13 => (@ex ?T14 (fun x14 => (@ex ?T15 (fun x15 => (@ex ?T16 (fun x16 => (@ex ?T17 (fun x17 => (@ex ?T18 (fun x18 => (@ex ?T19 (fun x19 => (@ex ?T20 (fun x20 => (@ex ?T21 (fun x21 => (@ex ?T22 (fun x22 => (@ex ?T23 (fun x23 => (@ex ?T24 (fun x24 => (@ex ?T25 (fun x25 => (@?B x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25))))))))))))))))))))))))))))))))))))))))))))))))))) => refine (@i25 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end
  | 26%nat => lazymatch G with (@ex ?T1 (fun x1 => (@ex ?T2 (fun x2 => (@ex ?T3 (fun x3 => (@ex ?T4 (fun x4 => (@ex ?T5 (fun x5 => (@ex ?T6 (fun x6 => (@ex ?T7 (fun x7 => (@ex ?T8 (fun x8 => (@ex ?T9 (fun x9 => (@ex ?T10 (fun x10 => (@ex ?T11 (fun x11 => (@ex ?T12 (fun x12 => (@ex ?T13 (fun x13 => (@ex ?T14 (fun x14 => (@ex ?T15 (fun x15 => (@ex ?T16 (fun x16 => (@ex ?T17 (fun x17 => (@ex ?T18 (fun x18 => (@ex ?T19 (fun x19 => (@ex ?T20 (fun x20 => (@ex ?T21 (fun x21 => (@ex ?T22 (fun x22 => (@ex ?T23 (fun x23 => (@ex ?T24 (fun x24 => (@ex ?T25 (fun x25 => (@ex ?T26 (fun x26 => (@?B x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26))))))))))))))))))))))))))))))))))))))))))))))))))))) => refine (@i26 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end
  end.
Ltac nexists k := first [ lazymatch goal with |- ?G0 => let G := eval hnf in G0 in nexists_fast k G end | do_nat k ltac:(fun _ => eexists) ].

(* [comment removed for export] *)
Ltac nfx_2 G PO T := nfl_2 1%nat G PO T; clear PO; do 2 (let x := fresh "x" in intro x); intro PO.
Ltac nfx_3 G PO T := nfl_3 1%nat G PO T; clear PO; do 3 (let x := fresh "x" in intro x); intro PO.
Ltac nfx_4 G PO T := nfl_4 1%nat G PO T; clear PO; do 4 (let x := fresh "x" in intro x); intro PO.
Ltac nfx_5 G PO T := nfl_5 1%nat G PO T; clear PO; do 5 (let x := fresh "x" in intro x); intro PO.
Ltac nfx_6 G PO T := nfl_6 1%nat G PO T; clear PO; do 6 (let x := fresh "x" in intro x); intro PO.
Ltac nfx_7 G PO T := nfl_7 1%nat G PO T; clear PO; do 7 (let x := fresh "x" in intro x); intro PO.
Ltac nfx_8 G PO T := nfl_8 1%nat G PO T; clear PO; do 8 (let x := fresh "x" in intro x); intro PO.
Ltac nfx_9 G PO T := nfl_9 1%nat G PO T; clear PO; do 9 (let x := fresh "x" in intro x); intro PO.
Ltac nfx_10 G PO T := nfl_10 1%nat G PO T; clear PO; do 10 (let x := fresh "x" in intro x); intro PO.
Ltac nfx_11 G PO T := nfl_11 1%nat G PO T; clear PO; do 11 (let x := fresh "x" in intro x); intro PO.
Ltac nfx_12 G PO T := nfl_12 1%nat G PO T; clear PO; do 12 (let x := fresh "x" in intro x); intro PO.
Ltac nfx_13 G PO T := nfl_13 1%nat G PO T; clear PO; do 13 (let x := fresh "x" in intro x); intro PO.
Ltac nfx_14 G PO T := nfl_14 1%nat G PO T; clear PO; do 14 (let x := fresh "x" in intro x); intro PO.
Ltac nfx_15 G PO T := nfl_15 1%nat G PO T; clear PO; do 15 (let x := fresh "x" in intro x); intro PO.
Ltac nfx_16 G PO T := nfl_16 1%nat G PO T; clear PO; do 16 (let x := fresh "x" in intro x); intro PO.
Ltac nfx_17 G PO T := nfl_17 1%nat G PO T; clear PO; do 17 (let x := fresh "x" in intro x); intro PO.
Ltac nfx_18 G PO T := nfl_18 1%nat G PO T; clear PO; do 18 (let x := fresh "x" in intro x); intro PO.
Ltac nfx_19 G PO T := nfl_19 1%nat G PO T; clear PO; do 19 (let x := fresh "x" in intro x); intro PO.
Ltac nfx_20 G PO T := nfl_20 1%nat G PO T; clear PO; do 20 (let x := fresh "x" in intro x); intro PO.
Ltac nfx_21 G PO T := nfl_21 1%nat G PO T; clear PO; do 21 (let x := fresh "x" in intro x); intro PO.
Ltac nfx_22 G PO T := nfl_22 1%nat G PO T; clear PO; do 22 (let x := fresh "x" in intro x); intro PO.
Ltac nfx_23 G PO T := nfl_23 1%nat G PO T; clear PO; do 23 (let x := fresh "x" in intro x); intro PO.
Ltac nfx_24 G PO T := nfl_24 1%nat G PO T; clear PO; do 24 (let x := fresh "x" in intro x); intro PO.
Ltac nfx_25 G PO T := nfl_25 1%nat G PO T; clear PO; do 25 (let x := fresh "x" in intro x); intro PO.
Ltac nfx_26 G PO T := nfl_26 1%nat G PO T; clear PO; do 26 (let x := fresh "x" in intro x); intro PO.
Ltac nel_exs PO T := lazymatch goal with |- ?G => first [ nfx_26 G PO T | nfx_25 G PO T | nfx_24 G PO T | nfx_23 G PO T | nfx_22 G PO T | nfx_21 G PO T | nfx_20 G PO T | nfx_19 G PO T | nfx_18 G PO T | nfx_17 G PO T | nfx_16 G PO T | nfx_15 G PO T | nfx_14 G PO T | nfx_13 G PO T | nfx_12 G PO T | nfx_11 G PO T | nfx_10 G PO T | nfx_9 G PO T | nfx_8 G PO T | nfx_7 G PO T | nfx_6 G PO T | nfx_5 G PO T | nfx_4 G PO T | nfx_3 G PO T | nfx_2 G PO T ] end.
Ltac destruct_exs_n PO :=
  let T := type of PO in let T' := eval hnf in T in
  lazymatch T' with
  | ex _ => first [ nel_exs PO T' | let x := fresh "x" in destruct PO as [x PO] ]; destruct_exs_n PO
  | _ => idtac
  end.
