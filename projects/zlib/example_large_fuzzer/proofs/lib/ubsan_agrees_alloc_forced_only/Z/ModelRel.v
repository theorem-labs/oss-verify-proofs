(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint mrel {A B : Type} (Q : A -> B -> Prop) (m1 : M A) (m2 : M B) : Prop :=
  match m1 with
  | MRet a => match m2 with MRet b => Q a b | _ => False end
  | MOut bs1 k1 => match m2 with MOut bs2 k2 => bs1 = bs2 /\ mrel Q k1 k2 | _ => False end
  | MExit c1 => match m2 with MExit c2 => c1 = c2 | _ => False end
  | MTry k1 => match m2 with MTry k2 => forall b, mrel Q (k1 b) (k2 b) | _ => False end
  end.

Section MRel.
  Context {A B : Type}.

End MRel.

Lemma mrel_bind : forall {A B C D : Type} (Q : A -> B -> Prop) (R : C -> D -> Prop)
    (m1 : M A) (m2 : M B) (f1 : A -> M C) (f2 : B -> M D),
  mrel Q m1 m2 ->
  (forall a b, Q a b -> mrel R (f1 a) (f2 b)) ->
  mrel R (mbind m1 f1) (mbind m2 f2).
Proof.
  intros A B C D Q R m1. induction m1 as [a|bs k IH|c|k IH]; intros m2 f1 f2 H Hf; destruct m2; cbn in *; try contradiction.
  - apply Hf. exact H.
  - destruct H as [-> H]. split; [reflexivity|]. apply IH; assumption.
  - exact H.
  - intro b. apply IH; [apply H | exact Hf].
Qed.

Lemma mrel_trans : forall {A B C : Type} (Q : A -> B -> Prop) (R : B -> C -> Prop)
    (m1 : M A) (m2 : M B) (m3 : M C),
  mrel Q m1 m2 -> mrel R m2 m3 -> mrel (fun a c => exists b, Q a b /\ R b c) m1 m3.
Proof.
  intros A B C Q R m1. induction m1 as [a|bs k IH|c|k IH]; intros m2 m3 H12 H23;
    destruct m2; cbn in *; try contradiction; destruct m3; cbn in *; try contradiction.
  - exists a0. split; assumption.
  - destruct H12 as [-> H12]. destruct H23 as [-> H23]. split; [reflexivity|]. eapply IH; eassumption.
  - congruence.
  - intro b. eapply IH; [apply H12 | apply H23].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint mall {A : Type} (P : A -> Prop) (m : M A) : Prop :=
  match m with
  | MRet a => P a
  | MOut _ k => mall P k
  | MExit _ => True
  | MTry k => forall b, mall P (k b)
  end.

Lemma mall_bind : forall {A B} (P : A -> Prop) (R : B -> Prop) (m : M A) (f : A -> M B),
  mall P m -> (forall a, P a -> mall R (f a)) -> mall R (mbind m f).
Proof.
  intros A B P R m. induction m as [a|bs k IH|c|k IH]; intros f H Hf; cbn in *.
  - apply Hf. exact H.
  - apply IH; assumption.
  - exact I.
  - intro b. apply IH; [apply H | exact Hf].
Qed.

Lemma mall_true : forall {A} (m : M A), mall (fun _ => True) m.
Proof. intros A m. induction m; cbn; auto. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition prod_rel {A1 A2 B1 B2 : Type} (RA : A1 -> A2 -> Prop) (RB : B1 -> B2 -> Prop)
  (p : A1 * B1) (q : A2 * B2) : Prop := RA (fst p) (fst q) /\ RB (snd p) (snd q).

Definition sum_rel {A1 A2 B1 B2 : Type} (RA : A1 -> A2 -> Prop) (RB : B1 -> B2 -> Prop)
  (p : A1 + B1) (q : A2 + B2) : Prop :=
  match p, q with
  | inl a, inl b => RA a b
  | inr a, inr b => RB a b
  | _, _ => False
  end.

Definition opt_rel {A1 A2 : Type} (RA : A1 -> A2 -> Prop) (p : option A1) (q : option A2) : Prop :=
  match p, q with
  | Some a, Some b => RA a b
  | None, None => True
  | _, _ => False
  end.

(* [comment removed for export] *)
Definition st_rel {St A B : Type} (R : A -> B -> Prop) (p : A * St) (q : B * St) : Prop :=
  R (fst p) (fst q) /\ snd p = snd q.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section SRel.
  Context {St : Type}.

  Definition srel {A B : Type} (R : A -> B -> Prop) (m1 : SM St A) (m2 : SM St B) : Prop :=
    forall s, mrel (st_rel R) (m1 s) (m2 s).

  (* [comment removed for export] *)
  Definition sall {A : Type} (I : St -> Prop) (P : A -> St -> Prop) (m : SM St A) : Prop :=
    forall s, I s -> mall (fun p => P (fst p) (snd p)) (m s).

  Lemma srel_ret : forall {A B} (R : A -> B -> Prop) (a : A) (b : B),
    R a b -> srel R (sret a) (sret b).
  Proof. intros A B R a b H s. cbn. split; [exact H | reflexivity]. Qed.

  Lemma srel_bind : forall {A B C D} (Q : A -> B -> Prop) (R : C -> D -> Prop)
      (m1 : SM St A) (m2 : SM St B) (f1 : A -> SM St C) (f2 : B -> SM St D),
    srel Q m1 m2 ->
    (forall a b, Q a b -> srel R (f1 a) (f2 b)) ->
    srel R (sbind m1 f1) (sbind m2 f2).
  Proof.
    intros A B C D Q R m1 m2 f1 f2 Hm Hf s. unfold sbind.
    eapply mrel_bind; [apply Hm|].
    intros [a s1] [b s2] [H1 H2]; cbn in *. subst s2. apply Hf. exact H1.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

End SRel.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma forZ_unfold : forall {A} lo hi (body : Z -> A -> A) a,
  forZ lo hi body a = if lo <? hi then forZ (lo + 1) hi body (body lo a) else a.
Proof.
  intros A lo hi body a. unfold forZ.
  destruct (Z.ltb_spec lo hi).
  - rewrite loopZ_step by lia. rewrite (proj2 (Z.ltb_lt lo hi)) by lia.
    replace (hi - lo - 1) with (hi - (lo + 1)) by lia. reflexivity.
  - rewrite loopZ_le0 by lia. reflexivity.
Qed.

Lemma forZ_rel : forall {A1 A2} (RA : Z -> A1 -> A2 -> Prop)
    lo hi (body1 : Z -> A1 -> A1) (body2 : Z -> A2 -> A2) a1 a2,
  (forall i a b, lo <= i < hi -> RA i a b -> RA (i + 1) (body1 i a) (body2 i b)) ->
  RA lo a1 a2 ->
  lo <= hi ->
  RA hi (forZ lo hi body1 a1) (forZ lo hi body2 a2).
Proof.
  intros A1 A2 RA lo hi body1 body2 a1 a2 Hb Ha Hle.
  remember (Z.to_nat (hi - lo)) as n eqn:Hn.
  revert lo a1 a2 Hb Ha Hle Hn. induction n as [|n IH]; intros lo a1 a2 Hb Ha Hle Hn.
  - assert (lo = hi) by lia. subst lo.
    rewrite (forZ_unfold hi hi body1), (forZ_unfold hi hi body2).
    rewrite (proj2 (Z.ltb_ge hi hi)) by lia. exact Ha.
  - rewrite (forZ_unfold lo hi body1), (forZ_unfold lo hi body2). rewrite (proj2 (Z.ltb_lt lo hi)) by lia.
    apply IH; [| apply Hb; [lia | exact Ha] | lia | lia].
    intros i x y Hi Hr. apply Hb; [lia | exact Hr].
Qed.

(* [comment removed for export] *)
Lemma forZ_ind : forall {A} (P : Z -> A -> Prop) lo hi (body : Z -> A -> A) a,
  (forall i x, lo <= i < hi -> P i x -> P (i + 1) (body i x)) ->
  P lo a -> lo <= hi -> P hi (forZ lo hi body a).
Proof.
  intros A P lo hi body a Hb Ha Hle.
  apply (proj1 (B := forZ lo hi body a = forZ lo hi body a)).
  apply (forZ_rel (fun i x y => P i x /\ x = y) lo hi body body a a); [|split; [exact Ha|reflexivity]|exact Hle].
  intros i x y Hi [Hp He]. subst y. split; [apply Hb; assumption | reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition agree {A : Type} (n : Z) (a1 a2 : parr A) : Prop :=
  arr_len a1 = arr_len a2 /\ forall i, 0 <= i < n -> arr_get a1 i = arr_get a2 i.

Section Agree.
  Context {A : Type}.
  Implicit Types a : parr A.

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

End Agree.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mall_sbind : forall {St A B} (P : A * St -> Prop) (R : B * St -> Prop)
    (m : SM St A) (f : A -> SM St B) s,
  mall P (m s) -> (forall a s', P (a, s') -> mall R (f a s')) -> mall R (sbind m f s).
Proof.
  intros St A B P R m f s Hm Hf. unfold sbind. eapply mall_bind; [exact Hm|].
  intros [a s'] H. apply Hf. exact H.
Qed.

Lemma mall_sbind_any : forall {St A B} (R : B * St -> Prop) (m : SM St A) (f : A -> SM St B) s,
  (forall a s', mall R (f a s')) -> mall R (sbind m f s).
Proof.
  intros St A B R m f s Hf. apply (mall_sbind (fun _ => True)); [apply mall_true|]. intros a s' _. apply Hf.
Qed.

(* [comment removed for export] *)

