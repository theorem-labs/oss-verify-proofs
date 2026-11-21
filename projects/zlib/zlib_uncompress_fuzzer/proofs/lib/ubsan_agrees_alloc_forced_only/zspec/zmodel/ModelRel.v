(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import Prog ZIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


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



















Section SRel.
  Context {St : Type}.





















End SRel.





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

Lemma forZ_ind : forall {A} (P : Z -> A -> Prop) lo hi (body : Z -> A -> A) a,
  (forall i x, lo <= i < hi -> P i x -> P (i + 1) (body i x)) ->
  P lo a -> lo <= hi -> P hi (forZ lo hi body a).
Proof.
  intros A P lo hi body a Hb Ha Hle.
  apply (proj1 (B := forZ lo hi body a = forZ lo hi body a)).
  apply (forZ_rel (fun i x y => P i x /\ x = y) lo hi body body a a); [|split; [exact Ha|reflexivity]|exact Hle].
  intros i x y Hi [Hp He]. subst y. split; [apply Hb; assumption | reflexivity].
Qed.


Definition agree {A : Type} (n : Z) (a1 a2 : parr A) : Prop :=
  arr_len a1 = arr_len a2 /\ forall i, 0 <= i < n -> arr_get a1 i = arr_get a2 i.

Section Agree.
  Context {A : Type}.
  Implicit Types a : parr A.



















End Agree.










