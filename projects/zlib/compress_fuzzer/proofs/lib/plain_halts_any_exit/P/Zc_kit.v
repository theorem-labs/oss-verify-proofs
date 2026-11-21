(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim ZApi ZHarness ZApiL ZHarnessL ZApiC ZHarnessC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Inductive Box (P : Prop) : Prop := box : P -> Box P.
Lemma unbox : forall P : Prop, Box P -> P.
Proof. intros P [H]. exact H. Qed.

Lemma zstore_nil : forall (l : list Z) o, zstore l o [] = l.
Proof. intros l o. reflexivity. Qed.

Section C2.
Variable za : zapiC.
Definition c2_after (n : nat) (x : c2L za) : option (c2L za * Z) :=
  match iterNL n (c2_stepP za) x with inl _ => None | inr r => r end.

Lemma c2_loop_after : forall N src level,
  c2_loop za N src level = c2_after (Z.to_nat (C2_FUEL N (zlength src))) (c2_x0 za N src level).
Proof. intros. unfold c2_loop, c2_after. rewrite iterZL_nat. destruct (iterNL _ _ _) as [a|r]; reflexivity. Qed.

Lemma c2_after_S : forall n x, c2_after (S n) x = match c2_stepP za x with inl x' => c2_after n x' | inr r => r end.
Proof. intros n x. unfold c2_after. cbn [iterNL]. destruct (c2_stepP za x) as [x'|r]; reflexivity. Qed.

Lemma c2_after_O : forall x, c2_after O x = None.
Proof. intros x. reflexivity. Qed.
End C2.
