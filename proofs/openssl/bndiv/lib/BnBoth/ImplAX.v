(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Malloc Prog BnBase BnModel BnTree BnInv.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import ARun ImplA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma safe_assoc_inv : forall {ptr A B C} (t : btree ptr A) (f : A -> btree ptr B) (g : B -> btree ptr C) X Q,
  safe (tbind (tbind t f) g) X Q -> safe (tbind t (fun a => tbind (f a) g)) X Q.
Proof.
  intros ptr A B C t. induction t as [a| |n k IH|p k IH]; intros f g X Q H; cbn [safe tbind] in *.
  - exact H.
  - exact H.
  - destruct H as (Hn & H). split; [exact Hn|]. intros q Hq. apply IH. apply H. exact Hq.
  - destruct H as (m & X' & E & H). exists m, X'. split; [exact E|]. apply IH. exact H.
Qed.

Lemma bbind_get : forall {B} r (f : bignum bptr -> BM (M := btree bptr) B) (ls : lstate bptr),
  bbind (tree_ops bptr) (bget (tree_ops bptr) r) f ls = f (getbn r ls) ls.
Proof. reflexivity. Qed.

Lemma bbind_set : forall {B} r b (f : unit -> BM (M := btree bptr) B) (ls : lstate bptr),
  bbind (tree_ops bptr) (bset (tree_ops bptr) r b) f ls = f tt (setbn r b ls).
Proof. reflexivity. Qed.

Lemma bbind_get_set : forall {B} r (g : bignum bptr -> bignum bptr) (f : unit -> BM (M := btree bptr) B) (ls : lstate bptr),
  bbind (tree_ops bptr) (bbind (tree_ops bptr) (bget (tree_ops bptr) r) (fun b => bset (tree_ops bptr) r (g b))) f ls =
  f tt (setbn r (g (getbn r ls)) ls).
Proof. reflexivity. Qed.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).

Lemma implA_assoc : forall {A B C} (t : btree bptr A) (f : A -> btree bptr B) (g : B -> btree bptr C) Σ
    (Q : C -> rts RT -> machine_state -> Prop) ms,
  implA (tbind t (fun a => tbind (f a) g)) Σ Q ms -> implA (tbind (tbind t f) g) Σ Q ms.
Proof. intros A B C t f g Σ Q ms H X Φ S. apply (H X Φ). apply safe_assoc_inv. exact S. Qed.

End WithRT.
