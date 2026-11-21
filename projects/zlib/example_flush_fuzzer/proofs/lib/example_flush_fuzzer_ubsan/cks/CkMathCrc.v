(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Lia Bool Btauto.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.cks Require Import CkTables CkModel CkXt CkMultmodp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).


Definition bytes (bs : list Z) : Prop := Forall (fun b => 0 <= b < 256) bs.





Lemma firstn_add_skipn : forall {A} (a b : nat) (l : list A),
  firstn a l ++ firstn b (skipn a l) = firstn (a + b) l.
Proof.
  intros A a. induction a as [|a IH]; intros b l; [reflexivity|].
  destruct l as [|x l]; cbn; [now rewrite firstn_nil | now rewrite IH].
Qed.









Lemma land_255 : forall x, Z.land x 255 = x mod 256.
Proof. intros x. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.














Lemma xtnl_locked : { f : nat -> Z -> Z | f = xtn }. Proof. exists xtn. reflexivity. Qed.
Definition xtnl : nat -> Z -> Z := proj1_sig xtnl_locked.

Definition comb5 (x0 x1 x2 x3 x4 : Z) : Z :=
  Z.lxor (xtnl 160 x0) (Z.lxor (xtnl 128 x1) (Z.lxor (xtnl 96 x2) (Z.lxor (xtnl 64 x3) (xtnl 32 x4)))).







Definition binv (l0 l1 l2 l3 l4 q : Z) : Prop := comb5 l0 l1 l2 l3 l4 = xtnl 160 q.







































