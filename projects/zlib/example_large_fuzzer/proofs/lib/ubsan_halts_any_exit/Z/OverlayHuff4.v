(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import Wf_nat.
From Stdlib Require Import Permutation.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayHuff1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayHuff2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayHuff3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma fib_nat_step n : fib_nat (S (S n)) = fib_nat (S n) + fib_nat n.
Proof. reflexivity. Qed.
Lemma fib_nat_nonneg n : 0 <= fib_nat n.
Proof. induction n as [n IH] using lt_wf_ind. destruct n as [|[|n]]; [cbn; lia|cbn; lia|]. rewrite fib_nat_step. pose proof (IH n ltac:(lia)). pose proof (IH (S n) ltac:(lia)). lia. Qed.
Lemma fib_step d : 0 <= d -> fib (d + 2) = fib (d + 1) + fib d.
Proof. intros. unfold fib. replace (Z.to_nat (d + 2)) with (S (S (Z.to_nat d))) by lia. replace (Z.to_nat (d + 1)) with (S (Z.to_nat d)) by lia. apply fib_nat_step. Qed.
Lemma fib_nonneg d : 0 <= fib d. Proof. unfold fib. apply fib_nat_nonneg. Qed.

Lemma fib_1 : fib 1 = 1. Proof. reflexivity. Qed.
Lemma fib_2 : fib 2 = 1. Proof. reflexivity. Qed.

Section GTree.
Variable g : gtree.
Hypothesis G : gtree_ok g.

Notation lo := (g_lo g).
Notation hi := (g_hi g).
Notation par := (g_par g).
Notation leaf := (g_leaf g).
Notation wt := (g_wt g).
Notation ext := (g_ext g).
Notation depth := (g_depth g).
Notation leaves := (leaves g).
Let allpos_in := allpos_in g G. Let nonroot_in := nonroot_in g G. Let leaves_in := leaves_in g G.
Let depth_step := depth_step g G. Let wt_nonneg := wt_nonneg g G.
Let depth_nonneg := depth_nonneg g G. Let depth_root := depth_root g G. Let lohi := lohi g G.
Let root_internal := root_internal g G. Let ext_mono := ext_mono g G. Let leaves_nodup := leaves_nodup g.


Definition Dmax : Z := lmax (fun i => depth i) leaves.



Lemma sib_ge_children a s c : lo < a <= hi -> lo < s <= hi -> s <> a -> par s = par a ->
  lo < c <= hi -> par c = a -> wt c <= wt s.
Proof.
  intros Ha Hs NE Ps Hc Pc.
  assert (c <> s) by (intros ->; pose proof (go_par_lt g G a Ha); rewrite Pc in Ps; lia).
  pose proof (go_ext_par g G c Hc ltac:(rewrite Pc; lia)) as E1. rewrite Pc in E1.
  assert (ext c <> ext s) by (intros E; apply H; apply (go_ext_inj g G); auto).
  destruct (go_ext_sib g G a s Ha Hs ltac:(auto) ltac:(auto)) as [E|E]; apply ext_mono; auto; lia.
Qed.

Lemma fib_inv x s : lo < x <= hi -> lo < s <= hi -> s <> x -> par s = par x ->
  fib (depth x + 1) * wt x + fib (depth x) * wt s <= g_W g.
Proof.
  intros Hx. remember (Z.to_nat (x - lo)) as n eqn:E. revert x Hx E s.
  induction n as [n IH] using lt_wf_ind; intros x Hx E s Hs NE Ps.
  pose proof (go_par_lt g G x Hx) as P. rewrite (depth_step x Hx).
  destruct (sibling g G x Hx) as (s' & Hs' & NEs' & Ps' & ONLY & _ & Wp).
  assert (s' = s) by (destruct (ONLY s Hs Ps) as [->| ->]; [congruence|reflexivity]). subst s'.
  destruct (Z.eq_dec (par x) lo) as [R|NR].
  -
    rewrite R in Wp. rewrite R. rewrite depth_root. replace (1 + 0 + 1) with 2 by lia. replace (1 + 0) with 1 by lia.
    rewrite fib_1, fib_2. unfold g_W. lia.
  -
    destruct (sibling g G (par x) ltac:(lia)) as (t & Ht & NEt & Pt & _ & _ & _).
    pose proof (IH (Z.to_nat (par x - lo)) ltac:(lia) (par x) ltac:(lia) eq_refl t Ht NEt Pt) as IHp.
    pose proof (sib_ge_children (par x) t x ltac:(lia) Ht NEt Pt Hx eq_refl) as TX.
    pose proof (depth_nonneg (par x) ltac:(lia)) as D0.
    rewrite Wp in IHp.
    replace (1 + depth (par x) + 1) with (depth (par x) + 2) by lia. replace (1 + depth (par x)) with (depth (par x) + 1) by lia.
    rewrite fib_step by lia.
    pose proof (fib_nonneg (depth (par x))). pose proof (fib_nonneg (depth (par x) + 1)).
    pose proof (wt_nonneg x ltac:(lia)). pose proof (wt_nonneg s ltac:(lia)). nia.
Qed.

Theorem fib_bound x : lo <= x <= hi -> fib (depth x + 1) * wt x <= g_W g.
Proof.
  intros Hx. destruct (Z.eq_dec x lo) as [->|NE].
  - rewrite depth_root. replace (0 + 1) with 1 by lia. rewrite fib_1. unfold g_W. lia.
  - destruct (sibling g G x ltac:(lia)) as (s & Hs & NEs & Ps & _).
    pose proof (fib_inv x s ltac:(lia) Hs NEs Ps). pose proof (fib_nonneg (depth x)). pose proof (wt_nonneg s ltac:(lia)). nia.
Qed.

End GTree.
