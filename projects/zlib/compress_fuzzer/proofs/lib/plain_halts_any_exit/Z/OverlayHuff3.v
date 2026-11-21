(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import Wf_nat.
From Stdlib Require Import Permutation.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import OverlayIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import OverlayHuff1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import OverlayHuff2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

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
Notation allpos := (allpos g).
Notation nonroot := (nonroot g).
Notation leaves := (leaves g).
Notation internals := (internals g).
Let allpos_in := allpos_in g G. Let nonroot_in := nonroot_in g G. Let leaves_in := leaves_in g G.
Let internals_in := internals_in g G. Let depth_step := depth_step g G. Let wt_nonneg := wt_nonneg g G.
Let depth_nonneg := depth_nonneg g G. Let depth_root := depth_root g G. Let lohi := lohi g G.
Let root_internal := root_internal g G. Let ext_mono := ext_mono g G.
Let allpos_nodup := allpos_nodup g. Let nonroot_nodup := nonroot_nodup g. Let leaves_nodup := leaves_nodup g.

Definition born (x : Z) : Z :=
  if leaf x then 0 else 1 + lmax (fun c => if par c =? x then ext c else 0) nonroot.

Definition alive (T x : Z) : bool := (born x <=? T) && ((x =? lo) || (T <=? ext x)).
Definition forest (T : Z) : list Z := filter (alive T) allpos.

Definition rest (T : Z) : Z := lsum (fun p => if negb (leaf p) && (T <? born p) then wt p else 0) allpos.
Definition Tend : Z := born lo.

Lemma sibling a : lo < a <= hi ->
  exists b, lo < b <= hi /\ b <> a /\ par b = par a /\
            (forall c, lo < c <= hi -> par c = par a -> c = a \/ c = b) /\
            (ext a = ext b + 1 \/ ext b = ext a + 1) /\ wt (par a) = wt a + wt b.
Proof.
  intros Ha. pose proof (go_par_lt g G a Ha) as P. pose proof (go_par_int g G a Ha) as I.
  destruct (go_two g G (par a) ltac:(unfold g_pos; lia) I) as (u & v & NE & Hu & Hv & Pu & Pv & ONLY).
  assert (W := go_wt_sum g G (par a) u v ltac:(unfold g_pos; lia) I Hu Hv NE Pu Pv).
  destruct (ONLY a Ha eq_refl) as [E|E].
  - subst u. exists v. split; [exact Hv|]. split; [congruence|]. split; [congruence|]. split.
    { intros c Hc Pc. destruct (ONLY c Hc ltac:(congruence)); auto. }
    split; [|congruence]. apply (go_ext_sib g G); auto; congruence.
  - subst v. exists u. split; [exact Hu|]. split; [congruence|]. split; [congruence|]. split.
    { intros c Hc Pc. destruct (ONLY c Hc ltac:(congruence)); auto. }
    split; [apply (go_ext_sib g G); auto; congruence|]. lia.
Qed.

Section Round.
Variable T : Z.
Variable a : Z.
Variable b : Z.
Hypothesis Ha : lo < a <= hi.
Hypothesis Hb : lo < b <= hi.
Hypothesis NEab : a <> b.
Hypothesis Pab : par b = par a.
Hypothesis Ea : ext a = T.
Hypothesis Eb : ext b = T + 1.
Hypothesis ONLY : forall c, lo < c <= hi -> par c = par a -> c = a \/ c = b.

Let p := par a.

Lemma T0 : 0 <= T. Proof. rewrite <- Ea. apply (go_ext_nonneg g G). exact Ha. Qed.

End Round.

Variable K : Z.
Hypothesis Kpos : 0 <= K.

Definition Q (T : Z) : Prop := forall sg, code_ok K sg (forest T) -> rest T <= csum wt sg (forest T).

Definition mid (T : Z) : Prop :=
  exists a b, lo < a <= hi /\ lo < b <= hi /\ a <> b /\ par b = par a /\ ext a = T - 1 /\ ext b = T.

End GTree.
