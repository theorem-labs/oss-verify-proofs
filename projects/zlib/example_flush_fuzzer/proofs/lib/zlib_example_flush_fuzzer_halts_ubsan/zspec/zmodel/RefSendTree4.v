(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees TreeModel ScanModel SendModel RefSendTree3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Walk.
Variables (PBL : Z) (ds : deflate_state) (t : tree_id) (mc : Z).
Local Notation L i := (Len ds t i).

Definition SL (s : deflate_state) (n pl c k mx mn : Z) : deflate_state :=
  send_tree_loop (Z.to_nat (mc + 1 - n)) s t mc n pl c k mx mn.
Definition OK (s : deflate_state) (n pl c k mx mn : Z) : Prop :=
  send_tree_ok PBL (Z.to_nat (mc + 1 - n)) s t mc n pl c k mx mn.

Lemma SL_step : forall s n pl c k mx mn, 0 <= n <= mc -> 1 <= mn ->
  SL s n pl c k mx mn =
    (let nl := Len s t (n + 1) in
     if (k + 1 <? mx) && (c =? nl) then SL s (n + 1) pl nl (k + 1) mx mn
     else let '(mx', mn') := tree_counts c nl in
          SL (sbs_run s (st_calls s mn c pl (k + 1))) (n + 1) c nl 0 mx' mn').
Proof.
  intros s n pl c k mx mn Hn Hmn. unfold SL.
  replace (Z.to_nat (mc + 1 - n)) with (Datatypes.S (Z.to_nat (mc + 1 - (n + 1)))) by lia.
  rewrite send_loop_S by exact Hmn. replace (n <=? mc) with true by (symmetry; apply Z.leb_le; lia). cbv zeta.
  destruct ((k + 1 <? mx) && (c =? Len s t (n + 1))); [reflexivity|].
  destruct (tree_counts c (Len s t (n + 1))); reflexivity.
Qed.

Lemma SL_out : forall s n pl c k mx mn, mc < n -> SL s n pl c k mx mn = s.
Proof. intros. unfold SL. apply send_loop_out. lia. Qed.

Lemma OK_step : forall s n pl c k mx mn, 0 <= n <= mc ->
  OK s n pl c k mx mn ->
    (let nl := Len s t (n + 1) in
     if (k + 1 <? mx) && (c =? nl) then OK s (n + 1) pl nl (k + 1) mx mn
     else let '(mx', mn') := tree_counts c nl in
          sbs_ok PBL s (st_calls s mn c pl (k + 1))
          /\ OK (sbs_run s (st_calls s mn c pl (k + 1))) (n + 1) c nl 0 mx' mn').
Proof.
  intros s n pl c k mx mn Hn H. unfold OK in *.
  replace (Z.to_nat (mc + 1 - n)) with (Datatypes.S (Z.to_nat (mc + 1 - (n + 1)))) in H by lia.
  cbn [send_tree_ok] in H. replace (n <=? mc) with true in H by (symmetry; apply Z.leb_le; lia).
  cbv zeta in H. exact H.
Qed.

Definition cnts (pl c : Z) : Z * Z := if c =? 0 then (138, 3) else if c =? pl then (6, 3) else (7, 4).

Lemma cnts_tree_counts : forall c nl, tree_counts c nl = cnts c nl.
Proof. intros c nl. unfold tree_counts, cnts. rewrite (Z.eqb_sym c nl). reflexivity. Qed.

Definition BND (pl c k mx mn : Z) : Prop :=
  (pl = -1 \/ 0 <= pl <= 15) /\ 0 <= c <= 15 /\ 0 <= k < mx /\ (mx, mn) = cnts pl c.

Lemma BND_facts : forall pl c k mx mn, BND pl c k mx mn ->
  (mx = 138 \/ mx = 6 \/ mx = 7) /\ (mn = 3 \/ mn = 4) /\ (c = 0 -> mn = 3) /\ (c <> 0 -> c <> pl -> mn = 4).
Proof.
  intros pl c k mx mn (_ & _ & _ & E). unfold cnts in E.
  destruct (Z.eqb_spec c 0); [injection E; intros; subst; lia|].
  destruct (Z.eqb_spec c pl); injection E; intros; subst; lia.
Qed.

Local Notation cnts0 := (RefSendTree3.cnts0 ds t).

Definition send_tree_safe : Prop := OK ds 0 (-1) (L 0) 0 (fst cnts0) (snd cnts0).
End Walk.
