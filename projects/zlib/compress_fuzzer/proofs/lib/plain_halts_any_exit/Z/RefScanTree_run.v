(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeMem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ScanModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Trees.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Walk.
Variable S : Z.
Variable p : ds_ptrs.
Variable ds : deflate_state.
Variable t : tree_id.
Variable mc : Z.
Local Notation T := (S + toff t).
Hypothesis HL : tree_lens ds.

Hypothesis HtB : t <> TB.

Hypothesis Hmc : 0 <= mc /\ mc + 1 < tsize t.

Hypothesis Hlen : forall i, 0 <= i <= mc -> 0 <= Len ds t i <= 15.

Hypothesis Hdl : forall i, 0 <= i < tsize t -> 0 <= arr_get (tree_dl ds t) i < 65536.
Hypothesis Hbl : forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc ds) i < 65536.

Definition SG : deflate_state := set_Len ds t (mc + 1) 65535.

Definition LF : franges := [(S + toff t + 4 * (mc + 1) + 2, 2); (S + 2748, 156)].

Let Ht : 212 <= toff t /\ toff t + 4 * tsize t <= 2904 /\ 1 <= tsize t <= 573 := toff_tsize t.
Let HlenD : arr_len (tree_dl ds t) = tsize t := tree_lens_dl ds t HL.
Let HlenB : arr_len (ds_bl_tree_fc ds) = 39 := proj1 (proj2 (proj2 (proj2 (proj2 HL)))).

Lemma Ht2 : toff t + 4 * tsize t <= 2748.
Proof. clear -HtB. destruct t; cbn; [lia | lia | congruence]. Qed.

Lemma SG_len_dl : forall t', arr_len (tree_dl SG t') = tsize t'.
Proof. intros t'. unfold SG. rewrite tree_dl_len_set_Len. apply tree_lens_dl. exact HL. Qed.

Lemma SG_Len : forall i, Len SG t i = if mc + 1 =? i then 65535 else Len ds t i.
Proof.
  intros i. unfold SG. rewrite Len_set_Len by (rewrite HlenD; lia).
  destruct (mc + 1 =? i); reflexivity.
Qed.

Lemma SG_dl_range : forall i, 0 <= i < tsize t -> 0 <= arr_get (tree_dl SG t) i < 65536.
Proof.
  intros i Hi. change (arr_get (tree_dl SG t) i) with (Len SG t i). rewrite SG_Len.
  destruct (mc + 1 =? i); [lia|]. unfold Len. apply Hdl. exact Hi.
Qed.

Definition stF (b : arr) (f : nat) (x : Z) : Z :=
  match f with 0%nat => pb (tree_dl SG t) x | _ => pb b x end.
Definition VB : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 600); (35%nat, 600); (37%nat, 65536);
   (38%nat, 200); (39%nat, 200); (40%nat, 10); (41%nat, 65536); (42%nat, 65536)].

Definition VBp : bounds := VB ++ [(36%nat, 65536)].

Local Ltac nf :=
  cbn [stF];
  repeat match goal with H : pb ?a ?e = _ |- context [pb ?a ?e] => rewrite !H end.

Local Ltac open_cregs H :=
  let H' := fresh "CR'" in pose proof H as H';
  destruct H' as (P10 & P29 & P17 & P30 & P31 & P1).

Local Ltac len_fact i V :=
  assert (V : pb (tree_dl SG t) i = Len SG t i)
    by (unfold Len; apply (pb_get (tree_dl SG t)); [intros q Hq; apply SG_dl_range; rewrite SG_len_dl in Hq; exact Hq | rewrite SG_len_dl; lia]).

Local Ltac bl_fact b i V :=
  assert (V : pb b i = arr_get b i)
    by (apply (pb_get b); [intros q Hq; match goal with R : forall j, 0 <= j < 39 -> _ |- _ => apply R; lia end | lia]).

Definition SL (b : arr) (n pl c k mx mn : Z) : arr :=
  ds_bl_tree_fc (scan_tree_loop (Z.to_nat (mc + 1 - n)) (set_bl_tree_fc SG b) t mc n pl c k mx mn).

Definition BND (n pl c k mx mn : Z) : Prop :=
  (pl = -1 \/ 0 <= pl <= 15) /\ 0 <= c < 65536 /\ (n <= mc -> c <= 15)
  /\ 0 <= k < mx /\ (mx = 138 \/ mx = 6 \/ mx = 7) /\ (mn = 3 \/ mn = 4).

Local Ltac frc2 a b := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; rewrite (a r Hr); exact (b r Hr).
Local Ltac frc3 a b c := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; rewrite (a r Hr), (b r Hr); exact (c r Hr).

End Walk.
