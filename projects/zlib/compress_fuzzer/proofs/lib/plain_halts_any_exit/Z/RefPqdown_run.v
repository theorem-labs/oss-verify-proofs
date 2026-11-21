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
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeMem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
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
Local Notation hl := (ds_heap_len ds).
Local Notation T := (S + toff t).
Local Notation TF := (tree_fc ds t).
Local Notation DP := (ds_depth ds).
Hypothesis HL : tree_lens ds.

Hypothesis Hhl : 1 <= hl <= 572.

Hypothesis Hpq : pq_ok (tsize t) ds.

Hypothesis Hfreq : forall i, 0 <= i < tsize t -> 0 <= arr_get TF i < 65536.
Hypothesis Hdep : forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256.

Definition LF : franges := [(S + 3008, 2292)].

Let Ht : 212 <= toff t /\ toff t + 4 * tsize t <= 2904 /\ 1 <= tsize t <= 573 := toff_tsize t.
Let HlenF : arr_len TF = tsize t := tree_lens_fc ds t HL.
Let HlenD : arr_len DP = 573 := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HL))))))).
Let HlenH : arr_len (ds_heap ds) = 573 := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HL))))))).

Definition pqF (h : arr) (f : nat) (x : Z) : Z :=
  match f with 0%nat => pb TF x | 1%nat => hv h x | _ => wb DP x end.
Definition VB : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 600); (35%nat, 573); (36%nat, 600); (37%nat, 600); (38%nat, 600)].

Definition sel (h : arr) (j : Z) : Z :=
  if (j <? hl) && smaller ds t (arr_get h (j + 1)) (arr_get h j) then j + 1 else j.

Local Ltac node h i V R PF PD :=
  assert (R : 0 <= arr_get h i < tsize t) by (auto with zarith || (match goal with Hr : forall n, 1 <= n <= hl -> _ |- _ => apply Hr; lia end));
  assert (V : hv h i = arr_get h i) by (apply hv_get; lia);
  assert (PF : pb TF (arr_get h i) = Freq ds t (arr_get h i)) by (unfold Freq; apply (pb_get TF); [intros q Hq; apply Hfreq; lia | lia]);
  assert (PD : wb DP (arr_get h i) = depth_get ds (arr_get h i)) by (unfold depth_get; apply (wb_get DP); [intros q Hq; apply Hdep; lia | lia]).

Local Ltac nf :=
  cbn [pqF];
  repeat match goal with H : hv ?hh ?e = arr_get ?hh ?e |- context [hv ?hh ?e] => rewrite !H end;
  repeat match goal with H : pb ?a ?e = _ |- context [pb ?a ?e] => rewrite !H end;
  repeat match goal with H : wb ?a ?e = _ |- context [wb ?a ?e] => rewrite !H end.

Local Ltac open_hregs H :=
  let H' := fresh "HR'" in pose proof H as H';
  destruct H' as (P10 & P11 & P13 & P5 & P15 & P6 & P28 & P7 & P30 & P1).

Local Ltac open_mregs H :=
  let H' := fresh "MR'" in pose proof H as H';
  destruct H' as ((P10 & P11 & P13 & P5 & P15 & P6 & P28 & P7 & P30 & P1) & P12 & P17 & P14).

Local Ltac vt := first [ reflexivity | nf; reflexivity | nf; assumption | nf; lia ].

End Walk.
