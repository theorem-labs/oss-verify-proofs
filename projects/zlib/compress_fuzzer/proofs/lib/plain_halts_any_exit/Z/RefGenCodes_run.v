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
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import GenCodesModel.
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
Variable sp : Z.
Local Notation T := (S + toff t).
Local Notation BLC := (ds_bl_count ds).
Local Notation DL := (tree_dl ds t).
Hypothesis HL : tree_lens ds.

Hypothesis Hsp : 0 <= sp /\ sp + 80 <= 2 ^ 63.
Hypothesis Hmc : 0 <= mc < tsize t.

Hypothesis Hlen : forall i, 0 <= i <= mc -> 0 <= Len ds t i <= 15.

Hypothesis Hdl : forall i, 0 <= i < tsize t -> 0 <= arr_get DL i < 65536.
Hypothesis Hblc : forall i, 0 <= i < 16 -> 0 <= arr_get BLC i < 65536.

Definition LF : franges := [(sp + 48, 32); (S + toff t, 4 * tsize t)].

Let Ht : 212 <= toff t /\ toff t + 4 * tsize t <= 2904 /\ 1 <= tsize t <= 573 := toff_tsize t.
Let HlenD : arr_len DL = tsize t := tree_lens_dl ds t HL.

Definition gcF (nc : arr) (f : nat) (x : Z) : Z :=
  match f with 0%nat => pb BLC x | 1%nat => pb DL x | _ => pb nc x end.
Definition VB : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 600); (35%nat, 2 ^ 63); (36%nat, 600); (37%nat, 16);
   (38%nat, 65536); (39%nat, 65536)].

Local Ltac nf :=
  cbn [gcF];
  repeat match goal with H : pb ?a ?e = _ |- context [pb ?a ?e] => rewrite !H end.

Local Ltac open_cregs H :=
  let H' := fresh "CR'" in pose proof H as H'; destruct H' as (P21 & P2 & P11 & P16).

Local Ltac len_fact i V :=
  assert (V : pb DL i = Len ds t i) by (unfold Len; apply (pb_get DL); [intros q Hq; apply Hdl; rewrite HlenD in Hq; exact Hq | rewrite HlenD; lia]).

Local Ltac frc2 a b := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; rewrite (a r Hr); exact (b r Hr).
Local Ltac frc3 a b c := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; rewrite (a r Hr), (b r Hr); exact (c r Hr).
Local Ltac frc4 a b c d := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; rewrite (a r Hr), (b r Hr), (c r Hr); exact (d r Hr).

Local Ltac szw16 :=
  first [ reflexivity
        | rewrite <- (mod_pow2_mod_pow2 (szwrap 32 _) 32 16) by lia; rewrite szwrap_eqm by lia;
          rewrite (mod_pow2_mod_pow2 _ 32 16) by lia; reflexivity ].

End Walk.
