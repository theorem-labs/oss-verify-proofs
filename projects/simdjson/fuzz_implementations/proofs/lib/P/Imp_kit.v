(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Image ZBridge Step.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Layout Sj_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Sj_stage1_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma rw_cells_split_at : forall m A cs n, rw_cells psegs m A cs ->
  rw_cells psegs m A (firstn n cs) /\ rw_cells psegs m (A + Z.of_nat (cells_size (firstn n cs))) (skipn n cs).
Proof. intros m A cs n H. rewrite <- (firstn_skipn n cs) in H. apply Sj_stage1_kit.rw_cells_app in H. exact H. Qed.

Lemma rw_cells_join : forall m A cs1 A' cs2, rw_cells psegs m A cs1 -> rw_cells psegs m A' cs2 -> A' = A + Z.of_nat (cells_size cs1) ->
  rw_cells psegs m A (cs1 ++ cs2).
Proof. intros m A cs1 A' cs2 H1 H2 ->. apply Sj_stage1_kit.rw_cells_app. split; assumption. Qed.

Ltac split_cells H n H1 H2 :=
  destruct (rw_cells_split_at _ _ _ n H) as [H1 H2]; clear H;
  cbn [firstn skipn cells_size csize Nat.add] in H1, H2;
  lazymatch type of H2 with rw_cells _ _ (?b + Z.of_nat ?c) _ =>
    let zc := eval vm_compute in (Z.of_nat c) in change (Z.of_nat c) with zc in H2;
    first [ is_Zlit b; let v := eval vm_compute in (b + zc)%Z in change (b + zc)%Z with v in H2
          | lazymatch b with
            | (?b0 + ?b1)%Z => is_Zlit b1; let v := eval vm_compute in (b1 + zc)%Z in replace (b0 + b1 + zc)%Z with (b0 + v)%Z in H2 by lia
            | _ => idtac end
          | idtac ]
  | _ => idtac end.

Goal forall m q j, rw_cells psegs m (q + 304) [CB 136 j; C8 (Z_to_bv 64 0)] -> rw_cells psegs m (q + 440) [C8 (Z_to_bv 64 0)].
Proof. intros m q j H. split_cells H 1%nat H1 H2. exact H2. Qed.

Ltac byaddr mm a H := lazymatch goal with X : rw_cells _ mm a _ |- _ => rename X into H end.
