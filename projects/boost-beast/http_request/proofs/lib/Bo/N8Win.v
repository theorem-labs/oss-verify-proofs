(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Arr CellsX TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface AsCXXHeap AsWalk AsStack0 N8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac win_side_fast := cbn [fst snd]; clear; unfold AFS_SIZE, AFS_HDR, AFS_FLAGS; rewrite ?fsz_1, ?fsz_4; lia.
Ltac win_side_kit := cbn [fst snd]; unfold AFS_SIZE, AFS_HDR, AFS_FLAGS in *; rewrite ?fsz_1, ?fsz_4 in *; lia_arith.

(* [comment removed for export] *)
Ltac stack0_via_aapp_kit :=
  match goal with
  | K : aapp ?A ?n |- _ => solve [apply (stack0_ok_aapp A n _ _ K); win_side_kit]
  | K : aapp ?A ?n /\ _ |- _ => solve [apply (stack0_ok_aapp A n _ _ (proj1 K)); win_side_kit]
  | K : _ /\ aapp ?A ?n |- _ => solve [apply (stack0_ok_aapp A n _ _ (proj2 K)); win_side_kit]
  end.
Ltac aconst_via_aapp_kit :=
  match goal with
  | K : aapp ?A ?n |- _ => solve [apply (aconst_ok_aapp A n _ _ K); win_side_kit]
  | K : aapp ?A ?n /\ _ |- _ => solve [apply (aconst_ok_aapp A n _ _ (proj1 K)); win_side_kit]
  | K : _ /\ aapp ?A ?n |- _ => solve [apply (aconst_ok_aapp A n _ _ (proj2 K)); win_side_kit]
  end.

(* [comment removed for export] *)
Ltac win_not_app l :=
  lazymatch l with
  | context [sh _] => idtac
  | context [Z.shiftr _ _] => idtac
  | _ => first [ lazymatch goal with _ : aceil <= l |- _ => idtac end
               | assert_succeeds (assert (aceil <= l) by lia_t1) ]
  end.

Ltac stack0_via_aapp_fast :=
  lazymatch goal with
  | |- stack0_ok (?l, ?h) =>
      first [ match goal with
              | K : aapp ?A ?n |- _ => lazymatch l with context [A] => idtac end; solve [apply (stack0_ok_aapp A n _ _ K); first [win_side_fast | win_side_kit]]
              end
            | tryif win_not_app l then fail else stack0_via_aapp_kit ]
  | _ => stack0_via_aapp_kit
  end.
Ltac aconst_via_aapp_fast :=
  lazymatch goal with
  | |- aconst_ok (?l, ?h) =>
      first [ match goal with
              | K : aapp ?A ?n |- _ => lazymatch l with context [A] => idtac end; solve [apply (aconst_ok_aapp A n _ _ K); first [win_side_fast | win_side_kit]]
              end
            | tryif win_not_app l then fail else aconst_via_aapp_kit ]
  | _ => aconst_via_aapp_kit
  end.
