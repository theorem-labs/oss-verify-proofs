(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate
  TreeModel FillWinModel SendModel CompressModel DeflRoom OverlayFBS OverlayFlush OverlayNeed OverlayTFB
  RefFlushBlk11 RefDeflateRel RefDeflateSafe DeflateInv DeflInvFbo DeflInvCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Theorem tfb_safe_holds : tfb_safe_stmt.
Proof.
  intros syms s buf len last FB HL.
  apply (tfb_safe_need syms s buf len last FB).
  apply (dyn_need_ge512 syms s buf len last FB). unfold LS. exact HL.
Qed.

Theorem tfb_room_holds : tfb_room_stmt.
Proof.
  intros syms s buf len last FB HL.
  apply (tfb_room_need syms s buf len last FB).
  apply (dyn_need_ge512 syms s buf len last FB). unfold LS. exact HL.
Qed.

Theorem deflate_DI : deflate_safe_stmtG.
Proof. exact (deflate_safeG tfb_safe_holds tfb_room_holds). Qed.


