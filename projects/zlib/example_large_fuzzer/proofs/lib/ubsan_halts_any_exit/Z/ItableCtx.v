(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inftrees.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition ty_code (t : codetype) : Z := match t with CODES => 0 | LENS => 1 | DISTS => 2 end.

Set Implicit Arguments.
Unset Implicit Arguments.

Definition LFall (sp FR WP WN TB TN TP BP : Z) : franges := [(sp, FR); (WP, 2 * WN); (TB, 4 * TN); (TP, 8); (BP, 4)].
Definition LF0 (sp FR : Z) : franges := [(sp, FR)].
Definition LF1 (sp FR WP WN : Z) : franges := [(sp, FR); (WP, 2 * WN)].

Definition slots_ok (sp : Z) (l : list (Z * nat * Z)) : Prop :=
  forall e, In e l -> let '(o, w, _) := e in 0 <= o /\ sp + o + Z.of_nat w <= 2 ^ 64.
Definition SVok (sp ARlo ARhi : Z) (SV : list (Z * nat * Z)) : Prop :=
  fslots_miss SV ARlo (ARhi - ARlo) = true /\ slots_ok sp SV.

Section Facts.

End Facts.
