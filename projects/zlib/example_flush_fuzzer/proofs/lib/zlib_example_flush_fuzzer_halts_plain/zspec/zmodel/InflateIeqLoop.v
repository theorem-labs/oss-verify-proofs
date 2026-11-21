(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate InflateGarbBase InflateGarb
  InflateInv InflateInvKit InflateInvLoop.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import InflateIeq InflateIeqKit InflateIeqArms1 InflateIeqArms2 InflateIeqArms3 InflateIeqFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Section Loop.
  Variables (iv : ivariant) (flush NI NO WN TOT0 : Z).
  Hypothesis NI32 : 0 <= NI < 2 ^ 32.
  Hypothesis NO32 : 0 <= NO < 2 ^ 32.
  Local Notation pinv := (pinv NI NO WN TOT0).

  Ltac arm L E SQ PI HCC HWD :=
    first [ exact (L E SQ)
          | exact (L PI E SQ)
          | exact (L E (HCC ltac:(rewrite E; reflexivity)) SQ)
          | exact (L E HWD SQ) ].




End Loop.
