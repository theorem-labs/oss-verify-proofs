(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate InflateGarbBase InflateGarb
  InflateInv InflateInvRun InflateInvTab InflateInvDec InflateInvKit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import InflateIeq InflateIeqKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section C1.
  Variables (iv : ivariant) (flush : Z).

  Ltac prep Hm SQ s1 s2 c r :=
    dstate1 s1; dstate2 s2; dcall c; dregs r; cdt_red; proj_cbn_in Hm; subst; seq_open SQ.






























End C1.
