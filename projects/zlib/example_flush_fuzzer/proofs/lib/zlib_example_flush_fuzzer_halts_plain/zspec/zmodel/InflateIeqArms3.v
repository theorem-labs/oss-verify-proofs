(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate InflateGarbBase InflateGarb
  InftreesCoverage ItCovPre ItCovIface ItCovMain ItCovExt
  InflateInv InflateInvRun InflateInvTab InflateInvDec InflateInvKit InflateInvCov InflateInvTbl
  InflateInvArms5 InflateInvArms6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import InflateIeq InflateIeqKit InflateIeqArms1 InflateIeqArms2.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope am_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).








Section C3.
  Variables (iv : ivariant) (flush : Z) (NI NO WN TOT0 : Z).
  Hypothesis NI32 : 0 <= NI < 2 ^ 32.
  Hypothesis NO32 : 0 <= NO < 2 ^ 32.
  Local Notation pinv := (pinv NI NO WN TOT0).
  Hypothesis FASTC : forall s1 s2 c d r, is_mode s1 = LEN -> CC s1 -> SEQX (chk_guard s1 r) s1 s2 ->
    WEQ (LOAD (inflate_fast (RESTORE (mkW s1 c r)))) (LOAD (inflate_fast (RESTORE (mkW s2 (cdt c d) r)))).

  Ltac prep Hm SQ s1 s2 c r :=
    dstate1 s1; dstate2 s2; dcall c; dregs r; cdt_red; proj_cbn_in Hm; subst; seq_open SQ.





  Ltac hc1 HT := intros h; rewrite !code_at_cat; cbn [is_codes];
                 match goal with CO : forall i, _ -> arr_get _ i = arr_get _ i |- _ => exact (TV_read1 _ _ _ _ _ _ HT CO h) end.















End C3.
