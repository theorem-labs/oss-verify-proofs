(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import State Run MemImageType.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma sanitizer_source_le_shipped : SanitizerBudgets.lim_source <= ShippedBudgets.lim_source.
Proof. unfold SanitizerBudgets.lim_source, ShippedBudgets.lim_source, sanitizer_source_limit, source_alloc_limit. lia. Qed.
Section Shrink.
Hypothesis SHRINK : forall cfg Ls1 Ls2 Lt (S T : Image), Ls1 <= Ls2 ->
strong_universal_error_free_T_scfg_budgets_abort cfg Ls2 Lt S T -> strong_universal_error_free_T_scfg_budgets_abort cfg Ls1 Lt S T.
Theorem shipped_to_sanitizer : forall cfg (S T : Image),
strong_universal_error_free_T_scfg_budgets_abort cfg ShippedBudgets.lim_source ShippedBudgets.lim_target S T ->
strong_universal_error_free_T_scfg_budgets_abort cfg SanitizerBudgets.lim_source SanitizerBudgets.lim_target S T.
Proof.
intros cfg S T H. rewrite sanitizer_budgets_target_is_shipped.
exact (SHRINK cfg _ _ _ S T sanitizer_source_le_shipped H).
Qed.
End Shrink.
