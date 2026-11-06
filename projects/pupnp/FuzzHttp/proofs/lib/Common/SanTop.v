(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Common Require Import BudgetBridge.
Open Scope Z_scope.

Lemma san_lim_target_eq : SanitizerBudgets.lim_target = ShippedBudgets.lim_target.
Proof. reflexivity. Qed.

Lemma san_le_shipped_src : SanitizerBudgets.lim_source <= ShippedBudgets.lim_source.
Proof. cbv. discriminate. Qed.

Theorem scfg_pinned_to_sanitizer : forall (cfg : SpuriousCfg) (S T : Image),
  strong_universal_error_free_T_scfg cfg S T ->
  strong_universal_error_free_T_scfg_budgets cfg SanitizerBudgets.lim_source SanitizerBudgets.lim_target S T.
Proof.
  intros cfg S T H.
  rewrite san_lim_target_eq.
  apply (sue_budgets_source_shrink cfg SanitizerBudgets.lim_source ShippedBudgets.lim_source ShippedBudgets.lim_target S T
           san_le_shipped_src).
  exact (strong_universal_error_free_T_scfg_budgets_of_scfg cfg S T H).
Qed.
