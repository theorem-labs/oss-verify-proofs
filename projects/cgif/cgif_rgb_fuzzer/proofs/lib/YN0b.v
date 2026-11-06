(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
Open Scope Z_scope.
Definition SRC_LIM_MIN : Z := 2 ^ 31.
Lemma SRC_LIM_MIN_le_source : SRC_LIM_MIN <= source_alloc_limit.
Proof. unfold SRC_LIM_MIN, source_alloc_limit. cbn. lia. Qed.

Lemma SRC_LIM_MIN_le_sanitizer : SRC_LIM_MIN <= SanitizerBudgets.lim_source.
Proof. unfold SRC_LIM_MIN, SanitizerBudgets.lim_source, sanitizer_source_limit. cbn. lia. Qed.

