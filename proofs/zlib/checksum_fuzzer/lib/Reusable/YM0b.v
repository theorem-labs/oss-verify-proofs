(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
Open Scope Z_scope.
Definition SRC_LIM_MIN : Z := 2 ^ 34.
Lemma SRC_LIM_MIN_le_source : SRC_LIM_MIN <= source_alloc_limit.
Proof. unfold SRC_LIM_MIN, source_alloc_limit. cbn. lia. Qed.
Lemma SRC_LIM_MIN_le_target : SRC_LIM_MIN <= target_alloc_limit.
Proof. unfold SRC_LIM_MIN, target_alloc_limit. cbn. lia. Qed.
Lemma SRC_LIM_MIN_le_shipped : SRC_LIM_MIN <= ShippedBudgets.lim_source.
Proof. exact SRC_LIM_MIN_le_source. Qed.
