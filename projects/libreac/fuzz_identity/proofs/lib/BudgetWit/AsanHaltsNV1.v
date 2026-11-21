(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: the released proof of libreac/fuzz_identity's asan_halts, applied at the one-byte-file input BudgetWit/AsanFuzz1.v gives, where all three of its premises hold. *)
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From LinuxProcessSemantics.LinuxProcessSem Require Import State Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.libreac.fuzz_identity Require Images Statements.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit Require WitInput1 AsanFuzz1.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require IdentTop.

(** [Statements.asan_halts], which the released [IdentTop.ident_asan_halts_of_parts]
    proves, at [WitInput1.wit_input1] (argv = [[]; "in"], the file "in" holding
    one zero byte: argc = 2, the allocator's growth path) and the entry
    [AsanFuzz1.asan_budget_witness_file1_at] gives: its three premises hold
    there and its conclusion holds with no hypothesis left. *)
Theorem asan_halts_not_vacuous_file1 :
exists en, valid_entry OSSVerify.libreac.fuzz_identity.Images.asan en WitInput1.wit_input1 /\
valid_input WitInput1.wit_input1 /\
~ run_scfg_budget_refused forced_only_cfg OSSVerify.libreac.fuzz_identity.Images.asan
    Budgets.Standard.lim_source en WitInput1.wit_input1 /\
must_exit_in_scfg forced_only_cfg Exits.ok_or_refused OSSVerify.libreac.fuzz_identity.Images.asan
    Budgets.Standard.lim_source en WitInput1.wit_input1.
Proof.
destruct AsanFuzz1.asan_budget_witness_file1_at as (en & Hen & Hinp & Hnr).
exists en. split; [exact Hen | split; [exact Hinp | split; [exact Hnr |]]].
exact (OSSVerify.Proofs.libreac.fuzz_identity.lib.A.IdentTop.ident_asan_halts_of_parts en WitInput1.wit_input1 Hen Hinp Hnr).
Qed.
