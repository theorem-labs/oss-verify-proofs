(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: the released proof of libreac/fuzz_identity's asan_halts, applied at the point BudgetWit/AsanWitness.v gives, where all three of its premises hold. *)
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From LinuxProcessSemantics.LinuxProcessSem Require Import State Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.libreac.fuzz_identity Require Images Statements.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit Require AsanWitness.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require IdentTop.

(** [Statements.asan_halts], which the released [IdentTop.ident_asan_halts_of_parts]
    proves, at an entry and an input that meet all three of its premises
    ([AsanWitness.asan_budget_witness]): its conclusion holds there with no
    hypothesis left. *)
Theorem asan_halts_not_vacuous :
exists en inp, valid_entry OSSVerify.libreac.fuzz_identity.Images.asan en inp /\ valid_input inp /\
~ run_scfg_budget_refused forced_only_cfg OSSVerify.libreac.fuzz_identity.Images.asan
    Budgets.Standard.lim_source en inp /\
must_exit_in_scfg forced_only_cfg Exits.ok_or_refused OSSVerify.libreac.fuzz_identity.Images.asan
    Budgets.Standard.lim_source en inp.
Proof.
destruct AsanWitness.asan_budget_witness as (en & inp & Hen & Hinp & Hnr).
exists en, inp. split; [exact Hen | split; [exact Hinp | split; [exact Hnr |]]].
exact (OSSVerify.Proofs.libreac.fuzz_identity.lib.A.IdentTop.ident_asan_halts_of_parts en inp Hen Hinp Hnr).
Qed.
