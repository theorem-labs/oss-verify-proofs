(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: the released proof of reac-repacer/fuzz_wire's asan_halts, applied at the point BudgetWit/AsanWitness.v gives, where all three of its premises hold; made as libreac/fuzz_identity's lib/BudgetWit/AsanHaltsNV.v is made. *)
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From LinuxProcessSemantics.LinuxProcessSem Require Import State Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.reac_repacer.fuzz_wire Require Images Statements.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.BudgetWit Require AsanWitness.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require WireClose.

(** [Statements.asan_halts], which the released [WireClose.wire_asan_halts_of_parts]
    proves (proofs/asan_halts/Proof.v applies it through lib/Theorems.v's
    [reac_repacer_fuzz_wire_asan_halts], a Definition equal to it), at an entry and
    an input that meet all three of its premises
    ([AsanWitness.asan_budget_witness]): its conclusion holds there with no
    hypothesis left. *)
Theorem asan_halts_not_vacuous :
exists en inp, valid_entry OSSVerify.reac_repacer.fuzz_wire.Images.asan en inp /\ valid_input inp /\
~ run_scfg_budget_refused forced_only_cfg OSSVerify.reac_repacer.fuzz_wire.Images.asan
    Budgets.Standard.lim_source en inp /\
must_exit_in_scfg forced_only_cfg Exits.ok_or_refused OSSVerify.reac_repacer.fuzz_wire.Images.asan
    Budgets.Standard.lim_source en inp.
Proof.
destruct AsanWitness.asan_budget_witness as (en & inp & Hen & Hinp & Hnr).
exists en, inp. split; [exact Hen | split; [exact Hinp | split; [exact Hnr |]]].
exact (OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.WireClose.wire_asan_halts_of_parts en inp Hen Hinp Hnr).
Qed.
