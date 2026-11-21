(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: the released proof of libreac/fuzz_boxreg's asan_halts, applied at the point BudgetWit/AsanWitness.v gives, where all three of its premises hold; following libreac/fuzz_identity's lib/BudgetWit/AsanHaltsNV.v. *)
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From LinuxProcessSemantics.LinuxProcessSem Require Import State Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.libreac.fuzz_boxreg Require Images Statements.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.BudgetWit Require AsanWitness.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require BoxClose.

(** [Statements.asan_halts], which the released [BoxClose.box_asan_halts]
    proves, at an entry and an input that meet all three of its premises
    ([AsanWitness.asan_budget_witness]): its conclusion holds there with no
    hypothesis left.  [asan_halts/Proof.v] applies
    [Theorems.libreac_fuzz_boxreg_asan_halts], which lib/Theorems.v defines as
    this same term; it is named here directly because lib/Theorems.v also
    requires the plain, UBSan and ASan+UBSan trees. *)
Theorem asan_halts_not_vacuous :
exists en inp, valid_entry OSSVerify.libreac.fuzz_boxreg.Images.asan en inp /\ valid_input inp /\
~ run_scfg_budget_refused forced_only_cfg OSSVerify.libreac.fuzz_boxreg.Images.asan
    Budgets.Standard.lim_source en inp /\
must_exit_in_scfg forced_only_cfg Exits.ok_or_refused OSSVerify.libreac.fuzz_boxreg.Images.asan
    Budgets.Standard.lim_source en inp.
Proof.
destruct AsanWitness.asan_budget_witness as (en & inp & Hen & Hinp & Hnr).
exists en, inp. split; [exact Hen | split; [exact Hinp | split; [exact Hnr |]]].
exact (OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog.BoxClose.box_asan_halts en inp Hen Hinp Hnr).
Qed.
