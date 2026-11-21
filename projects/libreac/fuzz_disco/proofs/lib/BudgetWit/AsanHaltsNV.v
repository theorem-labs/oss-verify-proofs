(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: the released proof of libreac/fuzz_disco's asan_halts, applied at the point BudgetWit/AsanWitness.v gives, where all three of its premises hold; following libreac/fuzz_identity's lib/BudgetWit/AsanHaltsNV.v. *)
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From LinuxProcessSemantics.LinuxProcessSem Require Import State Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.libreac.fuzz_disco Require Images Statements.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.BudgetWit Require AsanWitness.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require AD2p DiscoRoA.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require DiscoLibX.

(** [Statements.asan_halts], which the released
    [AD2p.disco_asan_halts_of_parts DiscoRoA.disco_H_RO DiscoLibX.disco_lib_x_all_acfn]
    proves, at an entry and an input that meet all three of its premises
    ([AsanWitness.asan_budget_witness]): its conclusion holds there with no
    hypothesis left.  [asan_halts/Proof.v] applies
    [Theorems.libreac_fuzz_disco_asan_halts], which lib/Theorems.v defines as
    this same term; it is written here directly because lib/Theorems.v also
    requires the plain, UBSan and ASan+UBSan trees. *)
Theorem asan_halts_not_vacuous :
exists en inp, valid_entry OSSVerify.libreac.fuzz_disco.Images.asan en inp /\ valid_input inp /\
~ run_scfg_budget_refused forced_only_cfg OSSVerify.libreac.fuzz_disco.Images.asan
    Budgets.Standard.lim_source en inp /\
must_exit_in_scfg forced_only_cfg Exits.ok_or_refused OSSVerify.libreac.fuzz_disco.Images.asan
    Budgets.Standard.lim_source en inp.
Proof.
destruct AsanWitness.asan_budget_witness as (en & inp & Hen & Hinp & Hnr).
exists en, inp. split; [exact Hen | split; [exact Hinp | split; [exact Hnr |]]].
exact (OSSVerify.Proofs.libreac.fuzz_disco.lib.A.AD2p.disco_asan_halts_of_parts
  OSSVerify.Proofs.libreac.fuzz_disco.lib.A.DiscoRoA.disco_H_RO
  OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog.DiscoLibX.disco_lib_x_all_acfn en inp Hen Hinp Hnr).
Qed.
