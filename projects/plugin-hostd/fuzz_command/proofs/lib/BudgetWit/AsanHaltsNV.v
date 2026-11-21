(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: the released proof of plugin-hostd/fuzz_command's asan_halts, applied at the point BudgetWit/AsanWitness.v gives, where all three of its premises hold; made as libreac/fuzz_identity's lib/BudgetWit/AsanHaltsNV.v is made. *)
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From LinuxProcessSemantics.LinuxProcessSem Require Import State Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.plugin_hostd.fuzz_command Require Images Statements.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.BudgetWit Require AsanWitness.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require CmdTop.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtDtorExit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdProgClosed.

(** [Statements.asan_halts], which the released term proves: proofs/asan_halts/Proof.v
    applies [Theorems.plugin_hostd_fuzz_command_asan_halts], defined in lib/Theorems.v
    as [A/CmdTop.v]'s [cmd_asan_halts_of_parts] at [A/Rt/RtDtorExit.v]'s
    [cmd_dtor_exit] and [A/Prog/CmdProgClosed.v]'s [cmd_ltoi_all], the term applied
    below (lib/Theorems.v itself is not loaded, since it also loads the other builds'
    proofs).  At an entry and an input that meet all three of its premises
    ([AsanWitness.asan_budget_witness]), its conclusion holds there with no
    hypothesis left. *)
Theorem asan_halts_not_vacuous :
exists en inp, valid_entry OSSVerify.plugin_hostd.fuzz_command.Images.asan en inp /\ valid_input inp /\
~ run_scfg_budget_refused forced_only_cfg OSSVerify.plugin_hostd.fuzz_command.Images.asan
    Budgets.Standard.lim_source en inp /\
must_exit_in_scfg forced_only_cfg Exits.ok_or_refused OSSVerify.plugin_hostd.fuzz_command.Images.asan
    Budgets.Standard.lim_source en inp.
Proof.
destruct AsanWitness.asan_budget_witness as (en & inp & Hen & Hinp & Hnr).
exists en, inp. split; [exact Hen | split; [exact Hinp | split; [exact Hnr |]]].
exact (@OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.CmdTop.cmd_asan_halts_of_parts
  OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt.RtDtorExit.cmd_dtor_exit
  (fun rc => @OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog.CmdProgClosed.cmd_ltoi_all rc)
  en inp Hen Hinp Hnr).
Qed.
