(** Refutation of OSSVerify.Tests.toy.ebreak.Statements.asan_agrees_in_abort_modelled_asan:
    on one valid input and valid entries the plain run is never refused memory and errors at its first instruction, on lps's abort input (tests/proofs/lib/EbreakRun.v). *)
From Stdlib Require Import ZArith.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Tests.toy.ebreak Require Statements.
From OSSVerify.Tests.proofs.lib Require EbreakRun.

Theorem asan_agrees_in_abort_modelled_asan_refuted : ~ Statements.asan_agrees_in_abort_modelled_asan.
Proof. exact (EbreakRun.ebreak_refutes_agrees_in_abort_modelled Env.alloc_forced_only Budgets.Asan.lim_source Budgets.Asan.lim_target). Qed.
