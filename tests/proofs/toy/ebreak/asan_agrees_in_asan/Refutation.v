(** Refutation of OSSVerify.Tests.toy.ebreak.Statements.asan_agrees_in_asan:
    on one valid input and valid entries the plain run is never refused memory and errors at its first instruction (tests/proofs/lib/EbreakRun.v). *)
From Stdlib Require Import ZArith.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Tests.toy.ebreak Require Statements.
From OSSVerify.Tests.proofs.lib Require EbreakRun.

Theorem asan_agrees_in_asan_refuted : ~ Statements.asan_agrees_in_asan.
Proof. exact (EbreakRun.ebreak_refutes_agrees_in Env.alloc_forced_only Budgets.Asan.lim_source Budgets.Asan.lim_target). Qed.
