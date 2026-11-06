(** Refutation of OSSVerify.Tests.toy.ebreak.Statements.asan_agrees_standard:
    on one valid input and valid entries the plain run is never refused memory and errors at its first instruction (tests/proofs/lib/EbreakRun.v). *)
From Stdlib Require Import ZArith.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Tests.toy.ebreak Require Statements.
From OSSVerify.Tests.proofs.lib Require EbreakRun.

Theorem asan_agrees_standard_refuted : ~ Statements.asan_agrees_standard.
Proof. exact (EbreakRun.ebreak_refutes_agrees Budgets.Standard.lim_source Budgets.Standard.lim_target). Qed.
