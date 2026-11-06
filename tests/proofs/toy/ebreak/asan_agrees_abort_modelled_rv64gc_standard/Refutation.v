(** Refutation of OSSVerify.Tests.toy.ebreak.Statements.asan_agrees_abort_modelled_rv64gc_standard:
    on one valid input and valid entries the plain run is never refused memory and errors at its first instruction, on lps's abort input, whose AT_HWCAP word is RV64GC (tests/proofs/lib/EbreakRun.v). *)
From Stdlib Require Import ZArith.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Tests.toy.ebreak Require Statements.
From OSSVerify.Tests.proofs.lib Require EbreakRun.

Theorem asan_agrees_abort_modelled_rv64gc_standard_refuted : ~ Statements.asan_agrees_abort_modelled_rv64gc_standard.
Proof. exact (EbreakRun.ebreak_refutes_agrees_abort_modelled_rv64gc Budgets.Standard.lim_source Budgets.Standard.lim_target). Qed.
