(** Refutation of OSSVerify.Tests.toy.ebreak.Statements.plain_halts_any:
    on lps's demo input and entry the run is never refused memory and errors at its first instruction, so it never exits (tests/proofs/lib/EbreakRun.v). *)
From Stdlib Require Import ZArith.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Tests.toy.ebreak Require Statements.
From OSSVerify.Tests.proofs.lib Require EbreakRun.

Theorem plain_halts_any_refuted : ~ Statements.plain_halts_any.
Proof. exact (EbreakRun.ebreak_refutes_halts_within_budget Budgets.Standard.lim_source Exits.any). Qed.
