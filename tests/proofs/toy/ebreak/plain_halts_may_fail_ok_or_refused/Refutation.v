(** Refutation of OSSVerify.Tests.toy.ebreak.Statements.plain_halts_may_fail_ok_or_refused:
    on lps's demo input and entry the run is never refused memory and errors at its first instruction, so it never exits (tests/proofs/lib/EbreakRun.v). *)
From Stdlib Require Import ZArith.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Tests.toy.ebreak Require Statements.
From OSSVerify.Tests.proofs.lib Require EbreakRun.

Theorem plain_halts_may_fail_ok_or_refused_refuted : ~ Statements.plain_halts_may_fail_ok_or_refused.
Proof. exact (EbreakRun.ebreak_refutes_halts_may_fail Exits.ok_or_refused). Qed.
