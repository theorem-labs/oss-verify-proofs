(** Refutation of OSSVerify.Tests.toy.ebreak.Statements.plain_halts_may_fail_rejected:
    on lps's demo input and entry the run is never refused memory and errors at its first instruction, so it never exits (tests/proofs/lib/EbreakRun.v). *)
From Stdlib Require Import ZArith.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Tests.toy.ebreak Require Statements.
From OSSVerify.Tests.proofs.lib Require EbreakRun.

Theorem plain_halts_may_fail_rejected_refuted : ~ Statements.plain_halts_may_fail_rejected.
Proof. exact (EbreakRun.ebreak_refutes_halts_may_fail (cons (stdpp.bitvector.definitions.Z_to_bv _ 78%Z) Exits.ok_or_refused)). Qed.
