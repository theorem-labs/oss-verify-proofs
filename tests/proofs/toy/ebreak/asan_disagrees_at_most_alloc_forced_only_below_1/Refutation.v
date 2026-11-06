(** Refutation of OSSVerify.Tests.toy.ebreak.Statements.asan_disagrees_at_most_alloc_forced_only_below_1:
    lps's finite-input witness weighs 1, the whole mass, and the builds disagree on it (the plain run errors), so the disagreements weigh more than b * M for every b < 1 (tests/proofs/lib/EbreakRun.v). *)
From Stdlib Require Import ZArith.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Tests.toy.ebreak Require Statements.
From OSSVerify.Tests.proofs.lib Require EbreakRun.

Theorem asan_disagrees_at_most_alloc_forced_only_below_1_refuted : ~ Statements.asan_disagrees_at_most_alloc_forced_only_below_1.
Proof. exact (EbreakRun.ebreak_refutes_disagrees_at_most_below_1 Env.alloc_forced_only). Qed.
