(** Refutation of OSSVerify.Tests.toy.ebreak.Statements.asan_maybe_diff_below_1:
    the classifier, lps's ebreak image, gives lps's finite-input witness no firm answer, and that input weighs 1, the whole mass, so the maybe inputs weigh more than b * M for every b < 1 (tests/proofs/lib/ClassifierRun.v). *)
From OSSVerify.Tests.toy.ebreak Require Statements.
From OSSVerify.Tests.proofs.lib Require ClassifierRun.

Theorem asan_maybe_diff_below_1_refuted : ~ Statements.asan_maybe_diff_below_1.
Proof. exact ClassifierRun.ebreak_refutes_maybe_at_most_below_1. Qed.
