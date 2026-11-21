(** Refutation of OSSVerify.Tests.toy.ebreak.Statements.asan_maybe_diff_no_distribution:
    the classifier, lps's ebreak image, faults at its first instruction, so lps's finite-input witness gets neither yes nor no from it and is a maybe input (tests/proofs/lib/ClassifierRun.v). *)
From OSSVerify.Tests.toy.ebreak Require Statements.
From OSSVerify.Tests.proofs.lib Require ClassifierRun.

Theorem asan_maybe_diff_no_distribution_refuted : ~ Statements.asan_maybe_diff_no_distribution.
Proof. exact ClassifierRun.ebreak_refutes_maybe_empty. Qed.
