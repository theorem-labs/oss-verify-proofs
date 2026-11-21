(** Refutation of OSSVerify.Tests.toy.ebreak.Statements.asan_ca_total:
    the classifier, lps's ebreak image, faults at its first instruction, so on lps's finite-input witness it exits with no code at all (tests/proofs/lib/ClassifierRun.v). *)
From OSSVerify.Tests.toy.ebreak Require Statements.
From OSSVerify.Tests.proofs.lib Require ClassifierRun.

Theorem asan_ca_total_refuted : ~ Statements.asan_ca_total.
Proof. exact ClassifierRun.ebreak_refutes_classifier_total3. Qed.
