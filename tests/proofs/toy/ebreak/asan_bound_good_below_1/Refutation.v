(** Refutation of OSSVerify.Tests.toy.ebreak.Statements.asan_bound_good_below_1:
    the classifier, lps's ebreak image, does not accept lps's finite-input witness, and that input weighs 1, the whole mass, so the inputs it does not accept weigh more than b * M for every b < 1 (tests/proofs/lib/ClassifierRun.v). *)
From OSSVerify.Tests.toy.ebreak Require Statements.
From OSSVerify.Tests.proofs.lib Require ClassifierRun.

Theorem asan_bound_good_below_1_refuted : ~ Statements.asan_bound_good_below_1.
Proof. exact ClassifierRun.ebreak_refutes_classifier_rejects_at_most_below_1. Qed.
