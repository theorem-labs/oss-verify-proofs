(** Refutation of OSSVerify.Tests.toy.ebreak.Statements.asan_cb_sound_may_fail_published_reject_all:
    the classifier, lps's exit1 image, answers no on lps's finite-input witness, on which each build agrees with itself, its own original (tests/proofs/lib/ClassifierRun.v). *)
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Tests.toy.ebreak Require Statements.
From OSSVerify.Tests.proofs.lib Require ClassifierRun.

Theorem asan_cb_sound_may_fail_published_reject_all_refuted :
  ~ Statements.asan_cb_sound_may_fail_published_reject_all.
Proof. exact (ClassifierRun.exit1_refutes_classifies_patch_diff_sound Env.may_fail). Qed.
