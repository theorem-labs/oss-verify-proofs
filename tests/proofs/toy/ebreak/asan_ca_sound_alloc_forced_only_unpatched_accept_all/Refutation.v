(** Refutation of OSSVerify.Tests.toy.ebreak.Statements.asan_ca_sound_alloc_forced_only_unpatched_accept_all:
    the classifier, lps's exit0 image, answers yes on lps's finite-input witness, on which the originals, the builds' own images, disagree (tests/proofs/lib/ClassifierRun.v). *)
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Tests.toy.ebreak Require Statements.
From OSSVerify.Tests.proofs.lib Require ClassifierRun.

Theorem asan_ca_sound_alloc_forced_only_unpatched_accept_all_refuted :
  ~ Statements.asan_ca_sound_alloc_forced_only_unpatched_accept_all.
Proof. exact (ClassifierRun.exit0_refutes_classifies_good_inputs_sound Env.alloc_forced_only). Qed.
