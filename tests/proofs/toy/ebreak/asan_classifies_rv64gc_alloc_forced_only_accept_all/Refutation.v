(** Refutation of OSSVerify.Tests.toy.ebreak.Statements.asan_classifies_rv64gc_alloc_forced_only_accept_all:
    the classifier exits 0 on lps's finite-input witness, on which the builds disagree (tests/proofs/lib/EbreakRun.v). *)
From Stdlib Require Import ZArith.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Tests.toy.ebreak Require Statements.
From OSSVerify.Tests.proofs.lib Require EbreakRun.

Theorem asan_classifies_rv64gc_alloc_forced_only_accept_all_refuted : ~ Statements.asan_classifies_rv64gc_alloc_forced_only_accept_all.
Proof. exact (EbreakRun.asan_refutes_classifies_rv64gc Env.alloc_forced_only). Qed.
