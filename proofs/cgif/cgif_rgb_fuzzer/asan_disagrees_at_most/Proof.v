From Stdlib Require Import QArith.
From OssFuzzTheorems.cgif.cgif_rgb_fuzzer Require Statements.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require ConstAccept.

Theorem asan_disagrees_at_most_holds : OssFuzzTheorems.cgif.cgif_rgb_fuzzer.Statements.asan_disagrees_at_most 0.
Proof. exact OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib.ConstAccept.asan_bound_0. Qed.
