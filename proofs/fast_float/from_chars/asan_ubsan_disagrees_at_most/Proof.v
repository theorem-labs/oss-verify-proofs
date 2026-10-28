From Stdlib Require Import QArith.
From OssFuzzTheorems.fast_float.from_chars Require Statements.
From OssFuzzTheorems.Proofs.fast_float.from_chars.lib Require ConstAccept.

Theorem asan_ubsan_disagrees_at_most_holds : OssFuzzTheorems.fast_float.from_chars.Statements.asan_ubsan_disagrees_at_most 0.
Proof. exact OssFuzzTheorems.Proofs.fast_float.from_chars.lib.ConstAccept.asan_ubsan_bound_0. Qed.
