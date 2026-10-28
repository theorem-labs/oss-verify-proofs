From Stdlib Require Import QArith.
From OssFuzzTheorems.yajl_ruby.json_fuzzer Require Statements.
From OssFuzzTheorems.Proofs.yajl_ruby.json_fuzzer.lib Require ConstAccept.

Theorem asan_disagrees_at_most_holds : OssFuzzTheorems.yajl_ruby.json_fuzzer.Statements.asan_disagrees_at_most 0.
Proof. exact OssFuzzTheorems.Proofs.yajl_ruby.json_fuzzer.lib.ConstAccept.asan_bound_0. Qed.
