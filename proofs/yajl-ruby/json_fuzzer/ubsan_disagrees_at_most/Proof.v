From Stdlib Require Import QArith.
From OssFuzzTheorems.yajl_ruby.json_fuzzer Require Statements.
From OssFuzzTheorems.Proofs.yajl_ruby.json_fuzzer.lib Require ConstAccept.

Theorem ubsan_disagrees_at_most_holds : OssFuzzTheorems.yajl_ruby.json_fuzzer.Statements.ubsan_disagrees_at_most 0.
Proof. exact OssFuzzTheorems.Proofs.yajl_ruby.json_fuzzer.lib.ConstAccept.ubsan_bound_0. Qed.
