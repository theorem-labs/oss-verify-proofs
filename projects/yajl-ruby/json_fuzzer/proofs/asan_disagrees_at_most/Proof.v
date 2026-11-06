From Stdlib Require Import QArith.
From OSSVerify.yajl_ruby.json_fuzzer Require Statements.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib Require ConstAccept.

Theorem asan_disagrees_at_most_holds : OSSVerify.yajl_ruby.json_fuzzer.Statements.asan_disagrees_at_most 0.
Proof. exact OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.ConstAccept.asan_bound_0. Qed.
