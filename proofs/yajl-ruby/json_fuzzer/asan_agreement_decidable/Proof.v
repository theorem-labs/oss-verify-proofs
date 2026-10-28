From OssFuzzTheorems.yajl_ruby.json_fuzzer Require Statements.
From OssFuzzTheorems.Proofs.yajl_ruby.json_fuzzer.lib Require ConstAccept.

Theorem asan_agreement_decidable_holds : OssFuzzTheorems.yajl_ruby.json_fuzzer.Statements.asan_agreement_decidable.
Proof. exact OssFuzzTheorems.Proofs.yajl_ruby.json_fuzzer.lib.ConstAccept.asan_decidable. Qed.
