From OssFuzzTheorems.yajl_ruby.json_fuzzer Require Statements.
From OssFuzzTheorems.Proofs.yajl_ruby.json_fuzzer.lib Require ConstAccept.

Theorem ubsan_agreement_decidable_holds : OssFuzzTheorems.yajl_ruby.json_fuzzer.Statements.ubsan_agreement_decidable.
Proof. exact OssFuzzTheorems.Proofs.yajl_ruby.json_fuzzer.lib.ConstAccept.ubsan_decidable. Qed.
