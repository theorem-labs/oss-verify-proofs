From OSSVerify.yajl_ruby.json_fuzzer Require Statements.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib Require ConstAccept.

Theorem asan_agreement_decidable_holds : OSSVerify.yajl_ruby.json_fuzzer.Statements.asan_agreement_decidable.
Proof. exact OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.ConstAccept.asan_decidable. Qed.
