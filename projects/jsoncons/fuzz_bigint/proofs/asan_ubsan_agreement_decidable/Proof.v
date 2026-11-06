From OSSVerify.jsoncons.fuzz_bigint Require Statements.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require ConstAccept.

Theorem asan_ubsan_agreement_decidable_holds : OSSVerify.jsoncons.fuzz_bigint.Statements.asan_ubsan_agreement_decidable.
Proof. exact OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.ConstAccept.asan_ubsan_decidable. Qed.
