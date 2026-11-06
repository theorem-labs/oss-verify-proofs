From OSSVerify.jsoncons.fuzz_bigint Require Statements.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Theorems.

Theorem asan_agrees_holds : OSSVerify.jsoncons.fuzz_bigint.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.Theorems.fuzz_bigint_asan_agrees. Qed.
