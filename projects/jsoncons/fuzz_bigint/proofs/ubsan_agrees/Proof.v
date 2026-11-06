From OSSVerify.jsoncons.fuzz_bigint Require Statements.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.jsoncons.fuzz_bigint.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.Theorems.fuzz_bigint_ubsan_agrees. Qed.
