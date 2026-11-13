From OSSVerify.simdjson.fuzz_utf8 Require Statements.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Halts Require HaltsUbsan.

Theorem ubsan_halts_holds : OSSVerify.simdjson.fuzz_utf8.Statements.ubsan_halts.
Proof. exact OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Halts.HaltsUbsan.halts_ubsan. Qed.
