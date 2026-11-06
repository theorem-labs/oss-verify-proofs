From OSSVerify.simdjson.fuzz_dump Require Statements.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib Require Theorems.

Theorem asan_ubsan_agrees_holds : OSSVerify.simdjson.fuzz_dump.Statements.asan_ubsan_agrees.
Proof. exact OSSVerify.Proofs.simdjson.fuzz_dump.lib.Theorems.fuzz_dump_both_cfg. Qed.
