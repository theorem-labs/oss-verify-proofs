From OSSVerify.simdjson.fuzz_dump Require Statements.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.simdjson.fuzz_dump.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.simdjson.fuzz_dump.lib.Theorems.fuzz_dump_ubsan_cfg. Qed.
