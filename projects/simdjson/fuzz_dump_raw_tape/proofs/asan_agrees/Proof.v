From OSSVerify.simdjson.fuzz_dump_raw_tape Require Statements.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib Require Theorems.

Theorem asan_agrees_holds : OSSVerify.simdjson.fuzz_dump_raw_tape.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Theorems.fuzz_dump_raw_tape_asan_cfg. Qed.
