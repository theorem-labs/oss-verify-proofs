From OssFuzzTheorems.simdjson.fuzz_dump_raw_tape Require Statements.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib Require Theorems.

Theorem asan_ubsan_agrees_holds : OssFuzzTheorems.simdjson.fuzz_dump_raw_tape.Statements.asan_ubsan_agrees.
Proof. exact OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Theorems.fuzz_dump_raw_tape_both_cfg. Qed.
