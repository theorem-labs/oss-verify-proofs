From OssFuzzTheorems.simdjson.fuzz_dump Require Statements.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib Require Theorems.

Theorem asan_ubsan_agrees_holds : OssFuzzTheorems.simdjson.fuzz_dump.Statements.asan_ubsan_agrees.
Proof. exact OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Theorems.fuzz_dump_both_cfg. Qed.
