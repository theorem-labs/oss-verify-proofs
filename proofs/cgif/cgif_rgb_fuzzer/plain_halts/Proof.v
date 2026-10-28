From OssFuzzTheorems.cgif.cgif_rgb_fuzzer Require Statements.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Theorems.

Theorem plain_halts_holds : OssFuzzTheorems.cgif.cgif_rgb_fuzzer.Statements.plain_halts.
Proof. exact OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib.Theorems.halts_allowed_cgif_cgif_rgb_fuzzer_halts_plain_forced_only. Qed.
