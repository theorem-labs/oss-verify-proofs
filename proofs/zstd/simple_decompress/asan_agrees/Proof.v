From OssFuzzTheorems.zstd.simple_decompress Require Statements.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib Require Theorems.

Theorem asan_agrees_holds : OssFuzzTheorems.zstd.simple_decompress.Statements.asan_agrees.
Proof. exact OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Theorems.strong_universal_error_free_simple_decompress_asan. Qed.
