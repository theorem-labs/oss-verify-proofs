From OssFuzzTheorems.zstd.huf_decompress Require Statements.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require Theorems.

Theorem asan_ubsan_agrees_holds : OssFuzzTheorems.zstd.huf_decompress.Statements.asan_ubsan_agrees.
Proof. exact OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Theorems.strong_universal_error_free_huf_decompress_both. Qed.
