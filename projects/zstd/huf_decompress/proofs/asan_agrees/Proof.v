From OSSVerify.zstd.huf_decompress Require Statements.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require Theorems.

Theorem asan_agrees_holds : OSSVerify.zstd.huf_decompress.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.zstd.huf_decompress.lib.Theorems.strong_universal_error_free_huf_decompress_asan. Qed.
