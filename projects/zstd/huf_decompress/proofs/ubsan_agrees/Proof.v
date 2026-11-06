From OSSVerify.zstd.huf_decompress Require Statements.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.zstd.huf_decompress.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.zstd.huf_decompress.lib.Theorems.strong_universal_error_free_huf_decompress_ubsan. Qed.
