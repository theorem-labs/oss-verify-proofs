From OSSVerify.zstd.simple_decompress Require Statements.
From OSSVerify.Proofs.zstd.simple_decompress.lib Require Theorems.

Theorem asan_ubsan_agrees_holds : OSSVerify.zstd.simple_decompress.Statements.asan_ubsan_agrees.
Proof. exact OSSVerify.Proofs.zstd.simple_decompress.lib.Theorems.strong_universal_error_free_simple_decompress_both. Qed.
