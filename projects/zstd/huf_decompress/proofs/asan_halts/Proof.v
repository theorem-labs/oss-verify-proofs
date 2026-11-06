From OSSVerify.zstd.huf_decompress Require Statements.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require Theorems.

Theorem asan_halts_holds : OSSVerify.zstd.huf_decompress.Statements.asan_halts.
Proof. exact OSSVerify.Proofs.zstd.huf_decompress.lib.Theorems.halts_allowed_zstd_huf_decompress_halts_asan. Qed.
