From OSSVerify.zstd.zstd_frame_info Require Statements.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib Require Theorems.

Theorem asan_ubsan_halts_holds : OSSVerify.zstd.zstd_frame_info.Statements.asan_ubsan_halts.
Proof. exact OSSVerify.Proofs.zstd.zstd_frame_info.lib.Theorems.halts_allowed_zstd_zstd_frame_info_halts_both. Qed.
