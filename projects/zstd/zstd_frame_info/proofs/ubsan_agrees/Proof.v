From OSSVerify.zstd.zstd_frame_info Require Statements.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.zstd.zstd_frame_info.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.zstd.zstd_frame_info.lib.Theorems.strong_universal_error_free_zstd_frame_info_ubsan. Qed.
