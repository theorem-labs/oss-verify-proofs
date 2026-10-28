From OssFuzzTheorems.zstd.zstd_frame_info Require Statements.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib Require Theorems.

Theorem ubsan_agrees_holds : OssFuzzTheorems.zstd.zstd_frame_info.Statements.ubsan_agrees.
Proof. exact OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Theorems.strong_universal_error_free_zstd_frame_info_ubsan. Qed.
