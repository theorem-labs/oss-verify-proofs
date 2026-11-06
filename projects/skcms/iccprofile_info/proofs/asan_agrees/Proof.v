From OSSVerify.skcms.iccprofile_info Require Statements.
From OSSVerify.Proofs.skcms.iccprofile_info.lib Require Theorems.

Theorem asan_agrees_holds : OSSVerify.skcms.iccprofile_info.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.skcms.iccprofile_info.lib.Theorems.strong_universal_error_free_fuzz_iccprofile_info_asan. Qed.
