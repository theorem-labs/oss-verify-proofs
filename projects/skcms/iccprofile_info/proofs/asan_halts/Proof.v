From OSSVerify.skcms.iccprofile_info Require Statements.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Halts Require HaltsSan.

Theorem asan_halts_holds : OSSVerify.skcms.iccprofile_info.Statements.asan_halts.
Proof. exact OSSVerify.Proofs.skcms.iccprofile_info.lib.Halts.HaltsSan.halts_skcms_iccprofile_info_asan. Qed.
