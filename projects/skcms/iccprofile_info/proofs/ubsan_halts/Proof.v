From OSSVerify.skcms.iccprofile_info Require Statements.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Halts Require HaltsTops.

Theorem ubsan_halts_holds : OSSVerify.skcms.iccprofile_info.Statements.ubsan_halts.
Proof. exact OSSVerify.Proofs.skcms.iccprofile_info.lib.Halts.HaltsTops.halts_skcms_iccprofile_info_ubsan. Qed.
