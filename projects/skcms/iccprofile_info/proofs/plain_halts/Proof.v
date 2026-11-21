From OSSVerify.skcms.iccprofile_info Require Statements.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Halts Require HaltsTops.

Theorem plain_halts_holds : OSSVerify.skcms.iccprofile_info.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.skcms.iccprofile_info.lib.Halts.HaltsTops.halts_skcms_iccprofile_info_plain. Qed.
