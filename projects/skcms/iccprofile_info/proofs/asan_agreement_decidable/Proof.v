From OSSVerify.skcms.iccprofile_info Require Statements.
From OSSVerify.Proofs.skcms.iccprofile_info.lib Require ConstAccept.

Theorem asan_agreement_decidable_holds : OSSVerify.skcms.iccprofile_info.Statements.asan_agreement_decidable.
Proof. exact OSSVerify.Proofs.skcms.iccprofile_info.lib.ConstAccept.asan_decidable. Qed.
