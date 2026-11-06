From OSSVerify.skcms.iccprofile_info Require Statements.
From OSSVerify.Proofs.skcms.iccprofile_info.lib Require ConstAccept.

Theorem ubsan_agreement_decidable_holds : OSSVerify.skcms.iccprofile_info.Statements.ubsan_agreement_decidable.
Proof. exact OSSVerify.Proofs.skcms.iccprofile_info.lib.ConstAccept.ubsan_decidable. Qed.
