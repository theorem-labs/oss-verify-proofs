From Stdlib Require Import QArith.
From OSSVerify.skcms.iccprofile_info Require Statements.
From OSSVerify.Proofs.skcms.iccprofile_info.lib Require ConstAccept.

Theorem asan_disagrees_at_most_holds : OSSVerify.skcms.iccprofile_info.Statements.asan_disagrees_at_most 0.
Proof. exact OSSVerify.Proofs.skcms.iccprofile_info.lib.ConstAccept.asan_bound_0. Qed.
