From Stdlib Require Import QArith.
From OssFuzzTheorems.skcms.iccprofile_info Require Statements.
From OssFuzzTheorems.Proofs.skcms.iccprofile_info.lib Require ConstAccept.

Theorem ubsan_disagrees_at_most_holds : OssFuzzTheorems.skcms.iccprofile_info.Statements.ubsan_disagrees_at_most 0.
Proof. exact OssFuzzTheorems.Proofs.skcms.iccprofile_info.lib.ConstAccept.ubsan_bound_0. Qed.
