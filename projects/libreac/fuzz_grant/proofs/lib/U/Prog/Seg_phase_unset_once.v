From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import GrantSlotPlan HeadampSched.

Theorem seg_phase_unset_once_holds : phase_unset_once.
Proof. exact HeadampSched.phase_unset_once_holds. Qed.
