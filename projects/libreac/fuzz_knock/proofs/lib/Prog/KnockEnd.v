From OSSVerify.libreac.fuzz_knock Require Statements.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require FrameProof FrameProofMF.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Prog Require KnockSlot.

Theorem plain_halts_holds : Statements.plain_halts.
Proof. exact (KnockSlot.plain_halts_of_frame FrameProof.frame_plain_holds). Qed.

Theorem plain_halts_may_fail_holds : Statements.plain_halts_may_fail.
Proof. exact (KnockSlot.plain_halts_may_fail_of_frame FrameProofMF.frame_plain_mf_holds). Qed.
