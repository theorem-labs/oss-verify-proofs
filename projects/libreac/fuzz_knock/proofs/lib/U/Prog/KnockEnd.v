From OSSVerify.libreac.fuzz_knock Require Statements.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.U Require FrameProof FrameProofMF.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.U.Prog Require KnockSlot.

Theorem ubsan_halts_holds : Statements.ubsan_halts.
Proof. exact (KnockSlot.ubsan_halts_of_frame FrameProof.frame_ubsan_holds). Qed.

Theorem ubsan_halts_may_fail_holds : Statements.ubsan_halts_may_fail.
Proof. exact (KnockSlot.ubsan_halts_may_fail_of_frame FrameProofMF.frame_ubsan_mf_holds). Qed.
