From OSSVerify.reac_pw.fuzz_qdisc Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib Require FrameProof FrameProofMF.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Prog Require QdiscSlot.

Theorem plain_halts_holds : Statements.plain_halts.
Proof. exact (QdiscSlot.plain_halts_of_frame FrameProof.frame_plain_holds). Qed.

Theorem plain_halts_may_fail_holds : Statements.plain_halts_may_fail.
Proof. exact (QdiscSlot.plain_halts_may_fail_of_frame FrameProofMF.frame_plain_mf_holds). Qed.
