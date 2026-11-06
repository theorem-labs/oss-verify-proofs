From OSSVerify.reac_pw.fuzz_qdisc Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.U Require FrameProof FrameProofMF.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.U.Prog Require QdiscSlot.

Theorem ubsan_halts_holds : Statements.ubsan_halts.
Proof. exact (QdiscSlot.ubsan_halts_of_frame FrameProof.frame_ubsan_holds). Qed.

Theorem ubsan_halts_may_fail_holds : Statements.ubsan_halts_may_fail.
Proof. exact (QdiscSlot.ubsan_halts_may_fail_of_frame FrameProofMF.frame_ubsan_mf_holds). Qed.
