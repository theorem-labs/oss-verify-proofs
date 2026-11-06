From OSSVerify.libdiginet.fuzz_codec Require Statements.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require FrameProof FrameProofMF.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require LLVMFuzzerTestOneInput_c CodecSlot.

Theorem plain_halts_holds : LLVMFuzzerTestOneInput_c.codec_main_contract -> Statements.plain_halts.
Proof. intros HMAIN. exact (CodecSlot.plain_halts_of_frame HMAIN FrameProof.frame_plain_holds). Qed.

Theorem plain_halts_may_fail_holds : LLVMFuzzerTestOneInput_c.codec_main_contract -> Statements.plain_halts_may_fail.
Proof. intros HMAIN. exact (CodecSlot.plain_halts_may_fail_of_frame HMAIN FrameProofMF.frame_plain_mf_holds). Qed.
