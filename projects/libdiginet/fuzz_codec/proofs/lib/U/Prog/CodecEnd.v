From OSSVerify.libdiginet.fuzz_codec Require Statements.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require FrameProof FrameProofMF.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require LLVMFuzzerTestOneInput_c CodecSlot.

Theorem ubsan_halts_holds : LLVMFuzzerTestOneInput_c.codec_main_contract -> Statements.ubsan_halts.
Proof. intros HMAIN. exact (CodecSlot.ubsan_halts_of_frame HMAIN FrameProof.frame_ubsan_holds). Qed.

Theorem ubsan_halts_may_fail_holds : LLVMFuzzerTestOneInput_c.codec_main_contract -> Statements.ubsan_halts_may_fail.
Proof. intros HMAIN. exact (CodecSlot.ubsan_halts_may_fail_of_frame HMAIN FrameProofMF.frame_ubsan_mf_holds). Qed.
