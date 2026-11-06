From OSSVerify.libdiginet.fuzz_frame Require Statements.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.libdiginet.fuzz_frame.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Theorems.libdiginet_fuzz_frame_ubsan_agrees. Qed.
