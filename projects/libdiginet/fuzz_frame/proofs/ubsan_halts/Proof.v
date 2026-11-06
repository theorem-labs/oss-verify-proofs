From OSSVerify.libdiginet.fuzz_frame Require Statements.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib Require Theorems.

Theorem ubsan_halts_holds : OSSVerify.libdiginet.fuzz_frame.Statements.ubsan_halts.
Proof. exact OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Theorems.libdiginet_fuzz_frame_ubsan_halts. Qed.
