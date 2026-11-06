From OSSVerify.libdiginet.fuzz_transport Require Statements.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.libdiginet.fuzz_transport.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Theorems.libdiginet_fuzz_transport_ubsan_agrees. Qed.
