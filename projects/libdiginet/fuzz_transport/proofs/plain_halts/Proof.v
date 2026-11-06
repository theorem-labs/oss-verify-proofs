From OSSVerify.libdiginet.fuzz_transport Require Statements.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Theorems.

Theorem plain_halts_holds : OSSVerify.libdiginet.fuzz_transport.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Theorems.libdiginet_fuzz_transport_plain_halts. Qed.
