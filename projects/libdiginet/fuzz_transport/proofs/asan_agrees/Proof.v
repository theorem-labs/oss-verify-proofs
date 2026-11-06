From OSSVerify.libdiginet.fuzz_transport Require Statements.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require TheoremsAsan.

Theorem asan_agrees_holds : OSSVerify.libdiginet.fuzz_transport.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TheoremsAsan.libdiginet_fuzz_transport_asan_agrees. Qed.
