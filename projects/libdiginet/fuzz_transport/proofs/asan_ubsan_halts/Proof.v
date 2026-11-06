From OSSVerify.libdiginet.fuzz_transport Require Statements.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require TheoremsAsan.

Theorem asan_ubsan_halts_holds : OSSVerify.libdiginet.fuzz_transport.Statements.asan_ubsan_halts.
Proof. exact OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TheoremsAsan.libdiginet_fuzz_transport_asan_ubsan_halts. Qed.
