From OSSVerify.libpcap.fuzz_pcap Require Statements.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib Require ConstAccept.

Theorem asan_ubsan_agreement_decidable_holds : OSSVerify.libpcap.fuzz_pcap.Statements.asan_ubsan_agreement_decidable.
Proof. exact OSSVerify.Proofs.libpcap.fuzz_pcap.lib.ConstAccept.asan_ubsan_decidable. Qed.
