From OSSVerify.libpcap.fuzz_pcap Require Statements.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib Require ConstAccept.

Theorem asan_agreement_decidable_holds : OSSVerify.libpcap.fuzz_pcap.Statements.asan_agreement_decidable.
Proof. exact OSSVerify.Proofs.libpcap.fuzz_pcap.lib.ConstAccept.asan_decidable. Qed.
