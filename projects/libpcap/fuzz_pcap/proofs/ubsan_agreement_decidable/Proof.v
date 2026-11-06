From OSSVerify.libpcap.fuzz_pcap Require Statements.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib Require ConstAccept.

Theorem ubsan_agreement_decidable_holds : OSSVerify.libpcap.fuzz_pcap.Statements.ubsan_agreement_decidable.
Proof. exact OSSVerify.Proofs.libpcap.fuzz_pcap.lib.ConstAccept.ubsan_decidable. Qed.
