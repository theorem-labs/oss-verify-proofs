From OSSVerify.libpcap.fuzz_pcap Require Statements.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib Require Theorems.

Theorem plain_halts_holds : OSSVerify.libpcap.fuzz_pcap.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Theorems.halts_allowed_libpcap_fuzz_pcap_halts_plain. Qed.
