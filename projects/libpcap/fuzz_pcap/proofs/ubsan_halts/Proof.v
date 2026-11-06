From OSSVerify.libpcap.fuzz_pcap Require Statements.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib Require Theorems.

Theorem ubsan_halts_holds : OSSVerify.libpcap.fuzz_pcap.Statements.ubsan_halts.
Proof. exact OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Theorems.halts_allowed_libpcap_fuzz_pcap_halts_ubsan. Qed.
