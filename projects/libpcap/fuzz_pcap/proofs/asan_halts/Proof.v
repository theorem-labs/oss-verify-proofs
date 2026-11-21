From OSSVerify.libpcap.fuzz_pcap Require Statements.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib Require Theorems.

Theorem asan_halts_holds : OSSVerify.libpcap.fuzz_pcap.Statements.asan_halts.
Proof. exact OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Theorems.halts_allowed_libpcap_fuzz_pcap_halts_asan. Qed.
