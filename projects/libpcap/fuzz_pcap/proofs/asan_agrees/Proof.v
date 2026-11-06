From OSSVerify.libpcap.fuzz_pcap Require Statements.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib Require Theorems.

Theorem asan_agrees_holds : OSSVerify.libpcap.fuzz_pcap.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Theorems.strong_universal_error_free_fuzz_pcap_asan. Qed.
