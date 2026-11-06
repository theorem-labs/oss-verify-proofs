From OSSVerify.libreac.fuzz_pcap Require Statements.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Theorems.

Theorem asan_ubsan_agrees_holds : OSSVerify.libreac.fuzz_pcap.Statements.asan_ubsan_agrees.
Proof. exact OSSVerify.Proofs.libreac.fuzz_pcap.lib.Theorems.libreac_fuzz_pcap_asan_ubsan_agrees. Qed.
