From OSSVerify.libreac.fuzz_pcap Require Statements.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.libreac.fuzz_pcap.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.libreac.fuzz_pcap.lib.Theorems.libreac_fuzz_pcap_ubsan_agrees. Qed.
