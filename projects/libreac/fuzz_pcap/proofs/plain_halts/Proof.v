From OSSVerify.libreac.fuzz_pcap Require Statements.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Theorems.

Theorem plain_halts_holds : OSSVerify.libreac.fuzz_pcap.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.libreac.fuzz_pcap.lib.Theorems.libreac_fuzz_pcap_plain_halts. Qed.
