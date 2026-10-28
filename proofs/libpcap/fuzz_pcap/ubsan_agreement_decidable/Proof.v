From OssFuzzTheorems.libpcap.fuzz_pcap Require Statements.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib Require ConstAccept.

Theorem ubsan_agreement_decidable_holds : OssFuzzTheorems.libpcap.fuzz_pcap.Statements.ubsan_agreement_decidable.
Proof. exact OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.ConstAccept.ubsan_decidable. Qed.
