From OssFuzzTheorems.libpcap.fuzz_pcap Require Statements.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib Require ConstAccept.

Theorem asan_ubsan_agreement_decidable_holds : OssFuzzTheorems.libpcap.fuzz_pcap.Statements.asan_ubsan_agreement_decidable.
Proof. exact OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.ConstAccept.asan_ubsan_decidable. Qed.
