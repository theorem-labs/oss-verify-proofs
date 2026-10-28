From Stdlib Require Import QArith.
From OssFuzzTheorems.libpcap.fuzz_pcap Require Statements.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib Require ConstAccept.

Theorem ubsan_disagrees_at_most_holds : OssFuzzTheorems.libpcap.fuzz_pcap.Statements.ubsan_disagrees_at_most 0.
Proof. exact OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.ConstAccept.ubsan_bound_0. Qed.
