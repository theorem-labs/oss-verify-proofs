From Stdlib Require Import QArith.
From OSSVerify.libpcap.fuzz_pcap Require Statements.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib Require ConstAccept.

Theorem asan_disagrees_at_most_holds : OSSVerify.libpcap.fuzz_pcap.Statements.asan_disagrees_at_most 0.
Proof. exact OSSVerify.Proofs.libpcap.fuzz_pcap.lib.ConstAccept.asan_bound_0. Qed.
