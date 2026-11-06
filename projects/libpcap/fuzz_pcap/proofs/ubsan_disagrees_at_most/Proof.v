From Stdlib Require Import QArith.
From OSSVerify.libpcap.fuzz_pcap Require Statements.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib Require ConstAccept.

Theorem ubsan_disagrees_at_most_holds : OSSVerify.libpcap.fuzz_pcap.Statements.ubsan_disagrees_at_most 0.
Proof. exact OSSVerify.Proofs.libpcap.fuzz_pcap.lib.ConstAccept.ubsan_bound_0. Qed.
