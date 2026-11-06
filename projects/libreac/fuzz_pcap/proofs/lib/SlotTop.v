From OSSVerify.libreac.fuzz_pcap Require Statements.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import ZComplete ZAllocator.

Theorem plain_halts_from_slot : zlib_checksum_contract -> Statements.plain_halts.
Proof.
  intros H. apply plain_halts_from_runtime_contracts. apply runtime_contracts_from_checksum. exact H.
Qed.
