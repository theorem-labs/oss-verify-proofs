From OSSVerify.reac_repacer.fuzz_wire Require Statements.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U Require Import ZComplete ZAllocator.

Theorem ubsan_halts_from_slot : zlib_checksum_contract -> Statements.ubsan_halts.
Proof.
  intros H. apply plain_halts_from_runtime_contracts. apply runtime_contracts_from_checksum. exact H.
Qed.
