From OSSVerify.libreac.fuzz_disco Require Statements.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import ZComplete ZAllocator.

Theorem ubsan_halts_from_slot : zlib_checksum_contract -> Statements.ubsan_halts.
Proof.
  intros H. apply plain_halts_from_runtime_contracts. apply runtime_contracts_from_checksum. exact H.
Qed.
