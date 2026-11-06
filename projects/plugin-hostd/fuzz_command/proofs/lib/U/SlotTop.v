From OSSVerify.plugin_hostd.fuzz_command Require Statements.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import ZComplete ZAllocator.

Theorem ubsan_halts_from_slot : zlib_checksum_contract -> Statements.ubsan_halts.
Proof.
  intros H. apply plain_halts_from_runtime_contracts. apply runtime_contracts_from_checksum. exact H.
Qed.
