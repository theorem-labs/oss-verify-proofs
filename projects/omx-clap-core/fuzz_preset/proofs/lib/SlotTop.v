From OSSVerify.omx_clap_core.fuzz_preset Require Statements.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import ZComplete ZAllocator.

Theorem plain_halts_from_slot : zlib_checksum_contract -> Statements.plain_halts.
Proof.
  intros H. apply plain_halts_from_runtime_contracts. apply runtime_contracts_from_checksum. exact H.
Qed.
