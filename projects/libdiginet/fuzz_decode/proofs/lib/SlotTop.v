(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/SlotTop.v for libdiginet/fuzz_decode; no image value changed; module path OSSVerify.Proofs.libdiginet.fuzz_decode.lib. *)
From OSSVerify.libdiginet.fuzz_decode Require Statements.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import ZComplete ZAllocator.

Theorem plain_halts_from_slot : zlib_checksum_contract -> Statements.plain_halts.
Proof.
  intros H. apply plain_halts_from_runtime_contracts. apply runtime_contracts_from_checksum. exact H.
Qed.
