(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/Prog/memset.v for libdiginet/fuzz_decode; no image value changed; module path OSSVerify.Proofs.libdiginet.fuzz_decode.lib. *)
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import memset_c.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require R_memset.

Theorem memset_holds : memset_contract.
Proof. exact R_memset.memset_spec. Qed.
