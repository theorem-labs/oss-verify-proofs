(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/U/Prog/memset.v for libdiginet/fuzz_frame; no image value changed; module path OSSVerify.Proofs.libdiginet.fuzz_frame.lib. *)
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require Import memset_c.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require R_memset.

Theorem memset_holds : memset_contract.
Proof. exact R_memset.memset_spec. Qed.
