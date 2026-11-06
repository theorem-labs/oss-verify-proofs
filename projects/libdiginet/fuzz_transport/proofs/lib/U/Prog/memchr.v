(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/U/Prog/memchr.v at bf7779f81ed764787b77895d2f5c0db2627f33f3 for libdiginet/fuzz_transport; no image value changed; module path OSSVerify.Proofs.libdiginet.fuzz_transport.lib. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memchr_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require R_memchr.

Theorem memchr_holds : memchr_contract.
Proof. exact R_memchr.memchr_spec. Qed.
