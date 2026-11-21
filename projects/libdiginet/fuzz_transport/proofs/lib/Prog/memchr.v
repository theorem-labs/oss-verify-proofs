(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/Prog/memchr.v for libdiginet/fuzz_transport; no image value changed; module path OSSVerify.Proofs.libdiginet.fuzz_transport.lib. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import memchr_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require R_memchr.

Theorem memchr_holds : memchr_contract.
Proof. exact R_memchr.memchr_spec. Qed.
