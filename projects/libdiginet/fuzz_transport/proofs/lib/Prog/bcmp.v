(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/Prog/bcmp.v for libdiginet/fuzz_transport; no image value changed; module path OSSVerify.Proofs.libdiginet.fuzz_transport.lib. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import bcmp_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require R_memchr.

Theorem bcmp_holds : bcmp_contract.
Proof. exact R_memchr.R_memcmp.bcmp_spec. Qed.
