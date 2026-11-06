(* Ported by a Theorem Labs lane from a working branch affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/A/Prog/memchr.v, unchanged. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Prog Require Import memchr_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require R_memchr.

Theorem memchr_holds : memchr_contract.
Proof. exact R_memchr.memchr_spec. Qed.
