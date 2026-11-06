(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/Prog/memchr.v: ported from a working branch affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/B/Prog/memchr.v, which equals the A->B relocation (Theorem Labs tools) of lib/A/Prog/memchr.v at a working branch 5d8d8a15571 modulo module paths; module paths for this tree. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Prog Require Import memchr_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require R_memchr.

Theorem memchr_holds : memchr_contract.
Proof. exact R_memchr.memchr_spec. Qed.
