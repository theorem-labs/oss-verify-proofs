(* Ported by RtStr from proofs/omx-clap-core/fuzz_manifest/lib/A/Prog/memchr.v, unchanged. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import memchr_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require R_memchr.

Theorem memchr_holds : memchr_contract.
Proof. exact R_memchr.memchr_spec. Qed.
