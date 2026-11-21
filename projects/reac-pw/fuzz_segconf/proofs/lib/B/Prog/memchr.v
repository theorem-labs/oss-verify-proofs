(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/Prog/memchr.v: ported from proofs/omx-clap-core/fuzz_manifest/lib/B/Prog/memchr.v, which equals the A->B relocation (asan-kit elfmap.py + remap.py) of lib/A/Prog/memchr.v modulo module paths; module paths for this tree. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import memchr_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require R_memchr.

Theorem memchr_holds : memchr_contract.
Proof. exact R_memchr.memchr_spec. Qed.
