From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import memchr_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require R_memchr.

Theorem memchr_holds : memchr_contract.
Proof. exact R_memchr.memchr_spec. Qed.
