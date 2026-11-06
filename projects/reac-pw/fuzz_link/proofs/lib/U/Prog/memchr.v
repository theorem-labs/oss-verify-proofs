From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require Import memchr_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U Require R_memchr.

Theorem memchr_holds : memchr_contract.
Proof. exact R_memchr.memchr_spec. Qed.
