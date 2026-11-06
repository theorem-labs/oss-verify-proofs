From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import memchr_c.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require R_memchr.

Theorem memchr_holds : memchr_contract.
Proof. exact R_memchr.memchr_spec. Qed.
