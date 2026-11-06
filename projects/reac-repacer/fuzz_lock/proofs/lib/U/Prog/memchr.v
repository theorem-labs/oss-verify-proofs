From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require Import memchr_c.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require R_memchr.

Theorem memchr_holds : memchr_contract.
Proof. exact R_memchr.memchr_spec. Qed.
