From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Prog Require Import memset_c.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib Require R_memset.

Theorem memset_holds : memset_contract.
Proof. exact R_memset.memset_spec. Qed.
