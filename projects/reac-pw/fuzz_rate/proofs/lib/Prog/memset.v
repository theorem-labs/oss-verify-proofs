From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import memset_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require R_memset.

Theorem memset_holds : memset_contract.
Proof. exact R_memset.memset_spec. Qed.
