From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog Require Import memset_c.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require R_memset.

Theorem memset_holds : memset_contract.
Proof. exact R_memset.memset_spec. Qed.
