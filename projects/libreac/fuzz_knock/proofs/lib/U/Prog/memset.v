From OSSVerify.Proofs.libreac.fuzz_knock.lib.U.Prog Require Import memset_c.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.U Require R_memset.

Theorem memset_holds : memset_contract.
Proof. exact R_memset.memset_spec. Qed.
