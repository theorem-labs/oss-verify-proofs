From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require Import strchr_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U Require R_strchr.

Theorem strchr_holds : strchr_contract.
Proof. exact R_strchr.strchr_spec. Qed.
