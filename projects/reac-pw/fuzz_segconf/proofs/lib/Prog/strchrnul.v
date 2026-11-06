From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import strchrnul_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require R_strchr.

Theorem strchrnul_holds : strchrnul_contract.
Proof. exact R_strchr.strchrnul_spec. Qed.
