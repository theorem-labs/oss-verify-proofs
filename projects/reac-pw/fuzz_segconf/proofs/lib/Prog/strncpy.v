From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import strncpy_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.P0 Require F_stpncpy.

Theorem strncpy_holds : strncpy_contract.
Proof. exact F_stpncpy.strncpy_spec. Qed.
