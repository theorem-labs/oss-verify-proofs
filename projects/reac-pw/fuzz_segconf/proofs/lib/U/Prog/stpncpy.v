From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import stpncpy_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U0.P0 Require F_stpncpy.

Theorem stpncpy_holds : stpncpy_contract.
Proof. exact F_stpncpy.stpncpy_spec. Qed.
