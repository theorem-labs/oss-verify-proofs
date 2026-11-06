From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import twoway_strstr_c TwSetup_c TwFront TwBack.

Theorem twoway_strstr_holds : twoway_strstr_contract.
Proof. exact (tw_front tw_back). Qed.
