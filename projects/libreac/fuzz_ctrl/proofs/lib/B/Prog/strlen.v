From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import strlen_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require R_strlen.

Theorem strlen_holds : strlen_contract.
Proof. exact R_strlen.strlen_spec. Qed.
