From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import strlen_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require R_strlen.

Theorem strlen_holds : strlen_contract.
Proof. exact R_strlen.strlen_spec. Qed.
