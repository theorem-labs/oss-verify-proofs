From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import strlen_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require R_strlen.

Theorem strlen_holds : strlen_contract.
Proof. exact R_strlen.strlen_spec. Qed.
