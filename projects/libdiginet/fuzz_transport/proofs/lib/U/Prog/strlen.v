From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import strlen_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require R_strlen.

Theorem strlen_holds : strlen_contract.
Proof. exact R_strlen.strlen_spec. Qed.
