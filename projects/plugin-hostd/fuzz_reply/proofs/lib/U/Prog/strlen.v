From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import strlen_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require R_strlen.

Theorem strlen_holds : strlen_contract.
Proof. exact R_strlen.strlen_spec. Qed.
