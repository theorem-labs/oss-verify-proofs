From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import strlen_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require R_strlen.

Theorem strlen_holds : strlen_contract.
Proof. exact R_strlen.strlen_spec. Qed.
