From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import memset_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require R_memset.

Theorem memset_holds : memset_contract.
Proof. exact R_memset.memset_spec. Qed.
