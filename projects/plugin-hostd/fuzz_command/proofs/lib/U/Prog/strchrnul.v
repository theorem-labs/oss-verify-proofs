From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import strchrnul_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require R_strchr.

Theorem strchrnul_holds : strchrnul_contract.
Proof. exact R_strchr.strchrnul_spec. Qed.
