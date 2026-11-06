From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import strchrnul_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require R_strchr.

Theorem strchrnul_holds : strchrnul_contract.
Proof. exact R_strchr.strchrnul_spec. Qed.
