From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import memchr_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require R_memchr.

Theorem memchr_holds : memchr_contract.
Proof. exact R_memchr.memchr_spec. Qed.
