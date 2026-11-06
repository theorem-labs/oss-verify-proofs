From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import memchr_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require R_memchr.

Theorem memchr_holds : memchr_contract.
Proof. exact R_memchr.memchr_spec. Qed.
