From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import memchr_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require R_memchr.

Theorem memchr_holds : memchr_contract.
Proof. exact R_memchr.memchr_spec. Qed.
