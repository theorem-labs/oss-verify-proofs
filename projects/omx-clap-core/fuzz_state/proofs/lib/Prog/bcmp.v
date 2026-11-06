From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import bcmp_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require R_memchr.

Theorem bcmp_holds : bcmp_contract.
Proof. exact R_memchr.R_memcmp.bcmp_spec. Qed.
