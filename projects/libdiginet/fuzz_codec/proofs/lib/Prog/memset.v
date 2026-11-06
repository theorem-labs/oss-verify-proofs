From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import memset_c.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require R_memset.

Theorem memset_holds : memset_contract.
Proof. exact R_memset.memset_spec. Qed.
