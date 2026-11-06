From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import memset_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require R_memset.

Theorem memset_holds : memset_contract.
Proof. exact R_memset.memset_spec. Qed.
