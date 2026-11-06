From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import bcmp_c.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require R_memchr.

Theorem bcmp_holds : bcmp_contract.
Proof. exact R_memchr.R_memcmp.bcmp_spec. Qed.
