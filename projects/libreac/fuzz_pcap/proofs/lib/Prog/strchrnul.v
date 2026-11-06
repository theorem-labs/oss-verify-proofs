From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import strchrnul_c.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require R_strchr.

Theorem strchrnul_holds : strchrnul_contract.
Proof. exact R_strchr.strchrnul_spec. Qed.
