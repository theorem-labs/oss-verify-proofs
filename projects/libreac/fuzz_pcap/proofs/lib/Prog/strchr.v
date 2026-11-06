From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import strchr_c.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require R_strchr.

Theorem strchr_holds : strchr_contract.
Proof. exact R_strchr.strchr_spec. Qed.
