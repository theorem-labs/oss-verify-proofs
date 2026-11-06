From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import strchr_c.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require R_strchr.

Theorem strchr_holds : strchr_contract.
Proof. exact R_strchr.strchr_spec. Qed.
