From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import strlen_c.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require R_strlen.

Theorem strlen_holds : strlen_contract.
Proof. exact R_strlen.strlen_spec. Qed.
