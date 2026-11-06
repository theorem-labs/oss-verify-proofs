(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/A/Prog/memset.v at 2d2ff01bb6f2 relocated to reac-pw/fuzz_rate's ASan image A: module paths changed; numerals by port_core 1e42da8952ec (ledger provenance/reloc/A-Snp.tsv). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Prog Require Import memset_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require R_memset.

Theorem memset_holds : memset_contract.
Proof. exact R_memset.memset_spec. Qed.
