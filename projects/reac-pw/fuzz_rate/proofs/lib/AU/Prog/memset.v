(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/A/Prog/memset.v at 2d2ff01bb6f2 relocated to reac-pw/fuzz_rate's ASan image A: module paths changed; numerals by port_core 1e42da8952ec (ledger provenance/reloc/A-Snp.tsv). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/Prog/memset.v at 71994ff034c7, derived by derive_y.py: addresses moved from reac-pw/fuzz_rate's asan image (image A) to its asan-ubsan image (image B), the image module Asan -> AsanUbsan; the Modified-by lines above describe how lib/A/Prog/memset.v was made and quote that file's image-A values; the code below carries image B's values; a numeral in a comment that quotes the donor's text (lib/A/Prog/memset.v keeps its donor's comment text) is kept as lib/A/Prog/memset.v writes it. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU.Prog Require Import memset_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require R_memset.

Theorem memset_holds : memset_contract.
Proof. exact R_memset.memset_spec. Qed.
