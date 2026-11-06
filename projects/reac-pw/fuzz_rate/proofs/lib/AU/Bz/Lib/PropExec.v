(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/A/Bz/Lib/PropExec.v at 2d2ff01bb6f2 relocated to reac-pw/fuzz_rate's ASan image A: module paths changed; numerals by port_core 1e42da8952ec (ledger provenance/reloc/A-Snp.tsv). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/Bz/Lib/PropExec.v at 71994ff034c7, derived by derive_y.py: addresses moved from reac-pw/fuzz_rate's asan image (image A) to its asan-ubsan image (image B), the image module Asan -> AsanUbsan; the Modified-by lines above describe how lib/A/Bz/Lib/PropExec.v was made and quote that file's image-A values; the code below carries image B's values; a numeral in a comment that quotes the donor's text (lib/A/Bz/Lib/PropExec.v keeps its donor's comment text) is kept as lib/A/Bz/Lib/PropExec.v writes it. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU.Bz Require BvWfKernel.
(* [comment removed for export] *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU.Bz.Common Require Export PropExec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU.Bz.Lib Require Export LiaTuning.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
