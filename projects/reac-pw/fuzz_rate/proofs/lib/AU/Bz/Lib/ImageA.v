(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/A/Bz/Lib/ImageA.v at 2d2ff01bb6f2 relocated to reac-pw/fuzz_rate's ASan image A: module paths changed; numerals by port_core 1e42da8952ec (ledger provenance/reloc/A-Snp.tsv). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/Bz/Lib/ImageA.v at 71994ff034c7, derived by derive_y.py: addresses moved from reac-pw/fuzz_rate's asan image (image A) to its asan-ubsan image (image B), the image module Asan -> AsanUbsan; the Modified-by lines above describe how lib/A/Bz/Lib/ImageA.v was made and quote that file's image-A values; the code below carries image B's values; a numeral in a comment that quotes the donor's text (lib/A/Bz/Lib/ImageA.v keeps its donor's comment text) is kept as lib/A/Bz/Lib/ImageA.v writes it. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU.Bz Require BvWfKernel.
(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.reac_pw.fuzz_rate.images Require Import AsanUbsan AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition asegs : list Segment := AsanUbsan.M.loaded_segments.
Definition bsegs : list Segment := AsanUbsan.M.loaded_segments.
