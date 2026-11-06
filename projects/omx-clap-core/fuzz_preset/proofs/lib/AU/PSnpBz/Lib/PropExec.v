(* Modified by Theorem Labs, 2026-10: moved from image B (fuzz_preset.asan-ubsan f8f98a95), commit 3244f5c71f6, to the #102 pin B' (fuzz_preset.asan-ubsan d663f82d, unstripped c90d4fa5): 0 address numerals by the frozen alreloc (sha256 c4338d099cfb8025, commit d99acc3edd9, same-unit move, --assume-source), each by symbol + offset in both images, or for a .rodata string by its unique content in both; GXA keys and history lines kept (report and decisions: the relocation record, the internal file resolve-B-why.tsv). *)
(* Modified by Theorem Labs, 2026-10: relocated onto omx-clap-core/fuzz_preset.asan-ubsan (image B, f8f98a95) from commit 7e395de08f5 proofs/omx-clap-core/fuzz_manifest/lib/A/Bz/Lib/PropExec.v: module paths (lib/A/Bz -> lib/AU/PSnpBz), the image binding Asan -> AsanUbsan, and 0 address numerals by alreloc (sha256 c4338d099cfb8025, commit d99acc3edd97, --build asan-ubsan --from-build asan), each by symbol + offset in both images (per-numeral report: the relocation record, reloc-B). *)
(* Ported by the runtime port from commit affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/A/Bz/Lib/PropExec.v, unchanged. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz Require BvWfKernel.
(* [comment removed for export] *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.Common Require Export PropExec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.Lib Require Export LiaTuning.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
