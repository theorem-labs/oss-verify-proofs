(* Modified by Theorem Labs, 2026-10: moved from image A (fuzz_preset.asan d83eb25d), commit 3244f5c71f6, to the #102 pin A' (fuzz_preset.asan 1be0f53d, unstripped bff8519b): 0 address numerals by the frozen alreloc (sha256 c4338d099cfb8025, commit d99acc3edd9, same-unit move, --assume-source), each by symbol + offset in both images, or for a .rodata string by its unique content in both; GXA keys and history lines kept (report and decisions: the relocation record, the internal file resolve-A-why.tsv). *)
(* Modified by Theorem Labs, 2026-10: relocated onto omx-clap-core/fuzz_preset.asan (image A, d83eb25d) from commit 3e35620c52e proofs/omx-clap-core/fuzz_manifest/lib/A/Prog/memset.v: module paths (lib/A/Prog/memset.v -> lib/A/PSnpL3/Prog/memset.v; lib/A/{Spec,Strw,Ox} -> preset's own lib/... (byte-identical modulo module paths, reused)) and the address numerals by alreloc (sha256 c4338d099cfb8025, commit d99acc3edd97), each by symbol + offset in both images (per-numeral report: the relocation record, A-run). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpL3.Prog Require Import memset_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpL3 Require R_memset.

Theorem memset_holds : memset_contract.
Proof. exact R_memset.memset_spec. Qed.
