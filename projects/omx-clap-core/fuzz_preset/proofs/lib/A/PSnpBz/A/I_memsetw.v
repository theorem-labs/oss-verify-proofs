(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/bzip2/bzip2_compress_target/lib/K/A/I_memsetw.v, with its module paths, module names and addresses changed; 560 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: moved from image A (fuzz_preset.asan d83eb25d), commit 3244f5c71f6, to the #102 pin A' (fuzz_preset.asan 1be0f53d, unstripped bff8519b): 8 address numerals by the frozen alreloc (sha256 c4338d099cfb8025, commit d99acc3edd9, same-unit move, --assume-source), each by symbol + offset in both images, or for a .rodata string by its unique content in both; GXA keys and history lines kept (report and decisions: the relocation record, the internal file resolve-A-why.tsv). *)
(* Modified by Theorem Labs, 2026-10: relocated onto omx-clap-core/fuzz_preset.asan (image A, d83eb25d) from commit 3e35620c52e proofs/omx-clap-core/fuzz_manifest/lib/A/Bz/A/I_memsetw.v: module paths (lib/A/Bz -> lib/A/PSnpBz) and the address numerals by alreloc (sha256 c4338d099cfb8025, commit d99acc3edd97), each by symbol + offset in both images (per-numeral report: the relocation record, A-run).. Runtime-option and runtime-state cells this walk loads (by its numerals): __asan::replace_intrin_cached, __interception::real_memset, __asan_shadow_memory_dynamic_address, .got+0x60, .got+0xbc8. The option cells read the same defaults in the source and target images: each embeds `__asan_default_options` = "allocator_may_return_null=1" and nothing else (fm fuzz_manifest.asan; preset rebuilt fuzz_preset.asan / .asan-ubsan); none is a pipeline-N patched image. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.Lib Require Import Tac ImageA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.A Require Import R_small.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition icells_ms (m : mem) : Prop :=
  ro_cells asegs m 0xa2010 [C8 (Z_to_bv 64 0xaaeb8)]            (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa2b78 [C8 (Z_to_bv 64 0xabb99)]         (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa3e90 [C8 (Z_to_bv 64 0x9b6b8)]         (* [comment removed for export] *)
  /\ ro_cells asegs m 0xaaeb8 [C8 (Z_to_bv 64 0x7fff8000)]      (* [comment removed for export] *)
  /\ ro_cells asegs m 0xabb99 [C1 (Z_to_bv 8 1)].              (* [comment removed for export] *)
