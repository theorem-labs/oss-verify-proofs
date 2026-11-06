(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/bzip2/bzip2_compress_target/lib/K/P/Startup_glue.v, with its module paths changed; 3 of its 13 lines of code are new or changed and 73 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: moved from image A (fuzz_preset.asan d83eb25d), commit 3244f5c71f6, to the #102 pin A' (fuzz_preset.asan 1be0f53d, unstripped bff8519b): 0 address numerals by the frozen alreloc (sha256 c4338d099cfb8025, commit d99acc3edd9, same-unit move, --assume-source), each by symbol + offset in both images, or for a .rodata string by its unique content in both; GXA keys and history lines kept (report and decisions: the relocation record, the internal file resolve-A-why.tsv). *)
(* Modified by Theorem Labs, 2026-10: relocated onto omx-clap-core/fuzz_preset.asan (image A, d83eb25d) from commit 7e395de08f5 proofs/omx-clap-core/fuzz_manifest/lib/A/Bz/P/Startup_glue.v: module paths (lib/A/Bz -> lib/A/PSnpBz) and 0 address numerals by alreloc (sha256 c4338d099cfb8025, commit d99acc3edd97), each by symbol + offset in both images (per-numeral report: the relocation record, reloc-A). *)
(* Ported by the runtime port from commit affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/A/Bz/P/Startup_glue.v, unchanged. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.P Require Import Str_tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac astep := lstep; try (first [if_true | if_false]).
Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => constr_eq q p end.
Ltac steps_to p := repeat (tryif at_pc p then fail else astep).
