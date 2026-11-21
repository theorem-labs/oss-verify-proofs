(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Lemma no_image_asan : forall s1 s2, 0x67e000 <= s1 -> no_image asegs s1 s2.
Proof. intros s1 s2 H z Hz. apply ref_find_segment_none; lia. Qed.

End CANSEC1.
Notation rt_got m :=
  (rw_cells asegs m 0xd0180 [C8 (Z_to_bv 64 0x16a4a8); C8 (Z_to_bv 64 0xd6178); C8 (Z_to_bv 64 0xd8978);
                              C8 (Z_to_bv 64 0xd9668); C8 (Z_to_bv 64 0xd9670); C8 (Z_to_bv 64 0xd9660)]).
Notation rt_got_ric m := (rw_cells asegs m 0xd0cf8 [C8 (Z_to_bv 64 0xd9659)]).
Notation rt_shbase m := (rw_cells asegs m 0xd8978 [C8 (Z_to_bv 64 0x7fff8000)]).
Notation rt_inited m := (rw_cells asegs m 0xd9658 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]).
Notation rt_layout m := (rw_cells asegs m 0xd9660 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
Notation rt_real_mem m := (rw_cells asegs m 0xd2040 [C8 (Z_to_bv 64 0xc64c8); C8 (Z_to_bv 64 0xc68cc)]).
Notation rt_real_wcslen m := (rw_cells asegs m 0xd1f00 [C8 (Z_to_bv 64 0xc63cc)]).
Notation rt_real_read m := (rw_cells asegs m 0xd1f10 [C8 (Z_to_bv 64 0xcbbcc)]).
Notation rt_real_printf m := (rw_cells asegs m 0xd1f30 [C8 (Z_to_bv 64 0xc5e14); C8 (Z_to_bv 64 0xc2d04)]).
