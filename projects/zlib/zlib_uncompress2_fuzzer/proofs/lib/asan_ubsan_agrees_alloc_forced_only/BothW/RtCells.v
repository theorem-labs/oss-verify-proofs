(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Lemma no_image_asan : forall s1 s2, 0x67f000 <= s1 -> no_image bsegs s1 s2.
Proof. intros s1 s2 H z Hz. apply ref_find_segment_none; lia. Qed.

End CANSEC1.
Notation rt_got m :=
  (rw_cells bsegs m 0xd15c0 [C8 (Z_to_bv 64 0x16b8e8); C8 (Z_to_bv 64 0xd75b8); C8 (Z_to_bv 64 0xd9db8);
                              C8 (Z_to_bv 64 0xdaaa8); C8 (Z_to_bv 64 0xdaab0); C8 (Z_to_bv 64 0xdaaa0)]).
Notation rt_got_ric m := (rw_cells bsegs m 0xd2138 [C8 (Z_to_bv 64 0xdaa99)]).
Notation rt_shbase m := (rw_cells bsegs m 0xd9db8 [C8 (Z_to_bv 64 0x7fff8000)]).
Notation rt_inited m := (rw_cells bsegs m 0xdaa98 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]).
Notation rt_layout m := (rw_cells bsegs m 0xdaaa0 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
Notation rt_real_mem m := (rw_cells bsegs m 0xd3480 [C8 (Z_to_bv 64 0xc7908); C8 (Z_to_bv 64 0xc7d0c)]).
Notation rt_real_wcslen m := (rw_cells bsegs m 0xd3340 [C8 (Z_to_bv 64 0xc780c)]).
Notation rt_real_read m := (rw_cells bsegs m 0xd3350 [C8 (Z_to_bv 64 0xcd00c)]).
Notation rt_real_printf m := (rw_cells bsegs m 0xd3370 [C8 (Z_to_bv 64 0xc7254); C8 (Z_to_bv 64 0xc4144)]).
