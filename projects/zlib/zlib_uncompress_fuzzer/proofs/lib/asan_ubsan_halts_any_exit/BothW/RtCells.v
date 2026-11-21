(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.BothW Require Import BImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Lemma no_image_asan : forall s1 s2, 0x67f000 <= s1 -> no_image bsegs s1 s2.
Proof. intros s1 s2 H z Hz. apply ref_find_segment_none; lia. Qed.

End CANSEC1.
Notation rt_got m :=
  (rw_cells bsegs m 0xd1320 [C8 (Z_to_bv 64 0x16b668); C8 (Z_to_bv 64 0xd7338); C8 (Z_to_bv 64 0xd9b38);
                              C8 (Z_to_bv 64 0xda828); C8 (Z_to_bv 64 0xda830); C8 (Z_to_bv 64 0xda820)]).
Notation rt_got_ric m := (rw_cells bsegs m 0xd1e98 [C8 (Z_to_bv 64 0xda819)]).
Notation rt_shbase m := (rw_cells bsegs m 0xd9b38 [C8 (Z_to_bv 64 0x7fff8000)]).
Notation rt_inited m := (rw_cells bsegs m 0xda818 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]).
Notation rt_layout m := (rw_cells bsegs m 0xda820 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
Notation rt_real_mem m := (rw_cells bsegs m 0xd31e0 [C8 (Z_to_bv 64 0xc7668); C8 (Z_to_bv 64 0xc7a6c)]).
Notation rt_real_wcslen m := (rw_cells bsegs m 0xd30a0 [C8 (Z_to_bv 64 0xc756c)]).
Notation rt_real_read m := (rw_cells bsegs m 0xd30b0 [C8 (Z_to_bv 64 0xccd6c)]).
Notation rt_real_printf m := (rw_cells bsegs m 0xd30d0 [C8 (Z_to_bv 64 0xc6fb4); C8 (Z_to_bv 64 0xc3ea4)]).
