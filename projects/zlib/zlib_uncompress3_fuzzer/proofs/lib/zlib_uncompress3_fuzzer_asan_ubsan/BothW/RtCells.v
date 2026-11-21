(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.BothW Require Import BImg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Lemma no_image_asan : forall s1 s2, 0x67f000 <= s1 -> no_image bsegs s1 s2.
Proof. intros s1 s2 H z Hz. apply ref_find_segment_none; lia. Qed.

End CANSEC1.
Notation rt_got m :=
  (rw_cells bsegs m 0xd16a8 [C8 (Z_to_bv 64 0x16b9e8); C8 (Z_to_bv 64 0xd76b8); C8 (Z_to_bv 64 0xd9eb8);
                              C8 (Z_to_bv 64 0xdaba8); C8 (Z_to_bv 64 0xdabb0); C8 (Z_to_bv 64 0xdaba0)]).
Notation rt_got_ric m := (rw_cells bsegs m 0xd2220 [C8 (Z_to_bv 64 0xdab99)]).
Notation rt_shbase m := (rw_cells bsegs m 0xd9eb8 [C8 (Z_to_bv 64 0x7fff8000)]).
Notation rt_inited m := (rw_cells bsegs m 0xdab98 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]).
Notation rt_layout m := (rw_cells bsegs m 0xdaba0 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
Notation rt_real_mem m := (rw_cells bsegs m 0xd3568 [C8 (Z_to_bv 64 0xc79f4); C8 (Z_to_bv 64 0xc7df8)]).
Notation rt_real_wcslen m := (rw_cells bsegs m 0xd3428 [C8 (Z_to_bv 64 0xc78f8)]).
Notation rt_real_read m := (rw_cells bsegs m 0xd3438 [C8 (Z_to_bv 64 0xcd0f8)]).
Notation rt_real_printf m := (rw_cells bsegs m 0xd3458 [C8 (Z_to_bv 64 0xc7340); C8 (Z_to_bv 64 0xc4230)]).
