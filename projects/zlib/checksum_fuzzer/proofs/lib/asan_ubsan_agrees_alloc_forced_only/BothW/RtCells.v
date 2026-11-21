(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Lemma no_image_asan : forall s1 s2, 0x5f7000 <= s1 -> no_image bsegs s1 s2.
Proof. intros s1 s2 H z Hz. apply ref_find_segment_none; lia. Qed.

End CANSEC1.
Notation rt_got m :=
  (rw_cells bsegs m 0x998c8 [C8 (Z_to_bv 64 0x133628); C8 (Z_to_bv 64 0x9f2f8); C8 (Z_to_bv 64 0xa1af8);
                              C8 (Z_to_bv 64 0xa27e8); C8 (Z_to_bv 64 0xa27f0); C8 (Z_to_bv 64 0xa27e0)]).
Notation rt_got_ric m := (rw_cells bsegs m 0x9a440 [C8 (Z_to_bv 64 0xa27d9)]).
Notation rt_shbase m := (rw_cells bsegs m 0xa1af8 [C8 (Z_to_bv 64 0x7fff8000)]).
Notation rt_inited m := (rw_cells bsegs m 0xa27d8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]).
Notation rt_layout m := (rw_cells bsegs m 0xa27e0 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
Notation rt_real_mem m := (rw_cells bsegs m 0x9b730 [C8 (Z_to_bv 64 0x92c08); C8 (Z_to_bv 64 0x9300c)]).
Notation rt_real_wcslen m := (rw_cells bsegs m 0x9b5f8 [C8 (Z_to_bv 64 0x92b0c)]).
Notation rt_real_read m := (rw_cells bsegs m 0x9b608 [C8 (Z_to_bv 64 0x9830c)]).
Notation rt_real_printf m := (rw_cells bsegs m 0x9b628 [C8 (Z_to_bv 64 0x92558); C8 (Z_to_bv 64 0x8f448)]).
