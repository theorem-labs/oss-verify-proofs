(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW Require Import AImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Lemma no_image_asan : forall s1 s2, 0x67e000 <= s1 -> no_image asegs s1 s2.
Proof. intros s1 s2 H z Hz. apply ref_find_segment_none; lia. Qed.

End CANSEC1.
Notation rt_got m :=
  (rw_cells asegs m 0xcfe20 [C8 (Z_to_bv 64 0x16a168); C8 (Z_to_bv 64 0xd5e38); C8 (Z_to_bv 64 0xd8638);
                              C8 (Z_to_bv 64 0xd9328); C8 (Z_to_bv 64 0xd9330); C8 (Z_to_bv 64 0xd9320)]).
Notation rt_got_ric m := (rw_cells asegs m 0xd0998 [C8 (Z_to_bv 64 0xd9319)]).
Notation rt_shbase m := (rw_cells asegs m 0xd8638 [C8 (Z_to_bv 64 0x7fff8000)]).
Notation rt_inited m := (rw_cells asegs m 0xd9318 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]).
Notation rt_layout m := (rw_cells asegs m 0xd9320 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
Notation rt_real_mem m := (rw_cells asegs m 0xd1ce0 [C8 (Z_to_bv 64 0xc6168); C8 (Z_to_bv 64 0xc656c)]).
Notation rt_real_wcslen m := (rw_cells asegs m 0xd1ba0 [C8 (Z_to_bv 64 0xc606c)]).
Notation rt_real_read m := (rw_cells asegs m 0xd1bb0 [C8 (Z_to_bv 64 0xcb86c)]).
Notation rt_real_printf m := (rw_cells asegs m 0xd1bd0 [C8 (Z_to_bv 64 0xc5ab4); C8 (Z_to_bv 64 0xc29a4)]).
