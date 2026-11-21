(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW Require Import AImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Lemma no_image_asan : forall s1 s2, 0x67e000 <= s1 -> no_image asegs s1 s2.
Proof. intros s1 s2 H z Hz. apply ref_find_segment_none; lia. Qed.

End CANSEC1.
Notation rt_got m :=
  (rw_cells asegs m 0xd00b0 [C8 (Z_to_bv 64 0x16a3e8); C8 (Z_to_bv 64 0xd60b8); C8 (Z_to_bv 64 0xd88b8);
                              C8 (Z_to_bv 64 0xd95a8); C8 (Z_to_bv 64 0xd95b0); C8 (Z_to_bv 64 0xd95a0)]).
Notation rt_got_ric m := (rw_cells asegs m 0xd0c28 [C8 (Z_to_bv 64 0xd9599)]).
Notation rt_shbase m := (rw_cells asegs m 0xd88b8 [C8 (Z_to_bv 64 0x7fff8000)]).
Notation rt_inited m := (rw_cells asegs m 0xd9598 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]).
Notation rt_layout m := (rw_cells asegs m 0xd95a0 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
Notation rt_real_mem m := (rw_cells asegs m 0xd1f70 [C8 (Z_to_bv 64 0xc63fc); C8 (Z_to_bv 64 0xc6800)]).
Notation rt_real_wcslen m := (rw_cells asegs m 0xd1e30 [C8 (Z_to_bv 64 0xc6300)]).
Notation rt_real_read m := (rw_cells asegs m 0xd1e40 [C8 (Z_to_bv 64 0xcbb00)]).
Notation rt_real_printf m := (rw_cells asegs m 0xd1e60 [C8 (Z_to_bv 64 0xc5d48); C8 (Z_to_bv 64 0xc2c38)]).
