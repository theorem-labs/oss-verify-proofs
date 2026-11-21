(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW Require Import AImg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Lemma no_image_asan : forall s1 s2, 0x5f7000 <= s1 -> no_image asegs s1 s2.
Proof. intros s1 s2 H z Hz. apply ref_find_segment_none; lia. Qed.

End CANSEC1.
Notation rt_got m :=
  (rw_cells asegs m 0x99778 [C8 (Z_to_bv 64 0x133528); C8 (Z_to_bv 64 0x9f1f8); C8 (Z_to_bv 64 0xa19f8);
                              C8 (Z_to_bv 64 0xa26e8); C8 (Z_to_bv 64 0xa26f0); C8 (Z_to_bv 64 0xa26e0)]).
Notation rt_got_ric m := (rw_cells asegs m 0x9a2f0 [C8 (Z_to_bv 64 0xa26d9)]).
Notation rt_shbase m := (rw_cells asegs m 0xa19f8 [C8 (Z_to_bv 64 0x7fff8000)]).
Notation rt_inited m := (rw_cells asegs m 0xa26d8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]).
Notation rt_layout m := (rw_cells asegs m 0xa26e0 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
Notation rt_real_mem m := (rw_cells asegs m 0x9b5e0 [C8 (Z_to_bv 64 0x92ab8); C8 (Z_to_bv 64 0x92ebc)]).
Notation rt_real_wcslen m := (rw_cells asegs m 0x9b4a8 [C8 (Z_to_bv 64 0x929bc)]).
Notation rt_real_read m := (rw_cells asegs m 0x9b4b8 [C8 (Z_to_bv 64 0x981bc)]).
Notation rt_real_printf m := (rw_cells asegs m 0x9b4d8 [C8 (Z_to_bv 64 0x92408); C8 (Z_to_bv 64 0x8f2f8)]).
