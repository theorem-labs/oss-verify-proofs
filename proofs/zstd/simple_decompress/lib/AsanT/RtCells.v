(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Step.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma no_image_asan : forall s1 s2, 0x625000 <= s1 -> no_image bsegs s1 s2.
Proof. intros s1 s2 H z Hz. apply ref_find_segment_none; lia. Qed.

(* [comment removed for export] *)
End CANSEC1.
Notation rt_got m :=
  (rw_cells bsegs m 0xc72f8 [C8 (Z_to_bv 64 0x161828); C8 (Z_to_bv 64 0xcd4f8); C8 (Z_to_bv 64 0xcfcf8);
                              C8 (Z_to_bv 64 0xd09e8); C8 (Z_to_bv 64 0xd09f0); C8 (Z_to_bv 64 0xd09e0)]).
(* [comment removed for export] *)
Notation rt_got_ric m := (rw_cells bsegs m 0xc7e70 [C8 (Z_to_bv 64 0xd09d9)]).
(* [comment removed for export] *)
Notation rt_shbase m := (rw_cells bsegs m 0xcfcf8 [C8 (Z_to_bv 64 0x7fff8000)]).
(* [comment removed for export] *)
Notation rt_inited m := (rw_cells bsegs m 0xd09d8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]).
(* [comment removed for export] *)
Notation rt_layout m := (rw_cells bsegs m 0xd09e0 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
(* [comment removed for export] *)
Notation rt_real_mem m := (rw_cells bsegs m 0xc91b0 [C8 (Z_to_bv 64 0xc0638); C8 (Z_to_bv 64 0xc0a3c)]).
Notation rt_real_wcslen m := (rw_cells bsegs m 0xc9160 [C8 (Z_to_bv 64 0xc0ec4)]).
Notation rt_real_read m := (rw_cells bsegs m 0xc9088 [C8 (Z_to_bv 64 0xc5d3c)]).
Notation rt_real_printf m := (rw_cells bsegs m 0xc90a8 [C8 (Z_to_bv 64 0xbff88); C8 (Z_to_bv 64 0xbce78)]).
