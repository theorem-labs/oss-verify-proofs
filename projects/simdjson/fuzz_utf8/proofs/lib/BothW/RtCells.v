(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import BImg.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma no_image_asan : forall s1 s2, 0x6d2000 <= s1 -> no_image bsegs s1 s2.
Proof. intros s1 s2 H z Hz. apply ref_find_segment_none; lia. Qed.

(* [comment removed for export] *)
End CANSEC1.
Notation rt_got m :=
  (rw_cells bsegs m 0x171fe8 [C8 (Z_to_bv 64 0x20cba8); C8 (Z_to_bv 64 0x178878); C8 (Z_to_bv 64 0x17b078);
                              C8 (Z_to_bv 64 0x17bd68); C8 (Z_to_bv 64 0x17bd70); C8 (Z_to_bv 64 0x17bd60)]).
(* [comment removed for export] *)
Notation rt_got_ric m := (rw_cells bsegs m 0x172b60 [C8 (Z_to_bv 64 0x17bd59)]).
(* [comment removed for export] *)
Notation rt_shbase m := (rw_cells bsegs m 0x17b078 [C8 (Z_to_bv 64 0x7fff8000)]).
(* [comment removed for export] *)
Notation rt_inited m := (rw_cells bsegs m 0x17bd58 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]).
(* [comment removed for export] *)
Notation rt_layout m := (rw_cells bsegs m 0x17bd60 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
(* [comment removed for export] *)
Notation rt_real_mem m := (rw_cells bsegs m 0x174058 [C8 (Z_to_bv 64 0x16438c); C8 (Z_to_bv 64 0x164790)]).
Notation rt_real_wcslen m := (rw_cells bsegs m 0x173fa8 [C8 (Z_to_bv 64 0x164f94)]).
Notation rt_real_read m := (rw_cells bsegs m 0x173ea8 [C8 (Z_to_bv 64 0x16ad90)]).
Notation rt_real_printf m := (rw_cells bsegs m 0x173ed8 [C8 (Z_to_bv 64 0x162050); C8 (Z_to_bv 64 0x15bd6c)]).
