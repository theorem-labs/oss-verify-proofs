(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import BImg.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma no_image_asan : forall s1 s2, 0x6d4000 <= s1 -> no_image bsegs s1 s2.
Proof. intros s1 s2 H z Hz. apply ref_find_segment_none; lia. Qed.

(* [comment removed for export] *)
End CANSEC1.
Notation rt_got m :=
  (rw_cells bsegs m 0x173cc8 [C8 (Z_to_bv 64 0x20efa8); C8 (Z_to_bv 64 0x17ac78); C8 (Z_to_bv 64 0x17d478);
                              C8 (Z_to_bv 64 0x17e168); C8 (Z_to_bv 64 0x17e170); C8 (Z_to_bv 64 0x17e160)]).
(* [comment removed for export] *)
Notation rt_got_ric m := (rw_cells bsegs m 0x174840 [C8 (Z_to_bv 64 0x17e159)]).
(* [comment removed for export] *)
Notation rt_shbase m := (rw_cells bsegs m 0x17d478 [C8 (Z_to_bv 64 0x7fff8000)]).
(* [comment removed for export] *)
Notation rt_inited m := (rw_cells bsegs m 0x17e158 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]).
(* [comment removed for export] *)
Notation rt_layout m := (rw_cells bsegs m 0x17e160 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
(* [comment removed for export] *)
Notation rt_real_mem m := (rw_cells bsegs m 0x175d18 [C8 (Z_to_bv 64 0x165dd8); C8 (Z_to_bv 64 0x1661dc)]).
Notation rt_real_wcslen m := (rw_cells bsegs m 0x175c68 [C8 (Z_to_bv 64 0x1669e0)]).
Notation rt_real_read m := (rw_cells bsegs m 0x175b68 [C8 (Z_to_bv 64 0x16c7dc)]).
Notation rt_real_printf m := (rw_cells bsegs m 0x175b98 [C8 (Z_to_bv 64 0x163a9c); C8 (Z_to_bv 64 0x15d7b8)]).
