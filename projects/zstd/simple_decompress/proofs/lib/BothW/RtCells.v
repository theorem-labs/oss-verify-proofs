(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma no_image_asan : forall s1 s2, 0x629000 <= s1 -> no_image bsegs s1 s2.
Proof. intros s1 s2 H z Hz. apply ref_find_segment_none; lia. Qed.

(* [comment removed for export] *)
End CANSEC1.
Notation rt_got m :=
  (rw_cells bsegs m 0xcb990 [C8 (Z_to_bv 64 0x165e28); C8 (Z_to_bv 64 0xd1af8); C8 (Z_to_bv 64 0xd42f8);
                              C8 (Z_to_bv 64 0xd4fe8); C8 (Z_to_bv 64 0xd4ff0); C8 (Z_to_bv 64 0xd4fe0)]).
(* [comment removed for export] *)
Notation rt_got_ric m := (rw_cells bsegs m 0xcc508 [C8 (Z_to_bv 64 0xd4fd9)]).
(* [comment removed for export] *)
Notation rt_shbase m := (rw_cells bsegs m 0xd42f8 [C8 (Z_to_bv 64 0x7fff8000)]).
(* [comment removed for export] *)
Notation rt_inited m := (rw_cells bsegs m 0xd4fd8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]).
(* [comment removed for export] *)
Notation rt_layout m := (rw_cells bsegs m 0xd4fe0 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
(* [comment removed for export] *)
Notation rt_real_mem m := (rw_cells bsegs m 0xcd848 [C8 (Z_to_bv 64 0xc4ccc); C8 (Z_to_bv 64 0xc50d0)]).
Notation rt_real_wcslen m := (rw_cells bsegs m 0xcd7f8 [C8 (Z_to_bv 64 0xc5558)]).
Notation rt_real_read m := (rw_cells bsegs m 0xcd720 [C8 (Z_to_bv 64 0xca3d0)]).
Notation rt_real_printf m := (rw_cells bsegs m 0xcd740 [C8 (Z_to_bv 64 0xc461c); C8 (Z_to_bv 64 0xc150c)]).
