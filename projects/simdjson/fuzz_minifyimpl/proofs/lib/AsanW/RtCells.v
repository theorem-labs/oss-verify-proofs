(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma no_image_asan : forall s1 s2, 0x6c7000 <= s1 -> no_image asegs s1 s2.
Proof. intros s1 s2 H z Hz. apply ref_find_segment_none; lia. Qed.

(* [comment removed for export] *)
End CANSEC1.
Notation rt_got m :=
  (rw_cells asegs m 0x167008 [C8 (Z_to_bv 64 0x201ee8); C8 (Z_to_bv 64 0x16dbb8); C8 (Z_to_bv 64 0x1703b8);
                              C8 (Z_to_bv 64 0x1710a8); C8 (Z_to_bv 64 0x1710b0); C8 (Z_to_bv 64 0x1710a0)]).
(* [comment removed for export] *)
Notation rt_got_ric m := (rw_cells asegs m 0x167b80 [C8 (Z_to_bv 64 0x171099)]).
(* [comment removed for export] *)
Notation rt_shbase m := (rw_cells asegs m 0x1703b8 [C8 (Z_to_bv 64 0x7fff8000)]).
(* [comment removed for export] *)
Notation rt_inited m := (rw_cells asegs m 0x171098 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]).
(* [comment removed for export] *)
Notation rt_layout m := (rw_cells asegs m 0x1710a0 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
(* [comment removed for export] *)
Notation rt_real_mem m := (rw_cells asegs m 0x169058 [C8 (Z_to_bv 64 0x159104); C8 (Z_to_bv 64 0x159508)]).
Notation rt_real_wcslen m := (rw_cells asegs m 0x168fa8 [C8 (Z_to_bv 64 0x159d0c)]).
Notation rt_real_read m := (rw_cells asegs m 0x168ea8 [C8 (Z_to_bv 64 0x15fb08)]).
Notation rt_real_printf m := (rw_cells asegs m 0x168ed8 [C8 (Z_to_bv 64 0x156dc8); C8 (Z_to_bv 64 0x150ae4)]).
