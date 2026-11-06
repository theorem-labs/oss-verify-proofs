(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma no_image_asan : forall s1 s2, 0x665000 <= s1 -> no_image asegs s1 s2.
Proof. intros s1 s2 H z Hz. apply ref_find_segment_none; lia. Qed.

(* [comment removed for export] *)
End CANSEC1.
Notation rt_got m :=
  (rw_cells asegs m 0x1072f0 [C8 (Z_to_bv 64 0x1a1628); C8 (Z_to_bv 64 0x10d2f8); C8 (Z_to_bv 64 0x10faf8);
                              C8 (Z_to_bv 64 0x1107e8); C8 (Z_to_bv 64 0x1107f0); C8 (Z_to_bv 64 0x1107e0)]).
(* [comment removed for export] *)
Notation rt_got_ric m := (rw_cells asegs m 0x107e68 [C8 (Z_to_bv 64 0x1107d9)]).
(* [comment removed for export] *)
Notation rt_shbase m := (rw_cells asegs m 0x10faf8 [C8 (Z_to_bv 64 0x7fff8000)]).
(* [comment removed for export] *)
Notation rt_inited m := (rw_cells asegs m 0x1107d8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]).
(* [comment removed for export] *)
Notation rt_layout m := (rw_cells asegs m 0x1107e0 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
(* [comment removed for export] *)
Notation rt_real_mem m := (rw_cells asegs m 0x109240 [C8 (Z_to_bv 64 0xfd118); C8 (Z_to_bv 64 0xfd51c)]).
Notation rt_real_wcslen m := (rw_cells asegs m 0x1091c0 [C8 (Z_to_bv 64 0xfda48)]).
Notation rt_real_read m := (rw_cells asegs m 0x109100 [C8 (Z_to_bv 64 0x102904)]).
Notation rt_real_printf m := (rw_cells asegs m 0x109120 [C8 (Z_to_bv 64 0xfadb4); C8 (Z_to_bv 64 0xf5628)]).
