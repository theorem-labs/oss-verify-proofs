(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma no_image_asan : forall s1 s2, 0x671000 <= s1 -> no_image bsegs s1 s2.
Proof. intros s1 s2 H z Hz. apply ref_find_segment_none; lia. Qed.

(* [comment removed for export] *)
End CANSEC1.
Notation rt_got m :=
  (rw_cells bsegs m 0x112a70 [C8 (Z_to_bv 64 0x1ad1a8); C8 (Z_to_bv 64 0x118e78); C8 (Z_to_bv 64 0x11b678);
                              C8 (Z_to_bv 64 0x11c368); C8 (Z_to_bv 64 0x11c370); C8 (Z_to_bv 64 0x11c360)]).
(* [comment removed for export] *)
Notation rt_got_ric m := (rw_cells bsegs m 0x1135e8 [C8 (Z_to_bv 64 0x11c359)]).
(* [comment removed for export] *)
Notation rt_shbase m := (rw_cells bsegs m 0x11b678 [C8 (Z_to_bv 64 0x7fff8000)]).
(* [comment removed for export] *)
Notation rt_inited m := (rw_cells bsegs m 0x11c358 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]).
(* [comment removed for export] *)
Notation rt_layout m := (rw_cells bsegs m 0x11c360 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
(* [comment removed for export] *)
Notation rt_real_mem m := (rw_cells bsegs m 0x1149c0 [C8 (Z_to_bv 64 0x108898); C8 (Z_to_bv 64 0x108c9c)]).
Notation rt_real_wcslen m := (rw_cells bsegs m 0x114940 [C8 (Z_to_bv 64 0x1091c8)]).
Notation rt_real_read m := (rw_cells bsegs m 0x114880 [C8 (Z_to_bv 64 0x10e084)]).
Notation rt_real_printf m := (rw_cells bsegs m 0x1148a0 [C8 (Z_to_bv 64 0x106534); C8 (Z_to_bv 64 0x100da8)]).
