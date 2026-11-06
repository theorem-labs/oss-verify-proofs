(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma no_image_asan : forall s1 s2, 0x5f6000 <= s1 -> no_image bsegs s1 s2.
Proof. intros s1 s2 H z Hz. apply ref_find_segment_none; lia. Qed.

(* [comment removed for export] *)
End CANSEC1.
Notation rt_got m :=
  (rw_cells bsegs m 0x99000 [C8 (Z_to_bv 64 0x132b68); C8 (Z_to_bv 64 0x9e838); C8 (Z_to_bv 64 0xa1038);
                              C8 (Z_to_bv 64 0xa1d28); C8 (Z_to_bv 64 0xa1d30); C8 (Z_to_bv 64 0xa1d20)]).
(* [comment removed for export] *)
Notation rt_got_ric m := (rw_cells bsegs m 0x99b78 [C8 (Z_to_bv 64 0xa1d19)]).
(* [comment removed for export] *)
Notation rt_shbase m := (rw_cells bsegs m 0xa1038 [C8 (Z_to_bv 64 0x7fff8000)]).
(* [comment removed for export] *)
Notation rt_inited m := (rw_cells bsegs m 0xa1d18 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]).
(* [comment removed for export] *)
Notation rt_layout m := (rw_cells bsegs m 0xa1d20 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
(* [comment removed for export] *)
Notation rt_real_mem m := (rw_cells bsegs m 0x9ae90 [C8 (Z_to_bv 64 0x92340); C8 (Z_to_bv 64 0x92744)]).
Notation rt_real_wcslen m := (rw_cells bsegs m 0x9ae40 [C8 (Z_to_bv 64 0x92bcc)]).
Notation rt_real_read m := (rw_cells bsegs m 0x9ad68 [C8 (Z_to_bv 64 0x97a44)]).
Notation rt_real_printf m := (rw_cells bsegs m 0x9ad88 [C8 (Z_to_bv 64 0x91c90); C8 (Z_to_bv 64 0x8eb80)]).
