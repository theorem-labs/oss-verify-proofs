(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8j.v:156-159
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACes.v:275-277 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACim.v:270-271 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:1527-1530, 1556-1561 [Apache-2.0 OR MIT], for libreac/fuzz_identity's
   asan-ubsan build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_D4.v; 11 of its 49 lines of code are new or changed and 1040 lines of the source are left out. *)
(* seg_D4 hand: d4h_frame_read_stmt of lib/B/Prog/LLVMFuzzerTestOneInput_seg_D4_hand_stmt.v, the read premises
   src_ok / amem_range / shadow_hull_vis for m bytes inside a side-stack frame (cid, pos) of the state.
   - src_ok: the caller's present bytes, and 2 * ESTACK below sp is wider than the wrappers' ESTACK window.
   - amem_range: the frame lies in the application range below alloc_ceiling (YCbq.frames_bounds, from AR_frames_law).
   - shadow_hull_vis: the frame's shadow is present (IdentBFrame.shadow_hull_vis_of_frame, from AR_frames_law). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import LLVMFuzzerTestOneInput_seg_D4_hand_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
Section c.
Variable B : asyms.

Lemma d4h_frame_read : d4h_frame_read_stmt B.
Proof.
unfold d4h_frame_read_stmt.
intros LAWS ly S W mem md regs cid pos a m HAR Hin _ Hlo Hhi Hm Hv Hsp.
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (_ & Hce & Happ).
split; [|split].
- intros b Hb. split; [exact (Hv b Hb)|].
  pose proof (Hsp b Hb) as Hs. assert (Hes : ESTACK = 4096) by reflexivity.
  clear - Hs Hes. lia.
- exact (amem_range_sub_app _ _ a m Happ Hce Hlo Hhi Hm).
- intros Hm0. exact (shadow_hull_vis_of_frame SEGS B LAWS ly S W mem md cid pos a m HAR Hin Hlo Hhi Hm0).
Qed.

Check (d4h_frame_read : d4h_frame_read_stmt B).
End c.
End b.
End a.
