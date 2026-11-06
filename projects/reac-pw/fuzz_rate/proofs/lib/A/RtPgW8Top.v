(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at at 28fdc66416e (the call of
   __asan_memcpy in the journal) restated as hd_memcpy with the wrapper's same_but_materialized kept in the post as
   same_io, and proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v at 9e73ed57244 (m2_img_zone, m2_cstr_kept, the .rodata
   zone of m2_szone) restated as hd_img_zone / hd_cstr_kept / hd_szone for the .rodata range only; the rest of the
   file is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v, with its module paths and module names changed; 428 of its 517 lines of code are new or changed and 925 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgW6cTail.v, with its module paths changed; 758 of its 829 lines of code are new or changed and 446 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5Int.v at 3e85ad4cf5dd for
   reac-pw/fuzz_rate image A: the chained piece is rate's W8 instead of role's Int-7 pod, so there are four
   engine runs and three calls instead of two and one, the calls are __asan_memcpy as well as __asan_memset,
   the post is RtPgSteps.rts_post instead of a local copy, and the source of the two copies is the frame
   object e (which asks the frame / block separation of the kernel's AR_sep_law). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgW8Core.v; 17 of its 35 lines of code are new or changed and 811 lines of the source are left out. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a): the lane's delivered lemma, the walk
   piece "write + record" of LLVMFuzzerTestOneInput (0x80714), J 0x81e00 -> C 0x8127c / CL 0x82484, as
   lib/A/RtPgSeg.v states it. Proves no function (kind: segment lemma).

   It composes the pieces the lane proved: the four engine runs (lib/A/RtPgW8A.v, RtPgW8B.v, RtPgW8C.v,
   RtPgW8D.v) through lib/A/RtPgW8Core.v's rw8_core, and lib/A/RtPgW8.v's rw8_piece over it. What is left as a
   hypothesis is the kernel's contract of the two intrinsics the piece calls (YG0d.aintrin_realizes at
   __asan_memcpy 0x51860 and __asan_memset 0x51cfc), which the lane's runtime layer supplies. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YO09 YI16 YE00 YE01 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA RtPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import
RtPgW8Kit RtPgW8A RtPgW8B RtPgW8C RtPgW8D RtPgW8Core RtPgW8.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy RW8_CPY.
Hypothesis AMEMSET : aintrin_realizes rsegs B OSet RW8_SET.

Theorem rs_piece_W8 : rs_piece_W8_stmt rsegs B MT.
Proof using MTL LAWS AMEMCPY AMEMSET.
apply (rw8_piece B MT MTL LAWS).
exact (rw8_core B MT MTL LAWS AMEMCPY AMEMSET
  (rw8_runA B MT MTL LAWS) (rw8_runB B MT MTL LAWS) (rw8_runC1 B MT MTL LAWS)
  (rw8_runC0 B MT MTL LAWS) (rw8_runD B MT MTL LAWS)).
Qed.
End t.

Print Assumptions rs_piece_W8.
