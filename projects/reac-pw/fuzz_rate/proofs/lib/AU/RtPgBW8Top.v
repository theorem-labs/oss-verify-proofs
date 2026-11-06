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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgW8Top.v, with its module paths and module names changed; 24 of its 48 lines of code are new or changed and 11 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW8Top.v at 8f1d7a0a9084 for the same unit's
   image B (fuzz_rate.asan-ubsan): the piece statement is lib/AU/RtPgSegB.v's rsb_piece_W8_stmt; the runs are image
   B's four (lib/AU/RtPgBW8P.v, RtPgBW8C.v, RtPgBW8D.v) and the block lib/AU/RtPgBW8Core.v's; pod_write_ent's
   contract comes from its own walk (lib/AU/PweRun.v pod_write_ent_B); AR_laws is the kernel's YG0q.AR_laws_ok. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14): the lane's delivered lemma, the walk piece
   "write + record" of LLVMFuzzerTestOneInput (0x8076c), J 0x820dc -> C 0x813a0 / CL 0x824c0, as lib/AU/RtPgSegB.v
   states it. Proves no function (kind: segment lemma).

   It composes the pieces the lane proved: the four engine runs (lib/AU/RtPgBW8P.v run P, RtPgBW8C.v runs C1 and C0,
   RtPgBW8D.v run D) through lib/AU/RtPgBW8Core.v's rbw8_core, and lib/AU/RtPgBW8.v's rbw8_piece over it.
   rsb_piece_W8_pwe takes pod_write_ent's contract (lib/AU/PweSpec.v pod_write_ent_specX at 0x83cc4) as a hypothesis;
   rsb_piece_W8 discharges it with pod_write_ent's own walk (lib/AU/PweRun.v pod_write_ent_B). What is left as a
   hypothesis of rsb_piece_W8: the meter laws ameter_laws MT (as every piece of the walk), the kernel's contracts of
   the two intrinsics (YG0d.aintrin_realizes at __asan_memcpy 0x518b8 and __asan_memset 0x51d54, which the runtime
   layer supplies; the memset is pod_write_ent's), and the two symbol-record cells pod_write_ent reads the shadow
   offset through (as_got_shadow B = 0x9c170, as_shadow_cell B = 0xa4f38). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YO09 YI16 YE00 YE01 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import PweSpec RtPgImgB RtPgSegB RtPgStepsB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require PweKit PweRun.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import
RtPgBW8Kit RtPgBW8P RtPgBW8C RtPgBW8D RtPgBW8Core RtPgBW8.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy RBW8_CPY.

(* the piece, with pod_write_ent's contract as a hypothesis *)
Theorem rsb_piece_W8_pwe : pod_write_ent_specX rsegs B MT RBW8_PWE -> rsb_piece_W8_stmt rsegs B MT.
Proof using MTL AMEMCPY.
intros PWE. pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
apply (rbw8_piece B MT MTL LAWS).
exact (rbw8_core B MT MTL LAWS AMEMCPY PWE
  (rbw8_runP B MT MTL LAWS) (rbw8_runC1 B MT MTL LAWS) (rbw8_runC0 B MT MTL LAWS) (rbw8_runD B MT MTL LAWS)).
Qed.

(* the piece, with pod_write_ent's contract from its walk *)
Hypothesis AMEMSET : aintrin_realizes rsegs B OSet RTSB_MEMSET.
Hypothesis HBgot : as_got_shadow B = PweKit.PWE_GOT.
Hypothesis HBcell : as_shadow_cell B = PweKit.PWE_CELL.
Theorem rsb_piece_W8 : rsb_piece_W8_stmt rsegs B MT.
Proof using MTL AMEMCPY AMEMSET HBgot HBcell.
apply rsb_piece_W8_pwe.
exact (PweRun.pod_write_ent_B B MT MTL HBgot HBcell AMEMCPY AMEMSET).
Qed.
End t.

Print Assumptions rsb_piece_W8_pwe.

Print Assumptions rsb_piece_W8.
