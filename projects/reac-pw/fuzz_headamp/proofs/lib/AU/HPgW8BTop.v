(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at a529a88a618 (pa_i_memset_at, as
   hbp_i_memset_at; pa_i_bv5_cases, pa_i_cs, pa_i_pres and pa_i_mod16_sub, as hbp_i_*; pa_int7's route, one engine state
   up to each call and a fresh one after it) and proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at a529a88a618
   (pa_piece_int7, as hbp_piece_int7) for reac-pw/fuzz_headamp's image B: the block walked new against image B's own
   instructions (the scope stores of e, __asan_memset of e's body, the two header words, the out-of-line pod_write_ent
   under PweSpec.pod_write_ent_specX, the restores of the loop's three values), the cut states of lib/AU/HPgSeg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgPropInt.v; 532 of its 586 lines of code are new or changed and 907 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgW8B.v; 12 of its 39 lines of code are new or changed and 559 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the builder piece W8 of
   LLVMFuzzerTestOneInput 0x80c40, J 0x82618 -> C 0x81888 / CL 0x82a18 (pod.h:428-433), the statement
   lib/AU/HPgSeg.v hsu_piece_W8_stmt at headamp_himg_B / headamp_bld_B: lib/AU/HPgW8B.v's composition with every
   block and bookkeeping lemma of lib/AU/HPgW8BKit.v proved (HPgW8BBlk.v: A, C0, C2, D; HPgW8BBlkC1.v: C1;
   HPgW8BJ.v: the facts of the cut J; HPgW8BFin.v: the cuts C and CL from the end state). Proves no function (kind:
   segment lemma).

   OPEN SECTION HYPOTHESES (the files that discharge them): MTL (the meter's laws, the harness's top); PWE, the
   contract PweSpec.pod_write_ent_specX at image B's entry 0x84634 (the walk of pod_write_ent, from fuzz_rate's image-B
   walk by relocation); ACPY, the kernel's contract of __asan_memcpy (YG0d.aintrin_realizes OCpy) at image B's entry
   0x51d8c (the runtime layer of image B). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSteps HPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import PweSpec HPgW8BKit HPgW8B.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require HPgW8BBlk HPgW8BBlkC1 HPgW8BJ HPgW8BFin.
Import ListNotations.
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis PWE : pod_write_ent_specX rsegs B MT HW8_PWE.
Hypothesis ACPY : aintrin_realizes rsegs B OCpy HW8_MEMCPY.

Theorem hsu_piece_W8_headamp_B : hsu_piece_W8_stmt rsegs B MT headamp_himg_B headamp_bld_B.
Proof.
apply (hsu_piece_W8_B B MT MTL PWE ACPY).
- apply HPgW8BBlk.hw8_blkA; assumption.
- apply HPgW8BBlk.hw8_blkC0; assumption.
- apply HPgW8BBlkC1.hw8_blkC1; assumption.
- apply HPgW8BBlk.hw8_blkC2; assumption.
- apply HPgW8BBlk.hw8_blkD; assumption.
- apply HPgW8BJ.hw8_J_facts; assumption.
- apply HPgW8BFin.hw8_finish; assumption.
Qed.
End b.

Print Assumptions hsu_piece_W8_headamp_B.
