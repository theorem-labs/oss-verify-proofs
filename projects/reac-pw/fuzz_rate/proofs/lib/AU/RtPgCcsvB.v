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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgW8Top.v, with its module names changed; 30 of its 49 lines of code are new or changed and 16 lines of the source are left out. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on its unstripped twin
   sha256 a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1): the walk of check_csv (0x837c0, 1284
   bytes, 321 instructions) against lib/A/RtPgCSpec.v rt_check_csv_specX at image B's constants: entry 0x837c0, the
   class-2 side-stack frame, the stack bound RtPgImgB.T_csv_STK_B and closed_list at 0x21520.
   Proves function check_csv.

   The walk is the four segments of lib/AU/RtPgCcsvCutB.v, chained by its cc_chain (SRr_bind):
     S0 (RtPgCcsvS0B.v) the prologue, the class-2 frame call and the frame's header and shadow, 0x837c0 -> 0x83948;
     S1 (RtPgCcsvS1B.v) the three passes that build the list in want, 0x83948 -> 0x83a90 (image B's four bound
        checks there are not taken);
     S2 (RtPgCcsvS2B.v) the tail: the length test, the n = 0 / n > 0 arms with the bcmp wrapper call, the
        pointer-overflow check of buf + c (not taken), 0x83a90 -> 0x83b38;
     S3 (RtPgCcsvS3B.v) the release of the frame and the epilogue, 0x83b38 -> `ret` 0x83c6c.
   AR_laws (lib/Reusable/YG0q.v AR_laws_ok) is a theorem and is not a hypothesis here. The Section hypotheses are
   the runtime's laws, image B's symbol-record facts and image B's read-only data facts the segments call on:
   - the runtime: HAPI (api_env), ML (model_laws), SMP (stack_malloc_progressP), ASM2 (the class-2 frame
     allocation's contract, astack_malloc_realizes at class 2), FFL (frame_flag_lawP, the frame flag law the
     release uses), ABCMP (the bcmp wrapper's contract abcmp_realizes at image B's entry 0x42200 =
     RtPgStepsB.RTSB_BCMP), and the meter's MTL / MTF;
   - image B's symbol record: the class-2 allocation entry 0x3d164 (HSM2), the GOT words 0x9c170 / 0x9c1c8 (HGOTS /
     HGOTU) and the cells they point at, 0xa4f38 / 0xa4f40 (HCELLS / HCELLU);
   - image B's read-only data: HIMG, RtPgCSpec.rt_img_facts at image B's record RtPgImgB.rate_himg_B and range
     [IMG_LO, IMG_TOP), which rebuilds closed_list's rt_i32tab after the frame call.
   Each is of the type image A's walk of check_csv takes it at (lib/A/RtPgCcsvS0.v, S1, S3; the bcmp wrapper's
   contract at image A's entry in image A's tail), at image B's values; image B's close discharges them. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgCcsvCutB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require RtPgCcsvS0B RtPgCcsvS1B RtPgCcsvS2B RtPgCcsvS3B.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* image B's loaded segments, as lib/AU/RtPgCcsvCutB.v names them *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
(* the runtime's laws and contracts the segments call on (image B's close) *)
Hypothesis HAPI : api_env rsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASM2 : astack_malloc_realizes rsegs B 2.
Hypothesis FFL : frame_flag_lawP rsegs B.
Hypothesis ABCMP : abcmp_realizes rsegs B 0x42200.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
(* image B's symbol record: the class-2 allocation entry, the two GOT words and their cells *)
Hypothesis HSM2 : pc_stack_malloc (as_code B) 2 = 0x3d164.
Hypothesis HGOTS : as_got_shadow B = 0x9c170.
Hypothesis HGOTU : as_got_uar B = 0x9c1c8.
Hypothesis HCELLS : as_shadow_cell B = 0xa4f38.
Hypothesis HCELLU : as_uar_cell B = 0xa4f40.
(* image B's read-only data after the frame call *)
Hypothesis HIMG : rt_img_facts rsegs B rate_himg_B IMG_LO IMG_TOP.

Theorem rt_check_csv_B : rt_check_csv_specX rsegs B MT 0x837c0 2 T_csv_STK_B 0x21520.
Proof.
pose proof (AR_laws_ok rsegs B) as LAWS.
exact (cc_chain B MT
  (RtPgCcsvS0B.ccsv_S0 B MT LAWS HAPI ML SMP ASM2 MTL MTF HSM2 HGOTS HGOTU HCELLS HCELLU)
  (RtPgCcsvS1B.ccsv_S1 B MT LAWS HIMG)
  (RtPgCcsvS2B.ccsv_S2 B MT ABCMP)
  (RtPgCcsvS3B.ccsv_S3 B MT MTF ML FFL)).
Qed.
End t.

About rt_check_csv_B.
Print Assumptions rt_check_csv_B.
