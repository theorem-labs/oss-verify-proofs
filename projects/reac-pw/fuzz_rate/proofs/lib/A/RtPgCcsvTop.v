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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/AU/RtPgCcsvB.v, with its module paths, module names and addresses changed; 20 of its 48 lines of code are new or changed and 21 lines of the source are left out. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): the walk of check_csv
   (0x838e0, 1248 bytes, 312 instructions; fuzz_rate.c:217-229 with csv_holds :103-128 inlined).
   Proves function check_csv: `rt_check_csv_A` is lib/A/RtPgCSpec.v's `rt_check_csv_specX` at image A
   (a = 0x838e0, side-stack class 2, T = RtPgSiteA.T_csv_STK, closed_list at 0x21520).

   The proof is lib/A/RtPgCcsvCut.v's composer `cc_chain` (SRr_bind four times) applied to the four segment walks:
     S0  RtPgCcsvS0.ccsv_S0  0x838e0 -> 0x83a54  the saves, the realigned frame, the two .got reads, the class-2
                                                side-stack frame (__asan_stack_malloc_2 at 0x83958), the frame
                                                header and its 20 shadow granules;
     S1  RtPgCcsvS1.ccsv_S1  0x83a54 -> 0x83ba8  the three passes of the inlined csv_holds loop (want = the list of
                                                mask, its length in a4);
     S2  RtPgCcsvS2.ccsv_S2  0x83ba8 -> 0x83c40  the length test, the n = 0 / n > 0 arms, the bcmp wrapper call
                                                (0x421a8), the last byte;
     S3  RtPgCcsvS3.ccsv_S3  0x83c40 -> ret     the retired magic, the 32 0xf5 granules, the flag clear (the frame's
                                                inline release) and the epilogue, into RtPgCSpec.rt_cpost_o.
   Every abort arm (0x83d70, 0x83d88: the no-return helper, then abort) and every error-path arm
   (0x83d98 .. 0x83dbc) is shown not reached by the segment that holds its branch.

   The hypotheses below are what the segments take that no theorem of this tree gives; each is a fact of image A's
   symbol record B or of the meter, closed by the closing:
   - HAPI, ML, FFL: the closing's B record (A3's AD2l TfibB);
   - ASM2 : astack_malloc_realizes rsegs B 2   = A3's AF0u.v:516 stack_malloc2_contract at B;
   - ABCMP : abcmp_realizes rsegs B 0x421a8    = A3's AE2s.v:712 bcmp_icpt_contract at B
     (rsegs here and A3's AB1v.tfibsegs are both Asan.M.loaded_segments);
   - HSM2, HGOTS, HGOTU, HCELLS, HCELLU: image A's class-2 allocation entry and its two .got words and the cells
     they point at (measured on the pinned file: 0x9be70 holds 0xa4c38 = __asan_shadow_memory_dynamic_address,
     0x9bec8 holds 0xa4c40 = __asan_option_detect_stack_use_after_return);
   - HIMG : RtPgSiteA.rate_A_img_facts rsegs B, image A's record of its read-only data (A5 proves it);
   - MTL, MTF: the meter's laws (ameter_triv satisfies both, Reusable/YCbp.v).
   AR_laws (YG0q.v AR_laws_ok) and stack_malloc_progressP (model_laws' ml_stack_malloc_progress) are theorems and
   are not taken. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require RateCfg RateCsv.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgSiteA RtPgCcsvCut.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require RtPgCcsvS0 RtPgCcsvS1 RtPgCcsvS2 RtPgCcsvS3.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Local Open Scope Z_scope.

(* image A's loaded segments, the term every segment file names *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HAPI : api_env rsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP rsegs B.
Hypothesis ASM2 : astack_malloc_realizes rsegs B 2.
Hypothesis ABCMP : abcmp_realizes rsegs B 0x421a8.
Hypothesis HSM2 : pc_stack_malloc (as_code B) 2 = RtPgCcsvS0.CCS_SM2.
Hypothesis HGOTS : as_got_shadow B = RtPgCcsvS0.CCS_GOT_SH.
Hypothesis HGOTU : as_got_uar B = RtPgCcsvS0.CCS_GOT_UAR.
Hypothesis HCELLS : as_shadow_cell B = RtPgCcsvS0.CCS_SH_CELL.
Hypothesis HCELLU : as_uar_cell B = RtPgCcsvS0.CCS_UAR_CELL.
Hypothesis HIMG : rate_A_img_facts rsegs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.

Theorem rt_check_csv_A : rt_check_csv_specX rsegs B MT 0x838e0 2 T_csv_STK 0x21520.
Proof.
pose proof (AR_laws_ok rsegs B) as LAWS.
assert (SMP : stack_malloc_progressP B) by exact (ml_stack_malloc_progress _ ML).
apply cc_chain.
- eapply RtPgCcsvS0.ccsv_S0; eassumption.
- eapply RtPgCcsvS1.ccsv_S1; eassumption.
- eapply RtPgCcsvS2.ccsv_S2; eassumption.
- eapply RtPgCcsvS3.ccsv_S3; eassumption.
Qed.
End t.

About rt_check_csv_A.
Print Assumptions rt_check_csv_A.
