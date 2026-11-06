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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgW8Top.v, with its module names changed; 56 of its 75 lines of code are new or changed and 16 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgDcsv.v at 693242f63d54 for image B
   (fuzz_rate.asan-ubsan): the image is images.AsanUbsan; the parts are lib/AU/RtPgDcsvProB.v, RtPgDcsvBodyB.v and
   RtPgDcsvEpiB.v over lib/AU/RtPgDcsvDefsB.v; the top is stated at image B's entry 0x842d8 with image B's string and
   table addresses (equal to image A's). *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; addresses measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): the walk of
   reac_rate_drivable_csv (0x842d8, 1056 bytes, 264 instructions) against lib/A/RtPgCSpec.v rt_drivable_csv_specX
   at image B's constants. Proves function reac_rate_drivable_csv.

   The walk is the three parts of lib/AU/RtPgDcsvDefsB.v, chained by SRr_bind over the loop's three passes:
     the prologue (RtPgDcsvProB.v) from the entry to the loop head 0x84478 with the class-1 side-stack frame
     seated; the body (RtPgDcsvBodyB.v) once per pass i = 0, 1, 2, each from the head to the head of the next
     pass or, at i = 2, to the tail 0x8457c, with the two pointer-overflow trap branches of a pass decided not
     taken; the tail (RtPgDcsvEpiB.v) to the `ret`, with its three trap branches decided not taken.
   The cut state dc_core carries the function's journal with the frame (1, pos) on its own list, the registers
   the later parts read, the twelve cells of the real frame, the thirteen saves, the frame's flag pointer, the
   bytes of tmp (the model's csv_prefix of the mask after i passes, and a NUL), the frame's sixteen shadow
   bytes, and the string, table and read-only facts the contract's premises carry.

   rt_drivable_csv_of_parts is the chaining over any three proofs of the parts; rt_drivable_csv_B is the top, at
   the parts' own theorems dc_pro / dc_body / dc_epi, with dc_rt (RtPgDcsvDefsB.v: the runtime laws, the class-1
   frame law, the __asan_memcpy and snprintf wrapper contracts at image B's entries 0x518b8 and 0x4222c, and image
   B's symbol and read-only facts the walk calls on) as its only hypothesis. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require RateCfg RateCsv.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgDcsvDefsB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require RtPgDcsvProB RtPgDcsvBodyB RtPgDcsvEpiB.
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
(* the three parts *)
Hypothesis PRO : dc_pro_stmt B.
Hypothesis BODY : dc_body_stmt B.
Hypothesis EPI : dc_epi_stmt B MT.

Theorem rt_drivable_csv_of_parts :
rt_drivable_csv_specX rsegs B MT B_DCSV DC_CID T_dcsv_STK SNP_FMT SNP_COMMA SNP_EMPTY B_ORD.
Proof using PRO BODY EPI.
unfold rt_drivable_csv_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs mask buf n
  HPRE H10 Hmask H11 H12 Hn Hbuf Hcid Hcnt Hfmt Hcomma Hempty Hord Hrom Hfrm.
set (c := DCx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs mask buf n).
assert (Hpre : dc_pre B c).
{ unfold dc_pre, c.
  cbn [dx_STK dx_sp0 dx_FP dx_ly dx_S dx_W0 dx_mem0 dx_md0 dx_own dx_k dx_lyc dx_Sc dx_W dx_memc dx_mdc
       dx_regs dx_mask dx_buf dx_n].
  unfold dx_S0. cbn [dx_regs].
  repeat (split; [solve [assumption | exact Hbuf | exact Hcnt]|]). exact Hfrm. }
change (SRr rsegs W (cfg_at rsegs B_DCSV regs memc mdc) (dc_post B MT c)).
eapply SRr_bind; [exact (PRO c Hpre)|].
cbv beta. intros W1 cf1 Hw1 (fq1 & pos & S1 & regs1 & mem1 & md1 & -> & HL0).
eapply SRr_bind; [exact (BODY c 0%nat fq1 pos S1 W1 regs1 mem1 md1 Hpre HL0)|].
cbv beta. intros W2 cf2 Hw2 HN0. cbn [dc_next] in HN0.
destruct HN0 as (fq2 & pos2 & S2 & regs2 & mem2 & md2 & -> & HL1).
eapply SRr_bind; [exact (BODY c 1%nat fq2 pos2 S2 W2 regs2 mem2 md2 Hpre HL1)|].
cbv beta. intros W3 cf3 Hw3 HN1. cbn [dc_next] in HN1.
destruct HN1 as (fq3 & pos3 & S3 & regs3 & mem3 & md3 & -> & HL2).
eapply SRr_bind; [exact (BODY c 2%nat fq3 pos3 S3 W3 regs3 mem3 md3 Hpre HL2)|].
cbv beta. intros W4 cf4 Hw4 HN2. cbn [dc_next] in HN2.
destruct HN2 as (fq4 & pos4 & S4 & regs4 & mem4 & md4 & -> & HC3).
exact (EPI c fq4 pos4 S4 W4 regs4 mem4 md4 Hpre HC3).
Qed.
End t.

(* ============================ the top ============================
   At image B's entry and image B's addresses of the format "%s%d", the separators "," and "" and the table
   `ordered` (the call the image-B list segment M03 states: lib/AU/RtPgW14CsvB.v's hypothesis DCSV). *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis RT : dc_rt B MT.

Theorem rt_drivable_csv_B :
rt_drivable_csv_specX rsegs B MT 0x842d8 1 T_dcsv_STK 0x216c0 0x216e0 0x21700 0x216a0.
Proof using RT.
change (rt_drivable_csv_specX rsegs B MT B_DCSV DC_CID T_dcsv_STK SNP_FMT SNP_COMMA SNP_EMPTY B_ORD).
exact (rt_drivable_csv_of_parts B MT (RtPgDcsvProB.dc_pro B MT RT) (RtPgDcsvBodyB.dc_body B MT RT)
  (RtPgDcsvEpiB.dc_epi B MT RT)).
Qed.
End a.

Print Assumptions rt_drivable_csv_of_parts.
Print Assumptions rt_drivable_csv_B.
About rt_drivable_csv_B.
