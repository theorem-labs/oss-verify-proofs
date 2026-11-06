(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a): the walk of reac_rate_drivable_csv
   (0x84074, 980 bytes, 245 instructions) against lib/A/RtPgCSpec.v rt_drivable_csv_specX at image A's constants.
   Proves function reac_rate_drivable_csv.

   The walk is the three parts of lib/A/RtPgDcsvDefs.v, chained by SRr_bind over the loop's three passes:
     the prologue (RtPgDcsvPro.v) from the entry to the loop head 0x8420c with the class-1 side-stack frame
     seated; the body (RtPgDcsvBody.v) once per pass i = 0, 1, 2, each from the head to the head of the next
     pass or, at i = 2, to the tail 0x842f4; the tail (RtPgDcsvEpi.v) to the `ret`.
   The cut state dc_core carries the function's journal with the frame (1, pos) on its own list, the registers
   the later parts read, the twelve cells of the real frame, the thirteen saves, the frame's flag pointer, the
   bytes of tmp (the model's csv_prefix of the mask after i passes, and a NUL), the frame's sixteen shadow
   bytes, and the string, table and read-only facts the contract's premises carry.

   rt_drivable_csv_of_parts is the chaining over any three proofs of the parts; rt_drivable_csv_A is the top, at
   the parts' own theorems dc_pro / dc_body / dc_epi, with dc_rt (RtPgDcsvDefs.v, the runtime laws and image A's
   symbol and read-only facts the walk calls on) as its only hypothesis. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgDcsvDefs.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require RtPgDcsvPro RtPgDcsvBody RtPgDcsvEpi.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Rt Require Import SnprintfRateDef.
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
(* the three parts *)
Hypothesis PRO : dc_pro_stmt B.
Hypothesis BODY : dc_body_stmt B.
Hypothesis EPI : dc_epi_stmt B MT.

Theorem rt_drivable_csv_of_parts :
rt_drivable_csv_specX rsegs B MT A_DCSV DC_CID T_dcsv_STK SNP_FMT SNP_COMMA SNP_EMPTY A_ORD.
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
change (SRr rsegs W (cfg_at rsegs A_DCSV regs memc mdc) (dc_post B MT c)).
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

(* ============================ the top ============================ *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis RT : dc_rt B MT.

Theorem rt_drivable_csv_A :
rt_drivable_csv_specX rsegs B MT A_DCSV DC_CID T_dcsv_STK SNP_FMT SNP_COMMA SNP_EMPTY A_ORD.
Proof using RT.
exact (rt_drivable_csv_of_parts B MT (RtPgDcsvPro.dc_pro B MT RT) (RtPgDcsvBody.dc_body B MT RT)
  (RtPgDcsvEpi.dc_epi B MT RT)).
Qed.
End a.

Print Assumptions rt_drivable_csv_of_parts.
Print Assumptions rt_drivable_csv_A.
