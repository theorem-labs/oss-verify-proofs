(* B twin (fm.asan-ubsan) of lib/A/FMW_cno.v (a working branch 31d1eb57a40).
   check_no_overread 0x80bd4 (fuzz_manifest.c:176-189): check_no_overread_spec at CTX_check_no_overread, by chaining the
   17 segment lemmas of lib/B/FMW_cno_*.v over the resume points of lib/B/FMW_cno0.v. The context fixes ch = [] and
   ra = 0x80a6c (CNO_RA); quiet fixes fail = SIZE_MAX. Every inline shadow check tests a byte inside a block the
   function has just allocated, so the slow paths and their `jal __asan_report_store1` (0x80eac .. 0x80f00) are refuted,
   and the twelve UBSan overflow checks to 0x80ea0 are refuted in the segments that hold them. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d YC20 YC85.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI16 YK06 YM05 YCbp YG05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YF0l YF0m YCej.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_kit FMW_K FMW_kitS FMW_seg FMW_cno0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_cno_A1 FMW_cno_B1 FMW_cno_C1 FMW_cno_A2 FMW_cno_C3 FMW_cno_A3 FMW_cno_B2 FMW_cno_C2 FMW_cno_A4 FMW_cno_D FMW_cno_E1 FMW_cno_E2.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section S. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis FB : FmB B.                                   (* FMW_seg.v:32: code addresses, GOT/cell values, statics not owned *)
Hypothesis HB : TfibSyms B.                              (* YF0m.v (lib/ReusableB) *)
Hypothesis IMG : fm_img_facts tfibsegs B.                (* FMH_Fn.v:56 *)
Hypothesis UNIV : fm_univ B.                             (* FMH_Fn.v:70: incl Tfib_universe (as_universe B) *)
Hypothesis AMALLOC4 : amalloc04_rule tfibsegs B ameter_triv.   (* YC5d.v:57; ameter_triv YCbp.v:17, mo_ok = True *)
Hypothesis AFREE4 : afree04_rule tfibsegs B ameter_triv.       (* YC5d.v:76 *)
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy PC_memcpy.  (* YG0d.v:318 *)
Hypothesis AMEMSET : aintrin_realizes tfibsegs B OSet PC_memset.
Hypothesis NAMES : names_spec tfibsegs B CTX_lv2_locate_manifest_names.   (* FMH_Fn.v:234 *)

Theorem check_no_overread_holds : check_no_overread_spec tfibsegs B CTX_check_no_overread.
Proof.
intros ly S W regs mem md ch up tp ub tb live peak cnt fail HPRE HCTX H10 H11 H12 H13 Hsu Hst Hnzu Hnzt Hhu Hht
  Hlu Htn HG HQ Hlive Hev Hbb.
(* the one context: no frame chain below, ra = CNO_RA = 0x80a6c (LLVMFuzzerTestOneInput) *)
assert (Ech : ch = [] /\ raZ regs = CNO_RA).
{ unfold CTX_check_no_overread in HCTX. destruct HCTX as [E | []].
  destruct ch as [|c ch].
  - cbn [spine map] in E. injection E as E1. split; [reflexivity | symmetry; exact E1].
  - cbn [spine map] in E. injection E as _ E2. discriminate E2. }
destruct Ech as [-> Hra].
pose proof HQ as (Hfail & _). subst fail.
set (cx := mkNX ly S W regs mem md up tp ub tb live peak cnt).
assert (HBX : cno_base B cx)
  by exact (conj HPRE (conj Hra (conj H10 (conj H11 (conj H12 (conj H13 (conj Hsu (conj Hst (conj Hnzu (conj Hnzt
    (conj Hhu (conj Hht (conj Hlu (conj Htn (conj HG (conj HQ (conj Hlive (conj Hev Hbb)))))))))))))))))).
change (SRr tfibsegs (nx_W cx) (cfg_at tfibsegs A_check_no_overread (nx_regs cx) (nx_mem cx) (nx_md cx)) (cno_post B cx)).
clearbody cx.
(* the copy phase *)
eapply cno_seg_0; try eassumption. intros ly1 S1 W1 regs1 mem1 md1 u1 HP1.
eapply cno_seg_P1; try eassumption. intros ly2 S2 W2 regs2 mem2 md2 HQ1.
eapply cno_seg_Q1; try eassumption. intros ly3 S3 W3 regs3 mem3 md3 HR1.
eapply cno_seg_R1; try eassumption. intros ly4 S4 W4 regs4 mem4 md4 t1 HP2.
eapply cno_seg_P2; try eassumption. intros ly5 S5 W5 regs5 mem5 md5 HQ2.
eapply cno_seg_Q2; try eassumption. intros ly6 S6 W6 regs6 mem6 md6 HR2.
eapply cno_seg_R2; try eassumption. intros ly7 S7 W7 regs7 mem7 md7 u2 HP3.
eapply cno_seg_P3; try eassumption. intros ly8 S8 W8 regs8 mem8 md8 HQ3.
eapply cno_seg_Q3; try eassumption. intros ly9 S9 W9 regs9 mem9 md9 HR3.
eapply cno_seg_R3; try eassumption. intros ly10 S10 W10 regs10 mem10 md10 t2 HP4.
eapply cno_seg_P4; try eassumption. intros ly11 S11 W11 regs11 mem11 md11 HQ4.
eapply cno_seg_Q4; try eassumption. intros ly12 S12 W12 regs12 mem12 md12 HR4.
(* the two reader calls *)
eapply cno_seg_R4; try eassumption. intros ly13 S13 W13 regs13 mem13 md13 HN1.
eapply cno_seg_N1; try eassumption. intros ly14 S14 W14 regs14 mem14 md14 HN2.
(* the four frees *)
eapply cno_seg_N2; try eassumption. intros ly15 S15 W15 regs15 mem15 md15 HF1.
eapply cno_seg_F1; try eassumption. intros ly16 S16 W16 regs16 mem16 md16 HF2.
eapply cno_seg_F2; try eassumption. intros ly17 S17 W17 regs17 mem17 md17 HF3.
eapply cno_seg_F3; eassumption.
Qed.
End S.

Print Assumptions check_no_overread_holds.
