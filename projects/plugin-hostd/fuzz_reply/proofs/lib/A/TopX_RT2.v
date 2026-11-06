(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/TopX_RT2.v, with its module paths changed; 16 of its 58 lines of code are new or changed. *)
(* top_x group RT (TOPX-OWNERS.md (sha256 bb821fae800d; internal record)), the row lib/A/TopX_RT.v left
   open: A's top_x (W_LLVMFuzzerTestOneInput_top_x.v at integ bb9dae5d905)
     ASTRNLEN_x (top_x.v:264) : et_strnlen_spec_x TfibB ARX 0x10350 0x10370 (SIGMA WS_strnlen)
   PROVED at the instance ARX_rt (TopX_RT.v's verbatim copy of top_x.v:125-126's ARX:
   fun ly S Hp W mem md => ARcf (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = []).
   - The statement is RTx.v:172's astrnlen_whole_realizesM_x segs TfibB ARX_rt 0x10350 0x10370 (SIGMA WS_strnlen).
     It is convertible to top_x's et_strnlen_spec_x TfibB ARX 0x10350 0x10370 (SIGMA WS_strnlen) by unfolding only
     (W_LLVMFuzzerTestOneInput_event_x.v:162-177 against IcptRealizesX.v:124-139 / RTx.v:172-187): every premise and
     every post conjunct is the same text; ecall_pre_x is FCiface's on both sides; event_x's et_consts_view
     (W_LLVMFuzzerTestOneInput_event.v:79) and ConstsViewDef.v:19's consts_view have the same body; ARX and ARX_rt
     have the same body.  So the plug at the top is `exact topx_ASTRNLEN_x` after `unfold et_strnlen_spec_x`.  This
     file does not Require event_x.
   - The proof is lib/A/RT_strnlen_fit_x.v rt_strnlen_fit_x (the walk Rt/Strnlen.v:567 strnlen_icpt_realizesM_x
     through RTxIcpt.icpt_laws_of_rt) at ARX_rt, with its three premises closed at TfibB:
       rt_laws    : TopX_RT.rt_laws_ARX;
       zero-shadow: YCbqG.alx_zshadow of ARX_rt's AR_laws_x (W_journal_x.AR_laws_x_and_hp over
                    YGcallcf.AR_laws_x_cf (YG0lawscf.AR_laws_ok_cf), hl := cf_head: top_x.v:127-131's ARX_laws);
       TfibSyms   : AD2l.TfibB_syms.
   No premise is left: every lemma here is closed.  SNP_x, the group's other open row, is not in this file.
   QMm W1: topx_ASTRNLEN_x_W restates the row at top_x's W1 relation TopX_RT.ARX_rtW (the lift is in its comment);
   topx_ASTRNLEN_x at ARX_rt stays for the files that cite it. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD2l CfImgA CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YGcallcf YG0lawscf.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt.RTx.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.TopX_RT.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_strnlen_fit_x.
Import ListNotations.
Open Scope Z_scope.

Module RTX := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt.RTx.
Module T1 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.TopX_RT.
Module SNF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_strnlen_fit_x.

Section topx_rt2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).

(* top_x.v:127-131's ARX_laws, at TopX_RT.v's ARX_rt *)
Lemma ARX_rt_laws : AR_laws_x segs TfibB T1.ARX_rt (@cf_head CfParams_reply).
Proof.
  unfold T1.ARX_rt. apply AR_laws_x_and_hp.
  exact (AR_laws_x_cf (cp := CfParams_reply) segs TfibB (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB)).
Qed.

(* ASTRNLEN_x (top_x.v:264), in RTx's text: `exact` for et_strnlen_spec_x after unfolding it (header) *)
Lemma topx_ASTRNLEN_x : RTX.astrnlen_whole_realizesM_x segs TfibB T1.ARX_rt 0x10350 0x10370 (SIGMA WS_strnlen).
Proof.
  exact (SNF.rt_strnlen_fit_x TfibB T1.ARX_rt T1.rt_laws_ARX (YCbqG.alx_zshadow _ _ _ ARX_rt_laws) TfibB_syms).
Qed.

(* QMm W1 (a Theorem Labs lane 01:57Z split, lead a Theorem Labs lane): ASTRNLEN_x at top_x's W1 relation TopX_RT.ARX_rtW (top_x's ARX
   verbatim, carrying arodata_ok_cf).  Split the W1 pre (TopX_RT.ecall_pre_rtW), run topx_ASTRNLEN_x at ARX_rt, and
   rebuild the post: strnlen changes nothing outside its stack window [sp - 2 ESTACK, sp), which lies above the image
   (TopX_RT.stk_above_img and the pre's ly_stk_lo + 2 ESTACK <= sp), so arodata_ok_cf survives by TopX_RT.aro_keep_view
   with the write set False. *)
Lemma topx_ASTRNLEN_x_W : RTX.astrnlen_whole_realizesM_x segs TfibB T1.ARX_rtW 0x10350 0x10370 (SIGMA WS_strnlen).
Proof.
  intros ly S Hp W regs mem md x n HPRE Hlo Hpres G10 G11 Hn Hx Hxn HSRC HNS HAM HRA HHULL HCV.
  destruct (T1.ecall_pre_rtW _ _ _ _ _ _ _ HPRE) as (HPRE0 & HQ).
  eapply SRr_mono;
    [exact (topx_ASTRNLEN_x ly S Hp W regs mem md x n HPRE0 Hlo Hpres G10 G11 Hn Hx Hxn HSRC HNS HAM HRA HHULL HCV)|].
  intros W' c' _ (EW & regs' & mem' & md' & Hc & (HA' & HH') & Hrp & Hsm & HK & HV & Hpr).
  split; [exact EW|]. exists regs', mem', md'. split; [exact Hc|]. split.
  - split; [exact HA'|]. split; [exact HH'|].
    pose proof (T1.stk_above_img _ _ _ _ _ _ (proj1 HPRE0)) as HI.
    apply (T1.aro_keep_view ly S Hp W mem md mem' (fun _ => False) (fun a => spZ regs - 2 * ESTACK <= a < spZ regs)
             (proj1 HPRE0)); [intros a [] | | | exact HQ].
    + intros a Ha. cbv beta in Ha. unfold ESTACK in *. lia.
    + intros a Hb _ Hy. exact (HV a Hb Hy).
  - exact (conj Hrp (conj Hsm (conj HK (conj HV Hpr)))).
Qed.

End topx_rt2.
