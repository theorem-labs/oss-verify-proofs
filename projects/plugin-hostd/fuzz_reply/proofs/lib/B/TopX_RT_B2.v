(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: image B's (fuzz_reply.asan-ubsan) strlen contract at the B top's instance,
   PROVED with no premise:
     topx_ASTRLEN_B : astrlen_realizes_x TfibB ARX_rt (SIGMA WS_strlen)
   the hypothesis ASTRLEN of lib/B/W_check_shape_event.v:80 (Section c: astrlen_realizes_x B ARx (SIGMA WS_strlen))
   at B := TfibB and ARx := the B top's ARX (lib/B/W_LLVMFuzzerTestOneInput_top_x.v:154-155 at commit e43cf0c7bef),
   which lib/B/TopX_RT_lock.v restates VERBATIM as ARX_rt, with its five runtime laws rt_laws_ARX.
   It is the generic runtime twin lib/B/RT_strlen_x.rt_strlen_x applied at ARX_rt.  Its two image premises are closed
   at TfibB: FrShadowSyms TfibB (RT_kit.v:239: the shadow-offset cell's GOT slot 0x9df50 and the cell 0xa6638) by
   the fields as_got_shadow / as_shadow_cell of TfibB itself (lib/B/YD2l.v:21,23; lib/B has no W_palib_fr, and the
   B top keeps PALib TfibB as its Hypothesis TL, top_x.v:203, so RT_kit.fr_shadow_of_palib is not used), and
   TfibSyms TfibB by YD2l.TfibB_syms. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/TopX_RT_B2.v, with its module paths changed; 57 of its 84 lines of code are new or changed and 10 lines of the source are left out. *)
(* Image B's (fuzz_reply.asan-ubsan) strlen and strnlen contracts at the B top's instance,
   PROVED with no premise:
     topx_ASTRLEN_B  : astrlen_realizes_x TfibB ARX_rt (SIGMA WS_strlen)
     topx_ASTRNLEN_B : RTx.astrnlen_whole_realizes_x segs TfibB ARX_rt (SIGMA WS_strnlen)
   with ARx := the B top's ARX (lib/B/W_LLVMFuzzerTestOneInput_top_x.v:167-168 on window c052f9c9a32; :154-155 at
   commit e43cf0c7bef), which lib/B/TopX_RT_lock.v restates VERBATIM as ARX_rt, with its five runtime laws rt_laws_ARX.
   - topx_ASTRLEN_B is the hypothesis ASTRLEN of lib/B/W_check_shape_event.v:82 (Section c: astrlen_realizes_x B ARx
     (SIGMA WS_strlen)) at B := TfibB.  It is the generic runtime twin lib/B/RT_strlen_x.rt_strlen_x applied at
     ARX_rt.  Its two image premises are closed at TfibB: FrShadowSyms TfibB (RT_kit.v:239: the shadow-offset cell's
     GOT slot 0x9df50 and the cell 0xa6638) by the fields as_got_shadow / as_shadow_cell of TfibB itself
     (lib/B/YD2l.v:21,23; lib/B has no W_palib_fr, and the B top keeps PALib TfibB as its Hypothesis TL, top_x.v:203,
     so RT_kit.fr_shadow_of_palib is not used), and TfibSyms TfibB by YD2l.TfibB_syms.
   - topx_ASTRNLEN_B is the hypothesis ASTRNLEN_x of top_x.v:811 on window c052f9c9a32 (RTx.v:154's
     astrnlen_whole_realizes_x), the image-B
     twin of lib/A/TopX_RT2.v topx_ASTRNLEN_x.  It is lib/B/RT_strnlen_fit_x.v rt_strnlen_whole_fit_x (the walk
     lib/B/Rt/Strnlen.v strnlen_icpt_realizes_x through RTxIcpt.icpt_laws_of_rt) at ARX_rt, with its three premises
     closed at TfibB: rt_laws by TopX_RT_lock.rt_laws_ARX; the zero-shadow law by YCbqG.alx_zshadow of ARX_rt's
     AR_laws_x (ARX_rt_laws below: W_journal_x.AR_laws_x_and_hp over YGcallcf.AR_laws_x_cf (YG0lawscf.AR_laws_ok_cf),
     hl := cf_head, the proof of top_x.v:167-171's ARX_laws); TfibSyms by YD2l.TfibB_syms. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_listing W_place W_tbl W_kit W_pl W_img.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import CfImgB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YGcallcf YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YA0n.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt.RTx.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_kit.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_strlen_x.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_strnlen_fit_x.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.TopX_RT_lock.
Import ListNotations.
Open Scope Z_scope.

Module RTX := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt.RTx.
Module K := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_kit.
Module SX := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_strlen_x.
Module SNF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_strnlen_fit_x.
Module TRL := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.TopX_RT_lock.

Section topx_rt2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).

(* RT_kit.v:239 FrShadowSyms at TfibB: YD2l.v:21 as_shadow_cell := 0xa6638, YD2l.v:23 as_got_shadow := 0x9df50 *)
Lemma fr_shadow_TfibB : K.FrShadowSyms TfibB.
Proof. split; reflexivity. Qed.

(* ASTRLEN (W_check_shape_event.v:82) at the B top's ARX (top_x.v:154-155 = TopX_RT_lock.ARX_rt) *)
Lemma topx_ASTRLEN_B : astrlen_realizes_x TfibB TRL.ARX_rt (SIGMA WS_strlen).
Proof. exact (SX.rt_strlen_x TfibB TRL.ARX_rt TRL.rt_laws_ARX fr_shadow_TfibB TfibB_syms). Qed.

(* top_x.v:167-171's ARX_laws, at TopX_RT_lock.v's ARX_rt *)
Lemma ARX_rt_laws : AR_laws_x segs TfibB TRL.ARX_rt (@cf_head CfParams_reply).
Proof.
  unfold TRL.ARX_rt. apply AR_laws_x_and_hp.
  exact (AR_laws_x_cf (cp := CfParams_reply) segs TfibB (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB)).
Qed.

(* ASTRNLEN_x (top_x.v:811) at the B top's ARX (top_x.v:167-168 = TopX_RT_lock.ARX_rt) *)
Lemma topx_ASTRNLEN_B : RTX.astrnlen_whole_realizes_x segs TfibB TRL.ARX_rt (SIGMA WS_strnlen).
Proof.
  exact (SNF.rt_strnlen_whole_fit_x TfibB TRL.ARX_rt TRL.rt_laws_ARX (YCbqG.alx_zshadow _ _ _ ARX_rt_laws) TfibB_syms).
Qed.

(* ---- QMm W1 lifts (a Theorem Labs lane, 2026-10-31; a Theorem Labs lane's split 01:56Z, a Theorem Labs lane's shared lemmas in TopX_RT_lock.v):
   the two contracts above at top_x's W1 ARX, TopX_RT_lock.ARX_rtW (ARX_rt /\ arodata_ok_cf). strlen and strnlen write
   nothing: each post keeps every view off the call's 2 * ESTACK stack window, and that window lies above the image
   (TRL.stk_above_img), so arodata_ok_cf carries over by TRL.aro_keep_view with X := False and Y := the window. The
   lemmas at ARX_rt stay; top_x cites the _W names. ---- *)
Lemma topx_ASTRLEN_B_W : astrlen_realizes_x TfibB TRL.ARX_rtW (SIGMA WS_strlen).
Proof.
intros ly S Hp W regs mem md x k HPRE.
destruct (TRL.ecall_pre_rtW _ _ _ _ _ _ _ HPRE) as (HPRE0 & HQ).
pose proof HPRE0 as (HA & _ & _ & Hlo & _).
pose proof (TRL.stk_above_img _ _ _ _ _ _ HA) as HI.
intros. eapply YA0n.SRr_mono; [eapply (topx_ASTRLEN_B ly S Hp W regs mem md x k HPRE0); eassumption|].
intros W' c' _ (EW & regs' & mem' & md' & Hc & (HA' & HH') & Hrp & Hsm & HR & HV & Hpr).
split; [exact EW|]. exists regs', mem', md'. split; [exact Hc|].
split; [|exact (conj Hrp (conj Hsm (conj HR (conj HV Hpr))))].
split; [exact HA'|]. split; [exact HH'|].
apply (TRL.aro_keep_view ly S Hp W mem md mem' (fun _ => False) (fun a => spZ regs - 2 * ESTACK <= a < spZ regs) HA).
- intros a [].
- intros a Ha. cbv beta in Ha. unfold ESTACK in *. lia.
- intros a Ha _ HnY. exact (HV a Ha HnY).
- exact HQ.
Qed.

Lemma topx_ASTRNLEN_B_W : RTX.astrnlen_whole_realizes_x segs TfibB TRL.ARX_rtW (SIGMA WS_strnlen).
Proof.
intros ly S Hp W regs mem md x n HPRE.
destruct (TRL.ecall_pre_rtW _ _ _ _ _ _ _ HPRE) as (HPRE0 & HQ).
pose proof HPRE0 as (HA & _ & _ & Hlo & _).
pose proof (TRL.stk_above_img _ _ _ _ _ _ HA) as HI.
intros. eapply YA0n.SRr_mono; [eapply (topx_ASTRNLEN_B ly S Hp W regs mem md x n HPRE0); eassumption|].
intros W' c' _ (EW & regs' & mem' & md' & Hc & (HA' & HH') & Hrp & Hsm & HR & HV & Hpr).
split; [exact EW|]. exists regs', mem', md'. split; [exact Hc|].
split; [|exact (conj Hrp (conj Hsm (conj HR (conj HV Hpr))))].
split; [exact HA'|]. split; [exact HH'|].
apply (TRL.aro_keep_view ly S Hp W mem md mem' (fun _ => False) (fun a => spZ regs - 2 * ESTACK <= a < spZ regs) HA).
- intros a [].
- intros a Ha. cbv beta in Ha. unfold ESTACK in *. lia.
- intros a Ha _ HnY. exact (HV a Ha HnY).
- exact HQ.
Qed.

End topx_rt2.

Print Assumptions topx_ASTRLEN_B_W.
Print Assumptions topx_ASTRNLEN_B_W.
