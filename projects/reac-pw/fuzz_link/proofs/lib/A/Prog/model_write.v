(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_up.v, with its module paths and module names changed; 264 of its 309 lines of code are new or changed and 2644 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/fuzz_recv_cp.v; 57 of its 96 lines of code are new or changed and 270 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/check_refused.v, with its module names changed; 11 of its 39 lines of code are new or changed and 68 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/check_mark.v, with its module names changed; 60 of its 83 lines of code are new or changed and 16 lines of the source are left out. *)
(* model_write (fuzz_link.asan 0x88100, listing offset AF_model_write = 0x5f34) on image A against its contract
   lib/A/Prog/model_write_c.v `model_write_acontract` (aleaf_rd over the caller's journal), by the walk of
   lib/A/Prog/model_write*.v:
     model_writeHead.v   entry .. MID cut (+0x124): mw_head : mw_mid_obl -> the contract
     model_writeArms.v   MID cut: mw_mid : mw_exit_obl -> mw_send_obl -> mw_mid_obl
     model_writeSendB.v  SEND cut (+0x16c) .. RQ cut (+0x1d8): mw_send : mw_send_obl
     model_writeSendC.v  RQ cut .. EXIT cut (talk): mw_rq
     model_writeExit.v   EXIT cut (+0x210) .. ret: mw_exit : mw_exit_obl
   and the corollary on the image, with the runtime callees discharged by their closed lemmas (as
   lib/A/Prog/fuzz_send_img.v); the two own callees stay hypotheses: index_of (index_of_c.v) and
   talk (talk_c.v).

   Section hypotheses and their discharges on the image:
     ASM4    frame_alloc_4 (0x3ddc4)      lib/A/Rt/StackSideInst.v link_stack_malloc_4
     MF00    meta_fill_00 (0x55e74)       lib/A/Rt/SetShadow.v link_set_shadow_00
     MFF5    meta_fill_f5 (0x55f7c)       lib/A/Rt/SetShadow.v link_set_shadow_f5
     MFF8    meta_fill_f8 (0x55f94)       lib/A/Rt/SetShadow.v link_set_shadow_f8
     STRLEN  wrapper_strlen (0x43044)     lib/A/Rt/RtClosed.v cmd_strlen_closed
     AMSET   checked_memset (0x53214)     lib/A/AE2r.v asan_memset_realizes
     AMCPY   checked_memcpy (0x52d78)     lib/A/AE2q.v asan_memcpy_realizes
     IDX     index_of (0x86784)           not yet proved here: index_of_c.v
     TALK    talk (0x8763c)               not yet proved here: talk_c.v
   and the image instance: LAWS (AR_laws), TL (PALib), LV (LinkVals), TB (AF0m.PcapSyms), HSEGS (pa_segs =
   tfibsegs).

   Proves model_write (kind: function proof). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 SetShadowDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalk link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
index_of_c talk_c model_write_c model_writeDefs model_writeHead model_writeArms model_writeSendB model_writeExit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v AF0m AE2q AE2r.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtString RtClosed SetShadow StackSideInst.
Import ListNotations.
Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis LV : LinkVals.
Hypothesis TB : AF0m.PcapSyms B.
Hypothesis HSEGS : SEGS = AB1v.tfibsegs.
Hypothesis ASM4 : astack_malloc_realizes SEGS B 4.
Hypothesis MF00 : aset_shadow_realizes SEGS B (pa_sigma LS___asan_set_shadow_00) 0x00.
Hypothesis MFF5 : aset_shadow_realizes SEGS B (pa_sigma LS___asan_set_shadow_f5) 0xf5.
Hypothesis MFF8 : aset_shadow_realizes SEGS B (pa_sigma LS___asan_set_shadow_f8) 0xf8.
Hypothesis STRLEN : RtString.astrlen_realizes SEGS B (pa_sigma LS___interceptor_trampoline_strlen).
Hypothesis AMSET : aintrin_realizes SEGS B OSet (pa_sigma LS___asan_memset).
Hypothesis AMCPY : aintrin_realizes SEGS B OCpy (pa_sigma LS___asan_memcpy).
Hypothesis IDX : forall rlo rhi, index_of_acontract SK SEGS rlo rhi B.
Hypothesis TALK : forall rlo rhi, talk_acontract SK SEGS rlo rhi B.

Theorem model_write_aproof : forall rlo rhi, model_write_acontract SK SEGS rlo rhi B.
Proof using LAWS TL LV TB HSEGS ASM4 MF00 MFF5 MFF8 STRLEN AMSET AMCPY IDX TALK.
  assert (EXIT : mw_exit_obl SK B) by (eapply mw_exit; eassumption).
  assert (SEND : mw_send_obl SK B) by (eapply mw_send; eassumption).
  assert (MID : mw_mid_obl SK B) by (eapply mw_mid; eassumption).
  eapply mw_head; eassumption.
Qed.

End w.

Section img. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
Context {PI : PAImg link_listing}.
Theorem model_write_aproof_img : forall B, AR_laws pa_segs B -> PALib B -> LinkVals -> AF0m.PcapSyms B ->
  pa_segs = AB1v.tfibsegs ->
  (forall rlo rhi, index_of_acontract SK pa_segs rlo rhi B) ->
  (forall rlo rhi, talk_acontract SK pa_segs rlo rhi B) ->
  forall rlo rhi, model_write_acontract SK pa_segs rlo rhi B.
Proof.
  intros B LAWS TL LV TS Hsegs IDX TALK.
  pose proof LAWS as LAWS'. rewrite Hsegs in LAWS'.
  apply (model_write_aproof SK B LAWS TL LV TS Hsegs).
  - rewrite Hsegs. exact (StackSideInst.link_stack_malloc_4 B TS).
  - rewrite (lv_sigma LV). cbn [link_sigma]. rewrite Hsegs. exact (SetShadow.link_set_shadow_00 B LAWS' TS).
  - rewrite (lv_sigma LV). cbn [link_sigma]. rewrite Hsegs. exact (SetShadow.link_set_shadow_f5 B LAWS' TS).
  - rewrite (lv_sigma LV). cbn [link_sigma]. rewrite Hsegs. exact (SetShadow.link_set_shadow_f8 B LAWS' TS).
  - rewrite (lv_sigma LV). cbn [link_sigma]. rewrite Hsegs. exact (RtClosed.cmd_strlen_closed B TS).
  - (* AE2r.v's statement asks no amem_range of the destination: drop that premise (as LinkWalkKernInst.v) *)
    rewrite (lv_sigma LV). cbn [link_sigma]. rewrite Hsegs.
    intros ly S W regs mem md d x n HPRE H10 H11 H12 Hn Hd Hdn HD HAM HRA HHV HOP.
    eapply (AE2r.asan_memset_realizes B LAWS' TS); eassumption.
  - rewrite (lv_sigma LV). cbn [link_sigma]. rewrite Hsegs. exact (AE2q.asan_memcpy_realizes B LAWS' TS).
  - exact IDX.
  - exact TALK.
Qed.
End img.

Print Assumptions model_write_aproof.
Print Assumptions model_write_aproof_img.
