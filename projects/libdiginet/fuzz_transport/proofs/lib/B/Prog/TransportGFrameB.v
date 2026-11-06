(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc; file sha256 7a8df68f254a; donor not released), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the donors are proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v (sm_effect_journal, sm_call) and .../LLVMFuzzerTestOneInput_seg_exit_tail.v (t_flag_store_pi) at origin/ossv/recipes 88154566652a: module paths, listing symbol type and this image's own numbers changed, the fake-frame class is 1 (128 bytes) instead of 0, the hypotheses model_laws and api_env are dropped and the two frame-list facts they gave are computed from lib/Reusable/YG00.v's own stack_malloc and stack_free_state, and the four-byte shadow-check lemma, the region helpers and the stack-shadow helpers are new. *)
(* Modified by Theorem Labs, 2026-10: ported to libdiginet/fuzz_frame image A: module paths, listing symbol type dfsym and this unit's own names; the side-stack-frame class stays a parameter. *)
(* Modified by Theorem Labs, 2026-10: libdiginet/fuzz_frame image B's twin of this unit's lib/A/Prog/CanKit.v: module paths changed (lib/B/YB1v.v; the per-image lib/B/YCbq.v, YC5d.v, YImgTop.v and lib/B/Prog/PaJournal.v; lib/B/Prog/FrameBSyms.v, FrameBList.v, FrameBAddr.v, FrameBPa.v, FrameBImg.v and FrameBPaLib.v for the DgnFrame* listing files); the listing names are image B's (fbsym, frameb_listing, frameb_tpi, PI_frameb, PL_frameb for dfsym, dgnframe_listing, dgnframe_tpi, PI_dgnframe, PL_dgnframe). No statement changes otherwise. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/CanKit.v; 19 of its 72 lines of code are new or changed and 476 lines of the source are left out. *)
(* TransportGFrameB: image B's twin of lib/A/Prog/TransportGFrame.v, the side-stack frame kit of the G-form
   caller-journal walks (lib/A/W_journalG.v ajournal_gx with XO = 0 and OUT = [], over lib/A/Prog/TransportGCg.v).
   Nothing here names a program function.
   Only the listing-tied lemma has a twin here, under A's name:
   - gx_flag_store_pi: lib/B/Prog/CanKit.v can_flag_store_pi (a plain position-abstract run of image B's listing,
     transportb_tpi over pa_segs / pa_val at transportb_listing, that writes bytes the journal allows and the frame's
     flag byte, and leaves that byte 0, releases the frame) inside the G journal: TransportGCg.v gx_open gives the
     donor journal at a start memory that agrees with the G journal's outside G, and gx_pack0 packs it again there.
   Every other lemma of the frame kit is image-free (stated over any segs and B) and image B's walks Require it from
   lib/A/Prog/TransportGFrame.v as it stands: gx_stack_malloc_at (lib/B/Prog/CanKit.v can_stack_malloc_at has the same
   statement as A's), awr_ok_x_cons_own, dk_kept_step_gw, dkg_nf_sep_gw, dk_kept_nf_gw, dk_kept_nfz_gw, tw_kept_nf_g. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YCbq.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0p YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require CanKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module YI16 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI16.
Module CKB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.CanKit.

Section fp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Abbreviation SEGS := (@pa_segs _ transportb_listing PI_transportb).
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.

(* lib/B/Prog/CanKit.v can_flag_store_pi with the G journal before the run and in its continuation. *)
Lemma gx_flag_store_pi : forall G W n E ss ss' st ms STK sp0 FP ly S W0 mem md own' lyc Sc mdc k cid pos Q,
  img_env VAL A_LIM E ->
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
  sym_runN_pi transportb_tpi n ss = (ss', st) -> CKB.can_plain_stop st ->
  ajournal_gx SEGS B G 0 [] STK sp0 FP ly S W0 mem md ((cid, pos) :: own') lyc Sc W (ms_mem ms) mdc k ->
  0 <= cid ->
  (forall a, in_wrange E (ss_mem ss) a ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc ((cid, pos) :: own') a \/ a = flag_addr lyc cid pos) ->
  (forall msr, st_ok_pi SEGS VAL E ss' msr -> mbyte SEGS (ms_mem msr) (flag_addr lyc cid pos) = Some (Z_to_bv 8 0)) ->
  (forall ms' mat',
     st_ok_pi SEGS VAL E ss' (restrict (w_H W) ms') ->
     ajournal_gx SEGS B G 0 [] STK sp0 FP ly S W0 mem md own' lyc (stack_free_state cid pos Sc) W (ms_mem ms')
       (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
     frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
     frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     SRr SEGS W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr SEGS W (mkCfg ms mdc) Q.
Proof.
intros G W n E ss ss' st ms STK sp0 FP ly S W0 mem md own' lyc Sc mdc k cid pos Q HE HS Hrun Hst HJ Hcid Hwr Hflag0 Hk.
destruct (gx_open SEGS B G STK sp0 FP ly S W0 mem md ((cid, pos) :: own') lyc Sc W (ms_mem ms) mdc k HJ)
  as (memS & HJi & Hag & HSTK).
apply (CKB.can_flag_store_pi (SK := SK) B LAWS ASF FFL W n E ss ss' st ms STK sp0 FP ly S W0 memS md own' lyc Sc mdc k
  cid pos Q HE HS Hrun Hst HJi Hcid Hwr Hflag0).
intros ms' mat' HS' HJ' F1 F2 F3.
apply (Hk ms' mat' HS'); [|exact F1 | exact F2 | exact F3].
exact (gx_pack0 SEGS B G STK sp0 FP ly S W0 mem md own' lyc (stack_free_state cid pos Sc) W (ms_mem ms')
  (with_vm_backing (m_vm_lazy mdc) mat' mdc) k memS HSTK HJ' Hag).
Qed.
End fp.
