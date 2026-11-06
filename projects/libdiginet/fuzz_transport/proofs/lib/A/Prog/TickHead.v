(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 507 of its 622 lines of code are new or changed and 1024 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickHead_entry.v; 83 of its 145 lines of code are new or changed and 560 lines of the source are left out. *)
(* TickHead: Theorem tick_head : tick_head_stmt (lib/A/Prog/TickCut.v), the head piece of the walk of
   diginet_session_tick on fuzz_transport.asan (0x892b8 = transport_sigma TS_diginet_session_tick,
   AF_diginet_session_tick = 0x8054 of lib/A/Prog/DgnTransportList.v): from the entry to the cuts wake (+0x230), online
   (+0x384), step (+0x3c8) and epi (+0x7cc). Three parts, joined at the head's own cut (lib/A/Prog/TickHead_mid.v):
     lib/A/Prog/TickHead_entry.v  tkh_entry: the entry .. the call of __asan_set_shadow_f8 (+0x1ac) (tkh_call_at);
     tkh_call (here)              the call: the holds premise aset_shadow_realizes (transport_sigma
                                  TS___asan_set_shadow_f8) 0xf8 (tick_callees' first contract) as a step of the
                                  caller's G journal (lib/A/Prog/TransportGRt.v gx_set_shadow_at) with a0 = the body's
                                  shadow address (the frame's shadow byte 48), a1 = 186, inside the frame's 256 shadow
                                  bytes; it writes only those 186 shadow bytes of the own frame (TransportGCg.v
                                  dk_kept_own_g), so every fact of tkh_mid holds again at the return;
     lib/A/Prog/TickHead_disp.v   tkh_disp: the return (+0x1b0) .. the four cuts (tkh_ret_at). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg TransportGRt.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg session_lost_cg take_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_tick_cg TickCut TickHead_mid.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TickHead_entry TickHead_disp.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Section tj. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The call of __asan_set_shadow_f8 at +0x1ac, from the call cut to the return cut. *)
Lemma tkh_call : tkh_ret_at B MT -> tkh_call_at B MT.
Proof.
intros RET HLAWS HCALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F S2
  M MD rg HFIX MID Ha0 Ha1 Hra.
pose proof HLAWS as (HPCS & HCELLS & HTC & HGU & HGNE0 & HROU & HRNE & LAWS & MTL & MTF & SMP & FFL & HGX & HGNE).
pose proof HFIX as (HJe & _ & _ & Hgp & Htp & _ & _ & Hsp16 & Hlo & Hhi & _ & _ & _ & _ & _ & _
  & _ & _ & _ & _ & _ & _ & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof MID as (HJ & Hfrs & Eab & HMO & KG & GX & HFW & HFL & HNOW & HRG).
pose proof HRG as ((G2 & G3 & G4 & G8 & G9 & G18 & G27) & G19 & G20 & G22 & G24).
pose proof HJe as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : TICK_STK = 8880) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
destruct (can_sp1_facts (spZ regs - TICK_FRAME) ltac:(unfold TICK_FRAME; lia)
  ltac:(rewrite Zminus_mod, Hsp16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
rewrite <- Esp1 in Hsp1r, Hsp1al, Hsp1al16. unfold TICK_FRAME in Hsp1r.
unfold TICK_FBYTES in HFc, HFapp.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARM.
assert (HFd : 0 <= F / 8 /\ F / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
pose proof (proj1 HCALLEES fx) as ASR.
eapply SRr_bind.
{ eapply (gx_set_shadow_at (SK := tfib_sink_head) segs B LAWS transport_segs_low
    (transport_sigma TS___asan_set_shadow_f8) 0xf8 ASR TG.G_HARNESS W rg M STK sp0 FP ly S W0 mem0 md0
    ((TICK_CID, pos) :: own) lyc S2 MD k TICK_CID pos (SHADOW_OFF + F / 8 + 48) 186 (sp1 - sp0)
    (Z_to_bv 64 (BASE + TKH_RET)) HJ).
  - left. reflexivity.
  - exact Ha0.
  - exact Ha1.
  - lia.
  - rewrite <- EF. unfold shadow_addr. lia.
  - change (fs_frame_bytes TICK_CID / 8) with 256. rewrite <- EF. unfold shadow_addr. lia.
  - unfold spZ at 1. rewrite G2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, Hsp1al16, Hsp0a. reflexivity.
  - lia.
  - lia.
  - rewrite G3. exact Hgp.
  - rewrite G4. exact Htp.
  - exact Hra.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [unfold TKH_RET, AF_diginet_session_tick; lia | reflexivity]. }
cbv beta.
intros W2 c2 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & _ & Hkeep & Hgrow).
apply (RET HLAWS HCALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F S2
  mem3 md3 regs3 HFIX).
(* tkh_mid again at the return: the call wrote the frame's shadow bytes 48 .. 233 only *)
assert (NGH : forall a, SHADOW_OFF <= a -> ~ inG TG.G_HARNESS a).
{ intros a Ha Hg. pose proof (inG_low segs B transport_segs_low TG.G_HARNESS a HGX Hg) as Hl.
  unfold kLowMemEnd, SHADOW_OFF in *. lia. }
assert (KG3 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W mem3 (spZ regs - TICK_STK) (spZ regs) (fun _ => False)).
{ apply (dk_kept_own_g segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc S2 W memc mdc M MD M mem3
    (spZ regs - TICK_STK) (spZ regs) TICK_CID pos F (flag_addr lyc TICK_CID pos) (fun _ => False)
    (fun a => SHADOW_OFF + F / 8 + 48 <= a < SHADOW_OFF + F / 8 + 48 + 186)
    HGX HAR HARM Hfrs Eab EF eq_refl FFL); [lia | lia | intros a [] | | exact KG | exact Hkeep | exact Hgrow].
  intros a X. right; right; left. unfold dkg_nf. right; left. change (fs_frame_bytes TICK_CID / 8) with 256. lia. }
assert (GX3 : gx_kept segs TG.G_HARNESS W memc W mem3).
{ intros a Hg. pose proof (inG_low segs B transport_segs_low TG.G_HARNESS a HGX Hg) as Hl. unfold kLowMemEnd in Hl.
  rewrite (Hkeep a ltac:(lia) ltac:(intros X; exact (NGH a ltac:(unfold SHADOW_OFF in *; lia) Hg))).
  exact (GX a Hg). }
assert (HFW3 : Forall (fun o : Z * Z => rdword (aview segs (w_H W) mem3) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) TICK_SAVED).
{ apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) HFW o Ho) as Hv. rewrite <- Hv.
  assert (Hob : 8 <= fst o <= 104).
  { unfold TICK_SAVED in Ho. cbn [In] in Ho.
    repeat (destruct Ho as [Ho | Ho]; [subst o; cbn [fst]; lia |]). destruct Ho. }
  apply rdword_ext. intros i Hi. apply Hkeep; [lia | unfold SHADOW_OFF in *; lia]. }
assert (HFL3 : rdword (aview segs (w_H W) mem3) (F + TICK_FBYTES - 8) = Some (flag_addr lyc TICK_CID pos)).
{ rewrite <- HFL. unfold TICK_FBYTES. apply rdword_ext. intros i Hi. apply Hkeep; [lia|].
  pose proof (Z.div_pos F 8 ltac:(lia)) as HF8.
  destruct HFapp as (_ & [HL | [HH _]]); unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
assert (HNOW3 : rdword (aview segs (w_H W) mem3) (sp1 + 56) = Some now).
{ rewrite <- HNOW. apply rdword_ext. intros i Hi. apply Hkeep; [lia | unfold SHADOW_OFF in *; lia]. }
refine (conj HJ3 (conj Hfrs (conj Eab (conj HMO (conj KG3 (conj GX3 (conj HFW3 (conj HFL3 (conj HNOW3 _))))))))).
unfold tkh_regs, tick_regs_base.
assert (P2 : YK11.getr regs3 2 = YK11.getr rg 2) by exact (HP3 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : YK11.getr regs3 3 = YK11.getr rg 3) by exact (HP3 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : YK11.getr regs3 4 = YK11.getr rg 4) by exact (HP3 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : YK11.getr regs3 8 = YK11.getr rg 8) by exact (HP3 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : YK11.getr regs3 9 = YK11.getr rg 9) by exact (HP3 9 ltac:(unfold acallee_saved; lia)).
assert (P18 : YK11.getr regs3 18 = YK11.getr rg 18) by exact (HP3 18 ltac:(unfold acallee_saved; lia)).
assert (P19 : YK11.getr regs3 19 = YK11.getr rg 19) by exact (HP3 19 ltac:(unfold acallee_saved; lia)).
assert (P20 : YK11.getr regs3 20 = YK11.getr rg 20) by exact (HP3 20 ltac:(unfold acallee_saved; lia)).
assert (P22 : YK11.getr regs3 22 = YK11.getr rg 22) by exact (HP3 22 ltac:(unfold acallee_saved; lia)).
assert (P24 : YK11.getr regs3 24 = YK11.getr rg 24) by exact (HP3 24 ltac:(unfold acallee_saved; lia)).
assert (P27 : YK11.getr regs3 27 = YK11.getr rg 27) by exact (HP3 27 ltac:(unfold acallee_saved; lia)).
rewrite P2, P3, P4, P8, P9, P18, P19, P20, P22, P24, P27.
exact (conj (conj G2 (conj G3 (conj G4 (conj G8 (conj G9 (conj G18 G27)))))) (conj G19 (conj G20 (conj G22 G24)))).
Qed.

Lemma tkh_holds : @tick_head_stmt fx rc B MT.
Proof.
unfold tick_head_stmt. intros WAKE ONLINE STEP EPI.
exact (tkh_entry B MT (tkh_call (tkh_disp B MT WAKE ONLINE STEP EPI))).
Qed.
End tj.

(* The head piece of the walk of diginet_session_tick (TickCut.v tick_head_stmt), at every machine, run ceiling,
   record and meter. *)
Theorem tick_head : forall fx rc B MT, @tick_head_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@tkh_holds fx rc B MT). Qed.
Print Assumptions tick_head.
