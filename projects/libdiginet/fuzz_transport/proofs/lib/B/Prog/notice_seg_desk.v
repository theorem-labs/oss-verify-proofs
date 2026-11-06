(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 678 of its 962 lines of code are new or changed and 855 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/DgnBcHead.v, with its module paths, module names and numbers changed; 528 of its 590 lines of code are new or changed and 900 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/notice_seg_base.v; 308 of its 415 lines of code are new or changed and 483 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/notice_seg_acked.v, with its numbers changed; 262 of its 413 lines of code are new or changed and 264 lines of the source are left out. *)
(* notice_seg_desk: the N_DESK arm of notice's walk on fuzz_transport.asan-ubsan (lib/B/Prog/notice_cgW.v), from the
   jump `jr a0` (0x83474) with a0 = 0x83478:
     0x83478 - 0x83480  a0 = the auipc value 0x5e5478; a3 = GOT.desk (the 4-byte signed load at GOT + 208, read from
                        the region of that field, its value the world's u32), a2 = a3 + 1 (addiw);
     0x83484            `blt a2, a3` to the UBSan trap 0x83610: taken exactly at INT_MAX (nt_ovf_br), which notice_m
                        rules out (its int_inc is None there);
     0x83488            the store of a2 at a0 - 1096 = GOT + 208 (a0 pinned to that field's object + 1096);
     0x8348c - 0x83498  a0 = p, ra loaded back, sp = sp + 16, the jump (no link) to check_state_desk (0x854bc).
   check_state_desk runs from notice's entry sp and ra, so it returns to notice's caller: its contract (a donor-form
   callee, TransportGCg.v gx_call_cg) is applied at the call state, at the world after GOT.desk++ (nt_tw_set4) and at
   the notice whose announce is cut to its 20 bytes (nt_cut: every byte it names lies in a range notice_apart keeps
   apart from the store). Its post (relative to the call memory, its window CSDESK_STK, nothing written, X: the
   model's world is the one it was handed, and every byte of G kept) is folded with what the run to the call kept
   (relative to notice's entry memory: every byte outside notice's window and GOT.desk) by ntdesk_tail_fold into
   transport_notice_post. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_state_data_cg check_state_desk_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import notice_seg_base notice_seg_lib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.


Section desk. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* ---- the post of a donor callee reached by a tail jump ---- *)

(* THE DONOR-TAIL FOLD. A callee in the donor form, lifted by gx_call_cg, leaves transport_cg_post relative to the
   call memory memT, the call registers regsT and its window FSTK'. The walk that reached the call kept, from its own
   entry memory memc to memT, every byte acall_kept_g keeps at its own window [spZ regs - FSTK, spZ regs) and its
   written range Eo. When the callee's window lies inside the walk's, its written range inside Eo, its event bound
   inside the walk's, the call registers keep the walk's callee-saved registers and ra (a tail jump: the callee
   returns to the walk's caller), the two compose into transport_cg_post relative to memc, regs, FSTK and Eo. *)
Lemma ntdesk_tail_fold : forall (G : list (Z * Z)) STK sp0 FP ly S (W0 : world segs) mem0 md0 own lyc Sc
    (W : world segs) memc memT k (regs regsT : bvmap 5 word) (FSTK FSTK' EV EV' COST : Z) (Eo E' : Z -> Prop)
    (X X' : bvmap 5 word -> world segs -> (word -> option byte) -> Prop) (W2 : world segs) (c2 : config),
  alloc_ceiling <= spZ regs - FSTK -> spZ regs <= 2 ^ 64 ->
  spZ regs - FSTK <= spZ regsT - FSTK' -> spZ regsT <= spZ regs -> EV' <= EV ->
  (forall a, E' a -> Eo a) ->
  aregs_preserved regs regsT -> YK11.getr regsT 1 = YK11.getr regs 1 ->
  acall_kept_g segs B G lyc Sc W memc W memT (spZ regs - FSTK) (spZ regs) Eo ->
  (forall regs2 (W2' : world segs) mem2, X regs2 W2' mem2 -> X' regs2 W2' mem2) ->
  @transport_cg_post fx rc tfib_sink_head segs B MT G STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT k regsT
    FSTK' EV' COST E' X W2 c2 ->
  @transport_cg_post fx rc tfib_sink_head segs B MT G STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs
    FSTK EV COST Eo X' W2 c2.
Proof.
  intros G STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc memT k regs regsT FSTK FSTK' EV EV' COST Eo E' X X' W2 c2
    Hce H64 Hlo Hhi HEV HE HP Hra KW HX
    (ly2 & S2 & regs2 & mem2 & md2 & e & Hc & He & HJ & HP2 & Hfr & Hperm & HK & HMO & HXp).
  exists ly2, S2, regs2, mem2, md2, e.
  split; [rewrite Hc; f_equal; f_equal; exact Hra|].
  split; [lia|]. split; [exact HJ|].
  split; [exact (aregs_preserved_trans regs regsT regs2 HP HP2)|].
  split; [exact Hfr|]. split; [exact Hperm|].
  split; [exact (dk_kept_trans_g segs B G lyc Sc W memc W memT W2 mem2 (spZ regs - FSTK) (spZ regs)
    (spZ regsT - FSTK') (spZ regsT) Eo E' Hce H64 KW HK Hlo Hhi HE)|].
  split; [exact HMO | exact (HX _ _ _ HXp)].
Qed.

(* ---- the bytes the run to the call keeps ---- *)

(* What the run to the call keeps, as acall_kept_g at notice's window and written range (nt_close's first part). *)
Lemma ntdesk_kept : forall lyc Sc (W : world segs) memc mdc mT regs Bw n,
  AR_laws segs B -> gx_ok segs B TG.G_HARNESS_B -> @AR rc segs B lyc Sc W memc mdc ->
  (forall a, spZ regs - NOTICE_STK <= a < spZ regs -> apresent (w_H W) memc a) ->
  alloc_ceiling <= spZ regs - NOTICE_STK ->
  nt_KA W memc mT (nt_Zs regs Bw n) ->
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W mT (spZ regs - NOTICE_STK) (spZ regs) (notice_wr Bw n).
Proof.
  intros lyc Sc W memc mdc mT regs Bw n LAWS HGX HAR Hwin Hce [KA GA].
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (GLOW : forall a, inG TG.G_HARNESS_B a -> a < kLowMemEnd).
  { intros a Ha. exact (proj2 (transportb_segs_low a (proj1 (HGX a Ha)))). }
  apply (dk_kept_step_g segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc memc mT
    (spZ regs - NOTICE_STK) (spZ regs) (notice_wr Bw n) (nt_Zs regs Bw n) HAR).
  - apply dk_kept_refl_g. exact Hwin.
  - exact KA.
  - exact GA.
  - intros a [Hw | Hw] Hc; [exact Hw|]. exfalso. pose proof (GLOW a (nt_wr_G _ _ _ Hw)). unfold kLowMemEnd in *. lia.
  - intros b m i Hb Hi [Hw | Hw]; [|exact Hw]. exfalso.
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _). lia.
  - intros a [Hw | Hw] Hi HnG _ _.
    + pose proof (transportb_segs_low a Hi) as Hl. unfold kLowMemEnd in *. lia.
    + exact (HnG (nt_wr_G _ _ _ Hw)).
  - intros cid pos a Hin Hr [Hw | Hw]; [|exact Hw]. exfalso.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
Qed.

(* A range a callee reads lies in [0, 2 ^ 64) (trans_src_ok_place). *)
Lemma ntdesk_rng : forall lyc Sc (W : world segs) memc mdc q len,
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc -> trans_src_ok B lyc Sc W memc q len ->
  forall a, q <= a < q + len -> 0 <= a < 2 ^ 64.
Proof.
  intros lyc Sc W memc mdc q len LAWS HAR Hs a Ha. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (trans_src_ok_place B LAWS lyc Sc W memc mdc q len HAR Hs ltac:(lia)) as [H|H]; lia.
Qed.

(* The bytes of a range outside notice's window and apart from the store, kept. *)
Lemma ntdesk_keep : forall (W : world segs) memc mT regs Bw n q len,
  nt_KA W memc mT (nt_Zs regs Bw n) ->
  (forall a, q <= a < q + len -> 0 <= a < 2 ^ 64) ->
  decode_off_win regs NOTICE_STK q len ->
  (forall a, notice_wr Bw n a -> ~ (q <= a < q + len)) ->
  forall a, q <= a < q + len -> aview segs (w_H W) mT a = aview segs (w_H W) memc a.
Proof.
  intros W memc mT regs Bw n q len [KA _] HR Hoff Hap a Ha. apply KA; [exact (HR a Ha)|].
  intros [Hz | Hz]; [unfold decode_off_win in Hoff; lia | exact (Hap a Hz Ha)].
Qed.

(* The shadow band, kept: the walk changes only its stack window (above alloc_ceiling) and bytes of GOT and M. *)
Lemma ntdesk_band : forall (W : world segs) memc mT regs Bw n,
  alloc_ceiling <= spZ regs - NOTICE_STK -> nt_KA W memc mT (nt_Zs regs Bw n) ->
  forall s, kLowMemEnd <= s < kHighShadowEnd -> aview segs (w_H W) mT s = aview segs (w_H W) memc s.
Proof.
  intros W memc mT regs Bw n Hce [KA _] s Hs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  apply KA; [lia|]. intros Hz. destruct (nt_Zs_far regs Bw n s Hce Hz) as [H|H]; unfold TB_M, TB_GOT in *; lia.
Qed.

(* trans_src_ok of a range at the call memory. *)
Lemma ntdesk_src : forall lyc Sc (W : world segs) memc mdc mT regs Bw n q len,
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc ->
  alloc_ceiling <= spZ regs - NOTICE_STK -> nt_KA W memc mT (nt_Zs regs Bw n) ->
  trans_src_ok B lyc Sc W memc q len -> decode_off_win regs NOTICE_STK q len ->
  (forall a, notice_wr Bw n a -> ~ (q <= a < q + len)) ->
  trans_src_ok B lyc Sc W mT q len.
Proof.
  intros lyc Sc W memc mdc mT regs Bw n q len LAWS HAR Hce KA Hs Hoff Hap.
  apply (trans_src_ok_view B lyc Sc W W memc mT q len Hs).
  - exact (ntdesk_keep W memc mT regs Bw n q len KA (ntdesk_rng lyc Sc W memc mdc q len LAWS HAR Hs) Hoff Hap).
  - exact (ntdesk_band W memc mT regs Bw n Hce KA).
Qed.

(* An array of bytes inside such a range, at the call memory. *)
Lemma ntdesk_arr : forall lyc Sc (W : world segs) memc mdc mT regs Bw n q len q' (l : list byte),
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc -> nt_KA W memc mT (nt_Zs regs Bw n) ->
  trans_src_ok B lyc Sc W memc q len -> decode_off_win regs NOTICE_STK q len ->
  (forall a, notice_wr Bw n a -> ~ (q <= a < q + len)) ->
  q <= q' -> q' + Z.of_nat (length l) <= q + len ->
  garr8 segs (mrestrict (w_H W) memc) q' (map DSpec.bz l) ->
  garr8 segs (mrestrict (w_H W) mT) q' (map DSpec.bz l).
Proof.
  intros lyc Sc W memc mdc mT regs Bw n q len q' l LAWS HAR KA Hs Hoff Hap H1 H2 HG.
  apply (nt_garr8_keep W memc mT _ q' _ KA HG). intros a Ha. rewrite length_map in Ha. split.
  - exact (ntdesk_rng lyc Sc W memc mdc q len LAWS HAR Hs a ltac:(lia)).
  - intros [Hz | Hz].
    + unfold decode_off_win in Hoff. lia.
    + exact (Hap a Hz ltac:(lia)).
Qed.

Lemma ntdesk_garr8_firstn : forall (m : word -> option byte) q (l : list byte) j,
  garr8 segs m q (map DSpec.bz l) -> garr8 segs m q (map DSpec.bz (firstn j l)).
Proof.
  intros m q l j H. rewrite <- (firstn_skipn j l), map_app in H.
  exact (proj1 (proj1 (garr8_app segs m q _ _) H)).
Qed.

(* decode_off_win at the call: the same sp, and CSDESK_STK = NOTICE_STK. *)
Lemma ntdesk_off : forall regs regsT q len, spZ regsT = spZ regs ->
  decode_off_win regs NOTICE_STK q len -> decode_off_win regsT CSDESK_STK q len.
Proof.
  intros regs regsT q len Hsp H. unfold decode_off_win in *. rewrite Hsp, <- (proj2 notice_stk_eq). exact H.
Qed.

(* The notice check_state_desk gets, at the call memory: the struct, the body and the cut announce (each kept:
   outside notice's window, apart from the store). *)
Lemma ntdesk_ntc : forall lyc Sc (W : world segs) memc mdc mT regs regsT Bw n p Fr,
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc ->
  alloc_ceiling <= spZ regs - NOTICE_STK -> spZ regsT = spZ regs ->
  nt_KA W memc mT (nt_Zs regs Bw n) -> notice_apart W memc p n Fr Bw ->
  trans_ntc_at B lyc Sc W memc regs NOTICE_STK p n ->
  trans_ntc_at B lyc Sc W mT regsT CSDESK_STK p (nt_cut n).
Proof.
  intros lyc Sc W memc mdc mT regs regsT Bw n p Fr LAWS HAR Hce Hsp KA HAP
    (P0 & P8 & Hsrc & Hoff & NB & HNB & HNBL & Hk & Hs & Ho & Hr & Hpe & Hmac & Hbl & Hcnt & Hret & HBG & HBS & HBW
     & HANN).
  assert (HAPp : forall a, notice_wr Bw n a -> ~ (p <= a < p + NTC_SIZE)) by (intros a Hz; exact (proj1 (HAP a Hz))).
  assert (HAPb : forall a, notice_wr Bw n a ->
    ~ (TW.u_at NB 48 8 <= a < TW.u_at NB 48 8 + Z.of_nat (length (TI.n_body n))))
    by (intros a Hz; exact (proj1 (proj1 (proj2 (HAP a Hz)) NB HNB HNBL))).
  unfold trans_ntc_at, nt_cut.
  cbn [TI.n_kind TI.n_state TI.n_old TI.n_reason TI.n_counter TI.n_retry TI.n_mac_offset TI.n_pers TI.n_ann
    TI.n_body TI.n_body_len].
  split; [exact P0|]. split; [exact P8|].
  split; [exact (ntdesk_src lyc Sc W memc mdc mT regs Bw n p NTC_SIZE LAWS HAR Hce KA Hsrc Hoff HAPp)|].
  split; [exact (ntdesk_off regs regsT p NTC_SIZE Hsp Hoff)|].
  exists NB.
  split.
  { apply (ntdesk_arr lyc Sc W memc mdc mT regs Bw n p NTC_SIZE p NB LAWS HAR KA Hsrc Hoff HAPp); [lia | | exact HNB].
    rewrite HNBL. unfold NTC_SIZE. change (Z.of_nat 72) with 72. lia. }
  split; [exact HNBL|]. split; [exact Hk|]. split; [exact Hs|]. split; [exact Ho|]. split; [exact Hr|].
  split; [exact Hpe|]. split; [exact Hmac|]. split; [exact Hbl|]. split; [exact Hcnt|]. split; [exact Hret|].
  split; [apply (ntdesk_arr lyc Sc W memc mdc mT regs Bw n _ _ _ _ LAWS HAR KA HBS HBW HAPb); [lia | lia | exact HBG]|].
  split; [exact (ntdesk_src lyc Sc W memc mdc mT regs Bw n _ _ LAWS HAR Hce KA HBS HBW HAPb)|].
  split; [exact (ntdesk_off regs regsT _ _ Hsp HBW)|].
  revert HANN. destruct (TI.n_ann n) as [an|] eqn:EA; cbn [option_map]; intros HANN; [|exact HANN].
  destruct HANN as (A0 & A8 & AV & AN & AS & AW).
  assert (HAPa : forall a, notice_wr Bw n a -> ~ (TW.u_at NB 24 8 <= a < TW.u_at NB 24 8 + ANN_SIZE))
    by (intros a Hz; exact (proj2 (proj1 (proj2 (HAP a Hz)) NB HNB HNBL) ltac:(rewrite EA; discriminate))).
  unfold nt_ann_cut. cbn [TI.ta_version TI.ta_name].
  split; [exact A0|]. split; [exact A8|].
  split.
  { apply (ntdesk_arr lyc Sc W memc mdc mT regs Bw n _ ANN_SIZE _ _ LAWS HAR KA AS AW HAPa);
      [lia | | exact (ntdesk_garr8_firstn _ _ _ 10 AV)].
    rewrite length_firstn. unfold ANN_SIZE. lia. }
  split.
  { apply (ntdesk_arr lyc Sc W memc mdc mT regs Bw n _ ANN_SIZE _ _ LAWS HAR KA AS AW HAPa);
      [lia | | exact (ntdesk_garr8_firstn _ _ _ 10 AN)].
    rewrite length_firstn. unfold ANN_SIZE. lia. }
  split; [exact (ntdesk_src lyc Sc W memc mdc mT regs Bw n _ _ LAWS HAR Hce KA AS AW HAPa)|].
  exact (ntdesk_off regs regsT _ _ Hsp AW).
Qed.

(* The frame check_state_desk gets, at the call memory. *)
Lemma ntdesk_tf : forall lyc Sc (W : world segs) memc mdc mT regs regsT Bw n p Fr,
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc ->
  alloc_ceiling <= spZ regs - NOTICE_STK -> spZ regsT = spZ regs ->
  nt_KA W memc mT (nt_Zs regs Bw n) -> notice_apart W memc p n Fr Bw ->
  trans_tframe_at B lyc Sc W memc regs NOTICE_STK Fr ->
  trans_tframe_at B lyc Sc W mT regsT CSDESK_STK Fr.
Proof.
  intros lyc Sc W memc mdc mT regs regsT Bw n p Fr LAWS HAR Hce Hsp KA HAP HTF.
  destruct Fr as [fr|]; [|exact I].
  cbn [trans_tframe_at] in HTF |- *.
  destruct HTF as (F0 & FG & FS & FW).
  assert (HAPf : forall a, notice_wr Bw n a ->
    ~ (TI.tf_addr fr <= a < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr))))
    by (intros a Hz; exact (proj2 (proj2 (HAP a Hz)) fr eq_refl)).
  split; [exact F0|].
  split; [apply (ntdesk_arr lyc Sc W memc mdc mT regs Bw n _ _ _ _ LAWS HAR KA FS FW HAPf); [lia | lia | exact FG]|].
  split; [exact (ntdesk_src lyc Sc W memc mdc mT regs Bw n _ _ LAWS HAR Hce KA FS FW HAPf)|].
  exact (ntdesk_off regs regsT _ _ Hsp FW).
Qed.

(* ---- the arm ---- *)

Lemma nt_desk : @nt_path fx rc B MT TC.N_DESK NT_DESK.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB E ms md
  HC Ek HS HEI Elo Ed SHOK HJ KA0.
destruct (nt_basics B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB HC)
  as (HAR & Hwin & Hsp & Hce & Hm16 & Hp4096 & Hp47 & Hp8 & Hoffp & Hrd).
pose proof HC as [HCELLS HNCELLS LAWS MTL HGX HGE HDESK HLOST HDATA HACK HONL HJc Hra Hra4 Hgp Htp H11 Hsp16 Hlo Hhi
    HNT HTF HRO Htw Hm HAP HDT Hev HNB HNBL HK0 HK4 HK8 HK12 HK64 HK68].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : NOTICE_STK = 8240) by reflexivity.
destruct (nt_m_desk timg_B Fr Bw n Bw' Ek Hm) as [Hmax HBw].
destruct nt_cvals as (V1 & V95 & VN & V36 & V13 & V37 & V38 & V39 & V40 & V73 & V72 & V74 & V75 & V77 & VB).
(* the atoms the arm reads *)
assert (E38 : ew E 38 = Z_to_bv 64 (TW.u_at Bw (TW.OFF_GOT + 208) 4)).
{ rewrite (Elo 38%nat ltac:(lia)). exact (nt_E_atom regs NB Bw 6 ltac:(lia)). }
pose proof (TWL.u_at_range Bw (TW.OFF_GOT + 208) 4) as R38. change (8 * Z.of_nat 4) with 32 in R38.
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (Elo 2%nat ltac:(lia)), (nt_E_reg regs NB Bw 2 2%bv eq_refl); reflexivity).
assert (U37 : bv_unsigned (ew E (A_OBJ 37)) = TB_GOT + 208).
{ rewrite (HEI (A_OBJ 37) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), V37. reflexivity. }
assert (U37n : bv_unsigned (ew E 278) = TB_GOT + 208) by exact U37.
assert (U72 : bv_unsigned (ew E (A_HI 72)) = VAL (A_HI 72))
  by (apply HEI; unfold A_HI, A_OBJ, A_TEXT, A_LIM; lia).
assert (U72n : bv_unsigned (ew E 472) = VAL (A_HI 72)) by exact U72.
(* the world at the arm's entry, and the field's region *)
pose proof (nt_tw_Wn W memc (ms_mem ms) regs Bw ltac:(unfold TG.G_HARNESS_B_HI; lia) Htw KA0) as Htw0.
pose proof (nt_add E _ _ (nt_reg_fld 37 38) HS ltac:(vm_compute; reflexivity)) as HS2. clear HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts nt_ss_jr] in HS2.
specialize (HS2 ltac:(cbn [ms_mem restrict];
  exact (nt_fld_ok W (ms_mem ms) E Bw 37 38 208 U37 ltac:(lia) ltac:(unfold TW.SZ_GOT; lia) E38 Htw0))).
specialize (HS2 ltac:(cbn [all_disjoint]; split; [|exact I];
  unfold extent_disjoint, nt_reg_fld, nt_reg_frame;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite Usp, U37; unfold TB_GOT; lia)).
rename HS2 into HS.
assert (U11 : bv_unsigned (ew E 11) = p).
{ rewrite (Elo 11%nat ltac:(lia)), (nt_E_reg regs NB Bw 11 11%bv eq_refl), H11. apply unsigned_lit_small. lia. }
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (Elo 32%nat ltac:(lia)); exact (nt_E_atom regs NB Bw 0 ltac:(lia))).
pose proof (nt_facts_set E _ _ (nt_facts_g 37 (TB_GOT + 208)) HS
  (nt_facts_g_ok E (spZ regs) p 37 (TB_GOT + 208) Usp U11 E32 U37 ltac:(lia) Hsp16 ltac:(lia) Hp8
    ltac:(unfold TB_GOT; reflexivity))) as HS2.
clear HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2. rename HS2 into HS.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
(* run 1: the jump, the load of GOT.desk, the increment, to `blt` *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons_g.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?U37, ?U37n in Ha.
    apply nt_inG_GOT. lia. }
  apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Usp in Ha.
  left. split; [unfold awr_byte; left; lia | lia]. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms1 end.
assert (KA1 : nt_KA W memc (ms_mem ms1) (nt_Zs regs Bw n)).
{ apply (nt_KA_run _ _ W memc _ _ _ (nt_KA_mono W memc _ _ _ (nt_Wn_Zs regs Bw n) KA0) HFr HG).
  intros b wlo whi x Hin Hx. cbv beta.
  nt_win Hin Hx ltac:(rewrite ?Usp, ?U37, ?U37n in Hx; first
    [ left; unfold nt_Wn; lia
    | right; unfold notice_wr; right; right; right; left; split; [exact Ek|];
      unfold twb_fld, TW.A_GOT_desk; lia ]). }
clear HF HFr HG.
(* the runs of this arm make no fresh atom (sh_j = 0): the valuation stays E *)
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* the trap: GOT.desk = INT_MAX *)
  rewrite (nt_ovf_br E 38 _ E38 R38) in Hc. apply Z.eqb_eq in Hc. exfalso. apply Hmax. exact Hc.
- rewrite (nt_ovf_br E 38 _ E38 R38) in Hc. apply Z.eqb_neq in Hc.
  (* a0 pinned to the field's object + 1096 *)
  nt_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (VAL (A_HI 72))) Q10
    ltac:(cbn [sv_denot]; rewrite ?U72, ?U72n, Z.add_0_r; reflexivity).
  pose proof (nt_pin E _ _ (Z_to_bv 5 10) (SOff (A_OBJ 37) 1096) HS
    ltac:(cbn [ms_regs restrict]; rewrite Q10; cbn [sv_denot]; rewrite U37, V72; f_equal; lia)
    ltac:(vm_compute; reflexivity)) as HS3.
  clear HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts add_cond] in HS3. rename HS3 into HS.
  (* run 2: the store, a0 = p, the epilogue, to the tail jump to check_state_desk *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
    apply awr_ok_x_cons_g.
    { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?U37, ?U37n in Ha.
      apply nt_inG_GOT. lia. }
    apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Usp in Ha.
    left. split; [unfold awr_byte; left; lia | lia]. }
  set (mdF := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody mdF. clear mat.
  lazymatch type of HS with context [restrict _ ?m] => rename m into msF end.
  assert (KAF : nt_KA W memc (ms_mem msF) (nt_Zs regs Bw n)).
  { apply (nt_KA_run _ _ W memc _ _ _ KA1 HFr HG).
    intros b wlo whi x Hin Hx. cbv beta.
    nt_win Hin Hx ltac:(rewrite ?Usp, ?U37, ?U37n in Hx; first
      [ left; unfold nt_Wn; lia
      | right; unfold notice_wr; right; right; right; left; split; [exact Ek|];
        unfold twb_fld, TW.A_GOT_desk; lia ]). }
  clear HF HFr HG.
  (* the field's 4 bytes at the call *)
  pose proof (st_ok_region_nth E _ (restrict (w_H W) msF) 0 _ HS eq_refl) as RGF.
  cbn [ms_mem restrict] in RGF.
  destruct RGF as (_ & _ & _ & HCH). cbn [YP09.r_base YP09.r_chunks base_val] in HCH.
  apply Forall_cons_iff in HCH as [HCH _].
  rewrite ?U37, ?U37n in HCH.
  assert (HV4 : forall j, (j < 4)%nat ->
    aview segs (w_H W) (ms_mem msF) (TB_GOT + 208 + Z.of_nat j) =
    Some (YO0f.le_byte (TW.GOT_desk Bw + 1) 4 j)).
  { intros j Hj. pose proof (nt_chunk_aview W (ms_mem msF) E (TB_GOT + 208) 0 4 _ (Z.of_nat j) HCH ltac:(lia)) as X.
    rewrite Z.add_0_r in X. rewrite X. f_equal.
    apply (nt_inc_bytes E 38 _ j); [exact E38 | exact R38 | exact Hc | exact Hj]. }
  (* the registers at the call: ra and sp the entry's, a0 = p, gp, tp and the callee-saved registers kept *)
  nt_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
    ltac:(cbn [sv_denot]; rewrite (Elo 1%nat ltac:(lia)), (nt_E_reg regs NB Bw 1 1%bv eq_refl), Z.add_0_r,
            Z_to_bv_bv_unsigned; reflexivity).
  nt_reg HS (2%bv : bv 5) (YK11.getr regs 2) RF2
    ltac:(cbn [sv_denot]; rewrite (Elo 2%nat ltac:(lia)), (nt_E_reg regs NB Bw 2 2%bv eq_refl), Z.add_0_r,
            Z_to_bv_bv_unsigned; reflexivity).
  nt_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
    ltac:(cbn [sv_denot]; rewrite (Elo 3%nat ltac:(lia)), (nt_E_reg regs NB Bw 3 3%bv eq_refl), Z.add_0_r,
            Z_to_bv_bv_unsigned; exact Hgp).
  nt_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
    ltac:(cbn [sv_denot]; rewrite (Elo 4%nat ltac:(lia)), (nt_E_reg regs NB Bw 4 4%bv eq_refl), Z.add_0_r,
            Z_to_bv_bv_unsigned; exact Htp).
  nt_reg HS (10%bv : bv 5) (w64 p) R10
    ltac:(cbn [sv_denot]; rewrite (Elo 11%nat ltac:(lia)), (nt_E_reg regs NB Bw 11 11%bv eq_refl), Z.add_0_r,
            Z_to_bv_bv_unsigned; exact H11).
  assert (HspT : spZ (ms_regs msF) = spZ regs).
  { change (bv_unsigned (YK11.getr (ms_regs msF) 2) = bv_unsigned (YK11.getr regs 2)). rewrite RF2. reflexivity. }
  assert (HPF : aregs_preserved regs (ms_regs msF)).
  { apply (aregs_preserved_of_st_ok segs (w_H W) E _ msF regs (nt_vals NB Bw) HS).
    - split; [intros j Hj; rewrite (Elo j ltac:(lia)); unfold nt_E; apply Eimg_low; unfold A_TEXT; lia
             | rewrite Ed; reflexivity].
    - vm_compute. reflexivity. }
  (* the world after GOT.desk++ *)
  assert (HtwF : tw_at TMAP_B (aview segs (w_H W) (ms_mem msF)) (TW.set_GOT_desk Bw (TW.GOT_desk Bw + 1))).
  { unfold TW.set_GOT_desk, TW.A_GOT_desk.
    apply (nt_tw_set4 W memc (ms_mem msF) Bw TW.OFF_GOT TB_GOT TW.SZ_GOT 208 (TW.GOT_desk Bw + 1) Htw TMAP_B_GOT);
      [lia | unfold TW.SZ_GOT; lia | exact HV4 |].
    intros x Hx Hn. pose proof KAF as [KAx _]. apply KAx.
    + pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. lia.
    + unfold nt_Zs. intros [Hz | Hz].
      * pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_HI in Hh. lia.
      * apply Hn. unfold notice_wr in Hz.
        unfold TC.N_STATE, TC.N_ACKED, TC.N_ACK_LOST, TC.N_DESK, TC.N_DATA, TC.N_FOREIGN in Hz, Ek.
        destruct Hz as [(E' & _) | [(E' & _) | [(E' & _) | [(_ & Hz) | [(E' & _) | (E' & _)]]]]]; try lia.
        unfold twb_fld, TW.A_GOT_desk in Hz. lia. }
  (* check_state_desk's premises at the call state *)
  assert (P_ra : YK0s.ret_ok (YK11.getr (ms_regs msF) 1)) by (rewrite RF1; exact Hra).
  assert (P_ra4 : 4096 <= raZ (ms_regs msF))
    by (change (4096 <= bv_unsigned (YK11.getr (ms_regs msF) 1)); rewrite RF1; exact Hra4).
  assert (P_sp16 : spZ (ms_regs msF) mod 16 = 0) by (rewrite HspT; exact Hsp16).
  assert (P_lo : sp0 - STK <= spZ (ms_regs msF) - CSDESK_STK)
    by (rewrite HspT, <- (proj2 notice_stk_eq); exact Hlo).
  assert (P_hi : spZ (ms_regs msF) <= sp0) by (rewrite HspT; exact Hhi).
  assert (P_nt : trans_ntc_at B lyc Sc W (ms_mem msF) (ms_regs msF) CSDESK_STK p (nt_cut n))
    by exact (ntdesk_ntc lyc Sc W memc mdc (ms_mem msF) regs (ms_regs msF) Bw n p Fr LAWS HAR Hce HspT KAF HAP HNT).
  assert (P_tf : trans_tframe_at B lyc Sc W (ms_mem msF) (ms_regs msF) CSDESK_STK Fr)
    by exact (ntdesk_tf lyc Sc W memc mdc (ms_mem msF) regs (ms_regs msF) Bw n p Fr LAWS HAR Hce HspT KAF HAP HTF).
  assert (P_ro : trans_rom_view_rd W (ms_mem msF)) by exact (nt_ro_keep W memc (ms_mem msF) regs Bw n Hce KAF HRO).
  assert (P_m : TC.check_state_desk_m timg_B Fr (TW.set_GOT_desk Bw (TW.GOT_desk Bw + 1)) (nt_cut n) = Some (Bw', tt))
    by (rewrite nt_desk_cut; exact HBw).
  assert (P_ev : st_nev S + k + CSDESK_EV <= EV_MAX) by (unfold CSDESK_EV; unfold NOTICE_EV in Hev; exact Hev).
  assert (KW : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W (ms_mem msF) (spZ regs - NOTICE_STK) (spZ regs)
    (notice_wr Bw n)) by exact (ntdesk_kept lyc Sc W memc mdc (ms_mem msF) regs Bw n LAWS HGX HAR Hwin Hce KAF).
  (* the tail jump: check_state_desk through gx_call_cg *)
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (@cfg_at fx sg (transportb_sigma TB_check_state_desk) rg mm mdx) Q) end.
  pose proof (HDESK fx) as HD. unfold transport_check_state_desk_cg in HD.
  eapply SRr_mono.
  { apply (gx_call_cg segs B MT TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem msF) mdF k _
      (ms_regs msF) CSDESK_STK CSDESK_EV 0 (fun _ => False)
      (fun _ _ _ => Bw' = TW.set_GOT_desk Bw (TW.GOT_desk Bw + 1)) HGX HGE HJ).
    intros memS HJS.
    eapply SRr_mono.
    { exact (HD STK sp0 FP ly S W0 memS md0 own lyc Sc W (ms_mem msF) mdF k (ms_regs msF) p (nt_cut n) Fr
        (TW.set_GOT_desk Bw (TW.GOT_desk Bw + 1)) Bw' HJS P_ra P_ra4 R3 R4 R10 P_sp16 P_lo P_hi P_nt P_tf P_ro
        HtwF P_m P_ev). }
    intros W2 c2 _ H2. apply decode_cg_post_dcg. exact H2. }
  intros W2 c2 _ HP2. unfold transport_notice_post.
  refine (ntdesk_tail_fold TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc (ms_mem msF) k regs
    (ms_regs msF) NOTICE_STK CSDESK_STK NOTICE_EV CSDESK_EV 0 (notice_wr Bw n) (fun _ => False) _ _ W2 c2
    Hce ltac:(lia) ltac:(rewrite HspT, <- (proj2 notice_stk_eq); lia) ltac:(rewrite HspT; lia)
    ltac:(unfold CSDESK_EV, NOTICE_EV; lia) (fun a H => False_ind _ H) HPF RF1 KW _ HP2).
  intros regs2 W2' mem2 HX. cbv beta in HX |- *. destruct HX as [HB HG2]. rewrite HB.
  apply (tw_kept_GB _ _ _ HtwF). intros b0 n0 i Hin Hi.
  exact (gx_kept_rows segs _ W (ms_mem msF) W2' mem2 HG2 b0 n0 i Hin Hi).
Qed.
End desk.
