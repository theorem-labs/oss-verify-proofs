(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 678 of its 962 lines of code are new or changed and 855 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/DgnBcHead.v, with its module paths, module names and numbers changed; 528 of its 590 lines of code are new or changed and 900 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/notice_seg_base.v, with its numbers changed; 317 of its 395 lines of code are new or changed and 512 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/notice_seg_lost.v, with its numbers changed; 316 of its 437 lines of code are new or changed and 274 lines of the source are left out. *)
(* notice_seg_data: the N_DATA arm of notice's walk on fuzz_transport.asan-ubsan (lib/B/Prog/notice_cgW.v), from the
   jump `jr a0` (0x83474) with a0 = 0x834b0:
     0x834b0 - 0x834b4  a0 = p; the call of check_state_data (0x857cc) from sp - 16, return address 0x834b8;
     0x834b8 - 0x834c0  a0 = the auipc value 0x5e54b8; a2 = GOT.ndata (the 4-byte signed load at GOT + 220, read from
                        the region of that field, its value the world's u32), a1 = a2 + 1 (addiw);
     0x834c4            `blt a1, a2` to the UBSan trap 0x83610: taken exactly at INT_MAX (nt_ovf_br), which notice_m
                        rules out (its int_inc is None there);
     0x834c8            the store of a1 at a0 - 1148 = GOT + 220 (a0 pinned to that field's object + 1148);
     0x834cc - 0x8360c  the jump to the epilogue: ra loaded back, sp = sp + 16, return.
   check_state_data is a donor-form callee (TransportGCg.v gx_call_cg): its contract is applied at the call state (the
   run to the call stores nothing outside notice's window), at the notice whose announce is cut to its 20 bytes (nt_cut;
   every byte it names lies outside notice's window), with the body-range premises notice's statement carries. Its post
   is relative to the call memory and to the world W2 it returns: what the run to the call kept (ntdata_kept at the entry
   world) and what the callee kept compose by dk_kept_trans_g; the symbolic state at the return is rebuilt keeping the
   frame region (the callee writes nothing outside its window, and acall_kept_g keeps every byte above alloc_ceiling
   outside it); the callee keeps every byte of G, so GOT.ndata is read at the world Bw; the runs after the return keep
   acall_kept_g by ntdata_kept at W2. The post: the world is set_GOT_ndata Bw (GOT.ndata + 1) (nt_tw_set4). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
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
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The bytes the runs after the call change: notice's own 16-byte frame and GOT.ndata. *)
Definition ntdata_Z2 (regs : bvmap 5 word) (a : Z) : Prop :=
  (spZ regs - 16 <= a < spZ regs) \/ (TB_GOT + 220 <= a < TB_GOT + 224).

Section data. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* ---- what the walk keeps, as acall_kept_g ---- *)

(* acall_kept_g at notice's window, carried across a step at a later world W2 that changes only bytes of Zs, each in
   notice's window or in G (a copy of TransportGCg.v dk_kept_step_g whose step is at the world the callee returned,
   with the address facts of the entry state's AR). *)
Lemma ntdata_kept : forall lyc Sc (W : world segs) memc mdc (W2 : world segs) memX memY slo shi (Eo Zs : Z -> Prop),
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc ->
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 memX slo shi Eo ->
  nt_KA W2 memX memY Zs -> alloc_ceiling <= slo ->
  (forall a, Zs a -> (slo <= a < shi) \/ inG TG.G_HARNESS_B a) ->
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 memY slo shi Eo.
Proof.
  intros lyc Sc W memc mdc W2 memX memY slo shi Eo Zs LAWS HAR (K1 & K2 & K3 & K4 & K5 & K6) [Hkp Hgr] Hce HZ.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (GL : forall a, inG TG.G_HARNESS_B a -> a < kLowMemEnd)
    by (intros a Ha; exact (proj2 (transportb_segs_low a (trans_g_img a Ha)))).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hw. rewrite Hkp; [exact (K1 a Ha Hw) | lia |].
    intros HZa. destruct (HZ a HZa) as [H|H]; [exact (Hw H) | pose proof (GL a H); lia].
  - intros b m i Hb Hi Hn. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _).
    rewrite Hkp; [apply (K2 b m i Hb Hi Hn) | lia |].
    intros HZa. destruct (HZ _ HZa) as [H|H]; [lia|].
    exact (blk_img segs B LAWS lyc Sc W memc mdc b m (b + i) HAR Hb ltac:(lia) (trans_g_img _ H)).
  - intros a Hi HnG Hno He. pose proof (transportb_segs_low a Hi) as Hlow.
    rewrite Hkp; [exact (K3 a Hi HnG Hno He) | lia |].
    intros HZa. destruct (HZ a HZa) as [H|H]; [lia | exact (HnG H)].
  - intros cid pos a Hin Hr Hn.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    assert (Ha : 0 <= a < alloc_ceiling).
    { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
      pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
      assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
      pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
      unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
    rewrite Hkp; [apply (K4 cid pos a Hin Hr Hn) | lia |].
    intros HZa. destruct (HZ a HZa) as [H|H]; [lia|].
    destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr.
    + exact (frm_img segs B LAWS lyc Sc W memc mdc cid pos a HAR Hin Hr (trans_g_img a H)).
    + pose proof (GL a H). pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
      unfold shadow_addr, SHADOW_OFF, kLowMemEnd in *. lia.
  - intros a Ha Hw Hp. apply Hgr. exact (K5 a Ha Hw Hp).
  - intros a Ha. apply Hgr. apply K6. exact Ha.
Qed.

(* ---- what check_state_data gets at the call ---- *)

(* A range a callee reads lies in [0, 2 ^ 64) (trans_src_ok_place), and outside notice's window (decode_off_win). *)
Lemma ntdata_rng : forall lyc Sc (W : world segs) memc mdc regs q len,
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc ->
  trans_src_ok B lyc Sc W memc q len -> decode_off_win regs NOTICE_STK q len ->
  forall a, q <= a < q + len -> 0 <= a < 2 ^ 64 /\ ~ nt_Wn regs a.
Proof.
  intros lyc Sc W memc mdc regs q len LAWS HAR Hs Ho a Ha.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold nt_Wn, decode_off_win in *.
  destruct (trans_src_ok_place B LAWS lyc Sc W memc mdc q len HAR Hs ltac:(lia)) as [H|H]; lia.
Qed.

(* trans_src_ok of such a range at the call memory, and decode_off_win at the call's window (sp - 16, CSDATA_STK). *)
Lemma ntdata_src : forall lyc Sc (W : world segs) memc mdc m regs regs1 q len,
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc -> nt_KA W memc m (nt_Wn regs) ->
  alloc_ceiling <= spZ regs - NOTICE_STK -> spZ regs1 = spZ regs - 16 ->
  trans_src_ok B lyc Sc W memc q len -> decode_off_win regs NOTICE_STK q len ->
  trans_src_ok B lyc Sc W m q len /\ decode_off_win regs1 CSDATA_STK q len.
Proof.
  intros lyc Sc W memc mdc m regs regs1 q len LAWS HAR [KA _] Hce Hs1 Hs Ho.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : NOTICE_STK = 8240) by reflexivity. assert (FC : CSDATA_STK = 8224) by reflexivity.
  split.
  - apply (trans_src_ok_view B lyc Sc W W memc m q len Hs).
    + intros a Ha. destruct (ntdata_rng lyc Sc W memc mdc regs q len LAWS HAR Hs Ho a Ha) as [H1 H2].
      exact (KA a H1 H2).
    + intros s Hs'. apply KA; [lia | unfold nt_Wn; lia].
  - unfold decode_off_win in *. rewrite Hs1. lia.
Qed.

(* An array of bytes inside such a range, at the call memory. *)
Lemma ntdata_garr8 : forall lyc Sc (W : world segs) memc mdc m regs q len q' (l : list Z),
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc -> nt_KA W memc m (nt_Wn regs) ->
  trans_src_ok B lyc Sc W memc q len -> decode_off_win regs NOTICE_STK q len ->
  garr8 segs (mrestrict (w_H W) memc) q' l -> q <= q' -> q' + Z.of_nat (length l) <= q + len ->
  garr8 segs (mrestrict (w_H W) m) q' l.
Proof.
  intros lyc Sc W memc mdc m regs q len q' l LAWS HAR KA Hs Ho HG H1 H2.
  apply (nt_garr8_keep W memc m (nt_Wn regs) q' l KA HG).
  intros a Ha. apply (ntdata_rng lyc Sc W memc mdc regs q len LAWS HAR Hs Ho). lia.
Qed.

Lemma ntdata_garr8_firstn : forall (mm : word -> option byte) q (l : list byte) j,
  garr8 segs mm q (map DSpec.bz l) -> garr8 segs mm q (map DSpec.bz (firstn j l)).
Proof.
  intros mm q l j H. rewrite <- (firstn_skipn j l), map_app in H.
  exact (proj1 (proj1 (garr8_app segs mm q _ _) H)).
Qed.

(* The notice check_state_data gets, at the call memory and registers: the struct, the body and the cut announce. *)
Lemma ntdata_ntc : forall lyc Sc (W : world segs) memc mdc m regs regs1 p n,
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc -> nt_KA W memc m (nt_Wn regs) ->
  alloc_ceiling <= spZ regs - NOTICE_STK -> spZ regs1 = spZ regs - 16 ->
  trans_ntc_at B lyc Sc W memc regs NOTICE_STK p n ->
  trans_ntc_at B lyc Sc W m regs1 CSDATA_STK p (nt_cut n).
Proof.
  intros lyc Sc W memc mdc m regs regs1 p n LAWS HAR KA Hce Hs1 HNT.
  unfold trans_ntc_at in HNT |- *.
  destruct HNT as (P0 & P8 & Hsrc & Hoff & NB & HG & HL & K0 & K4 & K8 & K12 & Kp & Km & Kbl & Kc & Kr & HGb & Hsb & Hob
    & Hann).
  destruct (ntdata_src lyc Sc W memc mdc m regs regs1 _ _ LAWS HAR KA Hce Hs1 Hsrc Hoff) as [S1 O1].
  destruct (ntdata_src lyc Sc W memc mdc m regs regs1 _ _ LAWS HAR KA Hce Hs1 Hsb Hob) as [S2 O2].
  split; [exact P0|]. split; [exact P8|]. split; [exact S1|]. split; [exact O1|].
  exists NB.
  split.
  { apply (ntdata_garr8 lyc Sc W memc mdc m regs _ _ _ _ LAWS HAR KA Hsrc Hoff HG); [lia|].
    rewrite length_map, HL. unfold NTC_SIZE. change (Z.of_nat 72) with 72. lia. }
  split; [exact HL|]. split; [exact K0|]. split; [exact K4|]. split; [exact K8|]. split; [exact K12|].
  split; [exact Kp|]. split; [exact Km|]. split; [exact Kbl|]. split; [exact Kc|]. split; [exact Kr|].
  split.
  { apply (ntdata_garr8 lyc Sc W memc mdc m regs _ _ _ _ LAWS HAR KA Hsb Hob HGb); [lia|].
    rewrite length_map. lia. }
  split; [exact S2|]. split; [exact O2|].
  cbn [nt_cut TI.n_ann].
  revert Hann. destruct (TI.n_ann n) as [an|]; cbn [option_map]; intros Hann; [|exact Hann].
  destruct Hann as (A0 & A8 & HGv & HGn & Hsa & Hoa).
  destruct (ntdata_src lyc Sc W memc mdc m regs regs1 _ _ LAWS HAR KA Hce Hs1 Hsa Hoa) as [S3 O3].
  unfold nt_ann_cut. cbn [TI.ta_version TI.ta_name].
  split; [exact A0|]. split; [exact A8|].
  split.
  { apply (ntdata_garr8 lyc Sc W memc mdc m regs _ _ _ _ LAWS HAR KA Hsa Hoa (ntdata_garr8_firstn _ _ _ 10 HGv));
      [lia|].
    rewrite length_map, length_firstn. unfold ANN_SIZE. lia. }
  split.
  { apply (ntdata_garr8 lyc Sc W memc mdc m regs _ _ _ _ LAWS HAR KA Hsa Hoa (ntdata_garr8_firstn _ _ _ 10 HGn));
      [lia|].
    rewrite length_map, length_firstn. unfold ANN_SIZE. lia. }
  exact (conj S3 O3).
Qed.

(* The frame check_state_data gets, at the call memory and registers. *)
Lemma ntdata_tf : forall lyc Sc (W : world segs) memc mdc m regs regs1 (Fr : option TI.tframe),
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc -> nt_KA W memc m (nt_Wn regs) ->
  alloc_ceiling <= spZ regs - NOTICE_STK -> spZ regs1 = spZ regs - 16 ->
  trans_tframe_at B lyc Sc W memc regs NOTICE_STK Fr -> trans_tframe_at B lyc Sc W m regs1 CSDATA_STK Fr.
Proof.
  intros lyc Sc W memc mdc m regs regs1 Fr LAWS HAR KA Hce Hs1 HT.
  destruct Fr as [fr|]; [|exact I].
  cbn [trans_tframe_at] in HT |- *.
  destruct HT as (A0 & HG & Hs & Ho).
  destruct (ntdata_src lyc Sc W memc mdc m regs regs1 _ _ LAWS HAR KA Hce Hs1 Hs Ho) as [S1 O1].
  split; [exact A0|]. split; [|exact (conj S1 O1)].
  apply (ntdata_garr8 lyc Sc W memc mdc m regs _ _ _ _ LAWS HAR KA Hs Ho HG); [lia | rewrite length_map; lia].
Qed.

(* ---- the post at the return ---- *)

(* transport_notice_post at the world W2 the callee returned, from the callee's journal facts (no event, its frames and
   blocks, no meter charge), the walk's journal at the return, the kept bytes, the world relation and the registers. *)
Lemma ntdata_close : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB
    ly2 S2 (W2 : world segs) regsF mF mdF,
  nt_ctx B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2
    mF mdF k ->
  frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> mo_le MT Sc S2 0 ->
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 mF (spZ regs - NOTICE_STK) (spZ regs) (notice_wr Bw n) ->
  tw_at TMAP_B (aview segs (w_H W2) mF) Bw' ->
  aregs_preserved regs regsF -> YK11.getr regsF 1 = YK11.getr regs 1 ->
  forall mat, @transport_notice_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs n Bw Bw' W2
    (mkCfg (@YK11.mkst fx regsF (v_jalr (YK11.getr regsF 1) 0) mF (YK11.seg_rom segs))
      (with_vm_backing (m_vm_lazy mdF) mat mdF)).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB ly2 S2 W2 regsF mF mdF
    HC HJF Hfr Hperm HMO AK HtwF HP RF1 mat.
  pose proof HC as [HCELLS HNCELLS LAWS MTL HGX HGE HDESK HLOST HDATA HACK HONL HJc Hra Hra4 Hgp Htp H11 Hsp16 Hlo Hhi
    HNT HTF HRO Htw Hm HAP HDT Hev HNB HNBL HK0 HK4 HK8 HK12 HK64 HK68].
  unfold transport_notice_post, transport_cg_post.
  exists ly2, S2, regsF, mF, (with_vm_backing (m_vm_lazy mdF) mat mdF), 0.
  split.
  { rewrite RF1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
  split; [unfold NOTICE_EV; lia|].
  split; [rewrite Z.add_0_r; apply (ajournal_gx_materialize segs B LAWS transportb_segs_low); exact HJF|].
  split; [exact HP|]. split; [exact Hfr|]. split; [exact Hperm|]. split; [exact AK|].
  split; [exact HMO | exact HtwF].
Qed.

(* ---- the arm ---- *)

Lemma nt_data : @nt_path fx rc B MT TC.N_DATA NT_DATA.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB E ms md
  HC Ek HS HEI Elo Ed SHOK HJ KA0.
destruct (nt_basics B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB HC)
  as (HAR & Hwin & Hsp & Hce & Hm16 & Hp4096 & Hp47 & Hp8 & Hoffp & Hrd).
pose proof HC as [HCELLS HNCELLS LAWS MTL HGX HGE HDESK HLOST HDATA HACK HONL HJc Hra Hra4 Hgp Htp H11 Hsp16 Hlo Hhi
    HNT HTF HRO Htw Hm HAP HDT Hev HNB HNBL HK0 HK4 HK8 HK12 HK64 HK68].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : NOTICE_STK = 8240) by reflexivity.
assert (FC : CSDATA_STK = 8224) by reflexivity.
destruct (nt_m_data timg_B Fr Bw n Bw' Ek Hm) as (HDm & Hmax & HBw).
destruct (HDT Ek) as (HDsrc & HDoff & HDlen).
destruct nt_cvals as (V1 & V95 & VN & V36 & V13 & V37 & V38 & V39 & V40 & V73 & V72 & V74 & V75 & V77 & VB).
(* the atoms the arm reads *)
assert (E39 : ew E 39 = Z_to_bv 64 (TW.u_at Bw (TW.OFF_GOT + 220) 4)).
{ rewrite (Elo 39%nat ltac:(lia)). exact (nt_E_atom regs NB Bw 7 ltac:(lia)). }
pose proof (TWL.u_at_range Bw (TW.OFF_GOT + 220) 4) as R39. change (8 * Z.of_nat 4) with 32 in R39.
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (Elo 2%nat ltac:(lia)), (nt_E_reg regs NB Bw 2 2%bv eq_refl); reflexivity).
assert (U11 : bv_unsigned (ew E 11) = p).
{ rewrite (Elo 11%nat ltac:(lia)), (nt_E_reg regs NB Bw 11 11%bv eq_refl), H11. apply unsigned_lit_small. lia. }
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (Elo 32%nat ltac:(lia)); exact (nt_E_atom regs NB Bw 0 ltac:(lia))).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
pose proof (paj_ret_at (fx := fx) (PL := PL_transportb) (PI := PI_transportb)) as RET.
(* run 1: the jump, a0 = p, to the call of check_state_data *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Usp in Ha.
  left. split; [unfold awr_byte; left; lia | lia]. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
assert (KA1 : nt_KA W memc (ms_mem ms1) (nt_Wn regs)).
{ apply (nt_KA_run _ _ W memc _ _ _ KA0 HFr HG).
  intros b wlo whi x Hin Hx. cbv beta.
  nt_win Hin Hx ltac:(rewrite ?Usp in Hx; unfold nt_Wn; lia). }
clear HF HFr HG.
(* the registers at the call: sp - 16, ra = notice + 0x9c, gp, tp, a0 = p *)
nt_reg HS (Z_to_bv 5 2) (Z_to_bv 64 (spZ regs - 16)) Q2 ltac:(cbn [sv_denot]; rewrite Usp; f_equal; lia).
assert (ESP : bv_unsigned (YK11.getr (ms_regs ms1) (Z_to_bv 5 2)) = spZ regs - 16)
  by (rewrite Q2; apply unsigned_lit_small; lia).
assert (Hsp1 : spZ (ms_regs ms1) = spZ regs - 16) by exact ESP.
nt_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 8728)) R1 ltac:(apply codeptr_val; exact HEI).
nt_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; rewrite (Elo 3%nat ltac:(lia)), (nt_E_reg regs NB Bw 3 3%bv eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; exact Hgp).
nt_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; rewrite (Elo 4%nat ltac:(lia)), (nt_E_reg regs NB Bw 4 4%bv eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; exact Htp).
nt_reg HS (10%bv : bv 5) (w64 p) R10
  ltac:(cbn [sv_denot]; rewrite (Elo 11%nat ltac:(lia)), (nt_E_reg regs NB Bw 11 11%bv eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; exact H11).
(* check_state_data's premises at the call state *)
assert (P_ra : YK0s.ret_ok (YK11.getr (ms_regs ms1) 1)).
{ pose proof (ret_ok_codeptr_v (PI := PI_transportb) 8728 ltac:(lia) eq_refl) as X. rewrite <- R1 in X. exact X. }
assert (P_ra4 : 4096 <= raZ (ms_regs ms1)).
{ change (4096 <= bv_unsigned (YK11.getr (ms_regs ms1) 1)). rewrite R1, VB, unsigned_lit_small by lia. lia. }
assert (P_sp16 : spZ (ms_regs ms1) mod 16 = 0).
{ rewrite Hsp1. replace (spZ regs - 16) with (spZ regs + (-1) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16. }
assert (P_lo : sp0 - STK <= spZ (ms_regs ms1) - CSDATA_STK) by (rewrite Hsp1; lia).
assert (P_hi : spZ (ms_regs ms1) <= sp0) by (rewrite Hsp1; lia).
pose proof (nt_tw_Wn W memc (ms_mem ms1) regs Bw ltac:(unfold TG.G_HARNESS_B_HI; lia) Htw KA1) as Htw1.
assert (P_nt : trans_ntc_at B lyc Sc W (ms_mem ms1) (ms_regs ms1) CSDATA_STK p (nt_cut n))
  by exact (ntdata_ntc lyc Sc W memc mdc (ms_mem ms1) regs (ms_regs ms1) p n LAWS HAR KA1 Hce Hsp1 HNT).
assert (P_tf : trans_tframe_at B lyc Sc W (ms_mem ms1) (ms_regs ms1) CSDATA_STK Fr)
  by exact (ntdata_tf lyc Sc W memc mdc (ms_mem ms1) regs (ms_regs ms1) Fr LAWS HAR KA1 Hce Hsp1 HTF).
destruct (ntdata_src lyc Sc W memc mdc (ms_mem ms1) regs (ms_regs ms1) _ _ LAWS HAR KA1 Hce Hsp1 HDsrc HDoff)
  as [P_src P_off].
assert (P_m : TC.check_state_data_m Fr Bw (nt_cut n) = Some (Bw, tt)) by (rewrite nt_data_cut; exact HDm).
assert (P_len : TI.n_body_len (nt_cut n) < 2 ^ 32) by exact HDlen.
assert (P_ev : st_nev S + k + CSDATA_EV <= EV_MAX) by (unfold CSDATA_EV; unfold NOTICE_EV in Hev; exact Hev).
(* what the run to the call kept, as acall_kept_g at notice's window *)
assert (AK1 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W (ms_mem ms1) (spZ regs - NOTICE_STK) (spZ regs)
  (notice_wr Bw n)).
{ apply (ntdata_kept lyc Sc W memc mdc W memc (ms_mem ms1) _ _ _ (nt_Wn regs) LAWS HAR); [| exact KA1 | exact Hce |].
  - apply dk_kept_refl_g. exact Hwin.
  - intros a Ha. left. exact Ha. }
(* the call: check_state_data through gx_call_cg *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at fx sg (transportb_sigma TB_check_state_data) rg mm mdx) Q) end.
pose proof (HDATA fx) as HD. unfold transport_check_state_data_cg in HD.
eapply SRr_bind.
{ apply (gx_call_cg segs B MT TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms1) md1 k _
    (ms_regs ms1) CSDATA_STK CSDATA_EV 0 (fun _ => False) (fun _ _ _ => Bw = Bw) HGX HGE HJ).
  intros memS HJS.
  eapply SRr_mono.
  { exact (HD STK sp0 FP ly S W0 memS md0 own lyc Sc W (ms_mem ms1) md1 k (ms_regs ms1) p (nt_cut n) Fr Bw Bw
      HJS P_ra P_ra4 R3 R4 R10 P_sp16 P_lo P_hi P_nt P_tf Htw1 P_m P_src P_off P_len P_ev). }
  intros W2 c2 _ H2. apply decode_cg_post_dcg. exact H2. }
cbv beta. intros W2 c2 _ Hpost.
destruct Hpost as (ly2 & S2 & regs2 & mem2 & md2 & e & Hc2 & He & HJ2 & HP2 & Hfr2 & Hperm2 & HK2 & HMO2 & _ & HGK2).
subst c2.
assert (He0 : e = 0) by (unfold CSDATA_EV in He; lia). subst e. rewrite Z.add_0_r in HJ2.
rewrite Hsp1 in HK2.
(* what the run to the call and the callee kept, composed *)
assert (AKc : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 mem2 (spZ regs - NOTICE_STK) (spZ regs)
  (notice_wr Bw n)).
{ apply (dk_kept_trans_g segs B TG.G_HARNESS_B lyc Sc W memc W (ms_mem ms1) W2 mem2 (spZ regs - NOTICE_STK) (spZ regs)
    (spZ regs - 16 - CSDATA_STK) (spZ regs - 16) (notice_wr Bw n) (fun _ => False) Hce ltac:(lia) AK1 HK2);
    [lia | lia | intros a []]. }
(* the world at the return: the callee keeps every byte of G *)
assert (Htw2 : tw_at TMAP_B (aview segs (w_H W2) mem2) Bw).
{ apply (tw_kept_GB _ _ _ Htw1). intros b0 n0 i Hin Hi.
  exact (gx_kept_rows segs _ W (ms_mem ms1) W2 mem2 HGK2 b0 n0 i Hin Hi). }
(* the symbolic state at the return: the frame region kept *)
pose proof HK2 as (K1c & _ & _ & _ & K5c & _).
jafter_call_keep_pi HS 200%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0%nat] HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  unfold region_kept. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]. rewrite Usp.
  split; intros a Ha.
  - apply (mbyte_of_aview segs). apply K1c; lia.
  - intros _. apply (apresent_writable segs). apply K5c; [lia | lia |]. apply (proj2 KA1). apply Hwin. lia. }
specialize (HS2 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst ?f ?rg ?pc ?mm ?rom) ?mdx) ?Q =>
  replace pc with (Z_to_bv 64 (BASE + 8728)) by (symmetry; exact R1) end.
set (E1 := havoc E 200 (map (YK11.getr regs2) CLOB)) in HS.
assert (HEI1 : img_env VAL A_LIM E1)
  by (apply img_env_havoc; [exact HEI | rewrite length_map; apply Nat.leb_le; reflexivity]).
assert (E1lo : forall j, (j < 200)%nat -> ew E1 j = ew E j) by (intros j Hj; apply ew_havoc_old; exact Hj).
assert (Usp1 : bv_unsigned (ew E1 2) = spZ regs) by (rewrite E1lo by lia; exact Usp).
assert (U11_1 : bv_unsigned (ew E1 11) = p) by (rewrite E1lo by lia; exact U11).
assert (E32_1 : ew E1 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite E1lo by lia; exact E32).
assert (E39_1 : ew E1 39 = Z_to_bv 64 (TW.u_at Bw (TW.OFF_GOT + 220) 4)) by (rewrite E1lo by lia; exact E39).
assert (U38 : bv_unsigned (ew E1 (A_OBJ 38)) = TB_GOT + 220).
{ rewrite (HEI1 (A_OBJ 38) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), V38. reflexivity. }
assert (U38n : bv_unsigned (ew E1 279) = TB_GOT + 220) by exact U38.
assert (U74 : bv_unsigned (ew E1 (A_HI 74)) = VAL (A_HI 74))
  by (apply HEI1; unfold A_HI, A_OBJ, A_TEXT, A_LIM; lia).
assert (U74n : bv_unsigned (ew E1 474) = VAL (A_HI 74)) by exact U74.
(* the field's region and the facts *)
pose proof (nt_add E1 _ _ (nt_reg_fld 38 39) HS ltac:(vm_compute; reflexivity)) as HS2. clear HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
specialize (HS2 ltac:(exact (nt_fld_ok W2 mem2 E1 Bw 38 39 220 U38 ltac:(lia) ltac:(unfold TW.SZ_GOT; lia) E39_1 Htw2))).
specialize (HS2 ltac:(cbn [all_disjoint]; split; [|exact I];
  unfold extent_disjoint, nt_reg_fld;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite Usp1, U38; unfold TB_GOT; lia)).
rename HS2 into HS.
pose proof (nt_facts_set E1 _ _ (nt_facts_g 38 (TB_GOT + 220)) HS
  (nt_facts_g_ok E1 (spZ regs) p 38 (TB_GOT + 220) Usp1 U11_1 E32_1 U38 ltac:(lia) Hsp16 ltac:(lia) Hp8
    ltac:(unfold TB_GOT; reflexivity))) as HS2.
clear HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2. rename HS2 into HS.
assert (SHOK1 : sh_ok segs NT_Bx [] E1 (mrestrict (w_H W2) mem2)) by (unfold sh_ok; constructor).
pose proof (nt_KA_refl W2 mem2 (ntdata_Z2 regs)) as KB.
(* run 2: the load of GOT.ndata, the increment, to `blt` *)
paj_run_tok RUN HS HJ2 SHOK1 YC4b.Bspan.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons_g.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?U38, ?U38n in Ha.
    apply nt_inG_GOT. lia. }
  apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Usp1 in Ha.
  left. split; [unfold awr_byte; left; lia | lia]. }
set (md3 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md3. clear mat.
lazymatch type of HS with context [restrict _ ?m] => rename m into ms3 end.
assert (KB3 : nt_KA W2 mem2 (ms_mem ms3) (ntdata_Z2 regs)).
{ apply (nt_KA_run _ _ W2 mem2 _ _ _ KB HFr HG).
  intros b wlo whi x Hin Hx. cbv beta.
  nt_win Hin Hx ltac:(rewrite ?Usp1, ?U38, ?U38n in Hx; unfold ntdata_Z2; first [left; lia | right; lia]). }
clear HF HFr HG KB.
(* the runs after the call make no fresh atom (sh_j = 0): the valuation stays E1 *)
psrr_branch_tok RUN BR HS SHOK1 YC4b.Bspan.
- (* the trap: GOT.ndata = INT_MAX *)
  rewrite (nt_ovf_br E1 39 _ E39_1 R39) in Hc. apply Z.eqb_eq in Hc. exfalso. apply Hmax. exact Hc.
- rewrite (nt_ovf_br E1 39 _ E39_1 R39) in Hc. apply Z.eqb_neq in Hc.
  (* a0 pinned to the field's object + 1148 *)
  nt_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (VAL (A_HI 74))) Q10
    ltac:(cbn [sv_denot]; rewrite ?U74, ?U74n, Z.add_0_r; reflexivity).
  pose proof (nt_pin E1 _ _ (Z_to_bv 5 10) (SOff (A_OBJ 38) 1148) HS
    ltac:(cbn [ms_regs restrict]; rewrite Q10; cbn [sv_denot]; rewrite U38, V74; f_equal; lia)
    ltac:(vm_compute; reflexivity)) as HS3.
  clear HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts add_cond] in HS3. rename HS3 into HS.
  (* run 3: the store, the jump to the epilogue, to `ret` *)
  paj_run_tok RUN HS HJ2 SHOK1 YC4b.Bspan.
  { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
    apply awr_ok_x_cons_g.
    { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?U38, ?U38n in Ha.
      apply nt_inG_GOT. lia. }
    apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Usp1 in Ha.
    left. split; [unfold awr_byte; left; lia | lia]. }
  set (mdF := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody mdF. clear mat.
  lazymatch type of HS with context [restrict _ ?m] => rename m into msF end.
  assert (KBF : nt_KA W2 mem2 (ms_mem msF) (ntdata_Z2 regs)).
  { apply (nt_KA_run _ _ W2 mem2 _ _ _ KB3 HFr HG).
    intros b wlo whi x Hin Hx. cbv beta.
    nt_win Hin Hx ltac:(rewrite ?Usp1, ?U38, ?U38n in Hx; unfold ntdata_Z2; first [left; lia | right; lia]). }
  clear HF HFr HG.
  (* the field's 4 bytes at the return *)
  pose proof (st_ok_pi_region_nth E1 _ (restrict (w_H W2) msF) 0 _ HS eq_refl) as RGF.
  cbn [ms_mem restrict] in RGF.
  destruct RGF as (_ & _ & _ & HCH). cbn [YP09.r_base YP09.r_chunks base_val] in HCH.
  apply Forall_cons_iff in HCH as [HCH _].
  rewrite ?U38, ?U38n in HCH.
  assert (HV4 : forall j, (j < 4)%nat ->
    aview segs (@w_H segs W2) (ms_mem msF) (TB_GOT + 220 + Z.of_nat j) =
    Some (YO0f.le_byte (TW.GOT_ndata Bw + 1) 4 j)).
  { intros j Hj. pose proof (nt_chunk_aview W2 (ms_mem msF) E1 (TB_GOT + 220) 0 4 _ (Z.of_nat j) HCH ltac:(lia)) as X.
    rewrite Z.add_0_r in X. rewrite X. f_equal.
    apply (nt_inc_bytes E1 39 _ j); [exact E39_1 | exact R39 | exact Hc | exact Hj]. }
  nt_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
    ltac:(cbn [sv_denot]; rewrite (E1lo 1%nat ltac:(lia)), (Elo 1%nat ltac:(lia)),
            (nt_E_reg regs NB Bw 1 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  assert (HPF : aregs_preserved regs (ms_regs msF)).
  { apply (aregs_preserved_of_st_ok segs (w_H W2) E1 _ msF regs (nt_vals NB Bw) HS).
    - split; [intros j Hj; rewrite (E1lo j ltac:(lia)), (Elo j ltac:(lia)); unfold nt_E; apply Eimg_low;
              unfold A_TEXT; lia
             | transitivity (ed E); [reflexivity | rewrite Ed; reflexivity]].
    - vm_compute. reflexivity. }
  (* the world after GOT.ndata++ *)
  assert (HtwF : tw_at TMAP_B (aview segs (w_H W2) (ms_mem msF)) Bw').
  { rewrite HBw. unfold TW.set_GOT_ndata, TW.A_GOT_ndata.
    apply (nt_tw_set4 W2 mem2 (ms_mem msF) Bw TW.OFF_GOT TB_GOT TW.SZ_GOT 220 (TW.GOT_ndata Bw + 1) Htw2 TMAP_B_GOT);
      [lia | unfold TW.SZ_GOT; lia | exact HV4 |].
    intros x Hx Hn. pose proof KBF as [KBx _]. apply KBx.
    + pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. lia.
    + unfold ntdata_Z2. intros [Hz | Hz].
      * pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_HI in Hh. lia.
      * apply Hn. lia. }
  (* what the whole walk kept *)
  assert (AKF : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 (ms_mem msF) (spZ regs - NOTICE_STK) (spZ regs)
    (notice_wr Bw n)).
  { apply (ntdata_kept lyc Sc W memc mdc W2 mem2 (ms_mem msF) _ _ _ (ntdata_Z2 regs) LAWS HAR AKc KBF Hce).
    intros a [Ha | Ha]; [left; lia | right; apply nt_inG_GOT; lia]. }
  eapply (RET W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  exact (ntdata_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB ly2 S2 W2
    (ms_regs msF) (ms_mem msF) mdF HC HJ2 Hfr2 Hperm2 HMO2 AKF HtwF HPF RF1 mat').
Qed.
End data.
