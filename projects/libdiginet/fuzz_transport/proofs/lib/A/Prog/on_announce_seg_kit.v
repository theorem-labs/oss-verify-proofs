(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: the shared part of proofs/libreac/fuzz_decode/lib/A/Prog/check_round_trip_cg.v (origin/ossv/recipes 88154566652a: dec_utrace, the read-only reads and their two instance facts, the value-0 shadow granule of a table, the leaf instances dec_leaf_at / dec_leaf_wr_at and the runtime cells as constant cells of the record) for reac-repacer/fuzz_uci's image A: module paths changed, the image is the core's tfibsegs (lib/A/AB1v.v), the read-only reads and the cells are fuzz_uci.asan's, measured on the pinned image. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/reac-repacer/fuzz_uci/lib/A/Prog/UciCg.v, with its module paths changed. *)
(* Modified by Theorem Labs: the shared part of proofs/libreac/fuzz_decode/lib/A/Prog/check_round_trip_cg.v (origin/ossv/recipes 88154566652a: dec_utrace, the read-only reads and their two instance facts, the value-0 shadow granule of a table, the leaf instances dec_leaf_at / dec_leaf_wr_at and the runtime cells as constant cells of the record) for reac-repacer/fuzz_uci's image A: module paths changed, the image is the core's tfibsegs (lib/A/AB1v.v), the read-only reads and the cells are fuzz_uci.asan's, measured on the pinned image. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/UciCg.v, with its module paths changed; 778 of its 849 lines of code are new or changed and 69 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/DgnTransportCg.v, with its module paths and module names changed; 709 of its 816 lines of code are new or changed and 742 lines of the source are left out. *)
(* on_announce_seg_kit: the shared lemmas of the pieces of on_announce's image-A G-form walk (the cut contract
   lib/A/Prog/OnannCut.v, the statement lib/A/Prog/on_announce_cg.v). It proves no piece; each piece file
   on_announce_seg_<piece>.v Requires it. Lemmas of note:
   - onann_cur_ar: from onann_fix and onann_cur, AR at the entry and at the cut state, the layout facts (stack bounds,
     frame_addr / flag_addr of the cut layout are the entry's), the own class-4 frame and its flag byte;
   - onann_src_kept / onann_tf_call: a range placed by trans_src_ok at the entry and outside G is placed at the cut
     state (own frame on top of the entry's frames) with its bytes kept (TransportGNotice.v trans_src_ok_kept_gx's
     form, for an E inside G);
     trans_tframe_at at a call state; onann_rom_call: trans_rom_view_rd at the cut memory;
   - onann_wr_G / onann_wr_lowmem / onann_wr_nframe: the written range onann_wr lies in G, below kLowMemEnd, off the
     frames and their shadow; the inclusions of the callees' written ranges (onann_wr_dntc, onann_wr_fntc,
     onann_wr_slost, onann_wr_wake, onann_wr_mo) and of their TF apart clauses (onann_apart_ntc, onann_apart_wake,
     onann_apart_mo, onann_apart_slost);
   - the model: onann_dn_world / onann_fg_world (an N_DESK / N_FOREIGN call_notify sets GOT.desk / GOT.foreign
     only). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg send_control_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_wake_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import session_lost_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_personality_from_name_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require diginet_announce_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import on_announce_cg OnannCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TNeed TSess0 TSess TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TNotifyFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require codec_cells.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TNeed.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
Module CC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.codec_cells.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Local Abbreviation segs := tfibsegs.
Variable B : asyms.
Variable MT : ameter_ops.

(* ------------------------------------------------------------------ *)
(* 1. The written range onann_wr lies in G                             *)
(* ------------------------------------------------------------------ *)

(* A field of a TMAP_A row's payload is a range of G. *)
Lemma onann_fld_G : forall o bs sz A n a, In (o, bs, sz) TMAP_A -> o <= A -> A + n <= o + sz ->
  twa_fld o bs A n a -> inG TG.G_HARNESS a.
Proof.
  intros o bs sz A n a Hin H1 H2 H. unfold inG. apply Exists_exists. exists (bs, sz).
  split; [exact (TMAP_A_in_G o bs sz Hin) | unfold in_zr, twa_fld in *; cbn [fst snd]; lia].
Qed.

(* A field of g_s, GOT or M. *)
Lemma onann_gs_G : forall A n a, TW.OFF_g_s <= A -> A + n <= TW.OFF_g_s + TW.SZ_g_s ->
  twa_fld TW.OFF_g_s TA_g_s A n a -> inG TG.G_HARNESS a.
Proof. intros A n a H1 H2 H. exact (onann_fld_G _ _ _ A n a TMAP_A_g_s H1 H2 H). Qed.
Lemma onann_got_G : forall A n a, TW.OFF_GOT <= A -> A + n <= TW.OFF_GOT + TW.SZ_GOT ->
  twa_fld TW.OFF_GOT TA_GOT A n a -> inG TG.G_HARNESS a.
Proof. intros A n a H1 H2 H. exact (onann_fld_G _ _ _ A n a TMAP_A_GOT H1 H2 H). Qed.
Lemma onann_m_G : forall A n a, TW.OFF_M <= A -> A + n <= TW.OFF_M + TW.SZ_M ->
  twa_fld TW.OFF_M TA_M A n a -> inG TG.G_HARNESS a.
Proof. intros A n a H1 H2 H. exact (onann_fld_G _ _ _ A n a TMAP_A_M H1 H2 H). Qed.

(* A closed comparison of two world offsets, decided. *)
Local Ltac onann_cl := apply Z.leb_le; reflexivity.
Local Ltac onann_gs H := refine (onann_gs_G _ _ _ _ _ H); onann_cl.
Local Ltac onann_got H := refine (onann_got_G _ _ _ _ _ H); onann_cl.
Local Ltac onann_m H := refine (onann_m_G _ _ _ _ _ H); onann_cl.

Lemma onann_ntc_wr_G : forall X (n : TI.ntc) a, notice_wr X n a -> inG TG.G_HARNESS a.
Proof.
  intros X n a H. unfold notice_wr in H.
  destruct H as [(_ & [(Hg & H) | H]) | [(_ & H) | [(_ & H) | [(_ & H) | [(_ & H) | (_ & H)]]]]].
  - refine (onann_got_G _ _ a _ _ H);
      unfold TW.A_GOT_t_state, TW.GOT_t_ESZ, TW.OFF_GOT, TW.SZ_GOT, TC.TRANS_MAX in *; lia.
  - onann_got H.
  - onann_got H.
  - onann_m H.
  - onann_got H.
  - onann_got H.
  - onann_got H.
Qed.

Lemma onann_iosend_wr_G : forall n a, iosend_wr n a -> inG TG.G_HARNESS a.
Proof.
  intros n a H. unfold iosend_wr in H.
  destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[(s & Hs & H)|[H|H]]]]]]]]]]]]]]]]]].
  - refine (onann_fld_G _ _ _ _ _ _ TMAP_A_g_fail_next _ _ H); onann_cl.
  - onann_got H.
  - onann_got H.
  - onann_got H.
  - refine (onann_fld_G _ _ _ _ _ _ TMAP_A_g_last_counter _ _ H); onann_cl.
  - onann_m H.
  - onann_m H.
  - onann_m H.
  - onann_m H.
  - onann_m H.
  - onann_m H.
  - onann_m H.
  - onann_m H.
  - onann_m H.
  - onann_m H.
  - refine (onann_m_G _ _ a _ _ H); unfold TW.A_M_fly_frame, TW.OFF_M, TW.SZ_M, TC.SPEC_MAX_FRAME; lia.
  - refine (onann_fld_G _ _ _ _ _ _ TMAP_A_g_cmd _ _ H);
      unfold TW.A_Cmd_st, TW.OFF_g_cmd, TW.SZ_g_cmd, TC.CMDS_MAX in *; lia.
  - refine (onann_fld_G _ _ _ _ _ _ TMAP_A_g_q _ _ H); onann_cl.
  - refine (onann_fld_G _ _ _ _ _ _ TMAP_A_g_nq _ _ H); onann_cl.
Qed.

Lemma onann_wake_wr_G : forall X a, wake_wr X a -> inG TG.G_HARNESS a.
Proof.
  intros X a H. unfold wake_wr in H.
  destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|(_ & [H|H])]]]]]]]]]]]]].
  1-12: onann_gs H.
  - exact (onann_iosend_wr_G _ a H).
  - onann_gs H.
  - exact (onann_ntc_wr_G _ _ a H).
Qed.

Lemma onann_slost_wr_G : forall X why a, slost_wr X why a -> inG TG.G_HARNESS a.
Proof.
  intros X why a H. unfold slost_wr in H.
  destruct H as [H | [H | (_ & [H | H])]]; [onann_gs H | onann_gs H | onann_gs H | exact (onann_ntc_wr_G _ _ a H)].
Qed.

Lemma onann_mo_wr_G : forall X a, maybeon_wr X a -> inG TG.G_HARNESS a.
Proof.
  intros X a H. unfold maybeon_wr in H.
  destruct H as (_ & [H | (_ & [H | H])]); [onann_gs H | onann_gs H | exact (onann_ntc_wr_G _ _ a H)].
Qed.

(* Every byte on_announce may store is a byte of G. *)
Lemma onann_wr_G : forall (Bw b : list byte) (a : Z), onann_wr Bw b a -> inG TG.G_HARNESS a.
Proof.
  intros Bw b a H. unfold onann_wr in H.
  destruct H as [H|[H|[H|[H|[H|[(Bx & H)|[H|[H|[H|H]]]]]]]]].
  - onann_gs H.
  - onann_gs H.
  - exact (onann_ntc_wr_G _ _ a H).
  - onann_gs H.
  - exact (onann_slost_wr_G _ _ a H).
  - exact (onann_wake_wr_G _ a H).
  - onann_gs H.
  - exact (onann_mo_wr_G _ a H).
  - exact (onann_ntc_wr_G _ _ a H).
  - exact (onann_slost_wr_G _ _ a H).
Qed.

(* ... so it lies in G's hull, below kLowMemEnd and below every shadow byte. *)
Lemma onann_wr_lowmem : forall (Bw b : list byte) (a : Z), onann_wr Bw b a ->
  TG.G_HARNESS_LO <= a < TG.G_HARNESS_HI /\ a < kLowMemEnd /\ (forall x, 0 <= x -> a < shadow_addr x).
Proof.
  intros Bw b a H. pose proof (inG_G_HARNESS_hull a (onann_wr_G Bw b a H)) as Gh.
  split; [exact Gh|]. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Gh.
  split; [unfold kLowMemEnd; lia|].
  intros x Hx. pose proof (Z.div_pos x 8 Hx ltac:(lia)). unfold shadow_addr, SHADOW_OFF. lia.
Qed.

(* ... and off every live side-stack frame and its shadow bytes. *)
Lemma onann_wr_nframe : AR_laws segs B ->
  forall ly S (W : world segs) mem md cid pos (Bw b : list byte) (a : Z),
  @AR rc segs B ly S W mem md -> In (cid, pos) (frames S) -> onann_wr Bw b a ->
  ~ (frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid) /\
  ~ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8).
Proof.
  intros LAWS ly S W mem md cid pos Bw b a HAR Hin H.
  pose proof (onann_wr_G Bw b a H) as HG.
  destruct (onann_wr_lowmem Bw b a H) as (_ & _ & Hsh).
  destruct (frames_bounds segs B LAWS ly S W mem md cid pos HAR Hin) as (F1 & _ & _).
  pose proof (Hsh (frame_addr ly cid pos) ltac:(lia)) as Hs0.
  split.
  - intro Hr. exact (frm_img segs B LAWS ly S W mem md cid pos a HAR Hin Hr (trans_g_img a HG)).
  - intro Hs. unfold in_zr in Hs. cbn [fst snd] in Hs. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The callees' written ranges inside onann_wr                      *)
(* ------------------------------------------------------------------ *)

(* A notice of kind N_DESK stores GOT.desk only, N_FOREIGN GOT.foreign only, at any world. *)
Lemma onann_ntc_desk_wr : forall X (n : TI.ntc) a, TI.n_kind n = TC.N_DESK -> notice_wr X n a ->
  twa_fld TW.OFF_GOT TA_GOT TW.A_GOT_desk 4 a.
Proof.
  intros X n a K H. unfold notice_wr in H. rewrite K in H.
  destruct H as [(E & _) | [(E & _) | [(E & _) | [(_ & H) | [(E & _) | (E & _)]]]]];
    try (unfold TC.N_STATE, TC.N_ACKED, TC.N_ACK_LOST, TC.N_DESK, TC.N_DATA, TC.N_FOREIGN in E; discriminate E).
  exact H.
Qed.

Lemma onann_ntc_fg_wr : forall X (n : TI.ntc) a, TI.n_kind n = TC.N_FOREIGN -> notice_wr X n a ->
  twa_fld TW.OFF_GOT TA_GOT TW.A_GOT_foreign 4 a.
Proof.
  intros X n a K H. unfold notice_wr in H. rewrite K in H.
  destruct H as [(E & _) | [(E & _) | [(E & _) | [(E & _) | [(E & _) | (_ & H)]]]]];
    try (unfold TC.N_STATE, TC.N_ACKED, TC.N_ACK_LOST, TC.N_DESK, TC.N_DATA, TC.N_FOREIGN in E; discriminate E).
  exact H.
Qed.

(* An N_STATE notice's stores depend on the world through GOT.n only. *)
Lemma onann_ntc_state_wr : forall X Y (n m : TI.ntc) a, TI.n_kind n = TC.N_STATE -> TI.n_kind m = TC.N_STATE ->
  TW.GOT_n X = TW.GOT_n Y -> notice_wr X n a -> notice_wr Y m a.
Proof.
  intros X Y n m a Kn Km Eg H. unfold notice_wr in H |- *. rewrite Kn in H. rewrite Km, <- Eg.
  destruct H as [(_ & H) | [(E & _) | [(E & _) | [(E & _) | [(E & _) | (E & _)]]]]].
  - left. split; [reflexivity | exact H].
  - unfold TC.N_STATE, TC.N_ACKED in E. discriminate E.
  - unfold TC.N_STATE, TC.N_ACK_LOST in E. discriminate E.
  - unfold TC.N_STATE, TC.N_DESK in E. discriminate E.
  - unfold TC.N_STATE, TC.N_DATA in E. discriminate E.
  - unfold TC.N_STATE, TC.N_FOREIGN in E. discriminate E.
Qed.

(* The desk notice's stores (at any world X, any notice world Y). *)
Lemma onann_wr_dntc : forall X Y (Bw b : list byte) a,
  notice_wr X (onann_dntc timg_A Y b) a -> onann_wr Bw b a.
Proof.
  intros X Y Bw b a H. pose proof (onann_ntc_desk_wr X (onann_dntc timg_A Y b) a eq_refl H) as Hd.
  unfold onann_wr. right; right; left. unfold notice_wr. right; right; right; left.
  split; [reflexivity | exact Hd].
Qed.

(* The foreign notice's stores (at any world X, any notice world Y). *)
Lemma onann_wr_fntc : forall X Y (Bw b : list byte) a,
  notice_wr X (onann_fntc Y b) a -> onann_wr Bw b a.
Proof.
  intros X Y Bw b a H. pose proof (onann_ntc_fg_wr X (onann_fntc Y b) a eq_refl H) as Hd.
  unfold onann_wr. do 8 right. left. unfold notice_wr. do 5 right.
  split; [reflexivity | exact Hd].
Qed.

(* diginet_session_wake's stores, at any world. *)
Lemma onann_wr_wake : forall Bx (Bw b : list byte) a, wake_wr Bx a -> onann_wr Bw b a.
Proof.
  intros Bx Bw b a H. unfold onann_wr. do 5 right. left. exists Bx. exact H.
Qed.

(* The worlds' lengths and the reads the inlined session_lost and maybe_online's written ranges depend on. *)
Lemma onann_w1_len : forall (I : TI.timg) (Bw b : list byte), length Bw = Z.to_nat TW.W_LEN ->
  length (onann_w1 I Bw b) = Z.to_nat TW.W_LEN.
Proof.
  intros I Bw b L. unfold onann_w1. destruct (TN.diginet_personality_from_name (onann_name b)); [|exact L].
  unfold TW.set_S_personality. apply len_upd_W; [exact L | wnum | wnum].
Qed.

Lemma onann_sl_state : forall X, length X = Z.to_nat TW.W_LEN -> TW.S_state (slost_w1 X) = TW.S_state X.
Proof.
  intros X L. unfold slost_w1, TW.set_S_desk_counter_valid, TW.set_S_inflight, TW.S_state.
  rewrite !rd32_upd_W by wside. reflexivity.
Qed.

Lemma onann_sl_gotn : forall X, length X = Z.to_nat TW.W_LEN -> TW.GOT_n (slost_w2 X) = TW.GOT_n X.
Proof.
  intros X L. unfold slost_w2, slost_w1, TW.set_S_state, TW.set_S_desk_counter_valid, TW.set_S_inflight, TW.GOT_n.
  rewrite !rd32_upd_W by wside. reflexivity.
Qed.

(* An inlined session_lost copy's stores (at a world Bx with Bw's state and GOT.n, any reason) are the first
   copy's at Bw. *)
Lemma onann_wr_slost : forall (Bw b Bx : list byte) why a,
  length Bx = Z.to_nat TW.W_LEN -> length Bw = Z.to_nat TW.W_LEN ->
  TW.GOT_n Bx = TW.GOT_n Bw -> TW.S_state Bx = TW.S_state Bw ->
  slost_wr Bx why a -> onann_wr Bw b a.
Proof.
  intros Bw b Bx why a Lx Lw Eg Es H.
  assert (Es1 : TW.S_state (slost_w1 Bx) = TW.S_state (slost_w1 Bw))
    by (rewrite (onann_sl_state Bx Lx), (onann_sl_state Bw Lw); exact Es).
  assert (Eg2 : TW.GOT_n (slost_w2 Bx) = TW.GOT_n (slost_w2 Bw))
    by (rewrite (onann_sl_gotn Bx Lx), (onann_sl_gotn Bw Lw); exact Eg).
  unfold onann_wr. do 4 right. left.
  unfold slost_wr in H |- *.
  destruct H as [H | [H | (Hne & [H | H])]].
  - left. exact H.
  - right. left. exact H.
  - right. right. split; [rewrite <- Es1; exact Hne | left; exact H].
  - right. right. split; [rewrite <- Es1; exact Hne | right].
    exact (onann_ntc_state_wr (slost_w2 Bx) (slost_w2 Bw) (slost_ntc Bx why)
      (slost_ntc Bw TS0.DIGINET_R_DESK_OFFLINE) a eq_refl eq_refl Eg2 H).
Qed.

Lemma onann_mo_w1_state : forall X, length X = Z.to_nat TW.W_LEN -> TW.S_state (maybeon_w1 X) = TW.S_state X.
Proof.
  intros X L. unfold maybeon_w1, TW.set_S_next_keepalive_us, TW.S_state.
  rewrite rd32_upd_W by wside. reflexivity.
Qed.

Lemma onann_mo_w2_gotn : forall X, length X = Z.to_nat TW.W_LEN -> TW.GOT_n (maybeon_w2 X) = TW.GOT_n X.
Proof.
  intros X L. unfold maybeon_w2, maybeon_w1, TW.set_S_state, TW.set_S_next_keepalive_us, TW.GOT_n.
  rewrite !rd32_upd_W by wside. reflexivity.
Qed.

(* maybe_online's stores at a world are its stores at the world before a store of GOT.desk. *)
Lemma onann_mo_wr_desk : forall Y d a, length Y = Z.to_nat TW.W_LEN ->
  maybeon_wr (TW.set_GOT_desk Y d) a -> maybeon_wr Y a.
Proof.
  intros Y d a L H.
  assert (L2 : length (TW.set_GOT_desk Y d) = Z.to_nat TW.W_LEN)
    by (unfold TW.set_GOT_desk; apply len_upd_W; [exact L | wnum | wnum]).
  assert (Ego : maybeon_go (TW.set_GOT_desk Y d) = maybeon_go Y)
    by (unfold maybeon_go, TW.S_state, TW.S_wake_acked, TW.S_e1_named_us, TW.set_GOT_desk;
        rewrite !rd32_upd_W by wside; reflexivity).
  assert (Es : TW.S_state (TW.set_GOT_desk Y d) = TW.S_state Y)
    by (unfold TW.S_state, TW.set_GOT_desk; rewrite rd32_upd_W by wside; reflexivity).
  assert (Eg : TW.GOT_n (maybeon_w2 (TW.set_GOT_desk Y d)) = TW.GOT_n (maybeon_w2 Y))
    by (rewrite (onann_mo_w2_gotn _ L2), (onann_mo_w2_gotn Y L);
        unfold TW.GOT_n, TW.set_GOT_desk; rewrite rd32_upd_W by wside; reflexivity).
  unfold maybeon_wr in H |- *. destruct H as (Hgo & H). rewrite Ego in Hgo. split; [exact Hgo|].
  rewrite (onann_mo_w1_state Y L). rewrite (onann_mo_w1_state _ L2), Es in H.
  destruct H as [H | (Hne & [H | H])].
  - left. exact H.
  - right. split; [exact Hne | left; exact H].
  - right. split; [exact Hne | right].
    exact (onann_ntc_state_wr (maybeon_w2 (TW.set_GOT_desk Y d)) (maybeon_w2 Y) (maybeon_ntc (TW.set_GOT_desk Y d))
      (maybeon_ntc Y) a eq_refl eq_refl Eg H).
Qed.

(* The stores of :213 and :214 commute with the desk notice's store of GOT.desk. *)
Lemma onann_mo_comm : forall W1 d, length W1 = Z.to_nat TW.W_LEN ->
  TW.set_S_e1_named_us (TW.set_S_foreign (TW.set_GOT_desk W1 d) 0) 1 =
  TW.set_GOT_desk (TW.set_S_e1_named_us (TW.set_S_foreign W1 0) 1) d.
Proof.
  intros W1 d L. unfold TW.set_S_e1_named_us, TW.set_S_foreign, TW.set_GOT_desk.
  rewrite (upd_comm_W W1 (TW.put 4 d) (TW.put 4 0) TW.A_GOT_desk TW.A_S_foreign) by wside.
  rewrite (upd_comm_W (TW.upd W1 TW.A_S_foreign (TW.put 4 0)) (TW.put 4 d) (TW.put 4 1) TW.A_GOT_desk
    TW.A_S_e1_named_us) by wside.
  reflexivity.
Qed.

(* maybe_online's stores at the world of :213-214 after the desk notice B2 = set_GOT_desk (onann_w1 ..) d. *)
Lemma onann_wr_mo : forall (Bw b : list byte) d a, length Bw = Z.to_nat TW.W_LEN ->
  maybeon_wr (TW.set_S_e1_named_us (TW.set_S_foreign (TW.set_GOT_desk (onann_w1 timg_A Bw b) d) 0) 1) a ->
  onann_wr Bw b a.
Proof.
  intros Bw b d a L H.
  pose proof (onann_w1_len timg_A Bw b L) as L1.
  rewrite (onann_mo_comm _ d L1) in H.
  assert (L2 : length (TW.set_S_e1_named_us (TW.set_S_foreign (onann_w1 timg_A Bw b) 0) 1) = Z.to_nat TW.W_LEN)
    by (unfold TW.set_S_e1_named_us, TW.set_S_foreign; apply len_upd_W; [apply len_upd_W; [exact L1 | wnum | wnum]
        | wnum | wnum]).
  pose proof (onann_mo_wr_desk _ d a L2 H) as H2.
  unfold onann_wr. do 7 right. left. exact H2.
Qed.

(* The TF parts of the callees' apart clauses, from onann_apart and an inclusion into onann_wr. *)
Lemma onann_apart_ntc : forall (TF : option TI.tframe) (Bw b : list byte) (E : Z -> Prop),
  onann_apart TF Bw b -> (forall x, E x -> onann_wr Bw b x) ->
  forall x, E x ->
    forall fr, TF = Some fr -> ~ (TI.tf_addr fr <= x < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr))).
Proof. intros TF Bw b E Hap Hs x Hx. exact (Hap x (Hs x Hx)). Qed.

Lemma onann_apart_wake : forall (TF : option TI.tframe) (Bw b Bx : list byte),
  onann_apart TF Bw b -> wake_apart TF Bx.
Proof. intros TF Bw b Bx Hap x Hx. exact (Hap x (onann_wr_wake Bx Bw b x Hx)). Qed.

Lemma onann_apart_mo : forall (TF : option TI.tframe) (Bw b : list byte) d, length Bw = Z.to_nat TW.W_LEN ->
  onann_apart TF Bw b ->
  maybeon_apart TF (TW.set_S_e1_named_us (TW.set_S_foreign (TW.set_GOT_desk (onann_w1 timg_A Bw b) d) 0) 1).
Proof. intros TF Bw b d L Hap x Hx. exact (Hap x (onann_wr_mo Bw b d x L Hx)). Qed.

Lemma onann_apart_slost : forall (TF : option TI.tframe) (Bw b Bx : list byte) why,
  length Bx = Z.to_nat TW.W_LEN -> length Bw = Z.to_nat TW.W_LEN ->
  TW.GOT_n Bx = TW.GOT_n Bw -> TW.S_state Bx = TW.S_state Bw ->
  onann_apart TF Bw b -> slost_apart TF Bx why.
Proof.
  intros TF Bw b Bx why Lx Lw Eg Es Hap x Hx. exact (Hap x (onann_wr_slost Bw b Bx why x Lx Lw Eg Es Hx)).
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The model: the desk and foreign notices                          *)
(* ------------------------------------------------------------------ *)

(* check_state_desk returns its world. *)
Lemma onann_desk_same : forall (I : TI.timg) (F : option TI.tframe) X (n : TI.ntc) Y u,
  TC.check_state_desk_m I F X n = Some (Y, u) -> Y = X.
Proof.
  intros I F X n Y u. destruct u. unfold TC.check_state_desk_m.
  repeat (cbv beta iota zeta; match goal with |- context [match ?c with _ => _ end] => destruct c end);
    intros H; cbv beta iota zeta in H; try discriminate H; symmetry; exact (onann_some_inv _ _ H).
Qed.

(* An N_DESK notice changes GOT.desk only. *)
Lemma onann_notice_desk : forall (I : TI.timg) (F : option TI.tframe) Bx (n : TI.ntc) B2,
  TI.n_kind n = TC.N_DESK -> TC.notice_m I F Bx n = Some (B2, tt) -> exists d, B2 = TW.set_GOT_desk Bx d.
Proof.
  intros I F Bx n B2 K H. unfold TC.notice_m in H. rewrite K in H.
  cbn [Z.eqb TC.N_STATE TC.N_ACKED TC.N_ACK_LOST TC.N_DESK Pos.eqb] in H.
  destruct (TC.int_inc (TW.GOT_desk Bx)) as [d|]; [|discriminate H].
  exists d. exact (onann_desk_same I F (TW.set_GOT_desk Bx d) n B2 tt H).
Qed.

(* An N_FOREIGN notice changes GOT.foreign only. *)
Lemma onann_notice_fg : forall (I : TI.timg) (F : option TI.tframe) Bx (n : TI.ntc) B3,
  TI.n_kind n = TC.N_FOREIGN -> TC.notice_m I F Bx n = Some (B3, tt) -> exists d, B3 = TW.set_GOT_foreign Bx d.
Proof.
  intros I F Bx n B3 K H. unfold TC.notice_m in H. rewrite K in H.
  cbn [Z.eqb TC.N_STATE TC.N_ACKED TC.N_ACK_LOST TC.N_DESK TC.N_DATA TC.N_FOREIGN Pos.eqb] in H.
  destruct (TC.int_inc (TW.GOT_foreign Bx)) as [d|]; [|discriminate H].
  cbv beta iota in H. exists d. symmetry. exact (onann_some_inv _ _ H).
Qed.

(* The desk notice's call_notify returns set_GOT_desk of its world. *)
Lemma onann_dn_world : forall (Fr : option TI.tframe) (Bx b B2 : list byte),
  TSS.call_notify timg_A Fr Bx (onann_dntc timg_A Bx b) = Some (B2, tt) -> exists d, B2 = TW.set_GOT_desk Bx d.
Proof.
  intros Fr Bx b B2 H. unfold TSS.call_notify in H.
  destruct (TW.S_notify Bx =? TI.ti_notice timg_A); [|discriminate H].
  exact (onann_notice_desk timg_A Fr Bx (onann_dntc timg_A Bx b) B2 eq_refl H).
Qed.

(* The foreign notice's call_notify returns set_GOT_foreign of its world. *)
Lemma onann_fg_world : forall (Fr : option TI.tframe) (Bf b B3 : list byte),
  TSS.call_notify timg_A Fr Bf (onann_fntc Bf b) = Some (B3, tt) -> exists d, B3 = TW.set_GOT_foreign Bf d.
Proof.
  intros Fr Bf b B3 H. unfold TSS.call_notify in H.
  destruct (TW.S_notify Bf =? TI.ti_notice timg_A); [|discriminate H].
  exact (onann_notice_fg timg_A Fr Bf (onann_fntc Bf b) B3 eq_refl H).
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The cut state: AR, the layout, the own frame                     *)
(* ------------------------------------------------------------------ *)

(* What every piece takes from onann_fix and onann_cur (the shape of SlostNtc.v:552-595, SlostRel.v:231-266): AR at
   the entry and at the cut state; the cut layout's stack bounds, frame and flag addresses are the entry's; the own
   frame (ONANN_CID, pos) is live at F, its 1024 bytes and 128 shadow bytes present and not owned, off G, in
   application memory below alloc_ceiling and the stack window; its flag byte present, owned, off the frame and its
   shadow. The state variables are implicit: `onann_cur_ar B MT LAWS HFIX HCUR`. *)
Lemma onann_cur_ar :
  forall {STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
          ly2 S2 W2 mem2 md2 e},
  AR_laws segs B ->
  onann_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
  onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 e ->
  @AR rc segs B lyc Sc W memc mdc /\ @AR rc segs B ly2 S2 W2 mem2 md2 /\
  ly_stk_lo ly2 = ly_stk_lo lyc /\ ly_stk_hi ly2 = ly_stk_hi lyc /\
  (forall c p, frame_addr ly2 c p = frame_addr lyc c p) /\ (forall c p, flag_addr ly2 c p = flag_addr lyc c p) /\
  In (ONANN_CID, pos) (frames S2) /\ frame_addr ly2 ONANN_CID pos = F /\
  (forall a, F <= a < F + 1024 -> apresent (w_H W2) mem2 a /\ ~ aowned B ly2 S2 a) /\
  (forall i, 0 <= i < 128 ->
     apresent (w_H W2) mem2 (SHADOW_OFF + F / 8 + i) /\ ~ aowned B ly2 S2 (SHADOW_OFF + F / 8 + i)) /\
  (forall a, F <= a < F + 1024 -> ~ inG TG.G_HARNESS a) /\
  4096 <= F /\ F mod 64 = 0 /\ F + 1024 <= alloc_ceiling /\ in_app F 1024 /\
  alloc_ceiling <= ly_stk_lo lyc /\ ly_stk_lo lyc <= spZ regs - ONANN_STK /\ spZ regs <= ly_stk_hi lyc /\
  ly_stk_hi lyc <= 2 ^ 47 /\
  apresent (w_H W2) mem2 (flag_addr lyc ONANN_CID pos) /\ aowned B ly2 S2 (flag_addr lyc ONANN_CID pos) /\
  4096 <= flag_addr lyc ONANN_CID pos < alloc_ceiling /\
  (flag_addr lyc ONANN_CID pos < F \/ F + 1024 <= flag_addr lyc ONANN_CID pos) /\
  (flag_addr lyc ONANN_CID pos < SHADOW_OFF + F / 8 \/ SHADOW_OFF + F / 8 + 128 <= flag_addr lyc ONANN_CID pos).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
    ly2 S2 W2 mem2 md2 e LAWS HFIX HCUR.
  destruct HFIX as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & Hlo & Hhi & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & EF & HF0 & HF64 & HFc & HFapp).
  destruct HCUR as (HJ1 & _ & Hfrs & _ & HlyF & _).
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
  pose proof HJ0 as (_ & _ & (memS & HJi & _) & _).
  destruct HJi as (_ & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  destruct Hlyle as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ELO & EHI & _).
  pose proof HJ1 as (_ & _ & (memS2 & HJi2 & _) & _).
  destruct HJi2 as (_ & Hlyle2 & _).
  destruct Hlyle2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ELO2 & EHI2 & _).
  clear HJ0 HJ1.
  assert (EFA : forall c p, frame_addr ly2 c p = frame_addr lyc c p)
    by (intros c p; unfold frame_addr; rewrite HlyF; reflexivity).
  assert (EFL : forall c p, flag_addr ly2 c p = flag_addr lyc c p)
    by (intros c p; unfold flag_addr; rewrite HlyF; reflexivity).
  assert (Hin : In (ONANN_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
  assert (EF2 : frame_addr ly2 ONANN_CID pos = F) by (rewrite EFA; symmetry; exact EF).
  destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 ONANN_CID pos HAR2 Hin) as (_ & _ & HFb & HFsh).
  rewrite EF2 in HFb, HFsh.
  change (fs_frame_bytes ONANN_CID) with 1024 in HFb.
  change (fs_frame_bytes ONANN_CID / 8) with 128 in HFsh.
  assert (ESH : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity.
  rewrite ESH in HFsh.
  destruct (al_flag _ _ LAWS ly2 S2 W2 mem2 md2 ONANN_CID pos HAR2 Hin) as (HFLp & HFLo & HFLapp & HFLc).
  rewrite EFL in HFLp, HFLo, HFLapp, HFLc.
  destruct HFLapp as [HFL4096 _].
  assert (HFLF : flag_addr lyc ONANN_CID pos < F \/ F + 1024 <= flag_addr lyc ONANN_CID pos).
  { destruct (Z_lt_le_dec (flag_addr lyc ONANN_CID pos) F) as [h|h]; [left; exact h|].
    destruct (Z_lt_le_dec (flag_addr lyc ONANN_CID pos) (F + 1024)) as [h2|h2]; [|right; exact h2].
    exfalso. exact (proj2 (HFb _ (conj h h2)) HFLo). }
  assert (HFLS : flag_addr lyc ONANN_CID pos < SHADOW_OFF + F / 8 \/
                 SHADOW_OFF + F / 8 + 128 <= flag_addr lyc ONANN_CID pos).
  { destruct (Z_lt_le_dec (flag_addr lyc ONANN_CID pos) (SHADOW_OFF + F / 8)) as [h|h]; [left; exact h|].
    destruct (Z_lt_le_dec (flag_addr lyc ONANN_CID pos) (SHADOW_OFF + F / 8 + 128)) as [h2|h2]; [|right; exact h2].
    exfalso. pose proof (proj2 (HFsh (flag_addr lyc ONANN_CID pos - (SHADOW_OFF + F / 8)) ltac:(lia))) as Hno.
    replace (SHADOW_OFF + F / 8 + (flag_addr lyc ONANN_CID pos - (SHADOW_OFF + F / 8)))
      with (flag_addr lyc ONANN_CID pos) in Hno by lia.
    exact (Hno HFLo). }
  assert (HFG : forall a, F <= a < F + 1024 -> ~ inG TG.G_HARNESS a).
  { intros a Ha HG. apply (frm_img segs B LAWS ly2 S2 W2 mem2 md2 ONANN_CID pos a HAR2 Hin).
    - rewrite EF2. change (fs_frame_bytes ONANN_CID) with 1024. lia.
    - exact (trans_g_img a HG). }
  unfold ONANN_FBYTES in HFc, HFapp.
  split; [exact HARc|]. split; [exact HAR2|].
  split; [rewrite ELO2, ELO; reflexivity|]. split; [rewrite EHI2, EHI; reflexivity|].
  split; [exact EFA|]. split; [exact EFL|]. split; [exact Hin|]. split; [exact EF2|].
  split; [exact HFb|]. split; [exact HFsh|]. split; [exact HFG|].
  split; [exact HF0|]. split; [exact HF64|]. split; [exact HFc|]. split; [exact HFapp|].
  split; [rewrite ELO; exact Hceil|].
  split; [rewrite ELO; lia|].
  split; [rewrite EHI; lia|].
  split; [rewrite EHI; exact H47|].
  split; [exact HFLp|]. split; [exact HFLo|]. split; [split; [exact HFL4096 | exact HFLc]|].
  split; [exact HFLF | exact HFLS].
Qed.

(* ------------------------------------------------------------------ *)
(* 5. Ranges placed at the entry, at the cut state                     *)
(* ------------------------------------------------------------------ *)

(* trans_rom_view_rd at the cut memory: a TRANS_RO_RD byte is an image byte below G, not owned, not errno, so
   acall_kept_g's image clause keeps it (SlostNtc.v:893-897). *)
Lemma onann_rom_call : trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall lyc Sc (W : world segs) memc (W2 : world segs) mem2 slo shi (E : Z -> Prop),
  trans_rom_view_rd W memc ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem2 slo shi E ->
  trans_rom_view_rd W2 mem2.
Proof.
  intros HRU HRE lyc Sc W memc W2 mem2 slo shi E Hrom (_ & _ & K3 & _) a Ha.
  rewrite <- (Hrom a Ha).
  destruct (trans_ro_rd_scoped B HRU HRE a Ha) as [Ho He].
  apply (K3 a (trans_ro_img a Ha)); [|exact Ho | exact He].
  intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ha) as Rb.
  unfold TG.G_HARNESS_LO in Gh. lia.
Qed.

(* A range [q, q + n) placed by trans_src_ok at the entry, off G and outside the window [slo, shi), with the walk's
   written range E inside G: its bytes are the entry's and it is placed at the cut state (the own frame on top of
   the entry's frames, the same blocks, frame addresses and stack bounds). TransportGNotice.v trans_src_ok_kept_gx's
   form, for a written range inside G. *)
Lemma onann_src_kept : AR_laws segs B -> trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 pos slo shi (E : Z -> Prop) q n,
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  frames S2 = (ONANN_CID, pos) :: frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  (forall c p, frame_addr ly2 c p = frame_addr lyc c p) ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem2 slo shi E ->
  (forall a, E a -> inG TG.G_HARNESS a) ->
  (forall a, q <= a < q + n -> ~ inG TG.G_HARNESS a) ->
  (q + n <= slo \/ shi <= q) ->
  trans_src_ok B lyc Sc W memc q n -> 0 <= n ->
  trans_src_ok B ly2 S2 W2 mem2 q n /\
  (forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
Proof.
  intros LAWS HRU HRE lyc Sc W memc mdc ly2 S2 W2 mem2 md2 pos slo shi E q n HAR HAR2 Hfr Hperm Hfa Elo Ehi
    (K1 & K2 & K3 & K4 & _) HEG HnG Hoff Hs Hn.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HnE : forall a, q <= a < q + n -> ~ E a) by (intros a Ha He; exact (HnG a Ha (HEG a He))).
  assert (KS : forall cid p s, In (cid, p) (frames Sc) ->
     in_zr s (shadow_addr (frame_addr lyc cid p), fs_frame_bytes cid / 8) ->
     aview segs (w_H W2) mem2 s = aview segs (w_H W) memc s).
  { intros cid p s Hin Hs'. apply (K4 cid p s Hin (or_intror Hs')). intro He.
    pose proof (inG_G_HARNESS_hull s (HEG s He)) as Gh.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid p HAR Hin) as (F1 & _ & _).
    pose proof (Z.div_pos (frame_addr lyc cid p) 8 ltac:(lia) ltac:(lia)).
    unfold in_zr in Hs'. cbn [fst snd] in Hs'.
    unfold shadow_addr, SHADOW_OFF in Hs'. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Gh. lia. }
  assert (KV : forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
  { intros a Ha. destruct Hs as [(bA & nA & Hin & B1 & B2) | (HL & _)].
    - destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn0).
      pose proof (req_size_pos nA (proj1 Hn0)) as [_ Hreq].
      replace a with (bA + (a - bA)) by lia.
      apply (K2 bA nA (a - bA) Hin ltac:(lia)). replace (bA + (a - bA)) with a by lia. exact (HnE a Ha).
    - destruct HL as [(cid & p & Hin & F1 & F2) | [(HG & _) | [(S1 & S3) | (HR & _)]]].
      + apply (K4 cid p a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact (HnE a Ha)].
      + exfalso. exact (HnG a Ha (HG a Ha)).
      + destruct (trans_stk_bounds B lyc Sc W memc mdc HAR) as [T1 T2].
        apply K1; [lia|]. destruct Hoff as [Ho|Ho]; lia.
      + pose proof (HR a Ha) as Ra. destruct (trans_ro_rd_scoped B HRU HRE a Ra) as [Ho He].
        exact (K3 a (trans_ro_img a Ra) (HnG a Ha) Ho He). }
  split; [|exact KV].
  assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
    by (intros bm Hbm; exact (Permutation_in _ (Permutation_sym Hperm) Hbm)).
  assert (Hf : forall f, In f (frames Sc) -> In f (frames S2)) by (intros f Hf; rewrite Hfr; right; exact Hf).
  destruct Hs as [(bA & nA & Hin & B1 & B2) | (HL & Hrd)].
  - left. exists bA, nA. split; [exact (Hbl _ Hin) | lia].
  - assert (Hrd2 : decode_rd_ok W2 mem2 q n).
    { destruct HL as [HF | [(_ & Hsh) | [(S1 & S3) | (_ & Hsh)]]].
      - exact (decode_rd_ok_fake_kept_ge0 B LAWS lyc Sc W W2 memc mem2 mdc q n HAR HF Hrd Hn KV KS).
      - destruct (Hsh ly2 S2 W2 mem2 md2 HAR2) as [Ha Hh]. exact (trans_rd_ok_sh W W2 memc mem2 q n Hrd KV Ha Hh).
      - destruct (stack_zshadow_ra_ge0 B ly2 S2 W2 mem2 md2 q n HAR2 Hn ltac:(rewrite Elo; lia)
                    ltac:(rewrite Ehi; lia)) as [Ha Hh].
        exact (trans_rd_ok_sh W W2 memc mem2 q n Hrd KV Ha Hh).
      - destruct (Hsh ly2 S2 W2 mem2 md2 HAR2) as [Ha Hh]. exact (trans_rd_ok_sh W W2 memc mem2 q n Hrd KV Ha Hh). }
    exact (trans_src_ok_inner B lyc Sc W memc ly2 S2 W2 mem2 q n Hbl Hf Hfa Elo Ehi Hrd2 (or_intror (conj HL Hrd))).
Qed.

(* The current heap frame TF at a call state of the walk (registers regsC, the callee's window
   [spZ regsC - K, spZ regsC) inside the call's window): trans_tframe_at by onann_src_kept (TF is off G,
   trans_tf_off_g; onann_wr lies in G). *)
Lemma onann_tf_call : AR_laws segs B -> trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 pos
    (regs regsC : bvmap 5 word) (K : Z) (TF : option TI.tframe) (Bw b : list byte),
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  frames S2 = (ONANN_CID, pos) :: frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  (forall c p, frame_addr ly2 c p = frame_addr lyc c p) ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem2 (spZ regs - ONANN_STK) (spZ regs) (onann_wr Bw b) ->
  trans_tf_off_g TF ->
  spZ regs - ONANN_STK <= spZ regsC - K -> spZ regsC <= spZ regs ->
  trans_tframe_at B lyc Sc W memc regs ONANN_STK TF ->
  trans_tframe_at B ly2 S2 W2 mem2 regsC K TF.
Proof.
  intros LAWS HRU HRE lyc Sc W memc mdc ly2 S2 W2 mem2 md2 pos regs regsC K TF Bw b HAR HAR2 Hfr Hperm Hfa Elo
    Ehi HK HTFo Hw1 Hw2 HT.
  destruct TF as [fr|]; [|exact I].
  destruct HT as (Ha0 & Hg8 & Hsrc & Hoff).
  assert (Hn0 : 0 <= Z.of_nat (length (TI.tf_bytes fr))) by lia.
  assert (HnG : forall a, TI.tf_addr fr <= a < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr)) ->
    ~ inG TG.G_HARNESS a) by (intros a Ha; exact (HTFo fr eq_refl a Ha)).
  destruct (onann_src_kept LAWS HRU HRE lyc Sc W memc mdc ly2 S2 W2 mem2 md2 pos (spZ regs - ONANN_STK) (spZ regs)
    (onann_wr Bw b) (TI.tf_addr fr) (Z.of_nat (length (TI.tf_bytes fr))) HAR HAR2 Hfr Hperm Hfa Elo Ehi HK
    (onann_wr_G Bw b) HnG Hoff Hsrc Hn0) as [Hs2 KV].
  split; [exact Ha0|]. split.
  { eapply garr8_frame; [exact Hg8|]. intros a Ha. rewrite length_map in Ha.
    apply (YCbq.mbyte_of_aview segs). apply KV. exact Ha. }
  split; [exact Hs2|]. unfold decode_off_win in *. destruct Hoff as [Ho|Ho]; [left | right]; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 6. The model: lengths, g_fail_next, the run invariants, the name    *)
(* ------------------------------------------------------------------ *)

(* A closed comparison of world offsets (the lengths of put n v first). *)
Local Ltac onann_c :=
  rewrite ?TWL.length_put;
  cbv beta delta [TW.W_LEN TW.OFF_g_s TW.SZ_g_s TW.OFF_GOT TW.SZ_GOT TW.A_S_state TW.A_GOT_n TW.A_S_personality
    TW.A_S_foreign TW.A_S_e1_named_us TW.A_S_stats_rx_ignored TW.A_GOT_desk TW.A_GOT_foreign TW.A_S_inflight
    TW.A_S_desk_counter_valid TW.A_GOT_t_state TW.A_GOT_t_old TW.A_GOT_t_reason];
  lia.

(* A store into g_s's or GOT's payload keeps onann_ri: M's fly fields lie below g_s, g_ncmd between g_s and GOT,
   and with the index bound g_ncmd <= CMDS_MAX every command slot read lies in g_cmd. *)
Lemma onann_ri_upd : forall X k v, length X = Z.to_nat TW.W_LEN ->
  (TW.OFF_g_s <= k /\ k + Z.of_nat (length v) <= TW.OFF_g_s + TW.SZ_g_s) \/
  (TW.OFF_GOT <= k /\ k + Z.of_nat (length v) <= TW.OFF_GOT + TW.SZ_GOT) ->
  onann_ri X -> onann_ri (TW.upd X k v).
Proof.
  intros X k v L Hr (R1 & R2 & R3).
  cbv beta delta [TW.OFF_g_s TW.SZ_g_s TW.OFF_GOT TW.SZ_GOT] in Hr.
  assert (H0 : 0 <= k) by lia.
  assert (HW : k + Z.of_nat (length v) <= TW.W_LEN) by (cbv beta delta [TW.W_LEN]; lia).
  assert (Encmd : TW.g_ncmd (TW.upd X k v) = TW.g_ncmd X).
  { unfold TW.g_ncmd. apply (rd_upd_W X v k TW.OFF_g_ncmd 4 L H0 HW); cbv beta delta [TW.OFF_g_ncmd]; lia. }
  split; [|split].
  - assert (E1 : TW.M_fly_on (TW.upd X k v) = TW.M_fly_on X).
    { unfold TW.M_fly_on. apply (rd32_upd_W X v k TW.A_M_fly_on L H0 HW); cbv beta delta [TW.A_M_fly_on TW.OFF_M]; lia. }
    assert (E2 : TW.M_fly_len (TW.upd X k v) = TW.M_fly_len X).
    { unfold TW.M_fly_len. apply (rd_upd_W X v k TW.A_M_fly_len 8 L H0 HW); cbv beta delta [TW.A_M_fly_len TW.OFF_M]; lia. }
    rewrite E1, E2. exact R1.
  - intros s Hs Hst. rewrite Encmd in Hs.
    assert (Hs2 : s < TC.CMDS_MAX) by lia.
    cbv beta delta [TC.CMDS_MAX] in Hs2.
    assert (E3 : TW.Cmd_st (TW.upd X k v) s = TW.Cmd_st X s).
    { unfold TW.Cmd_st. apply (rd32_upd_W X v k (TW.A_Cmd_st s) L H0 HW); cbv beta delta [TW.A_Cmd_st TW.OFF_g_cmd]; lia. }
    assert (E4 : TW.Cmd_len (TW.upd X k v) s = TW.Cmd_len X s).
    { unfold TW.Cmd_len. apply (rd_upd_W X v k (TW.A_Cmd_len s) 1 L H0 HW); cbv beta delta [TW.A_Cmd_len TW.OFF_g_cmd]; lia. }
    rewrite E4. rewrite E3 in Hst. exact (R2 s Hs Hst).
  - rewrite Encmd. exact R3.
Qed.

(* A store into g_s's or GOT's payload keeps g_fail_next and the world's length. *)
Lemma onann_gfn_upd : forall X k v, length X = Z.to_nat TW.W_LEN ->
  (TW.OFF_g_s <= k /\ k + Z.of_nat (length v) <= TW.OFF_g_s + TW.SZ_g_s) \/
  (TW.OFF_GOT <= k /\ k + Z.of_nat (length v) <= TW.OFF_GOT + TW.SZ_GOT) ->
  TW.g_fail_next (TW.upd X k v) = TW.g_fail_next X /\ length (TW.upd X k v) = Z.to_nat TW.W_LEN.
Proof.
  intros X k v L Hr.
  cbv beta delta [TW.OFF_g_s TW.SZ_g_s TW.OFF_GOT TW.SZ_GOT] in Hr.
  assert (H0 : 0 <= k) by lia.
  assert (HW : k + Z.of_nat (length v) <= TW.W_LEN) by (cbv beta delta [TW.W_LEN]; lia).
  split.
  - unfold TW.g_fail_next. apply (rd_upd_W X v k TW.OFF_g_fail_next 1 L H0 HW); cbv beta delta [TW.OFF_g_fail_next]; lia.
  - exact (len_upd_W X v k L H0 HW).
Qed.

(* The two, for a store into g_s and for a store into GOT. *)
Lemma onann_gs_upd : forall X k v, length X = Z.to_nat TW.W_LEN ->
  TW.OFF_g_s <= k -> k + Z.of_nat (length v) <= TW.OFF_g_s + TW.SZ_g_s ->
  length (TW.upd X k v) = Z.to_nat TW.W_LEN /\ TW.g_fail_next (TW.upd X k v) = TW.g_fail_next X /\
  (onann_ri X -> onann_ri (TW.upd X k v)).
Proof.
  intros X k v L H1 H2.
  destruct (onann_gfn_upd X k v L (or_introl (conj H1 H2))) as [G L1].
  split; [exact L1|]. split; [exact G | exact (onann_ri_upd X k v L (or_introl (conj H1 H2)))].
Qed.

Lemma onann_got_upd : forall X k v, length X = Z.to_nat TW.W_LEN ->
  TW.OFF_GOT <= k -> k + Z.of_nat (length v) <= TW.OFF_GOT + TW.SZ_GOT ->
  length (TW.upd X k v) = Z.to_nat TW.W_LEN /\ TW.g_fail_next (TW.upd X k v) = TW.g_fail_next X /\
  (onann_ri X -> onann_ri (TW.upd X k v)).
Proof.
  intros X k v L H1 H2.
  destruct (onann_gfn_upd X k v L (or_intror (conj H1 H2))) as [G L1].
  split; [exact L1|]. split; [exact G | exact (onann_ri_upd X k v L (or_intror (conj H1 H2)))].
Qed.

(* A store into g_s or GOT off g_s.state and GOT.n keeps the length, g_fail_next, onann_ri, S_state and GOT_n. *)
Lemma onann_upd_keep : forall X k w, length X = Z.to_nat TW.W_LEN ->
  (TW.OFF_g_s <= k /\ k + Z.of_nat (length w) <= TW.OFF_g_s + TW.SZ_g_s) \/
  (TW.OFF_GOT <= k /\ k + Z.of_nat (length w) <= TW.OFF_GOT + TW.SZ_GOT) ->
  (k + Z.of_nat (length w) <= TW.A_S_state \/ TW.A_S_state + 4 <= k) ->
  (k + Z.of_nat (length w) <= TW.A_GOT_n \/ TW.A_GOT_n + 4 <= k) ->
  length (TW.upd X k w) = Z.to_nat TW.W_LEN /\ TW.g_fail_next (TW.upd X k w) = TW.g_fail_next X /\
  (onann_ri X -> onann_ri (TW.upd X k w)) /\ TW.S_state (TW.upd X k w) = TW.S_state X /\
  TW.GOT_n (TW.upd X k w) = TW.GOT_n X.
Proof.
  intros X k w L Hr Hs Hg.
  destruct (onann_gfn_upd X k w L Hr) as [G1 L1].
  pose proof (onann_ri_upd X k w L Hr) as R1.
  cbv beta delta [TW.OFF_g_s TW.SZ_g_s TW.OFF_GOT TW.SZ_GOT] in Hr.
  assert (H0 : 0 <= k) by lia.
  assert (HW : k + Z.of_nat (length w) <= TW.W_LEN) by (cbv beta delta [TW.W_LEN]; lia).
  split; [exact L1|]. split; [exact G1|]. split; [exact R1|]. split.
  - unfold TW.S_state. apply (rd32_upd_W X w k TW.A_S_state L H0 HW); [cbv beta delta [TW.A_S_state TW.OFF_g_s]; lia|].
    destruct Hs as [Hs|Hs]; [right | left]; exact Hs.
  - unfold TW.GOT_n. apply (rd32_upd_W X w k TW.A_GOT_n L H0 HW); [cbv beta delta [TW.A_GOT_n TW.OFF_GOT]; lia|].
    destruct Hg as [Hg|Hg]; [right | left]; exact Hg.
Qed.

(* The world setters of on_announce's own stores and of the desk and foreign notices: the length, g_fail_next,
   onann_ri, S_state and GOT_n carry. *)
Lemma onann_set_keep : forall X v, length X = Z.to_nat TW.W_LEN ->
  forall Y, Y = TW.set_S_personality X v \/ Y = TW.set_S_foreign X v \/ Y = TW.set_S_e1_named_us X v \/
    Y = TW.set_S_stats_rx_ignored X v \/ Y = TW.set_GOT_desk X v \/ Y = TW.set_GOT_foreign X v ->
  length Y = Z.to_nat TW.W_LEN /\ TW.g_fail_next Y = TW.g_fail_next X /\ (onann_ri X -> onann_ri Y) /\
  TW.S_state Y = TW.S_state X /\ TW.GOT_n Y = TW.GOT_n X.
Proof.
  intros X v L Y HY.
  destruct HY as [-> | [-> | [-> | [-> | [-> | ->]]]]];
    [unfold TW.set_S_personality | unfold TW.set_S_foreign | unfold TW.set_S_e1_named_us |
     unfold TW.set_S_stats_rx_ignored | unfold TW.set_GOT_desk | unfold TW.set_GOT_foreign];
    (apply onann_upd_keep; [exact L | onann_c | onann_c | onann_c]).
Qed.

(* The world after the personality's store. *)
Lemma onann_w1_keep : forall (I : TI.timg) (Bw b : list byte), length Bw = Z.to_nat TW.W_LEN ->
  length (onann_w1 I Bw b) = Z.to_nat TW.W_LEN /\ TW.g_fail_next (onann_w1 I Bw b) = TW.g_fail_next Bw /\
  (onann_ri Bw -> onann_ri (onann_w1 I Bw b)) /\ TW.S_state (onann_w1 I Bw b) = TW.S_state Bw /\
  TW.GOT_n (onann_w1 I Bw b) = TW.GOT_n Bw.
Proof.
  intros I Bw b L. unfold onann_w1. destruct (TN.diginet_personality_from_name (onann_name b)).
  - exact (onann_set_keep Bw (onann_pv I b) L _ (or_introl eq_refl)).
  - split; [exact L|]. split; [reflexivity|]. split; [intros R; exact R|]. split; reflexivity.
Qed.

(* check_state_online returns its world. *)
Lemma onann_online_same : forall X Y, TC.check_state_online_m X = Some (Y, tt) -> Y = X.
Proof.
  intros X Y H. unfold TC.check_state_online_m in H.
  match type of H with (if ?c then _ else _) = _ => destruct c end; [discriminate H|].
  symmetry. exact (onann_some_inv _ _ H).
Qed.

Lemma onann_state_fin : forall (n : TI.ntc) B1 g1 B',
  (if TI.n_state n =? TC.S_ONLINE then TC.check_state_online_m (TW.set_GOT_n B1 g1)
   else Some (TW.set_GOT_n B1 g1, tt)) = Some (B', tt) -> B' = TW.set_GOT_n B1 g1.
Proof.
  intros n B1 g1 B' H. destruct (TI.n_state n =? TC.S_ONLINE).
  - exact (onann_online_same _ _ H).
  - symmetry. exact (onann_some_inv _ _ H).
Qed.

(* An N_STATE notice stores GOT.t[GOT.n] and GOT.n only: g_fail_next, onann_ri and the length carry. *)
Lemma onann_state_res : forall (Fr : option TI.tframe) X (n : TI.ntc) B',
  TI.n_kind n = TC.N_STATE -> length X = Z.to_nat TW.W_LEN ->
  TC.notice_m timg_A Fr X n = Some (B', tt) ->
  TW.g_fail_next B' = TW.g_fail_next X /\ (onann_ri X -> onann_ri B') /\ length B' = Z.to_nat TW.W_LEN.
Proof.
  intros Fr X n B' K L H.
  unfold TC.notice_m in H. rewrite K in H. cbn [Z.eqb TC.N_STATE Pos.eqb] in H.
  destruct (TW.GOT_n X <? TC.TRANS_MAX) eqn:E1; [destruct (TW.GOT_n X <? 0) eqn:E2; [discriminate H|] |].
  - apply Z.ltb_lt in E1. apply Z.ltb_ge in E2. cbv beta delta [TC.TRANS_MAX] in E1.
    destruct (TC.int_inc (TW.GOT_n X)) as [g1|]; [|discriminate H].
    cbv beta iota in H. apply onann_state_fin in H. subst B'.
    unfold TW.set_GOT_n, TW.set_GOT_t_reason, TW.set_GOT_t_old, TW.set_GOT_t_state.
    destruct (onann_got_upd X (TW.A_GOT_t_state (TW.GOT_n X)) (TW.put 4 (TI.n_state n)) L
      ltac:(onann_c) ltac:(onann_c)) as (L1 & G1 & R1).
    destruct (onann_got_upd _ (TW.A_GOT_t_old (TW.GOT_n X)) (TW.put 4 (TI.n_old n)) L1
      ltac:(onann_c) ltac:(onann_c)) as (L2 & G2 & R2).
    destruct (onann_got_upd _ (TW.A_GOT_t_reason (TW.GOT_n X)) (TW.put 4 (TI.n_reason n)) L2
      ltac:(onann_c) ltac:(onann_c)) as (L3 & G3 & R3).
    destruct (onann_got_upd _ TW.A_GOT_n (TW.put 4 g1) L3 ltac:(onann_c) ltac:(onann_c)) as (L4 & G4 & R4).
    split; [rewrite G4, G3, G2, G1; reflexivity|]. split; [intros R; exact (R4 (R3 (R2 (R1 R)))) | exact L4].
  - destruct (TC.int_inc (TW.GOT_n X)) as [g1|]; [|discriminate H].
    cbv beta iota in H. apply onann_state_fin in H. subst B'.
    unfold TW.set_GOT_n.
    destruct (onann_got_upd X TW.A_GOT_n (TW.put 4 g1) L ltac:(onann_c) ltac:(onann_c)) as (L4 & G4 & R4).
    split; [exact G4|]. split; [exact R4 | exact L4].
Qed.

(* An inlined session_lost copy's model result: g_fail_next, onann_ri and the length carry (TSS.session_lost_m's
   stores of g_s.inflight, .desk_counter_valid, .state and the N_STATE notice's GOT.t[GOT.n] and GOT.n). *)
Lemma onann_slost_res : forall (Fr : option TI.tframe) (Bx : list byte) why B4,
  TSS.session_lost_m timg_A Fr Bx why = Some (B4, tt) -> length Bx = Z.to_nat TW.W_LEN ->
  TW.g_fail_next B4 = TW.g_fail_next Bx /\ (onann_ri Bx -> onann_ri B4) /\ length B4 = Z.to_nat TW.W_LEN.
Proof.
  intros Fr Bx why B4 H L.
  assert (S1 : length (slost_w1 Bx) = Z.to_nat TW.W_LEN /\ TW.g_fail_next (slost_w1 Bx) = TW.g_fail_next Bx /\
               (onann_ri Bx -> onann_ri (slost_w1 Bx))).
  { unfold slost_w1, TW.set_S_desk_counter_valid, TW.set_S_inflight.
    destruct (onann_gs_upd Bx TW.A_S_inflight (TW.put 4 0) L ltac:(onann_c) ltac:(onann_c)) as (La & Ga & Ra).
    destruct (onann_gs_upd _ TW.A_S_desk_counter_valid (TW.put 4 0) La ltac:(onann_c) ltac:(onann_c))
      as (Lb & Gb & Rb).
    split; [exact Lb|]. split; [rewrite Gb; exact Ga | intros R; exact (Rb (Ra R))]. }
  assert (S2 : length (slost_w2 Bx) = Z.to_nat TW.W_LEN /\ TW.g_fail_next (slost_w2 Bx) = TW.g_fail_next Bx /\
               (onann_ri Bx -> onann_ri (slost_w2 Bx))).
  { destruct S1 as (L1 & G1 & R1). unfold slost_w2, TW.set_S_state.
    destruct (onann_gs_upd _ TW.A_S_state (TW.put 4 TS0.DIGINET_S_IDLE) L1 ltac:(onann_c) ltac:(onann_c))
      as (Lc & Gc & Rc).
    split; [exact Lc|]. split; [rewrite Gc; exact G1 | intros R; exact (Rc (R1 R))]. }
  rewrite slost_model in H.
  destruct (TW.S_state (slost_w1 Bx) =? TS0.DIGINET_S_IDLE); cbv beta iota in H.
  - pose proof (onann_some_inv _ _ H) as E. subst B4. destruct S1 as (L1 & G1 & R1).
    split; [exact G1|]. split; [exact R1 | exact L1].
  - unfold TSS.call_notify in H. destruct (TW.S_notify (slost_w2 Bx) =? TI.ti_notice timg_A); [|discriminate H].
    destruct S2 as (L2 & G2 & R2).
    destruct (onann_state_res Fr (slost_w2 Bx) (slost_ntc Bx why) B4 eq_refl L2 H) as (G3 & R3 & L3).
    split; [rewrite G3; exact G2|]. split; [intros R; exact (R3 (R2 R)) | exact L3].
Qed.

(* An N_DESK or N_FOREIGN notice's model result: g_fail_next, onann_ri, the length, S_state and GOT_n carry. *)
Lemma onann_ntc_gfn : forall (Fr : option TI.tframe) X (n : TI.ntc) B2,
  (TI.n_kind n = TC.N_DESK \/ TI.n_kind n = TC.N_FOREIGN) -> length X = Z.to_nat TW.W_LEN ->
  TC.notice_m timg_A Fr X n = Some (B2, tt) ->
  TW.g_fail_next B2 = TW.g_fail_next X /\ (onann_ri X -> onann_ri B2) /\ length B2 = Z.to_nat TW.W_LEN /\
  TW.S_state B2 = TW.S_state X /\ TW.GOT_n B2 = TW.GOT_n X.
Proof.
  intros Fr X n B2 [K|K] L H.
  - destruct (onann_notice_desk timg_A Fr X n B2 K H) as (d & E). subst B2.
    destruct (onann_set_keep X d L (TW.set_GOT_desk X d) ltac:(do 4 right; left; reflexivity))
      as (L2 & G2 & R2 & S2 & N2).
    split; [exact G2|]. split; [exact R2|]. split; [exact L2|]. split; [exact S2 | exact N2].
  - destruct (onann_notice_fg timg_A Fr X n B2 K H) as (d & E). subst B2.
    destruct (onann_set_keep X d L (TW.set_GOT_foreign X d) ltac:(do 5 right; reflexivity))
      as (L2 & G2 & R2 & S2 & N2).
    split; [exact G2|]. split; [exact R2|]. split; [exact L2|]. split; [exact S2 | exact N2].
Qed.

(* The desk notice's and the foreign notice's call_notify results. *)
Lemma onann_dn_res : forall (Fr : option TI.tframe) (Bx b B2 : list byte),
  TSS.call_notify timg_A Fr Bx (onann_dntc timg_A Bx b) = Some (B2, tt) -> length Bx = Z.to_nat TW.W_LEN ->
  TW.g_fail_next B2 = TW.g_fail_next Bx /\ (onann_ri Bx -> onann_ri B2) /\ length B2 = Z.to_nat TW.W_LEN /\
  TW.S_state B2 = TW.S_state Bx /\ TW.GOT_n B2 = TW.GOT_n Bx.
Proof.
  intros Fr Bx b B2 H L. unfold TSS.call_notify in H.
  destruct (TW.S_notify Bx =? TI.ti_notice timg_A); [|discriminate H].
  exact (onann_ntc_gfn Fr Bx (onann_dntc timg_A Bx b) B2 (or_introl eq_refl) L H).
Qed.

Lemma onann_fg_res : forall (Fr : option TI.tframe) (Bf b B3 : list byte),
  TSS.call_notify timg_A Fr Bf (onann_fntc Bf b) = Some (B3, tt) -> length Bf = Z.to_nat TW.W_LEN ->
  TW.g_fail_next B3 = TW.g_fail_next Bf /\ (onann_ri Bf -> onann_ri B3) /\ length B3 = Z.to_nat TW.W_LEN /\
  TW.S_state B3 = TW.S_state Bf /\ TW.GOT_n B3 = TW.GOT_n Bf.
Proof.
  intros Fr Bf b B3 H L. unfold TSS.call_notify in H.
  destruct (TW.S_notify Bf =? TI.ti_notice timg_A); [|discriminate H].
  exact (onann_ntc_gfn Fr Bf (onann_fntc Bf b) B3 (or_intror eq_refl) L H).
Qed.

(* The body of a frame the parse accepted (fr_code b = 0): fr_body_len b bytes, from byte 30 on. *)
Lemma onann_body_len : forall b, DSpec.fr_code b = 0 ->
  0 <= DSpec.fr_body_len b /\ 30 + DSpec.fr_body_len b <= Z.of_nat (length b) /\
  length (DSpec.fr_body b) = Z.to_nat (DSpec.fr_body_len b).
Proof.
  intros b H. destruct (DSpec.fr_code_ok b H) as (L & _ & N1 & N2).
  unfold DSpec.fr_body, DSpec.fr_body_len. rewrite length_firstn, length_skipn. lia.
Qed.

(* The name's C string: the bytes copy_strz keeps hold no NUL, so cstring stops at the NUL it writes. *)
Lemma onann_cstring_af : forall src,
  CC.cstring (CC.zb (TSS.ann_field src)) = CC.zb (firstn (DSpec.copy_len 10 9 src) src).
Proof.
  intros src. unfold TSS.ann_field. change (DSpec.copy_len 10 9 src) with (DSpec.nz_run (firstn 9 src)).
  generalize 9%nat. intros n. revert src. induction n as [|n IH]; intros [|x l]; try reflexivity.
  cbn [firstn DSpec.nz_run].
  destruct (Z.eqb_spec (DSpec.bz x) 0) as [E|E]; [reflexivity|].
  cbn [firstn app]. unfold CC.zb in *. cbn [map CC.cstring].
  unfold DSpec.bz in E. apply Z.eqb_neq in E. rewrite E. cbv beta iota. f_equal. apply IH.
Qed.

Lemma onann_z_list_eqb : forall x y, TN.z_list_eqb x y = true -> x = y.
Proof.
  induction x as [|a x IH]; intros [|c y] H; cbn in H; try discriminate H; [reflexivity|].
  apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. subst c. f_equal. apply IH. exact H2.
Qed.

(* codec_cells.v from_name_res's test, as TNeed.v's search of personalities[] (image A's personalities). *)
Lemma onann_from_name_z : forall z,
  (if list_eq_dec Z.eq_dec z CC.NAME_C24 then TRANS_PERS
   else if list_eq_dec Z.eq_dec z CC.NAME_PC then TRANS_PERS + 24 else 0) =
  match TN.personality_name_find DLib.personalities 0 z with
  | Some i => TI.ti_personalities timg_A + 24 * i
  | None => 0
  end.
Proof.
  intros z.
  destruct (list_eq_dec Z.eq_dec z CC.NAME_C24) as [E1|E1]; [subst z; reflexivity|].
  destruct (list_eq_dec Z.eq_dec z CC.NAME_PC) as [E2|E2]; [subst z; reflexivity|].
  unfold DLib.personalities. cbn [TN.personality_name_find DLib.dp_announce_name].
  repeat match goal with |- context [TN.z_list_eqb z ?l] =>
    let H := fresh "H" in destruct (TN.z_list_eqb z l) eqn:H;
    [apply onann_z_list_eqb in H; subst z; exfalso; first [apply E1; reflexivity | apply E2; reflexivity] |]
  end.
  reflexivity.
Qed.

(* personality_from_name's result on the name the parse left at a + 10 is the model's personality pointer. *)
Lemma onann_pv_res : forall (b : list byte),
  trans_pfrom_res (TSS.ann_field (skipn 24 (DSpec.fr_body b))) = onann_pv timg_A b.
Proof.
  intros b. unfold trans_pfrom_res. rewrite onann_cstring_af.
  unfold onann_pv, onann_name, TN.diginet_personality_from_name.
  exact (onann_from_name_z
    (CC.zb (firstn (DSpec.copy_len 10 9 (skipn 24 (DSpec.fr_body b))) (skipn 24 (DSpec.fr_body b))))).
Qed.

Lemma onann_pfn_range : forall name i, TN.diginet_personality_from_name name = Some i -> i = 0 \/ i = 1.
Proof.
  intros name i. unfold TN.diginet_personality_from_name, DLib.personalities. cbn [TN.personality_name_find].
  destruct (TN.z_list_eqb _ _); [intros H; cbv beta iota in H; injection H; lia|].
  destruct (TN.z_list_eqb _ _); [intros H; cbv beta iota in H; injection H; lia |
    intros H; cbv beta iota in H; discriminate H].
Qed.

(* The personality pointer is 0 exactly when the name is neither entry's. *)
Lemma onann_pv_zero : forall (b : list byte),
  onann_pv timg_A b = 0 <-> TN.diginet_personality_from_name (onann_name b) = None.
Proof.
  intros b. unfold onann_pv. destruct (TN.diginet_personality_from_name (onann_name b)) as [i|] eqn:E.
  - pose proof (onann_pfn_range _ _ E) as Hi.
    rewrite <- trans_pfrom_pers. unfold TRANS_PERS.
    split; [intros H; exfalso; lia | intros H; discriminate H].
  - split; intros _; reflexivity.
Qed.

End k.
