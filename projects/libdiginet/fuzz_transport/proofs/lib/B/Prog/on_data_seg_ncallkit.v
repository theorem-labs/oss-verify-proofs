(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: the shared part of proofs/libreac/fuzz_decode/lib/A/Prog/check_round_trip_cg.v (origin/ossv/recipes 88154566652a: dec_utrace, the read-only reads and their two instance facts, the value-0 shadow granule of a table, the leaf instances dec_leaf_at / dec_leaf_wr_at and the runtime cells as constant cells of the record) for reac-repacer/fuzz_uci's image A: module paths changed, the image is the core's tfibsegs (lib/A/AB1v.v), the read-only reads and the cells are fuzz_uci.asan's, measured on the pinned image. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/reac-repacer/fuzz_uci/lib/A/Prog/UciCg.v, with its module paths changed. *)
(* Modified by Theorem Labs: the shared part of proofs/libreac/fuzz_decode/lib/A/Prog/check_round_trip_cg.v (origin/ossv/recipes 88154566652a: dec_utrace, the read-only reads and their two instance facts, the value-0 shadow granule of a table, the leaf instances dec_leaf_at / dec_leaf_wr_at and the runtime cells as constant cells of the record) for reac-repacer/fuzz_uci's image A: module paths changed, the image is the core's tfibsegs (lib/A/AB1v.v), the read-only reads and the cells are fuzz_uci.asan's, measured on the pinned image. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/UciCg.v, with its module paths changed; 778 of its 849 lines of code are new or changed and 69 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/DgnTransportCg.v, with its module paths and module names changed; 411 of its 515 lines of code are new or changed and 745 lines of the source are left out. *)
(* on_data_seg_ncallkit: the lemmas the notice-call piece of on_data's image-B walk (lib/B/Prog/on_data_seg_ncall.v)
   uses beyond the kit (lib/B/Prog/TransportGNoticeB.v, lib/A/Prog/TransportGNotice.v). Image B's twin of image A's
   on_data_seg_ncallkit.v: the same lemmas at image B's names (G_HARNESS_B, TMAP_B, the TB_* bases, m_set_cg.v twb_fld,
   timg_B), with the kit's lemmas where A's piece has a local one (notice_wr_G for A's odnc_nwr_G, frame_ra_zero and
   frame_hull_vis for A's odnc_ra_zero and odnc_hull_in).
   - The written ranges: every byte of on_data_cg.v ondata_wr is a byte of G (odnc_wr_G); a data notice's notice_wr
     (notice_cg.v) is GOT.ndata, the same bytes at every world (odnc_nwr_in).
   - The model: on the notice path call_notify's test holds and notice_m gives Bw' (odnc_call); the fields the notice
     path reads after the g_s stores of ondata_w2 and ondata_w3 (odnc_w2, odnc_w3); a data notice keeps g_fail_next
     and finds GOT.ndata non-negative (odnc_notice_data); the frame's body (odnc_body, odnc_garr8_body).
   - A range's placement (DgnTransportBCg.v trans_src_ok) carried from the call's entry state to a later state whose
     frames contain the entry's (odnc_src_carry: frames Sc a sub-list of the later frames), when each byte of the
     range is kept or a byte of G (odnc_kv) and the entry frames' shadow bytes are kept (odnc_ks), as acall_kept_g over
     a written range inside G gives them; the current heap frame carried so (odnc_tframe). The walk holds no
     gx_kept_ex (send_control's post pins G only to its model world), so TransportGNoticeB.v trans_src_ok_kept_gx and
     trans_tframe_at_kept_gx do not apply: a byte of G is visible at every memory instead.
   - The own frame: its notice's 72 bytes placed (odnc_ntc_src), the uniqueness of the bytes garr8 names
     (odnc_garr8_eq, odnc_map_bz_inj), notice's stores apart from what it reads (odnc_apart), and a step after notice
     that writes only the own frame's bytes keeps acall_kept_g (odnc_kept_w). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import CanKit TWorldB TImgB TransportGRwB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBList DgnTransportBPa DgnTransportBImg YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_cg send_control_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_data_cg on_data_seg_cut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGNotice.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGNoticeB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas TOpsKeep.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TNotifyFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TGNA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.TransportGNotice.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TOK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOpsKeep.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The written ranges                                               *)
(* ------------------------------------------------------------------ *)

(* The world offsets and image bases the written ranges name, as numerals. *)
Ltac odnc_offs :=
  unfold twb_fld, TW.A_GOT_t_state, TW.GOT_t_ESZ, TC.TRANS_MAX, TW.A_GOT_n, TW.A_GOT_acked, TW.A_GOT_desk,
    TW.A_GOT_ndata, TW.A_GOT_foreign, TW.A_M_fly_on, TW.A_GOT_e2, TW.A_GOT_e3, TW.A_GOT_acks, TW.A_M_host_counter,
    TW.A_M_next_ka, TW.A_M_last_display, TW.A_M_display_sent, TW.A_M_fly_cmd, TW.A_M_fly_counter,
    TW.A_M_fly_retries, TW.A_M_fly_sent, TW.A_M_fly_len, TW.A_M_fly_frame, TW.A_Cmd_st, TC.CMDS_MAX,
    TC.SPEC_MAX_FRAME, TW.A_S_stats_tx_frames, TW.A_S_stats_tx_acks, TW.A_S_stats_rx_data,
    TW.A_S_stats_rx_desk_retries, TW.A_S_backoff_until_us, TW.A_S_stats_rx_duplicates, TW.A_S_desk_counter,
    TW.A_S_desk_counter_valid, TW.OFF_GOT, TW.SZ_GOT, TW.OFF_M, TW.SZ_M, TW.OFF_g_s, TW.SZ_g_s, TW.OFF_g_cmd,
    TW.SZ_g_cmd, TW.OFF_g_q, TW.SZ_g_q, TW.OFF_g_nq, TW.SZ_g_nq, TW.OFF_g_last_counter, TW.SZ_g_last_counter,
    TW.OFF_g_fail_next, TB_GOT, TB_M, TB_g_s, TB_g_cmd, TB_g_q, TB_g_nq, TB_g_last_counter, TB_g_fail_next in *.

(* A payload byte of a row of TMAP_B is a byte of G. *)
Lemma odnc_inG_row : forall o b n a, In (o, b, n) TMAP_B -> b <= a < b + n -> inG TG.G_HARNESS_B a.
Proof.
  intros o b n a Hin Ha. unfold inG. apply Exists_exists. exists (b, n).
  split; [exact (TMAP_B_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia].
Qed.

(* io_send's stores for send_control's 60-byte frame are bytes of G. *)
Lemma odnc_iosend_G : forall a, iosend_wr SENDCTL_F a -> inG TG.G_HARNESS_B a.
Proof.
  intros a H. unfold iosend_wr, SENDCTL_F in H.
  destruct H as [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]]]]]]]]]]].
  - apply (odnc_inG_row _ _ _ a TMAP_B_g_fail_next). odnc_offs. lia.
  - apply (odnc_inG_row _ _ _ a TMAP_B_GOT). odnc_offs. lia.
  - apply (odnc_inG_row _ _ _ a TMAP_B_GOT). odnc_offs. lia.
  - apply (odnc_inG_row _ _ _ a TMAP_B_GOT). odnc_offs. lia.
  - apply (odnc_inG_row _ _ _ a TMAP_B_g_last_counter). odnc_offs. lia.
  - apply (odnc_inG_row _ _ _ a TMAP_B_M). odnc_offs. lia.
  - apply (odnc_inG_row _ _ _ a TMAP_B_M). odnc_offs. lia.
  - apply (odnc_inG_row _ _ _ a TMAP_B_M). odnc_offs. lia.
  - apply (odnc_inG_row _ _ _ a TMAP_B_M). odnc_offs. lia.
  - apply (odnc_inG_row _ _ _ a TMAP_B_M). odnc_offs. lia.
  - apply (odnc_inG_row _ _ _ a TMAP_B_M). odnc_offs. lia.
  - apply (odnc_inG_row _ _ _ a TMAP_B_M). odnc_offs. lia.
  - apply (odnc_inG_row _ _ _ a TMAP_B_M). odnc_offs. lia.
  - apply (odnc_inG_row _ _ _ a TMAP_B_M). odnc_offs. lia.
  - apply (odnc_inG_row _ _ _ a TMAP_B_M). odnc_offs. lia.
  - apply (odnc_inG_row _ _ _ a TMAP_B_M). odnc_offs. rewrite Z.min_l in H by lia. lia.
  - destruct H as (s & Hs & H). apply (odnc_inG_row _ _ _ a TMAP_B_g_cmd). odnc_offs. lia.
  - apply (odnc_inG_row _ _ _ a TMAP_B_g_q). odnc_offs. lia.
  - apply (odnc_inG_row _ _ _ a TMAP_B_g_nq). odnc_offs. lia.
Qed.

(* Every byte on_data's call may store is a byte of G. *)
Lemma odnc_wr_G : forall Bw b a, ondata_wr Bw b a -> inG TG.G_HARNESS_B a.
Proof.
  intros Bw b a H. unfold ondata_wr in H.
  destruct H as [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]].
  - apply (odnc_inG_row _ _ _ a TMAP_B_g_s). odnc_offs. lia.
  - exact (odnc_iosend_G a H).
  - apply (odnc_inG_row _ _ _ a TMAP_B_g_s). odnc_offs. lia.
  - apply (odnc_inG_row _ _ _ a TMAP_B_g_s). odnc_offs. lia.
  - apply (odnc_inG_row _ _ _ a TMAP_B_g_s). odnc_offs. lia.
  - apply (odnc_inG_row _ _ _ a TMAP_B_g_s). odnc_offs. lia.
  - apply (odnc_inG_row _ _ _ a TMAP_B_g_s). odnc_offs. lia.
  - apply (odnc_inG_row _ _ _ a TMAP_B_g_s). odnc_offs. lia.
  - apply (odnc_inG_row _ _ _ a TMAP_B_g_s). odnc_offs. lia.
  - exact (notice_wr_G Bw (ondata_ntc Bw b) a H).
Qed.

(* A data notice stores GOT.ndata, whatever the world. *)
Lemma odnc_nwr : forall X b a, notice_wr X (ondata_ntc X b) a -> twb_fld TW.OFF_GOT TB_GOT TW.A_GOT_ndata 4 a.
Proof.
  intros X b a H. unfold notice_wr, ondata_ntc in H. cbn [TI.n_kind] in H.
  destruct H as [(K & _) | [(K & _) | [(K & _) | [(K & _) | [(_ & H) | (K & _)]]]]];
    [ | | | | exact H | ];
    unfold TS0.DIGINET_N_DATA, TC.N_STATE, TC.N_ACKED, TC.N_ACK_LOST, TC.N_DESK, TC.N_FOREIGN in K; discriminate K.
Qed.

Lemma odnc_nwr_in : forall X Y b a, notice_wr X (ondata_ntc X b) a -> notice_wr Y (ondata_ntc Y b) a.
Proof.
  intros X Y b a H. pose proof (odnc_nwr X b a H) as Hf. unfold notice_wr.
  right; right; right; right; left. split; [reflexivity | exact Hf].
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The model                                                        *)
(* ------------------------------------------------------------------ *)

(* On the notice path (not a duplicate, not a keepalive), call_notify's test holds and notice gives Bw'. *)
Lemma odnc_call : forall (TF : option TI.tframe) Bw b now Bw' B1 r f,
  TSS.on_data_m timg_B TF Bw b now = Some (Bw', tt) ->
  TSS.send_control_m timg_B TF Bw TS0.DIGINET_CMD_ACK (DSpec.fr_send b) = Some (B1, (r, f)) ->
  ondata_dup (ondata_w2 B1 b r now) b = false -> DSpec.fr_keepalive b = false ->
  TW.S_notify (ondata_w3 (ondata_w2 B1 b r now) b) = TI.ti_notice timg_B /\
  TC.notice_m timg_B TF (ondata_w3 (ondata_w2 B1 b r now) b) (ondata_ntc (ondata_w3 (ondata_w2 B1 b r now) b) b) =
    Some (Bw', tt).
Proof.
  intros TF Bw b now Bw' B1 r f Hm Hsc Hd Hk.
  rewrite ondata_model, Hsc in Hm. cbv beta iota in Hm. rewrite Hd, Hk in Hm. cbv beta iota in Hm.
  unfold TSS.call_notify in Hm.
  destruct (Z.eqb_spec (TW.S_notify (ondata_w3 (ondata_w2 B1 b r now) b)) (TI.ti_notice timg_B)) as [E|E];
    [|discriminate Hm].
  split; [exact E | exact Hm].
Qed.

(* check_state_data returns the world it was given, and only when GOT.ndata is not negative. *)
Lemma odnc_csd : forall (F : option TI.tframe) X (n : TI.ntc) X1 u1,
  TC.check_state_data_m F X n = Some (X1, u1) -> X1 = X /\ 0 <= TW.GOT_ndata X.
Proof.
  intros F X n X1 u1. unfold TC.check_state_data_m. cbv zeta.
  destruct (_ || _); [intro HH; discriminate HH|].
  destruct (Z.ltb_spec (TW.GOT_ndata X) 0) as [Hneg|Hnn]; [intro HH; discriminate HH|].
  destruct (negb _); [intro HH; discriminate HH|].
  destruct (TC.frame_read _ _ _); [|intro HH; discriminate HH].
  destruct (_ <? _); [intro HH; discriminate HH|].
  destruct (_ || _); [intro HH; discriminate HH|].
  intro HH. destruct u1. split; [exact (eq_sym (od_some_inv X X1 HH)) | exact Hnn].
Qed.

(* A data notice: check_state_data returns its world, whose GOT.ndata is not negative, and the GOT.ndata store keeps
   g_fail_next. *)
Lemma odnc_notice_data : forall I (F : option TI.tframe) X (n : TI.ntc) X',
  TI.n_kind n = TC.N_DATA -> length X = Z.to_nat TW.W_LEN ->
  TC.notice_m I F X n = Some (X', tt) ->
  TW.g_fail_next X' = TW.g_fail_next X /\ 0 <= TW.GOT_ndata X.
Proof.
  intros I F X n X' K L H.
  unfold TC.notice_m in H. cbv zeta in H. rewrite K in H.
  replace (TC.N_DATA =? TC.N_STATE) with false in H by reflexivity.
  replace (TC.N_DATA =? TC.N_ACKED) with false in H by reflexivity.
  replace (TC.N_DATA =? TC.N_ACK_LOST) with false in H by reflexivity.
  replace (TC.N_DATA =? TC.N_DESK) with false in H by reflexivity.
  replace (TC.N_DATA =? TC.N_DATA) with true in H by reflexivity.
  cbv beta iota in H.
  destruct (TC.check_state_data_m F X n) as [[X1 u1]|] eqn:CSD; [|discriminate H].
  destruct (odnc_csd F X n X1 u1 CSD) as [-> Hnn].
  cbv beta iota in H.
  destruct (TC.int_inc (TW.GOT_ndata X)) as [d|]; [|discriminate H].
  cbv beta iota in H.
  pose proof (od_some_inv _ _ H) as EX. split; [|exact Hnn].
  rewrite <- EX. unfold TW.set_GOT_ndata.
  exact (proj1 (gfn_upd X (TW.put 4 d) TW.A_GOT_ndata L ltac:(unfold TW.A_GOT_ndata; lia)
    ltac:(rewrite TWL.length_put; unfold TW.A_GOT_ndata, TW.OFF_GOT, TW.W_LEN; lia))).
Qed.

(* The fields the notice path reads after on_data's g_s stores: GOT.ndata, OW's bodies, g_fail_next (odnc_gw), and,
   before the stores of :253-254, desk_counter and desk_counter_valid (odnc_gs). *)
Definition odnc_gw (X Y : list byte) : Prop :=
  length Y = Z.to_nat TW.W_LEN /\ TW.GOT_ndata Y = TW.GOT_ndata X /\
  (forall g, 0 <= g -> TC.OW_dn_body Y g = TC.OW_dn_body X g) /\ TW.g_fail_next Y = TW.g_fail_next X.
Definition odnc_gs (X Y : list byte) : Prop :=
  odnc_gw X Y /\ TW.S_desk_counter Y = TW.S_desk_counter X /\ TW.S_desk_counter_valid Y = TW.S_desk_counter_valid X.

Lemma odnc_gw_refl : forall X, length X = Z.to_nat TW.W_LEN -> odnc_gw X X.
Proof. intros X L. split; [exact L|]. split; [reflexivity|]. split; [intros; reflexivity | reflexivity]. Qed.

(* A store below g_fail_next (g_s's payload lies there) keeps odnc_gw. *)
Lemma odnc_gw_upd : forall X Y k v, odnc_gw X Y -> 0 <= k -> k + Z.of_nat (length v) <= TW.OFF_g_fail_next ->
  odnc_gw X (TW.upd Y k v).
Proof.
  intros X Y k v (L & G & O & FN) Hk Hl.
  assert (Hw : k + Z.of_nat (length v) <= TW.W_LEN) by (unfold TW.OFF_g_fail_next, TW.W_LEN in *; lia).
  split; [exact (len_upd_W Y v k L Hk Hw)|].
  split.
  { unfold TW.GOT_ndata in *.
    rewrite rd32_upd_W; [exact G | exact L | exact Hk | exact Hw | unfold TW.A_GOT_ndata, TW.OFF_GOT; lia |].
    right. unfold TW.A_GOT_ndata, TW.OFF_GOT, TW.OFF_g_fail_next in *. lia. }
  split.
  { intros g Hg. unfold TC.OW_dn_body in *.
    rewrite rd_upd_W; [exact (O g Hg) | exact L | exact Hk | exact Hw | unfold TC.A_OW_dn_body, TW.OFF_OW; lia |].
    right. unfold TC.A_OW_dn_body, TW.OFF_OW, TW.OFF_g_fail_next in *. lia. }
  { unfold TW.g_fail_next in *.
    rewrite rd_upd_W; [exact FN | exact L | exact Hk | exact Hw | unfold TW.OFF_g_fail_next; lia |].
    right. lia. }
Qed.

(* A store below g_fail_next and apart from desk_counter and desk_counter_valid keeps odnc_gs. *)
Lemma odnc_gs_upd : forall X Y k v, odnc_gs X Y -> 0 <= k -> k + Z.of_nat (length v) <= TW.OFF_g_fail_next ->
  (k + Z.of_nat (length v) <= TW.A_S_desk_counter \/ TW.A_S_desk_counter_valid + 4 <= k) ->
  odnc_gs X (TW.upd Y k v).
Proof.
  intros X Y k v (GW & D & V) Hk Hl Hd.
  pose proof GW as (L & _).
  assert (Hw : k + Z.of_nat (length v) <= TW.W_LEN) by (unfold TW.OFF_g_fail_next, TW.W_LEN in *; lia).
  split; [exact (odnc_gw_upd X Y k v GW Hk Hl)|].
  split.
  { unfold TW.S_desk_counter in *.
    rewrite rd_upd_W; [exact D | exact L | exact Hk | exact Hw | unfold TW.A_S_desk_counter, TW.OFF_g_s; lia |].
    unfold TW.A_S_desk_counter, TW.A_S_desk_counter_valid, TW.OFF_g_s in *.
    destruct Hd as [Hd|Hd]; [right | left]; lia. }
  { unfold TW.S_desk_counter_valid in *.
    rewrite rd32_upd_W; [exact V | exact L | exact Hk | exact Hw | unfold TW.A_S_desk_counter_valid, TW.OFF_g_s; lia |].
    unfold TW.A_S_desk_counter, TW.A_S_desk_counter_valid, TW.OFF_g_s in *.
    destruct Hd as [Hd|Hd]; [right | left]; lia. }
Qed.

Ltac odnc_k :=
  rewrite ?TWL.length_put;
  unfold TW.A_S_stats_tx_acks, TW.A_S_stats_rx_data, TW.A_S_stats_rx_desk_retries, TW.A_S_backoff_until_us,
    TW.A_S_desk_counter, TW.A_S_desk_counter_valid, TW.OFF_g_s, TW.OFF_g_fail_next;
  first [lia | left; lia | right; lia].

(* on_data's stores of :242-247 (ondata_w2) keep what the notice path reads, desk_counter included. *)
Lemma odnc_w2 : forall B1 b r now, length B1 = Z.to_nat TW.W_LEN -> odnc_gs B1 (ondata_w2 B1 b r now).
Proof.
  intros B1 b r now L.
  assert (G0 : odnc_gs B1 B1) by (split; [exact (odnc_gw_refl B1 L) | split; reflexivity]).
  unfold ondata_w2. destruct (r =? 0); destruct (DSpec.fr_retry b =? 0); cbv beta iota zeta;
  unfold TW.set_S_stats_tx_acks, TW.set_S_stats_rx_data, TW.set_S_stats_rx_desk_retries, TW.set_S_backoff_until_us;
  repeat (apply odnc_gs_upd; [ | odnc_k | odnc_k | odnc_k ]); exact G0.
Qed.

(* The stores of :253-254 (ondata_w3) keep GOT.ndata, OW's bodies and g_fail_next. *)
Lemma odnc_w3 : forall X b, length X = Z.to_nat TW.W_LEN -> odnc_gw X (ondata_w3 X b).
Proof.
  intros X b L. unfold ondata_w3, TW.set_S_desk_counter_valid, TW.set_S_desk_counter.
  apply odnc_gw_upd; [apply odnc_gw_upd; [exact (odnc_gw_refl X L) | odnc_k | odnc_k] | odnc_k | odnc_k].
Qed.

(* The frame's body: fr_body_len b bytes from b's byte 30 on, a 16-bit count less 16. *)
Lemma odnc_body : forall b, DSpec.fr_code b = 0 ->
  0 <= DSpec.fr_body_len b < 2 ^ 32 /\ Z.of_nat (length (DSpec.fr_body b)) = DSpec.fr_body_len b /\
  30 + DSpec.fr_body_len b <= Z.of_nat (length b).
Proof.
  intros b FC. destruct (DSpec.fr_code_ok b FC) as (L30 & _ & H16 & Hnb).
  assert (Hlt : DSpec.fr_numbytes b < 65536).
  { unfold DSpec.fr_numbytes, DSpec.be16, DSpec.at8, DSpec.bz.
    pose proof (bv_unsigned_in_range 8 (nth 14 b (DSpec.b8 0))) as R1.
    pose proof (bv_unsigned_in_range 8 (nth 15 b (DSpec.b8 0))) as R2.
    change (bv_modulus 8) with 256 in R1, R2. change (2 ^ 8) with 256. lia. }
  change (2 ^ 32) with 4294967296.
  unfold DSpec.fr_body_len. split; [lia|]. split; [|lia].
  unfold DSpec.fr_body, DSpec.fr_body_len. rewrite length_firstn, length_skipn. lia.
Qed.

(* The body's bytes, from b's at buf. *)
Lemma odnc_garr8_body : forall (sg : list Segment) m buf b, DSpec.fr_code b = 0 ->
  garr8 sg m buf (TW.zs b) -> garr8 sg m (buf + 30) (map DSpec.bz (DSpec.fr_body b)).
Proof.
  intros sg m buf b FC H. destruct (DSpec.fr_code_ok b FC) as (L30 & _ & _ & _).
  unfold TW.zs in H. rewrite <- (firstn_skipn 30 b) in H. rewrite map_app in H.
  apply garr8_app in H. destruct H as [_ H].
  rewrite length_map, length_firstn in H. replace (Nat.min 30 (length b)) with 30%nat in H by lia.
  change (Z.of_nat 30) with 30 in H.
  unfold DSpec.fr_body. rewrite <- (firstn_skipn (Z.to_nat (DSpec.fr_body_len b)) (skipn 30 b)) in H.
  rewrite map_app in H. apply garr8_app in H. destruct H as [H _]. exact H.
Qed.

(* garr8 names the bytes at a place: two lists of the same length garr8 puts there are equal. *)
Lemma odnc_garr8_eq : forall (sg : list Segment) m a (l l' : list Z),
  garr8 sg m a l -> garr8 sg m a l' -> length l = length l' -> l = l'.
Proof.
  intros sg m a l l' H H' L. apply (nth_ext l l' 0 0 L). intros j Hj.
  destruct (H j Hj) as [V R]. destruct (H' j ltac:(lia)) as [V' R'].
  pose proof (V 0%nat ltac:(lia)) as E. pose proof (V' 0%nat ltac:(lia)) as E'.
  rewrite E in E'.
  apply (f_equal (fun o : option byte => match o with Some x => bv_unsigned x | None => 0 end)) in E'.
  cbv beta iota in E'.
  rewrite (tw_le_byte1 _ R), (tw_le_byte1 _ R') in E'.
  rewrite !Z_to_bv_unsigned in E'. unfold bv_wrap in E'.
  change (bv_modulus 8) with 256 in E'. rewrite !Z.mod_small in E' by lia. exact E'.
Qed.

Lemma odnc_map_bz_inj : forall l l' : list byte, map DSpec.bz l = map DSpec.bz l' -> l = l'.
Proof.
  induction l as [|x l IH]; intros [|y l'] H; cbn [map] in H; try discriminate H; [reflexivity|].
  injection H as Hxy Hl. f_equal; [apply bv_eq; exact Hxy | exact (IH l' Hl)].
Qed.

(* ------------------------------------------------------------------ *)
(* 3. Windows                                                          *)
(* ------------------------------------------------------------------ *)

(* The window of a range moves from a caller's window to a callee's inside it. *)
Lemma odnc_off_win : forall (regs regsC : bvmap 5 word) K K' q n,
  decode_off_win regs K q n -> spZ regs - K <= spZ regsC - K' -> spZ regsC <= spZ regs ->
  decode_off_win regsC K' q n.
Proof. intros regs regsC K K' q n H H1 H2. unfold decode_off_win in *. destruct H as [H|H]; [left | right]; lia. Qed.

(* ------------------------------------------------------------------ *)
(* 4. Placements carried to a later state                              *)
(* ------------------------------------------------------------------ *)

Section mem. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Local Abbreviation segs := tfibsegs.

(* Each byte of a placed range outside the window, at the memory after a run that kept acall_kept_g over a written
   range inside G, is kept, or is a byte of G. *)
Lemma odnc_kv : AR_laws segs B -> trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall lyc Sc (W : world segs) memc mdc (W2 : world segs) mem2 slo shi (E : Z -> Prop) q n,
  @AR rc segs B lyc Sc W memc mdc ->
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 mem2 slo shi E ->
  (forall a, E a -> inG TG.G_HARNESS_B a) ->
  (q + n <= slo \/ shi <= q) ->
  trans_src_ok B lyc Sc W memc q n ->
  forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a \/ inG TG.G_HARNESS_B a.
Proof.
  intros LAWS HRU HRE lyc Sc W memc mdc W2 mem2 slo shi E q n HAR (K1 & K2 & K3 & K4 & _) HEG Hoff Hs a Ha.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (inGb TG.G_HARNESS_B a) eqn:Eg; [right; apply inGb_spec; exact Eg|].
  apply inGb_false in Eg. left.
  assert (HnE : ~ E a) by (intros HE; exact (Eg (HEG a HE))).
  destruct Hs as [(bA & nA & Hin & B1 & B2) | (HL & _)].
  - destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn0).
    pose proof (req_size_pos nA (proj1 Hn0)) as [_ Hreq].
    replace a with (bA + (a - bA)) by lia.
    apply (K2 bA nA (a - bA) Hin ltac:(lia)). replace (bA + (a - bA)) with a by lia. exact HnE.
  - destruct HL as [(cid & pos & Hin & F1 & F2) | [(HG & _) | [(S1 & S3) | (HR & _)]]].
    + apply (K4 cid pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact HnE].
    + exfalso. exact (Eg (HG a Ha)).
    + destruct (trans_stk_bounds B lyc Sc W memc mdc HAR) as [T1 T2]. apply K1; [lia|].
      intros [Hx1 Hx2]. destruct Hoff as [Ho|Ho]; lia.
    + pose proof (HR a Ha) as Ra. destruct (trans_ro_rd_scoped B HRU HRE a Ra) as [Ho He].
      exact (K3 a (trans_ro_img a Ra) Eg Ho He).
Qed.

(* The shadow bytes of the entry's frames are kept: a written range inside G lies below kLowMemEnd. *)
Lemma odnc_ks : AR_laws segs B ->
  forall lyc Sc (W : world segs) memc mdc (W2 : world segs) mem2 slo shi (E : Z -> Prop),
  @AR rc segs B lyc Sc W memc mdc ->
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 mem2 slo shi E ->
  (forall a, E a -> inG TG.G_HARNESS_B a) ->
  forall cid pos s, In (cid, pos) (frames Sc) ->
    in_zr s (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8) ->
    aview segs (w_H W2) mem2 s = aview segs (w_H W) memc s.
Proof.
  intros LAWS lyc Sc W memc mdc W2 mem2 slo shi E HAR (_ & _ & _ & K4 & _) HEG cid pos s Hin Hs.
  apply (K4 cid pos s Hin (or_intror Hs)). intros HE. pose proof (inG_G_HARNESS_hull s (HEG s HE)) as Gh.
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F1 & F2 & _).
  pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
  unfold in_zr in Hs. cbn [fst snd] in Hs.
  unfold shadow_addr, SHADOW_OFF, TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in *. lia.
Qed.

(* DgnTransportCg.v decode_rd_ok_fake_kept_ge0 with the range's bytes only visible at the later memory. *)
Lemma odnc_rd_fake : AR_laws segs B -> forall lyc Sc (W W' : world segs) memc mem' mdc q n,
  @AR rc segs B lyc Sc W memc mdc -> decode_in_fake lyc Sc q n -> decode_rd_ok W memc q n -> 0 <= n ->
  (forall a, q <= a < q + n -> aview segs (w_H W') mem' a <> None) ->
  (forall cid pos s, In (cid, pos) (frames Sc) ->
     in_zr s (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8) ->
     aview segs (w_H W') mem' s = aview segs (w_H W) memc s) ->
  decode_rd_ok W' mem' q n.
Proof.
  intros LAWS lyc Sc W W' memc mem' mdc q n HAR (cid & pos & Hin & F1 & F2) (R1 & R2 & R3 & R4 & R5 & R6) Hn HV K2.
  destruct (TransportGCg.dkg_frame_al64 segs B lyc Sc W memc mdc cid pos HAR Hin) as (A1 & A2 & A3).
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (B1 & B2 & _).
  assert (KG : forall g, frame_addr lyc cid pos <= g < frame_addr lyc cid pos + fs_frame_bytes cid ->
    aview segs (w_H W') mem' (shadow_addr g) = aview segs (w_H W) memc (shadow_addr g)).
  { intros g Hg. apply (K2 cid pos); [exact Hin|]. unfold in_zr, shadow_addr. cbn [fst snd].
    pose proof (Z.div_mod (frame_addr lyc cid pos) 64 ltac:(lia)).
    pose proof (Z.div_mod (fs_frame_bytes cid) 64 ltac:(lia)).
    pose proof (Z.div_mod (frame_addr lyc cid pos) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (frame_addr lyc cid pos) 8 ltac:(lia)).
    pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (fs_frame_bytes cid) 8 ltac:(lia)).
    pose proof (Z.div_mod g 8 ltac:(lia)). pose proof (Z.mod_pos_bound g 8 ltac:(lia)). lia. }
  split; [|split; [|split; [|exact (conj R4 (conj R5 R6))]]].
  - exact HV.
  - intros x Hx. destruct (R2 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
    change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x) in Hs |- *.
    rewrite (KG x ltac:(lia)). exact Hs.
  - intros s Hs.
    assert (Hhi : (frame_addr lyc cid pos + fs_frame_bytes cid) mod 64 = 0)
      by (rewrite Z.add_mod, A1, A2 by lia; reflexivity).
    destruct (trans_hull_in (frame_addr lyc cid pos) (frame_addr lyc cid pos + fs_frame_bytes cid) q n s
      A1 Hhi F1 F2 Hn Hs) as (g & Hg8 & Hg1 & Hg2 & ->).
    rewrite (KG g ltac:(lia)). exact (R3 _ Hs).
Qed.

(* The placement at a later state (ly2, S2) whose blocks and frames contain the entry's (frames Sc a sub-list of
   frames S2) at the same addresses and the same machine stack: each byte of the range kept or a byte of G (G is
   visible at every memory), the entry frames' shadow bytes kept. *)
Lemma odnc_src_carry : AR_laws segs B ->
  forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 q n,
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  (forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2)) ->
  (forall f, In f (frames Sc) -> In f (frames S2)) ->
  (forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos) ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc ->
  (forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a \/ inG TG.G_HARNESS_B a) ->
  (forall cid pos s, In (cid, pos) (frames Sc) ->
     in_zr s (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8) ->
     aview segs (w_H W2) mem2 s = aview segs (w_H W) memc s) ->
  trans_src_ok B lyc Sc W memc q n -> 0 <= n -> trans_src_ok B ly2 S2 W2 mem2 q n.
Proof.
  intros LAWS lyc Sc W memc mdc ly2 S2 W2 mem2 md2 q n HAR HAR2 Hbl Hfr Hfa Elo Ehi KV KS Hs Hn.
  destruct Hs as [(bA & nA & Hin & B1 & B2) | (HL & Hrd)].
  - left. exists bA, nA. split; [exact (Hbl _ Hin) | lia].
  - assert (HV : forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a <> None).
    { intros a Ha. destruct (KV a Ha) as [E | G].
      - rewrite E. exact (proj1 Hrd a Ha).
      - exact (gx_rw_vis segs TG.G_HARNESS_B a G_HARNESS_B_rw G (w_H W2) mem2). }
    assert (Hrd2 : decode_rd_ok W2 mem2 q n).
    { pose proof Hrd as (R1 & R2 & R3 & R4 & R5 & R6).
      destruct HL as [HF | [(_ & Hsh) | [(S1 & S3) | (_ & Hsh)]]].
      - exact (odnc_rd_fake LAWS lyc Sc W W2 memc mem2 mdc q n HAR HF Hrd Hn HV KS).
      - destruct (Hsh ly2 S2 W2 mem2 md2 HAR2) as [Ha Hh].
        exact (conj HV (conj Ha (conj Hh (conj R4 (conj R5 R6))))).
      - destruct (stack_zshadow_ra_ge0 B ly2 S2 W2 mem2 md2 q n HAR2 Hn ltac:(rewrite Elo; lia)
                    ltac:(rewrite Ehi; lia)) as [Ha Hh].
        exact (conj HV (conj Ha (conj Hh (conj R4 (conj R5 R6))))).
      - destruct (Hsh ly2 S2 W2 mem2 md2 HAR2) as [Ha Hh].
        exact (conj HV (conj Ha (conj Hh (conj R4 (conj R5 R6))))). }
    exact (trans_src_ok_inner B lyc Sc W memc ly2 S2 W2 mem2 q n Hbl Hfr Hfa Elo Ehi Hrd2 (or_intror (conj HL Hrd))).
Qed.

(* The current heap frame at a later state: its bytes are not bytes of G (trans_tf_off_g), so they are kept; its
   placement carried; its window moved to the callee's. *)
Lemma odnc_tframe : AR_laws segs B -> trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 (regs regsC : bvmap 5 word) K K'
    (E : Z -> Prop) (TF : option TI.tframe),
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  (forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2)) ->
  (forall f, In f (frames Sc) -> In f (frames S2)) ->
  (forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos) ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc ->
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 mem2 (spZ regs - K) (spZ regs) E ->
  (forall a, E a -> inG TG.G_HARNESS_B a) ->
  spZ regs - K <= spZ regsC - K' -> spZ regsC <= spZ regs ->
  trans_tf_off_g TF ->
  trans_tframe_at B lyc Sc W memc regs K TF ->
  trans_tframe_at B ly2 S2 W2 mem2 regsC K' TF.
Proof.
  intros LAWS HRU HRE lyc Sc W memc mdc ly2 S2 W2 mem2 md2 regs regsC K K' E TF HAR HAR2 Hbl Hfr Hfa Elo Ehi HK HEG
    Hw1 Hw2 HnoG HT.
  destruct TF as [fr|]; [|exact I].
  destruct HT as (Ha0 & Hg8 & Hsrc & Hoff).
  assert (Hn0 : 0 <= Z.of_nat (length (TI.tf_bytes fr))) by lia.
  pose proof (odnc_kv LAWS HRU HRE lyc Sc W memc mdc W2 mem2 (spZ regs - K) (spZ regs) E (TI.tf_addr fr)
    (Z.of_nat (length (TI.tf_bytes fr))) HAR HK HEG Hoff Hsrc) as KVG.
  assert (KV : forall a, TI.tf_addr fr <= a < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr)) ->
    aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
  { intros a Ha. destruct (KVG a Ha) as [E1 | G1]; [exact E1|]. exfalso. exact (HnoG fr eq_refl a Ha G1). }
  pose proof (odnc_ks LAWS lyc Sc W memc mdc W2 mem2 _ _ E HAR HK HEG) as KS.
  split; [exact Ha0|]. split.
  { eapply garr8_frame; [exact Hg8|]. intros a Ha. rewrite length_map in Ha.
    apply (mbyte_of_aview segs). apply KV. exact Ha. }
  split; [exact (odnc_src_carry LAWS lyc Sc W memc mdc ly2 S2 W2 mem2 md2 _ _ HAR HAR2 Hbl Hfr Hfa Elo Ehi KVG KS
                   Hsrc Hn0)|].
  exact (odnc_off_win regs regsC K K' _ _ Hoff Hw1 Hw2).
Qed.

(* ------------------------------------------------------------------ *)
(* 5. The own frame and the notice in it                               *)
(* ------------------------------------------------------------------ *)

(* The notice's 72 bytes at F + 32, in the own class-2 frame (a frame of the call state's frames), with shadow bytes
   4 .. 12 of the frame 0: placed by decode_in_fake, visible and marked usable, their hull visible. *)
Lemma odnc_ntc_src : AR_laws segs B ->
  forall ly2 S2 (W2 : world segs) mem2 md2 F pos,
  @AR rc segs B ly2 S2 W2 mem2 md2 -> In (ONDATA_CID, pos) (frames S2) ->
  frame_addr ly2 ONDATA_CID pos = F -> 4096 <= F -> F mod 64 = 0 -> F + 256 <= alloc_ceiling -> in_app F 256 ->
  (forall i, 4 <= i < 13 -> aview segs (w_H W2) mem2 (SHADOW_OFF + F / 8 + i) = Some 0) ->
  trans_src_ok B ly2 S2 W2 mem2 (F + 32) NTC_SIZE.
Proof.
  intros LAWS ly2 S2 W2 mem2 md2 F pos HAR Hin EF HF0 HF64 HFc HFapp ZS.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 ONDATA_CID pos HAR Hin) as (_ & _ & HFb & HFsh).
  rewrite EF in HFb, HFsh. change (fs_frame_bytes ONDATA_CID) with 256 in HFb.
  change (fs_frame_bytes ONDATA_CID / 8) with 32 in HFsh. change (shadow_addr F) with (SHADOW_OFF + F / 8) in HFsh.
  assert (DFm8 : F mod 8 = 0).
  { pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
    replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
  right. split.
  - left. exists ONDATA_CID, pos. split; [exact Hin|]. rewrite EF. change (fs_frame_bytes ONDATA_CID) with 256.
    unfold NTC_SIZE. lia.
  - unfold decode_rd_ok, NTC_SIZE. split; [|split; [|split; [|split; [|split]]]].
    + intros a Ha. apply can_aview_vis. exact (proj1 (HFb a ltac:(lia))).
    + apply (TGNA.frame_ra_zero _ F (F + 32) 72 4 13); [lia | exact DFm8 | lia | lia | exact ZS].
    + apply (TGNA.frame_hull_vis _ F 256 (F + 32) 72); [lia | exact HF64 | reflexivity | lia | lia | lia |].
      intros i Hi. change (shadow_addr F) with (SHADOW_OFF + F / 8). apply can_aview_vis. exact (proj1 (HFsh i Hi)).
    + apply (amem_range_sub_app F 256); [exact HFapp | lia | lia | lia | lia].
    + lia.
    + lia.
Qed.

(* A data notice's store (GOT.ndata, a byte of G) is apart from the notice's 72 bytes (a frame byte is not an image
   byte), from its body (no byte at buf is a byte of G; any NB garr8 puts at p is the notice's NB0), and from the
   current heap frame (it is a byte of ondata_wr, which ondata_apart keeps off TF). *)
Lemma odnc_apart : AR_laws segs B ->
  forall ly2 S2 (W2 : world segs) mem2 md2 (TF : option TI.tframe) Bw b X F pos buf NB0,
  @AR rc segs B ly2 S2 W2 mem2 md2 -> In (ONDATA_CID, pos) (frames S2) -> frame_addr ly2 ONDATA_CID pos = F ->
  ondata_apart TF Bw b ->
  garr8 segs (mrestrict (w_H W2) mem2) (F + 32) (map DSpec.bz NB0) -> length NB0 = 72%nat ->
  TW.u_at NB0 48 8 = buf + 30 ->
  (forall x, buf <= x < buf + Z.of_nat (length b) -> ~ inG TG.G_HARNESS_B x) ->
  30 + Z.of_nat (length (DSpec.fr_body b)) <= Z.of_nat (length b) ->
  notice_apart W2 mem2 (F + 32) (ondata_ntc X b) TF X.
Proof.
  intros LAWS ly2 S2 W2 mem2 md2 TF Bw b X F pos buf NB0 HAR Hin EF Hap HNB HNBl HN48 HnoG Hlen x Hx.
  assert (HxG : inG TG.G_HARNESS_B x) by exact (notice_wr_G X _ x Hx).
  assert (Hxw : ondata_wr Bw b x).
  { unfold ondata_wr. do 9 right. exact (odnc_nwr_in X Bw b x Hx). }
  split; [|split].
  - intros Hr. apply (frm_img segs B LAWS ly2 S2 W2 mem2 md2 ONDATA_CID pos x HAR Hin);
      [rewrite EF; change (fs_frame_bytes ONDATA_CID) with 256; unfold NTC_SIZE in Hr; lia|].
    exact (trans_g_img x HxG).
  - intros NB HNB' HNBl'.
    assert (ENB : NB = NB0).
    { apply odnc_map_bz_inj. apply (odnc_garr8_eq segs _ (F + 32) _ _ HNB' HNB). rewrite !length_map, HNBl, HNBl'.
      reflexivity. }
    subst NB. rewrite HN48. unfold ondata_ntc. cbn [TI.n_body TI.n_ann]. split.
    + intros Hb. apply (HnoG x); [lia | exact HxG].
    + intros Hn. exfalso. apply Hn. reflexivity.
  - intros fr Hfr. exact (Hap x Hxw fr Hfr).
Qed.

(* TransportGFrame.v dk_kept_step_gw for a step that changes only bytes of the call's window, of the own frame of
   class ONDATA_CID (its bytes, shadow bytes, flag byte), or of G, at a current world W1 and state (ly2, S2). *)
Lemma odnc_kept_w : AR_laws segs B -> gx_ok segs B TG.G_HARNESS_B -> frame_flag_lawP segs B ->
  forall lyc Sc ly2 S2 (W W1 : world segs) memc mdc mem2 md2 memX memY slo shi pos F FL (Eo Zs : Z -> Prop),
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W1 mem2 md2 ->
  frames S2 = (ONDATA_CID, pos) :: frames Sc -> (forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2)) ->
  ly_F ly2 = ly_F lyc -> F = frame_addr lyc ONDATA_CID pos -> FL = flag_addr lyc ONDATA_CID pos ->
  alloc_ceiling <= slo -> shi <= 2 ^ 64 ->
  (forall a, Zs a -> (slo <= a < shi) \/ dkg_nf ONDATA_CID F FL a \/ inG TG.G_HARNESS_B a) ->
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W1 memX slo shi Eo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W1) memY a = aview segs (w_H W1) memX a) ->
  (forall a, apresent (w_H W1) memX a -> apresent (w_H W1) memY a) ->
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W1 memY slo shi Eo.
Proof.
  intros LAWS HG FFL lyc Sc ly2 S2 W W1 memc mdc mem2 md2 memX memY slo shi pos F FL Eo Zs HARc HAR2 Hfrs Hbl ELF EF
    EFL Hce Hshi HZ KP Hkp Hgr.
  destruct (dkg_nf_sep_gw segs B LAWS transportb_segs_low lyc Sc ly2 S2 W1 mem2 md2 ONDATA_CID pos F FL HAR2 Hfrs Hbl
    ELF EF EFL FFL) as (N1 & N2 & N3 & N4).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  apply (dk_kept_step_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc W1 memX memY slo shi Eo Zs
    HARc KP Hkp Hgr).
  - intros a Ha Hc. destruct (HZ a Ha) as [Hw | [Hn | Hg]]; [exact Hw | pose proof (N4 a Hn); lia |].
    pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B a HG Hg). unfold kLowMemEnd in *. lia.
  - intros b m i Hb Hi Ha. exfalso. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HARc Hb) as (_ & H4096 & Hbc & _).
    destruct (HZ _ Ha) as [Hw | [Hn | Hg]]; [lia | exact (N1 b m i Hb Hi Hn) |].
    destruct (HG _ Hg) as [Hi' _]. exact (blk_img segs B LAWS lyc Sc W memc mdc b m (b + i) HARc Hb ltac:(lia) Hi').
  - intros a Ha Hi HnG _ _. exfalso. pose proof (transportb_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
    destruct (HZ a Ha) as [Hw | [Hn | Hg]]; [lia | exact (N2 a Hn Hi) | exact (HnG Hg)].
  - intros cid pos' a Hin Hr Ha. exfalso.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos' HARc Hin) as (G4096 & Gce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    destruct (HZ a Ha) as [Hw | [Hn | Hg]].
    + destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
      pose proof (shadow_range_end (frame_addr lyc cid pos') (fs_frame_bytes cid) Hfs) as Hse.
      assert (Hd : (frame_addr lyc cid pos' + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
      unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
    + exact (N3 cid pos' a Hin Hr Hn).
    + destruct (HG _ Hg) as [Hi _]. pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B a HG Hg) as Hl.
      destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr.
      * exact (frm_img segs B LAWS lyc Sc W memc mdc cid pos' a HARc Hin Hr Hi).
      * pose proof (Z.div_pos (frame_addr lyc cid pos') 8 ltac:(lia) ltac:(lia)).
        unfold shadow_addr, SHADOW_OFF, kLowMemEnd in *. lia.
Qed.

End mem.
