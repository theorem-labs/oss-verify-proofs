(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths and module names changed; 275 of its 337 lines of code are new or changed and 1077 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/DgnBcLoopCall.v, with its module paths and module names changed; 244 of its 307 lines of code are new or changed and 274 lines of the source are left out. *)
(* SrxData: the on_data arm of the image-A walk of diginet_session_rx, Theorem srx_data_ok : srx_data_stmt (SrxCut.v),
   code +0x44c .. +0x45c (0x879e0 .. 0x879f0).

   What the code does. +0x44c `addi a0, s4, 0`: a0 := s; +0x450 `addi a1, s6, 0`: a1 := f = F + 32; +0x454
   `addi a2, s3, 0`: a2 := now; +0x458 `jal on_data`: ra := the address of +0x45c, pc := 0x888d0; +0x45c `j +0x480`:
   to the tick cut. No store, no load, no instrumented access, no error path.

   The machine part is SrxAnn.v's with on_data_cg.v transport_on_data_cg for on_announce's contract (SrxArmKit.v
   srxa_dframe, srxa_tframe_call, srxa_after; every byte on_data stores is a byte of G: srxa_ondata_G). On this arm h.cmd
   is DIGINET_CMD_DATA, so the path to the closed test is srx_pre_acc's first case: the desk known, the source its MAC
   and the world Bx = Bw.

   on_data's premise (3), the OW.dn body range guarded by ondata_dup and fr_keepalive at on_data's world srx_w1 Bw now,
   comes from srx_ndata (SrxCut.v, at Bw and SRX_STK), whose eight guards hold on this path. The two stores of
   srx_w1 (g_s.stats.rx_frames, g_s.last_rx_us) touch neither S_desk_counter_valid, S_desk_counter nor GOT.ndata
   (srxd_w1_dcv, srxd_w1_dc, srxd_w1_got); OW_dn_body at an index g reads [OW + 256 + 24 g, + 8), which they miss when
   g >= 0 (srxd_w1_dn). A negative GOT.ndata would put that read on them (g = -2656 reads last_rx_us), so the arm
   takes 0 <= GOT_ndata Bw from the model (srxd_g0): on the path the guard leaves (not a duplicate, not a keepalive),
   on_data_m ends in call_notify of a data notice, whose check_state_data_m returns None when GOT.ndata < 0, and the
   stores before it (send_control_m: TOpsKeep.v send_control_m_keeps; ondata_w2, ondata_w3) keep GOT.ndata. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg send_control_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_body_check_cg take_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_wake_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import session_lost_cg on_ack_cg on_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_personality_from_name_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg on_announce_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_frame_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_tick_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require diginet_mac_is_digidesign_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_rx_cg SrxCut SrxArmKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess TWorldLemmas TOpsKeep.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TNotifyFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
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
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TOK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOpsKeep.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The model: the fields on_data's premise (3) reads                *)
(* ------------------------------------------------------------------ *)

(* srx_w1's two stores, g_s.stats.rx_frames (s + 18152) and g_s.last_rx_us (s + 176), keep the world's length and
   miss g_s.desk_counter_valid (s + 168), g_s.desk_counter (s + 164), GOT.ndata, and OW.dn[g] for g >= 0. *)
Lemma srxd_w1_len : forall Bw now, length Bw = Z.to_nat TW.W_LEN -> length (srx_w1 Bw now) = Z.to_nat TW.W_LEN.
Proof. intros Bw now L. unfold srx_w1, TW.set_S_last_rx_us, TW.set_S_stats_rx_frames. wlen. Qed.

Lemma srxd_w1_got : forall Bw now, length Bw = Z.to_nat TW.W_LEN -> TW.GOT_ndata (srx_w1 Bw now) = TW.GOT_ndata Bw.
Proof.
  intros Bw now L. unfold srx_w1, TW.set_S_last_rx_us, TW.set_S_stats_rx_frames, TW.GOT_ndata.
  rewrite !rd32_upd_W by wside. reflexivity.
Qed.

Lemma srxd_w1_dcv : forall Bw now, length Bw = Z.to_nat TW.W_LEN ->
  TW.S_desk_counter_valid (srx_w1 Bw now) = TW.S_desk_counter_valid Bw.
Proof.
  intros Bw now L. unfold srx_w1, TW.set_S_last_rx_us, TW.set_S_stats_rx_frames, TW.S_desk_counter_valid.
  rewrite !rd32_upd_W by wside. reflexivity.
Qed.

Lemma srxd_w1_dc : forall Bw now, length Bw = Z.to_nat TW.W_LEN ->
  TW.S_desk_counter (srx_w1 Bw now) = TW.S_desk_counter Bw.
Proof.
  intros Bw now L. unfold srx_w1, TW.set_S_last_rx_us, TW.set_S_stats_rx_frames, TW.S_desk_counter.
  rewrite !rd_upd_W by wside. reflexivity.
Qed.

(* The read [OW + 256 + 24 g, + 8) lies above both stores (OW follows g_s). Each offset comparison runs lia without
   the length hypothesis, whose Z.to_nat W_LEN lia would expand to a unary nat. *)
Lemma srxd_w1_dn : forall Bw now g, length Bw = Z.to_nat TW.W_LEN -> 0 <= g ->
  TC.OW_dn_body (srx_w1 Bw now) g = TC.OW_dn_body Bw g.
Proof.
  intros Bw now g L Hg.
  assert (G1 : 0 <= TC.A_OW_dn_body g) by (clear L; unfold TC.A_OW_dn_body, TW.OFF_OW; lia).
  assert (G2 : TW.A_S_last_rx_us + 8 <= TC.A_OW_dn_body g)
    by (clear L; unfold TC.A_OW_dn_body, TW.OFF_OW, TW.A_S_last_rx_us, TW.OFF_g_s; lia).
  assert (G3 : TW.A_S_stats_rx_frames + 8 <= TC.A_OW_dn_body g)
    by (clear L; unfold TC.A_OW_dn_body, TW.OFF_OW, TW.A_S_stats_rx_frames, TW.OFF_g_s; lia).
  unfold srx_w1, TW.set_S_last_rx_us, TW.set_S_stats_rx_frames, TC.OW_dn_body.
  rewrite rd_upd_W; [| wlen | wnum | wnum | exact G1 | right; rewrite TWL.length_put; exact G2].
  rewrite rd_upd_W; [reflexivity | exact L | wnum | wnum | exact G1 | right; rewrite TWL.length_put; exact G3].
Qed.

Lemma srxd_dup : forall Bw b now, length Bw = Z.to_nat TW.W_LEN -> ondata_dup (srx_w1 Bw now) b = ondata_dup Bw b.
Proof. intros Bw b now L. unfold ondata_dup. rewrite (srxd_w1_dcv Bw now L), (srxd_w1_dc Bw now L). reflexivity. Qed.

(* on_data's stores after send_control and before the duplicate test (ondata_w2: stats.tx_acks, stats.rx_data,
   stats.rx_desk_retries, backoff_until_us) and before the notice (ondata_w3: desk_counter, desk_counter_valid). *)
Lemma srxd_w2_len : forall B1 b r now, length B1 = Z.to_nat TW.W_LEN ->
  length (ondata_w2 B1 b r now) = Z.to_nat TW.W_LEN.
Proof.
  intros B1 b r now L. unfold ondata_w2.
  destruct (r =? 0); destruct (DSpec.fr_retry b =? 0); cbv beta iota zeta;
    unfold TW.set_S_stats_tx_acks, TW.set_S_stats_rx_data, TW.set_S_stats_rx_desk_retries,
      TW.set_S_backoff_until_us; wlen.
Qed.

Lemma srxd_w2_keep : forall B1 b r now, length B1 = Z.to_nat TW.W_LEN ->
  TW.S_desk_counter_valid (ondata_w2 B1 b r now) = TW.S_desk_counter_valid B1 /\
  TW.S_desk_counter (ondata_w2 B1 b r now) = TW.S_desk_counter B1 /\
  TW.GOT_ndata (ondata_w2 B1 b r now) = TW.GOT_ndata B1.
Proof.
  intros B1 b r now L. unfold ondata_w2.
  destruct (r =? 0); destruct (DSpec.fr_retry b =? 0); cbv beta iota zeta;
    unfold TW.set_S_stats_tx_acks, TW.set_S_stats_rx_data, TW.set_S_stats_rx_desk_retries,
      TW.set_S_backoff_until_us, TW.S_desk_counter_valid, TW.S_desk_counter, TW.GOT_ndata;
    (split; [|split]); rewrite ?rd32_upd_W, ?rd_upd_W by wside; reflexivity.
Qed.

Lemma srxd_w3_got : forall X b, length X = Z.to_nat TW.W_LEN -> TW.GOT_ndata (ondata_w3 X b) = TW.GOT_ndata X.
Proof.
  intros X b L. unfold ondata_w3, TW.set_S_desk_counter_valid, TW.set_S_desk_counter, TW.GOT_ndata.
  rewrite !rd32_upd_W by wside. reflexivity.
Qed.

(* On the path premise (3) guards (not a duplicate at on_data's world, not a keepalive), a successful on_data_m reads
   OW.dn[GOT.ndata] through check_state_data_m, which returns None when GOT.ndata < 0; GOT.ndata there is Bw's. *)
Lemma srxd_g0 : forall (TF : option TI.tframe) Bw b now B2, length Bw = Z.to_nat TW.W_LEN ->
  TSS.on_data_m timg_A TF (srx_w1 Bw now) b now = Some (B2, tt) ->
  ondata_dup (srx_w1 Bw now) b = false -> DSpec.fr_keepalive b = false -> 0 <= TW.GOT_ndata Bw.
Proof.
  intros TF Bw b now B2 L HM Hd Hk.
  pose proof (srxd_w1_len Bw now L) as L1.
  rewrite ondata_model in HM. revert HM.
  destruct (TSS.send_control_m timg_A TF (srx_w1 Bw now) TS0.DIGINET_CMD_ACK (DSpec.fr_send b)) as [[B1 [r1 x1]]|]
    eqn:ES; intros HM; cbv beta iota in HM; [|discriminate HM].
  pose proof (TOK.send_control_m_keep timg_A TF (srx_w1 Bw now) _ _ B1 (r1, x1) L1 ES) as (LB1 & _).
  pose proof (TOK.send_control_m_keeps timg_A TF (srx_w1 Bw now) _ _ B1 (r1, x1) L1 ES)
    as (_ & _ & EG1 & EC1 & EV1 & _ & _).
  pose proof (srxd_w2_keep B1 b r1 now LB1) as (W2V & W2C & W2G).
  assert (ED : ondata_dup (ondata_w2 B1 b r1 now) b = false).
  { rewrite <- Hd. unfold ondata_dup. rewrite W2V, W2C, EV1, EC1. reflexivity. }
  rewrite ED, Hk in HM. cbv beta iota in HM.
  set (B3 := ondata_w3 (ondata_w2 B1 b r1 now) b) in *.
  unfold TSS.call_notify in HM. revert HM.
  match goal with |- (if ?c then _ else _) = _ -> _ => destruct c end; intros HM; [|discriminate HM].
  unfold TC.notice_m in HM. cbv zeta in HM.
  assert (EK : TI.n_kind (ondata_ntc B3 b) = TC.N_DATA) by reflexivity.
  rewrite EK in HM.
  replace (TC.N_DATA =? TC.N_STATE) with false in HM by reflexivity.
  replace (TC.N_DATA =? TC.N_ACKED) with false in HM by reflexivity.
  replace (TC.N_DATA =? TC.N_ACK_LOST) with false in HM by reflexivity.
  replace (TC.N_DATA =? TC.N_DESK) with false in HM by reflexivity.
  replace (TC.N_DATA =? TC.N_DATA) with true in HM by reflexivity.
  cbv beta iota in HM. revert HM.
  destruct (TC.check_state_data_m TF B3 (ondata_ntc B3 b)) as [p|] eqn:EC; intros HM; cbv beta iota in HM;
    [|discriminate HM].
  clear HM. unfold TC.check_state_data_m in EC. cbv zeta in EC. revert EC.
  match goal with |- (if ?c then _ else _) = _ -> _ => destruct c end; intros EC; [discriminate EC|]. revert EC.
  destruct (TW.GOT_ndata B3 <? 0) eqn:Eg; intros EC; [discriminate EC|].
  apply Z.ltb_ge in Eg.
  assert (E3 : TW.GOT_ndata B3 = TW.GOT_ndata Bw).
  { unfold B3. rewrite (srxd_w3_got _ b (srxd_w2_len B1 b r1 now LB1)), W2G, EG1. exact (srxd_w1_got Bw now L). }
  lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The arm                                                          *)
(* ------------------------------------------------------------------ *)

(* The return address of the call, +0x45c: `j +0x480`. *)
Definition SRXD_RET : Z := SRX_DATA + 0x10.

Section data. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma srxd_data : @srx_data_stmt fx rc B MT.
Proof.
unfold srx_data_stmt. intros TICK. unfold srx_data_at, srx_arm_at.
intros LAWS0 HCALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw' Bx pos sp1 F
  ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HRD HDF HFB Htw Hgf Hinv Hpre Hst Hafter Hcmd HREGS.
cbv beta in Hcmd.
(* h.cmd = DATA: the path to the closed test is srx_pre_acc's first case, with the world Bw *)
destruct Hpre as (Hcode & Hmac & [(Hknown & Hmemeq & EBx) | (_ & Hann & _ & _)]);
  [|rewrite Hcmd in Hann; vm_compute in Hann; discriminate Hann].
subst Bx.
pose proof LAWS0 as (HSM & HCELLS & HSC & HGU & HGE0 & HRU & HRE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGE).
pose proof HCALLS as (_ & _ & _ & _ & _ & _ & _ & _ & HDATA & _).
pose proof (srxa_win B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F HFIX)
  as (Wm & Wa & Wb & Wc & Wd & We & Wf & Wg).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & H13 & Hsp16 & Hwin0 & Hhi0 & Hnow & Hbuf & Hgb
  & Hsrcb & Howb & Hboff & Htw0 & Hgf0 & Hm & HTF0 & Htfg & Hrom0 & Hapart & Hinv0 & Hnd0 & Hc1 & Hc4 & Hc5 & Hc0
  & Hc2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as (HJ1 & He & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw).
pose proof HRD as (Hgb2 & Hsrcb2 & HTF2 & Hrom2 & Hnd2).
pose proof HREGS as ((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R27) & R21 & R22).
assert (EV0 : SRX_EV = 0) by exact srx_ev_zero.
assert (ED0 : ONDATA_EV = 0) by reflexivity.
assert (HDS : ONDATA_STK <= ONANN_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HD0 : 0 <= ONDATA_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (He0 : e = 0) by lia. subst e.
(* the model: the switch at srx_w1 Bw now is on_data's call, then the tick *)
assert (HLB : length Bw = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw0).
assert (HLs : length (srx_w1 Bw now) = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw).
unfold srx_after in Hafter. rewrite (srx_sw_data timg_A TF (srx_w1 Bw now) b now Hcmd) in Hafter.
revert Hafter.
destruct (TSS.on_data_m timg_A TF (srx_w1 Bw now) b now) as [[B2 []]|] eqn:EA; intros Hafter;
  cbv beta iota in Hafter; [|discriminate Hafter].
(* +0x44c .. +0x458: the three moves, up to the call *)
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
pose proof (srxa_entry SRX_DATA W2 regs2 mem2) as HS.
assert (HEI : img_env VAL A_LIM (srxa_E regs2)) by apply srxa_env.
assert (EE : forall n (r0 : bv 5), Z.of_nat n = bv_unsigned r0 -> ew (srxa_E regs2) n = YK11.getr regs2 r0)
  by (intros n r0 Hn; apply srxa_ew; exact Hn).
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) (srxa_E regs2) (mrestrict (w_H W2) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
paj_run_tok RUN HS HJ1 SHOK SRXA_B0.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_nil. }
lazymatch type of HS with OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ _ _ (restrict _ ?msx) =>
  set (ms1 := msx) in * end.
(* the run stores nothing; HJ1 is now the journal after it *)
lazymatch goal with HFx : frame_of ?Ex ?rsx mem2 (ms_mem ms1) |- _ =>
  assert (Emem : ms_mem ms1 = mem2) by exact (frame_of_read_only Ex rsx mem2 (ms_mem ms1) eq_refl HFx) end.
rewrite Emem in HJ1.
(* the registers at the call *)
assert (HPR : aregs_preserved regs2 (ms_regs ms1)).
{ lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msx) =>
    apply (aregs_preserved_of_st_ok sg Hh Ex ssx msx regs2 [] HS (srxa_agree regs2));
    vm_compute; reflexivity end. }
srxa_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + SRXD_RET)) Q1 ltac:(apply codeptr_val; exact HEI).
srxa_reg HS (10%bv : bv 5) (w64 SRX_S) Q10
  ltac:(cbn [sv_denot]; rewrite (EE 20%nat 20%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R20).
srxa_reg HS (11%bv : bv 5) (w64 (F + SRX_F)) Q11
  ltac:(cbn [sv_denot]; rewrite (EE 22%nat 22%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R22).
srxa_reg HS (12%bv : bv 5) (w64 now) Q12
  ltac:(cbn [sv_denot]; rewrite (EE 19%nat 19%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R19).
assert (Q2 : YK11.getr (ms_regs ms1) 2 = w64 sp1) by exact (eq_trans (HPR 2 ltac:(hnf; lia)) R2).
assert (Q3 : YK11.getr (ms_regs ms1) 3 = w64 (as_gp B))
  by exact (eq_trans (eq_trans (HPR 3 ltac:(hnf; lia)) R3) Hgp).
assert (Q4 : YK11.getr (ms_regs ms1) 4 = w64 (as_tp B))
  by exact (eq_trans (eq_trans (HPR 4 ltac:(hnf; lia)) R4) Htp).
assert (USP : spZ (ms_regs ms1) = sp1) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
assert (EBR : BASE + SRXD_RET = 555504) by (vm_compute; reflexivity).
(* the premises of on_data's contract *)
assert (Pret : YK0s.ret_ok (YK11.getr (ms_regs ms1) 1)).
{ rewrite Q1. apply (ret_ok_codeptr_v (PI := PI_transport));
    [unfold SRXD_RET, SRX_DATA, AF_diginet_session_rx; lia | reflexivity]. }
assert (Pra : 4096 <= raZ (ms_regs ms1)) by (unfold raZ; rewrite Q1, EBR, unsigned_lit_small by lia; lia).
assert (Psp16 : spZ (ms_regs ms1) mod 16 = 0) by (rewrite USP; exact Wm).
assert (Pwin1 : sp0 - STK <= spZ (ms_regs ms1) - ONDATA_STK) by (rewrite USP; lia).
assert (Pwin2 : spZ (ms_regs ms1) <= sp0) by (rewrite USP; lia).
assert (PDF : trans_dframe_at B ly2 S2 W2 mem2 (ms_regs ms1) ONDATA_STK (F + SRX_F) buf b fj)
  by exact (srxa_dframe B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs (ms_regs ms1) buf now r b fj TF
    Bw Bw' pos sp1 F ly2 S2 W2 mem2 md2 0 ONDATA_STK HFIX HCUR HRD HDF HFB Hcode USP HDS).
assert (PTF : trans_tframe_at B ly2 S2 W2 mem2 (ms_regs ms1) ONDATA_STK TF)
  by exact (srxa_tframe_call B ly2 S2 W2 mem2 regs (ms_regs ms1) SRX_STK ONDATA_STK TF HTF2
    ltac:(rewrite USP; lia) ltac:(rewrite USP; lia)).
assert (PAP : ondata_apart TF (srx_w1 Bw now) b).
{ intros x Hx. apply Hapart. do 7 right. left. exists (srx_w1 Bw now). exact Hx. }
pose proof Hinv as (PI1 & _ & PI4 & _).
(* premise (3): srx_ndata's guards hold on this path; the range is read at Bw's OW.dn and GOT.ndata *)
assert (P3 : ondata_dup (srx_w1 Bw now) b = false -> DSpec.fr_keepalive b = false ->
  trans_src_ok B ly2 S2 W2 mem2 (TC.OW_dn_body (srx_w1 Bw now) (TW.GOT_ndata (srx_w1 Bw now))) (DSpec.fr_body_len b) /\
  decode_off_win (ms_regs ms1) ONDATA_STK (TC.OW_dn_body (srx_w1 Bw now) (TW.GOT_ndata (srx_w1 Bw now)))
    (DSpec.fr_body_len b)).
{ intros Hd Hk.
  pose proof (srxd_g0 TF Bw b now B2 HLB EA Hd Hk) as Hg.
  rewrite (srxd_w1_got Bw now HLB), (srxd_w1_dn Bw now _ HLB Hg).
  rewrite (srxd_dup Bw b now HLB) in Hd.
  destruct (Hnd2 Hcode Hcmd Hmac Hknown Hmemeq Hst Hd Hk) as [Hs Hw].
  split; [exact Hs|]. unfold decode_off_win in Hw |- *. rewrite USP.
  destruct Hw as [Hw | Hw]; [left | right]; lia. }
assert (PC2 : count_cid ONDATA_CID (frames S2) + 2 < fs_frames ONDATA_CID).
{ rewrite Hfrs.
  change (count_cid ONDATA_CID ((SRX_CID, pos) :: frames Sc)) with (0 + count_cid ONDATA_CID (frames Sc)). lia. }
assert (PEV : st_nev S + (k + 0) + ONDATA_EV <= EV_MAX) by lia.
(* +0x458: the call, at the pc the contract names *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (@cfg_at fx segs (transport_sigma TS_on_data) rg mm mdx) Qx) end.
rewrite Emem.
pose proof (HDATA fx) as HDf. unfold transport_on_data_cg in HDf.
eapply SRr_bind.
{ exact (HDf STK sp0 FP ly S W0 mem0 md0 ((SRX_CID, pos) :: own) ly2 S2 W2 mem2 _ (k + 0) (ms_regs ms1)
    (F + SRX_F) buf now b fj TF (srx_w1 Bw now) B2 HJ1 Pret Pra Q3 Q4 Q10 Q11 Q12 Psp16 Pwin1 Pwin2 Hnow PDF Htw Hgf
    EA PTF Htfg Hrom2 PAP PI1 PI4 P3 PC2 PEV). }
(* +0x45c: the post of the call *)
intros W3 c3 _ HPOST.
unfold transport_ondata_post, transport_cg_post in HPOST. cbv beta in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & e3 & -> & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 & Htw3 & Hgf3).
rewrite USP in HK3.
destruct (srxa_after B MT LAWS HRU HRE MTL FFL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF
  Bw Bw' pos sp1 F ly2 S2 W2 mem2 md2 0 ly3 S3 W3 mem3 md3 e3 ONDATA_STK (ondata_wr (srx_w1 Bw now) b) HFIX HCUR HTF2
  Hrom2 ltac:(lia) ltac:(lia) HJ3 Hfr3 Hperm3 HK3 Hmo3
  ltac:(intros a Ha; do 7 right; left; exists (srx_w1 Bw now); exact Ha)
  (srxa_ondata_G (srx_w1 Bw now) b) ltac:(lia)) as (HCUR3 & HTF3 & Hrom3).
pose proof HCUR3 as (HJ3' & _).
rewrite Q1.
(* +0x45c: `j +0x480`, to the tick cut *)
pose proof (srxa_entry SRXD_RET W3 regs3 mem3) as HS3.
assert (HEI3 : img_env VAL A_LIM (srxa_E regs3)) by apply srxa_env.
assert (SHOK3 : sh_ok segs (SLit 0) (@nil shent) (srxa_E regs3) (mrestrict (w_H W3) mem3)) by constructor.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
paj_run_to_tok RUNTO HS3 HJ3' SHOK3 SRXA_B0 SRX_TICK.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_nil. }
lazymatch type of HS3 with st_ok_pi _ _ _ _ (restrict _ ?msx) => set (ms4 := msx) in * end.
lazymatch goal with HFx : frame_of ?Ex ?rsx mem3 (ms_mem ms4) |- _ =>
  assert (Emem4 : ms_mem ms4 = mem3) by exact (frame_of_read_only Ex rsx mem3 (ms_mem ms4) eq_refl HFx) end.
rewrite Emem4 in HJ3'.
assert (HPR4 : aregs_preserved regs3 (ms_regs ms4)).
{ lazymatch type of HS3 with
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
    apply (aregs_preserved_of_st_ok sg Hh Ex (abs_ss vl ssx) msx regs3 [] HS3 (srxa_agree regs3));
    vm_compute; reflexivity end. }
assert (HPall : aregs_preserved regs2 (ms_regs ms4))
  by exact (aregs_preserved_trans _ _ _ (aregs_preserved_trans _ _ _ HPR HP3) HPR4).
pmkst HS3. rewrite Emem4.
exact (TICK LAWS0 HCALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw'
  (srx_w1 Bw now) B2 pos sp1 F ly3 S3 W3 mem3 _ (0 + e3) (ms_regs ms4) HFIX (conj HJ3' (proj2 HCUR3)) HTF3 Hrom3
  Htw3 Hgf3 HLs Hinv
  (eq_trans (srx_sw_data timg_A TF (srx_w1 Bw now) b now Hcmd) EA) Hafter
  (srxa_regs_base regs regs2 (ms_regs ms4) now sp1 F HREGS HPall)).
Qed.

End data.

Theorem srx_data_ok : forall fx rc B MT, @srx_data_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@srxd_data fx rc B MT). Qed.
