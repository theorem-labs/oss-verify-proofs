(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 329 of its 374 lines of code are new or changed and 1879 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickEpi.v, with its module names changed; 432 of its 478 lines of code are new or changed and 328 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickAckl_kit.v, with its module paths, module names and numbers changed; 94 of its 384 lines of code are new or changed and 188 lines of the source are left out. *)
(* TickBAckl_kit: the lemmas the ack-lost piece of diginet_session_tick's image-B walk (lib/B/Prog/TickBAckl.v, the
   code 0x89524 .. 0x8962c) uses beyond the kit, all closed. Image B's twin of image A's TickAckl_kit.v, at image B's
   statement (lib/B/Prog/diginet_session_tick_cg.v tick_ack_w1, tick_ack_ntc, tick_wr), cut file (lib/B/Prog/TickCutB.v
   tick_ackl_m), world table (lib/B/Prog/TWorldB.v TMAP_B) and notice (lib/B/Prog/notice_cg.v), with the notice at
   frame + 32 (image A: frame + 256).
   rule 24: proves no function (lemmas for a piece of a walk; the walk is composed at TickCutB.v tick_holds_of).
   - the model: the world after the two g_s stores at its numeral offsets, the fields notice reads there, call_notify's
     test, and that an N_ACK_LOST notice (TCb.v notice_m, :955-957) leaves set_M_fly_on B 0 (tba_notice_ack), so
     g_fail_next is kept (tba_gfn_b0) and the run invariants hold after it (tba_runinv_b0);
   - the world after the two stores (tba_tw_w1, TWorldG.v tw_write twice at TMAP_B);
   - tba_apart: notice_apart for the N_ACK_LOST notice (it writes M.fly.on, a byte of G: lib/B/Prog/TickBKit.v
     tick_wr_G);
   - tba_ntc_at: the 72 bytes at p = frame + 32 as trans_ntc_at reads tick_ack_ntc (trans_src_ok by TickBKit.v
     trans_src_ok_fake);
   - the byte-list reads of a notice built field by field, and the readings of cells the runs left (tba_vm_kept,
     tba_vm_eqm, tba_aview_val, tba_swrap_mod). The engine's region readings are TickBKit.v's (sn_chunk0B,
     sn_chunk_valB, sn_vm_wB); the frame's addressability and shadow hull and the bytes of a store are
     lib/A/Prog/TransportGNotice.v's (image-free: frame_ra_zero, frame_hull_vis, garr8_of_put). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k YE2y AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportGFrame TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
io_send_cg set_state_cg take_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
diginet_session_tick_cg TickCutB TransportGNoticeB TickBKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGNotice.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TNotifyFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TSessFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
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
Module TSF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSessFacts.
Module LB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Bytes.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The model                                                        *)
(* ------------------------------------------------------------------ *)

(* The world after the stores of 0 at s + 212 (:436) and of stats.ack_lost + 1 at s + 18240 (:437), at the numeral
   offsets the code uses. *)
Lemma tba_w1_eq : forall Bw, length Bw = Z.to_nat TW.W_LEN ->
  tick_ack_w1 Bw =
  TW.upd (TW.upd Bw (TW.OFF_g_s + 212) (TW.put 4 0)) (TW.OFF_g_s + 18240)
    (TW.put 8 (TS0.u64 (TW.u_at Bw (TW.OFF_g_s + 18240) 8 + 1))).
Proof.
  intros Bw L. unfold tick_ack_w1, TW.set_S_stats_ack_lost, TW.set_S_inflight, TW.S_stats_ack_lost.
  rewrite rd_upd_W by wside. reflexivity.
Qed.

Lemma tba_w1_len : forall Bw, length Bw = Z.to_nat TW.W_LEN -> length (tick_ack_w1 Bw) = Z.to_nat TW.W_LEN.
Proof. intros Bw L. rewrite (tba_w1_eq Bw L). wlen. Qed.

(* The fields the arm reads after its two stores are Bw's. *)
Lemma tba_w1_facts : forall Bw, length Bw = Z.to_nat TW.W_LEN ->
  TW.S_state (tick_ack_w1 Bw) = TW.S_state Bw /\
  TW.S_inflight_counter (tick_ack_w1 Bw) = TW.S_inflight_counter Bw /\
  TW.S_inflight_retries (tick_ack_w1 Bw) = TW.S_inflight_retries Bw /\
  TW.S_notify (tick_ack_w1 Bw) = TW.S_notify Bw /\
  TW.g_fail_next (tick_ack_w1 Bw) = TW.g_fail_next Bw.
Proof.
  intros Bw L. rewrite (tba_w1_eq Bw L).
  unfold TW.S_state, TW.S_inflight_counter, TW.S_inflight_retries, TW.S_notify, TW.g_fail_next, TW.s32_at.
  rewrite !rd_upd_W by wside. repeat split; reflexivity.
Qed.

(* An N_ACK_LOST notice (TCb.v notice_m, :955-957) clears M.fly.on and changes nothing else. *)
Lemma tba_notice_ack : forall I F B (n : TI.ntc) B',
  TI.n_kind n = TC.N_ACK_LOST -> TC.notice_m I F B n = Some (B', tt) -> B' = TW.set_M_fly_on B 0.
Proof.
  intros I F B n B' K H. unfold TC.notice_m in H. rewrite K in H.
  cbn [Z.eqb TC.N_STATE TC.N_ACKED TC.N_ACK_LOST Pos.eqb] in H.
  destruct (TC.check_inflight_lost_m B n) as [[B1 u]|] eqn:E; [|discriminate H].
  apply TSF.ck_inflight_lost in E. subst B1.
  symmetry. exact (f_equal (fun o : option (list byte * unit) => match o with Some (b, _) => b | None => B' end) H).
Qed.

(* What the ack-lost arm's model gives: call_notify's test holds, notice's world, and the tail at it. *)
Lemma tba_model : forall (TF : option TI.tframe) Bw now Bw' r, length Bw = Z.to_nat TW.W_LEN ->
  tick_ackl_m timg_B TF Bw now = Some (Bw', r) ->
  TW.S_notify Bw = TI.ti_notice timg_B /\
  TC.notice_m timg_B TF (tick_ack_w1 Bw) (tick_ack_ntc Bw) = Some (TW.set_M_fly_on (tick_ack_w1 Bw) 0, tt) /\
  tick_tail timg_B TF (TW.set_M_fly_on (tick_ack_w1 Bw) 0) now = Some (Bw', r).
Proof.
  intros TF Bw now Bw' r L H. unfold tick_ackl_m, TSS.call_notify in H.
  pose proof (tba_w1_facts Bw L) as (_ & _ & _ & Enf & _). rewrite Enf in H.
  destruct (Z.eqb_spec (TW.S_notify Bw) (TI.ti_notice timg_B)) as [E|E]; [|discriminate H].
  destruct (TC.notice_m timg_B TF (tick_ack_w1 Bw) (tick_ack_ntc Bw)) as [[B0 u]|] eqn:EN; [|discriminate H].
  destruct u.
  pose proof (tba_notice_ack _ _ _ (tick_ack_ntc Bw) _ eq_refl EN) as EB0. subst B0.
  split; [exact E|]. split; [reflexivity | exact H].
Qed.

(* notice's world keeps g_fail_next: the two stores and M.fly.on miss it. *)
Lemma tba_gfn_b0 : forall Bw, length Bw = Z.to_nat TW.W_LEN ->
  TW.g_fail_next (TW.set_M_fly_on (tick_ack_w1 Bw) 0) = TW.g_fail_next Bw.
Proof.
  intros Bw L. pose proof (tba_w1_len Bw L) as L1. pose proof (tba_w1_facts Bw L) as (_ & _ & _ & _ & G1).
  rewrite <- G1. unfold TW.set_M_fly_on, TW.g_fail_next. rewrite rd_upd_W by wside. reflexivity.
Qed.

(* The run invariants after the arm: (1) is vacuous (M.fly.on is 0); (2), (4) and (5) read bytes none of the three
   stores (g_s.inflight, g_s.stats.ack_lost, M.fly.on) writes. *)
Lemma tba_runinv_b0 : forall Bw, length Bw = Z.to_nat TW.W_LEN ->
  tick_runinv Bw -> tick_runinv (TW.set_M_fly_on (tick_ack_w1 Bw) 0).
Proof.
  intros Bw L (I1 & I2 & I4 & I5a & I5b).
  assert (EQ : TW.set_M_fly_on (tick_ack_w1 Bw) 0 =
    TW.upd (TW.upd (TW.upd Bw (TW.OFF_g_s + 212) (TW.put 4 0)) (TW.OFF_g_s + 18240)
      (TW.put 8 (TS0.u64 (TW.u_at Bw (TW.OFF_g_s + 18240) 8 + 1)))) TW.A_M_fly_on (TW.put 4 0))
    by (unfold TW.set_M_fly_on; rewrite (tba_w1_eq Bw L); reflexivity).
  assert (RD : forall k n, 0 <= k ->
    (k + Z.of_nat n <= TW.OFF_g_s + 212 \/ TW.OFF_g_s + 216 <= k) ->
    (k + Z.of_nat n <= TW.OFF_g_s + 18240 \/ TW.OFF_g_s + 18248 <= k) ->
    (k + Z.of_nat n <= TW.A_M_fly_on \/ TW.A_M_fly_on + 4 <= k) ->
    TW.u_at (TW.set_M_fly_on (tick_ack_w1 Bw) 0) k n = TW.u_at Bw k n).
  { intros k n Hk H1 H2 H3. rewrite EQ.
    rewrite rd_upd_W; [| wlen | unfold TW.A_M_fly_on, TW.OFF_M; lia | rewrite TWL.length_put; wnum | exact Hk |
      rewrite TWL.length_put; cbn [Z.of_nat Pos.of_succ_nat]; exact H3].
    rewrite rd_upd_W; [| wlen | wnum | rewrite TWL.length_put; wnum | exact Hk |
      rewrite TWL.length_put; cbn [Z.of_nat Pos.of_succ_nat]; lia].
    rewrite rd_upd_W; [reflexivity | exact L | wnum | rewrite TWL.length_put; wnum | exact Hk |
      rewrite TWL.length_put; cbn [Z.of_nat Pos.of_succ_nat]; lia]. }
  assert (CS : TW.OFF_g_s = 1648) by reflexivity.
  assert (CM : TW.A_M_fly_on = 96) by reflexivity.
  split; [|split; [|split; [|split]]].
  - intros Hon. exfalso. apply Hon. unfold TW.M_fly_on, TW.set_M_fly_on.
    rewrite TWL.s32_at_upd_put by (rewrite ?(tba_w1_len Bw L); wnum).
    reflexivity.
  - assert (EQd : TW.S_queued (TW.set_M_fly_on (tick_ack_w1 Bw) 0) = TW.S_queued Bw)
      by (unfold TW.S_queued, TW.A_S_queued; apply RD; cbn [Z.of_nat Pos.of_succ_nat]; lia).
    intros i Hi. rewrite EQd in Hi.
    unfold TW.S_queue_len. rewrite RD by (unfold TW.A_S_queue_len; cbn [Z.of_nat Pos.of_succ_nat]; lia).
    exact (I2 i Hi).
  - assert (EQn : TW.g_ncmd (TW.set_M_fly_on (tick_ack_w1 Bw) 0) = TW.g_ncmd Bw)
      by (unfold TW.g_ncmd, TW.OFF_g_ncmd; apply RD; cbn [Z.of_nat Pos.of_succ_nat]; lia).
    intros s Hs Hp. rewrite EQn in Hs.
    assert (Ept : TW.Cmd_st (TW.set_M_fly_on (tick_ack_w1 Bw) 0) s = TW.Cmd_st Bw s)
      by (unfold TW.Cmd_st, TW.s32_at, TW.A_Cmd_st, TW.OFF_g_cmd; f_equal; apply RD;
          cbn [Z.of_nat Pos.of_succ_nat]; lia).
    rewrite Ept in Hp.
    unfold TW.Cmd_len. rewrite RD by (unfold TW.A_Cmd_len, TW.OFF_g_cmd; cbn [Z.of_nat Pos.of_succ_nat]; lia).
    exact (I4 s Hs Hp).
  - unfold TW.S_cfg_max_cmds. rewrite RD by (unfold TW.A_S_cfg_max_cmds; cbn [Z.of_nat Pos.of_succ_nat]; lia).
    exact I5a.
  - unfold TW.S_cfg_max_body. rewrite RD by (unfold TW.A_S_cfg_max_body; cbn [Z.of_nat Pos.of_succ_nat]; lia).
    exact I5b.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. Reading a notice built field by field                            *)
(* ------------------------------------------------------------------ *)

Lemma tba_u_at_app_l : forall (l1 l2 : list byte) k n, 0 <= k -> k + Z.of_nat n <= Z.of_nat (length l1) ->
  TW.u_at (l1 ++ l2) k n = TW.u_at l1 k n.
Proof.
  intros l1 l2 k n Hk Hn. unfold TW.u_at, TW.sub. f_equal.
  rewrite skipn_app. replace (Z.to_nat k - length l1)%nat with 0%nat by lia. cbn [skipn].
  rewrite firstn_app. rewrite length_skipn. replace (n - (length l1 - Z.to_nat k))%nat with 0%nat by lia.
  cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.

Lemma tba_u_at_app_r : forall (l1 l2 : list byte) k n, Z.of_nat (length l1) <= k ->
  TW.u_at (l1 ++ l2) k n = TW.u_at l2 (k - Z.of_nat (length l1)) n.
Proof.
  intros l1 l2 k n Hk. unfold TW.u_at, TW.sub. f_equal.
  rewrite skipn_app. rewrite skipn_all2 by lia. cbn [app].
  f_equal. f_equal. lia.
Qed.

Lemma tba_u_at_put_n : forall n v k, k = 0 -> TW.u_at (TW.put n v) k n = v mod 2 ^ (8 * Z.of_nat n).
Proof. intros n v k ->. apply TWL.u_at_put. Qed.

Lemma tba_swrap32_mod : forall v, - 2 ^ 31 <= v < 2 ^ 31 -> bv_swrap 32 (v mod 2 ^ 32) = v.
Proof.
  intros v Hv. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  Z.div_mod_to_equations. lia.
Qed.

Lemma tba_firstn_repeat_le : forall (x : byte) j n, (j <= n)%nat -> firstn j (repeat x n) = repeat x j.
Proof. induction j as [|j IH]; intros n H; [reflexivity |]. destruct n as [|n]; [lia |]. cbn. f_equal. apply IH. lia. Qed.

Lemma tba_skipn_repeat_sub : forall (x : byte) k n, skipn k (repeat x n) = repeat x (n - k).
Proof.
  induction k as [|k IH]; intros n; [cbn [skipn]; rewrite Nat.sub_0_r; reflexivity |].
  destruct n as [|n]; [reflexivity |]. cbn. apply IH.
Qed.

Lemma tba_ble_zeros : forall j, bytes_le_to_Z (repeat (DSpec.b8 0) j) = 0.
Proof.
  intros j. rewrite LB.bytes_le_to_Z_le_val. induction j as [|j IH]; [reflexivity |].
  cbn [repeat map LB.le_val]. rewrite IH. reflexivity.
Qed.

Lemma tba_u_at_zeros : forall n k j, 0 <= k -> k + Z.of_nat j <= Z.of_nat n ->
  TW.u_at (repeat (DSpec.b8 0) n) k j = 0.
Proof.
  intros n k j Hk Hj. unfold TW.u_at, TW.sub. rewrite tba_skipn_repeat_sub, tba_firstn_repeat_le by lia.
  apply tba_ble_zeros.
Qed.

Ltac tba_ntc_norm := rewrite ?length_app, ?TWL.length_put, ?repeat_length.
Ltac tba_ntc_field :=
  repeat (rewrite tba_u_at_app_r by (tba_ntc_norm; cbn; lia); tba_ntc_norm);
  first [ rewrite tba_u_at_zeros by (tba_ntc_norm; cbn; lia)
        | rewrite tba_u_at_app_l by (tba_ntc_norm; cbn; lia); tba_ntc_norm;
          first [ rewrite tba_u_at_zeros by (cbn; lia) | rewrite tba_u_at_put_n by (cbn; lia) | idtac ]
        | rewrite tba_u_at_put_n by (cbn; lia)
        | idtac ];
  try reflexivity.

(* The N_ACK_LOST notice of :438-440: kind 5, state, every other field 0 but counter and retry. *)
Definition tba_ack_bytes (st cnt rt : Z) : list byte :=
  TW.put 4 5 ++ TW.put 4 st ++ repeat (DSpec.b8 0) 56 ++ TW.put 4 cnt ++ TW.put 2 rt ++ repeat (DSpec.b8 0) 2.

(* ------------------------------------------------------------------ *)
(* 3. Cells the runs left, read and carried                            *)
(* ------------------------------------------------------------------ *)

(* A cell of n bytes holding v is kept by a step that keeps the views of its n bytes. *)
Lemma tba_vm_kept : forall (H H' : word -> bool) (m m' : word -> option byte) a (n : nat) v,
  val_mem tfibsegs (mrestrict H m) a n v ->
  (forall j, (j < n)%nat -> aview tfibsegs H' m' (a + Z.of_nat j) = aview tfibsegs H m (a + Z.of_nat j)) ->
  val_mem tfibsegs (mrestrict H' m') a n v.
Proof.
  intros H H' m m' a n v V K j Hj. rewrite <- (V j Hj). apply (mbyte_of_aview tfibsegs). exact (K j Hj).
Qed.

(* A cell of w bytes holds v exactly when it holds any v' equal to v modulo 2 ^ (8 w). *)
Lemma tba_vm_eqm : forall (m : word -> option byte) a (w : nat) v v',
  v mod 2 ^ (8 * Z.of_nat w) = v' mod 2 ^ (8 * Z.of_nat w) ->
  val_mem tfibsegs m a w v -> val_mem tfibsegs m a w v'.
Proof. intros m a w v v' E H k Hk. rewrite (H k Hk). unfold YO0f.le_byte. rewrite E. reflexivity. Qed.

(* A sign-extended 32-bit value has the low k <= 32 bits of the value. *)
Lemma tba_swrap_mod : forall x k, 0 <= k <= 32 -> bv_swrap 32 x mod 2 ^ k = x mod 2 ^ k.
Proof.
  intros x k Hk. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  rewrite (Z.mod_eq (x + 2 ^ 31) (2 ^ 32)) by lia.
  replace (x + 2 ^ 31 - 2 ^ 32 * ((x + 2 ^ 31) / 2 ^ 32) - 2 ^ 31)
    with (x + (- (2 ^ (32 - k) * ((x + 2 ^ 31) / 2 ^ 32))) * 2 ^ k).
  - apply Z.mod_add. apply Z.pow_nonzero; lia.
  - replace (2 ^ 32) with (2 ^ (32 - k) * 2 ^ k) at 2 by (rewrite <- Z.pow_add_r by lia; f_equal; lia). ring.
Qed.

(* A cell of n bytes holding v, read byte by byte through the view. *)
Lemma tba_aview_val : forall (H : word -> bool) (m : word -> option byte) a (n : nat) v,
  val_mem tfibsegs (mrestrict H m) a n v ->
  forall j, (j < n)%nat -> aview tfibsegs H m (a + Z.of_nat j) = Some (YO0f.le_byte v n j).
Proof.
  intros H m a n v V j Hj. unfold aview. rewrite (V j Hj). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small.
  unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

(* The world relation after the stores of 0 at s + 212 and of stats.ack_lost + 1 at s + 18240 (TWorldG.v tw_write,
   twice, at TMAP_B). *)
Lemma tba_tw_w1 : forall (rd rd' : Z -> option Z) Bw, length Bw = Z.to_nat TW.W_LEN ->
  tw_at TMAP_B rd Bw ->
  (forall j, (j < 4)%nat -> rd' (TB_g_s + 212 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall j, (j < 8)%nat -> rd' (TB_g_s + 18240 + Z.of_nat j) =
     Some (YO0f.le_byte (TS0.u64 (TW.u_at Bw (TW.OFF_g_s + 18240) 8 + 1)) 8 j)) ->
  (forall x, tw_in TMAP_B x -> ~ (TB_g_s + 212 <= x < TB_g_s + 216) -> ~ (TB_g_s + 18240 <= x < TB_g_s + 18248) ->
     rd' x = rd x) ->
  tw_at TMAP_B rd' (tick_ack_w1 Bw).
Proof.
  intros rd rd' Bw L Hat HI HA HO.
  set (rdm := fun x => if ((TB_g_s + 18240 <=? x) && (x <? TB_g_s + 18248))%bool then rd x else rd' x).
  assert (H1 : tw_at TMAP_B rdm (TW.upd Bw (TW.OFF_g_s + 212) (TW.put 4 0))).
  { apply (tw_write TMAP_B rd rdm Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 212 4 0 TMAP_B_ok Hat TMAP_B_g_s);
      [lia | unfold TW.SZ_g_s; lia | |].
    - intros j Hj. unfold rdm.
      assert (Hb : ((TB_g_s + 18240 <=? TB_g_s + 212 + Z.of_nat j) && (TB_g_s + 212 + Z.of_nat j <? TB_g_s + 18248))%bool
        = false) by (apply andb_false_iff; left; apply Z.leb_gt; lia).
      rewrite Hb. exact (HI j Hj).
    - intros x Hx Hn. unfold rdm.
      destruct ((TB_g_s + 18240 <=? x) && (x <? TB_g_s + 18248))%bool eqn:Eb; [reflexivity|].
      apply andb_false_iff in Eb.
      apply HO; [exact Hx | lia |].
      destruct Eb as [Eb | Eb]; [apply Z.leb_gt in Eb | apply Z.ltb_ge in Eb]; lia. }
  rewrite (tba_w1_eq Bw L).
  apply (tw_write TMAP_B rdm rd' _ TW.OFF_g_s TB_g_s TW.SZ_g_s 18240 8 _ TMAP_B_ok H1 TMAP_B_g_s);
    [lia | unfold TW.SZ_g_s; lia | |].
  - intros j Hj. exact (HA j Hj).
  - intros x Hx Hn. unfold rdm.
    destruct ((TB_g_s + 18240 <=? x) && (x <? TB_g_s + 18248))%bool eqn:Eb; [|reflexivity].
    apply andb_true_iff in Eb. destruct Eb as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    exfalso. apply Hn. cbn [Z.of_nat Pos.of_succ_nat]. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The notice at frame + 32, its stores, and the current frame      *)
(* ------------------------------------------------------------------ *)

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Local Abbreviation segs := tfibsegs.

(* The 72 bytes at p: the stores of 5 and the state (4 bytes each), the memset's 64 zeros at p + 8, the counter
   (4 bytes) and the retry (2 bytes). *)
Lemma tba_nb : forall (H : word -> bool) (m : word -> option byte) p st cnt rt,
  val_mem segs (mrestrict H m) p 4 5 ->
  val_mem segs (mrestrict H m) (p + 4) 4 st ->
  (forall a, p + 8 <= a < p + 64 -> aview segs H m a = Some 0) ->
  val_mem segs (mrestrict H m) (p + 64) 4 cnt ->
  val_mem segs (mrestrict H m) (p + 68) 2 rt ->
  (forall a, p + 70 <= a < p + 72 -> aview segs H m a = Some 0) ->
  garr8 segs (mrestrict H m) p (map DSpec.bz (tba_ack_bytes st cnt rt)).
Proof.
  intros H m p st cnt rt V0 V4 Z8 V64 V68 Z70.
  assert (GZ : forall q n, (forall a, q <= a < q + Z.of_nat n -> aview segs H m a = Some 0) ->
    garr8 segs (mrestrict H m) q (map DSpec.bz (repeat (DSpec.b8 0) n))).
  { intros q n Hz. rewrite map_repeat. change (DSpec.bz (DSpec.b8 0)) with 0.
    apply garr8_zeros. intros a Ha.
    pose proof (Hz a ltac:(lia)) as Za. unfold aview in Za.
    destruct (YP09.mbyte segs (mrestrict H m) a) as [b|] eqn:Eb; [|discriminate Za].
    cbn in Za. injection Za as Hb. f_equal. apply bv_eq. rewrite Hb. reflexivity. }
  unfold tba_ack_bytes. rewrite !map_app.
  apply garr8_app. split; [exact (TGNA.garr8_of_put segs _ _ 4 5 V0) |].
  rewrite length_map, TWL.length_put. replace (p + Z.of_nat 4) with (p + 4) by lia.
  apply garr8_app. split; [exact (TGNA.garr8_of_put segs _ _ 4 st V4) |].
  rewrite length_map, TWL.length_put. replace (p + 4 + Z.of_nat 4) with (p + 8) by lia.
  apply garr8_app. split; [apply GZ; intros a Ha; apply Z8; lia |].
  rewrite length_map, repeat_length. replace (p + 8 + Z.of_nat 56) with (p + 64) by lia.
  apply garr8_app. split; [exact (TGNA.garr8_of_put segs _ _ 4 cnt V64) |].
  rewrite length_map, TWL.length_put. replace (p + 64 + Z.of_nat 4) with (p + 68) by lia.
  apply garr8_app. split; [exact (TGNA.garr8_of_put segs _ _ 2 rt V68) |].
  rewrite length_map, TWL.length_put. replace (p + 68 + Z.of_nat 2) with (p + 70) by lia.
  apply GZ. intros a Ha. apply Z70. lia.
Qed.

(* The notice at p = F + 32, as notice's statement reads it (check_state_data_cg.v trans_ntc_at). *)
Lemma tba_ntc_at : forall lyc S2 (W : world segs) memN mdN (regsC : bvmap 5 word) Bw F pos,
  AR_laws segs B -> @AR rc segs B lyc S2 W memN mdN -> In (TICK_CID, pos) (frames S2) ->
  F = frame_addr lyc TICK_CID pos -> 4096 <= F -> F mod 64 = 0 -> F + TICK_FBYTES <= alloc_ceiling ->
  in_app F TICK_FBYTES ->
  F + TICK_FBYTES <= spZ regsC - NOTICE_STK ->
  (forall i, 4 <= i < 13 -> aview segs (w_H W) memN (SHADOW_OFF + F / 8 + i) = Some 0) ->
  garr8 segs (mrestrict (w_H W) memN) (F + 32)
    (map DSpec.bz (tba_ack_bytes (TW.S_state (tick_ack_w1 Bw)) (TW.S_inflight_counter (tick_ack_w1 Bw))
       (DSpec.u16 (TW.S_inflight_retries (tick_ack_w1 Bw))))) ->
  trans_ntc_at B lyc S2 W memN regsC NOTICE_STK (F + 32) (tick_ack_ntc Bw).
Proof.
  intros lyc S2 W memN mdN regsC Bw F pos LAWS HAR Hin EF HF0 HF64 HFc HFapp Hwin ZS HNB.
  change TICK_FBYTES with 2048 in HFc, HFapp, Hwin.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (al_frames _ _ LAWS lyc S2 W memN mdN TICK_CID pos HAR Hin) as (_ & _ & HFb & HFsh).
  rewrite <- EF in HFb, HFsh. change (fs_frame_bytes TICK_CID) with 2048 in HFb.
  change (fs_frame_bytes TICK_CID / 8) with 256 in HFsh. change (shadow_addr F) with (SHADOW_OFF + F / 8) in HFsh.
  assert (DFm8 : F mod 8 = 0).
  { pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
    replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
  set (st := TW.S_state (tick_ack_w1 Bw)) in *.
  set (cnt := TW.S_inflight_counter (tick_ack_w1 Bw)) in *.
  set (rt := DSpec.u16 (TW.S_inflight_retries (tick_ack_w1 Bw))) in *.
  assert (Hst : - 2 ^ 31 <= st < 2 ^ 31) by (unfold st, TW.S_state; apply TWL.s32_range).
  assert (Hcnt : 0 <= cnt < 2 ^ 32) by (unfold cnt, TW.S_inflight_counter; exact (TWL.u_at_range _ _ 4)).
  assert (Hrt : 0 <= rt < 2 ^ 16) by (unfold rt, DSpec.u16; apply Z.mod_pos_bound; lia).
  unfold trans_ntc_at.
  split; [lia|]. split; [rewrite Z.add_mod, DFm8 by lia; reflexivity|].
  split.
  { apply (trans_src_ok_fake B).
    - unfold decode_in_fake. exists TICK_CID, pos. split; [exact Hin|]. rewrite <- EF.
      change (fs_frame_bytes TICK_CID) with 2048.
      unfold NTC_SIZE. lia.
    - unfold decode_rd_ok, NTC_SIZE. split; [|split; [|split; [|split; [|split]]]].
      + intros a Ha. apply can_aview_vis. exact (proj1 (HFb a ltac:(lia))).
      + apply (TGNA.frame_ra_zero _ F (F + 32) 72 4 13); [lia | exact DFm8 | lia | lia | exact ZS].
      + apply (TGNA.frame_hull_vis _ F 2048 (F + 32) 72); [lia | exact HF64 | reflexivity | lia | lia | lia |].
        intros i Hi. change (shadow_addr F) with (SHADOW_OFF + F / 8). apply can_aview_vis. exact (proj1 (HFsh i Hi)).
      + apply (amem_range_sub_app F 2048); [exact HFapp | lia | lia | lia | lia].
      + lia.
      + lia. }
  split; [left; unfold NTC_SIZE; lia|].
  exists (tba_ack_bytes st cnt rt).
  split; [exact HNB|].
  unfold tick_ack_ntc. fold st cnt. fold rt.
  cbn [TI.n_kind TI.n_state TI.n_old TI.n_reason TI.n_pers TI.n_mac_offset TI.n_body_len TI.n_counter TI.n_retry
    TI.n_body TI.n_ann length].
  unfold tba_ack_bytes, TW.s32_at.
  assert (Z0 : TW.u_at (TW.put 4 5 ++ TW.put 4 st ++ repeat (DSpec.b8 0) 56 ++ TW.put 4 cnt ++ TW.put 2 rt ++
    repeat (DSpec.b8 0) 2) 48 8 = 0) by tba_ntc_field.
  rewrite Z0.
  split; [tba_ntc_norm; reflexivity |].
  split; [tba_ntc_field |].
  split; [tba_ntc_field; apply tba_swrap32_mod; exact Hst |].
  split; [tba_ntc_field |].
  split; [tba_ntc_field |].
  split; [tba_ntc_field |].
  split; [tba_ntc_field |].
  split; [tba_ntc_field |].
  split; [tba_ntc_field; apply Z.mod_small; exact Hcnt |].
  split; [tba_ntc_field; apply Z.mod_small; cbn; lia |].
  split; [apply garr8_nil |].
  split; [exact (trans_src_ok_null B lyc S2 W memN) |].
  split; [left; lia |].
  tba_ntc_field.
Qed.

(* notice's stores (an N_ACK_LOST notice: M.fly.on, a byte of G) are apart from the notice's own bytes (a frame is
   not image), from its empty body, and from TF (tick_apart: they are bytes of tick_wr). *)
Lemma tba_apart : forall lyc S2 (W2 : world segs) mem2 md2 (W : world segs) memN (TF : option TI.tframe) Bw F pos,
  AR_laws segs B -> @AR rc segs B lyc S2 W2 mem2 md2 -> In (TICK_CID, pos) (frames S2) ->
  F = frame_addr lyc TICK_CID pos -> tick_apart TF Bw ->
  notice_apart W memN (F + 32) (tick_ack_ntc Bw) TF (tick_ack_w1 Bw).
Proof.
  intros lyc S2 W2 mem2 md2 W memN TF Bw F pos LAWS HAR Hin EF Hap x Hx.
  assert (Hw : tick_wr Bw x) by (do 15 right; left; exact Hx).
  split; [|split].
  - intros Hr. apply (frm_img segs B LAWS lyc S2 W2 mem2 md2 TICK_CID pos x HAR Hin);
      [rewrite <- EF; change (fs_frame_bytes TICK_CID) with 2048; unfold NTC_SIZE in Hr; lia|].
    exact (trans_g_img x (tick_wr_G Bw x Hw)).
  - intros NB _ _. split.
    + unfold tick_ack_ntc. cbn [TI.n_body length Z.of_nat]. lia.
    + intros Hn. exfalso. apply Hn. reflexivity.
  - intros fr Hfr. exact (Hap x Hw fr Hfr).
Qed.

End k.
