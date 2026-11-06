(* TRunInv: the run invariants and the harness global g_rx kept by the model functions the ASan walks of
   diginet_session_poll (AW69) and receive (AW70) call, at ANY timg I and ANY heap frame F. Image-free: this file
   Requires nothing under lib/A, lib/B or lib/Prog.

   run_inv is AW68's srx_inv (lib/A/Prog/SrxCut.v on cold/h-rw-man-2-aw68, 9d34492e7703, lines 151-156), restated over
   TModel's names: (1) M.fly.on <> 0 -> M.fly.len <= SPEC_MAX_FRAME; (2) the lengths of s->queue[0 .. s->queued) are at
   most DIGINET_CMD_MAX_LEN; (4) the PENDING commands below g_ncmd have a length of at most SPEC_CMD_MAX; (5)
   s->cfg.max_cmds and max_body are at least 1; and the two array bounds g_ncmd <= CMDS_MAX, s->queued <= QUEUE_MAX.

   The lemmas: tick_m_run_inv, tick_m_g_rx (diginet_session_tick_m), iorecv_m_run_inv, iorecv_m_g_rx (io_recv_m),
   mrx_m_run_inv (m_rx_m), rx_m_g_rx, rx_m_run_inv (diginet_session_rx_m), poll_m_run_inv, poll_m_g_rx
   (diginet_session_poll_m). The g_rx lemmas need only the length of the world: every write the model makes is bounded
   by the model's own tests (the queue index < 512, the g_cmd and g_q indices < CMDS_MAX, the frame build's code).

   Method: rk B0 B says B has B0's length and g_rx, and run_inv B0 gives the two halves of run_inv B (ri_f: the frame
   in flight, ri_q: the queues). Each model function keeps rk from its argument world to its result world. A write
   upd X k v keeps rk when [k, k + |v|) misses the bytes run_inv and g_rx read (outR); the other writes are
   M.fly.on := 0 (rk_fly_off), the frame in flight of io_send (:883-889; rk_fly_end: M.fly.len := min (len, 1514)),
   a command marked SENT (rk_cmd_sent) and take's queue compaction (take_rk).

   Reused, TModel: TIoSendFail.v isf_sent .. isf_disp (the checks of io_send return their world) and isf_tagged
   (tagged_of answers an index below CMDS_MAX); TIoRecv.v gk_split, some_pair_inv, some_triple_inv; TPoll.v poll_cases,
   poll_drain_cases, call_recv_inv; TWorldLemmas.v the upd / u_at / s32_at laws. TSim: SimLib.v wframe, wframe_refl,
   wframe_trans, wframe_u_at, wframe_s32_at; QueueFacts.v sq_ent, sq_ent_upd, S_queue_len_ent; TakeOk.v Rq, Rq_upd,
   sq_ent_length, rq_getters. The rest of TSim (TickOk.v, TickTake*.v, RxOk.v, RxData.v, RxAck.v, RxAnn*.v,
   Deadline.v, Agree.v) proves its facts under the simulation invariant agree, which these worlds need not satisfy, so
   no statement of theirs applies here. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import
  TWorld TWorldLemmas TImg TNeed TSess0 TCb TSess TIoSendFail TIoRecv.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TPoll.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import SimLib QueueFacts TakeOk.
Import ListNotations.
Open Scope Z_scope.

Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.

(* ------------------------------------------------------------------ *)
(* The invariant                                                      *)
(* ------------------------------------------------------------------ *)

Definition run_inv (Bx : list byte) : Prop :=
  (TW.M_fly_on Bx <> 0 -> TW.M_fly_len Bx <= TC.SPEC_MAX_FRAME) /\
  (forall i, 0 <= i < TW.S_queued Bx -> TW.S_queue_len Bx i <= TS0.DIGINET_CMD_MAX_LEN) /\
  (forall s, 0 <= s < TW.g_ncmd Bx -> TW.Cmd_st Bx s = TC.PENDING -> TW.Cmd_len Bx s <= DSpec.SPEC_CMD_MAX) /\
  1 <= TW.S_cfg_max_cmds Bx /\ 1 <= TW.S_cfg_max_body Bx /\
  TW.g_ncmd Bx <= TC.CMDS_MAX /\ TW.S_queued Bx <= TC.QUEUE_MAX.

(* its first conjunct (the frame in flight) and the other six (the queues and the configuration) *)
Definition ri_f (Bx : list byte) : Prop := TW.M_fly_on Bx <> 0 -> TW.M_fly_len Bx <= TC.SPEC_MAX_FRAME.
Definition ri_q (Bx : list byte) : Prop :=
  (forall i, 0 <= i < TW.S_queued Bx -> TW.S_queue_len Bx i <= TS0.DIGINET_CMD_MAX_LEN) /\
  (forall s, 0 <= s < TW.g_ncmd Bx -> TW.Cmd_st Bx s = TC.PENDING -> TW.Cmd_len Bx s <= DSpec.SPEC_CMD_MAX) /\
  1 <= TW.S_cfg_max_cmds Bx /\ 1 <= TW.S_cfg_max_body Bx /\
  TW.g_ncmd Bx <= TC.CMDS_MAX /\ TW.S_queued Bx <= TC.QUEUE_MAX.

Lemma run_inv_f : forall B, run_inv B -> ri_f B.
Proof. intros B H. exact (proj1 H). Qed.
Lemma run_inv_q : forall B, run_inv B -> ri_q B.
Proof. intros B H. exact (proj2 H). Qed.
Lemma fq_run_inv : forall B, ri_f B -> ri_q B -> run_inv B.
Proof. intros B Hf Hq. exact (conj Hf Hq). Qed.

(* ------------------------------------------------------------------ *)
(* The relation the model functions keep                              *)
(* ------------------------------------------------------------------ *)

Definition rk (B0 B : list byte) : Prop :=
  length B = length B0 /\ g_rx B = g_rx B0 /\ (run_inv B0 -> ri_f B) /\ (run_inv B0 -> ri_q B).
(* the same without the frame in flight: what holds between the writes of io_send's frame in flight *)
Definition rq (B0 B : list byte) : Prop :=
  length B = length B0 /\ g_rx B = g_rx B0 /\ (run_inv B0 -> ri_q B).

Lemma rk_refl : forall B, rk B B.
Proof.
  intros B. split; [reflexivity|]. split; [reflexivity|].
  split; [exact (run_inv_f B) | exact (run_inv_q B)].
Qed.

Lemma rk_rq : forall B0 B, rk B0 B -> rq B0 B.
Proof. intros B0 B (L & G & _ & Q). exact (conj L (conj G Q)). Qed.

Lemma rk_trans : forall B0 B1 B2, rk B0 B1 -> rk B1 B2 -> rk B0 B2.
Proof.
  intros B0 B1 B2 (L1 & G1 & F1 & Q1) (L2 & G2 & F2 & Q2).
  split; [congruence|]. split; [congruence|].
  split; intros H; [apply F2 | apply Q2]; exact (fq_run_inv B1 (F1 H) (Q1 H)).
Qed.

Lemma rk_len : forall B0 B, rk B0 B -> length B = length B0.
Proof. intros B0 B K. exact (proj1 K). Qed.

Lemma rk_g_rx : forall B0 B, rk B0 B -> g_rx B = g_rx B0.
Proof. intros B0 B K. exact (proj1 (proj2 K)). Qed.

Lemma rk_out : forall B0 B, length B0 = Z.to_nat TW.W_LEN -> run_inv B0 -> rk B0 B ->
  length B = Z.to_nat TW.W_LEN /\ run_inv B.
Proof.
  intros B0 B HL0 R (L & _ & F & Q). split; [rewrite L; exact HL0|]. exact (fq_run_inv B (F R) (Q R)).
Qed.

(* ------------------------------------------------------------------ *)
(* The bytes run_inv and g_rx read                                    *)
(* ------------------------------------------------------------------ *)

(* M.fly.on (4 bytes at 96), M.fly.len (8 at 1640), s->cfg.max_cmds / max_body (g_s + 52 .. 60), s->queue[] and
   s->queued (g_s + 1760 .. g_s + 18148), g_cmd[] (OFF_g_cmd .. OFF_g_q), g_ncmd, g_rx: [k, k + n) misses them *)
Definition outR (k n : Z) : Prop :=
  k + n <= A_M_fly_on \/
  (A_M_fly_on + 4 <= k /\ k + n <= A_M_fly_len) \/
  (A_M_fly_len + 8 <= k /\ k + n <= A_S_cfg_max_cmds) \/
  (A_S_cfg_max_body + 4 <= k /\ k + n <= A_S_queue_bytes 0) \/
  (A_S_queued + 4 <= k /\ k + n <= OFF_g_cmd) \/
  (OFF_g_q <= k /\ k + n <= OFF_g_ncmd) \/
  (OFF_g_ncmd + 4 <= k /\ k + n <= OFF_g_rx) \/
  OFF_g_rx + 8 <= k.

(* the same without M.fly.on and M.fly.len *)
Definition outRq (k n : Z) : Prop :=
  k + n <= A_S_cfg_max_cmds \/
  (A_S_cfg_max_body + 4 <= k /\ k + n <= A_S_queue_bytes 0) \/
  (A_S_queued + 4 <= k /\ k + n <= OFF_g_cmd) \/
  (OFF_g_q <= k /\ k + n <= OFF_g_ncmd) \/
  (OFF_g_ncmd + 4 <= k /\ k + n <= OFF_g_rx) \/
  OFF_g_rx + 8 <= k.

Ltac ri_num :=
  unfold outR, outRq in *;
  unfold
    A_Cfg_ack_timeout_ms, A_Cfg_auto_wake, A_Cfg_backoff_ms, A_Cfg_desk_mac, A_Cfg_desk_mac_set,
    A_Cfg_display_gap_us, A_Cfg_host_mac, A_Cfg_keepalive_ms, A_Cfg_max_body, A_Cfg_max_cmds, A_Cfg_max_retries,
    A_Cfg_offline_ms, A_Cfg_sum_mode, A_Cfg_wake_timeout_ms, A_Cmd_bytes, A_Cmd_display, A_Cmd_key, A_Cmd_len,
    A_Cmd_st, A_GOT_acked, A_GOT_acks, A_GOT_desk, A_GOT_e2, A_GOT_e3, A_GOT_foreign, A_GOT_n, A_GOT_ndata,
    A_GOT_t_old, A_GOT_t_reason, A_GOT_t_state, A_M_backoff_until, A_M_desk, A_M_desk_counter,
    A_M_desk_counter_valid, A_M_desk_known, A_M_display_sent, A_M_e1_us, A_M_e2_acked, A_M_fail, A_M_fly_cmd,
    A_M_fly_counter, A_M_fly_frame, A_M_fly_len, A_M_fly_on, A_M_fly_retries, A_M_fly_sent, A_M_foreign,
    A_M_host_counter, A_M_last_display, A_M_last_rx, A_M_next_ka, A_M_state, A_M_wake_sent, A_OW_acked,
    A_OW_acked_counter, A_OW_acked_retry, A_OW_acks, A_OW_desk, A_OW_desk_body, A_OW_desk_off, A_OW_desk_p,
    A_OW_dn_body, A_OW_dn_counter, A_OW_dn_len, A_OW_dn_retry, A_OW_e2, A_OW_e3, A_OW_foreign, A_OW_n, A_OW_ndata,
    A_OW_t_old, A_OW_t_reason, A_OW_t_state, A_S_backoff_until_us, A_S_cfg_ack_timeout_ms, A_S_cfg_auto_wake,
    A_S_cfg_backoff_ms, A_S_cfg_desk_mac, A_S_cfg_desk_mac_set, A_S_cfg_display_gap_us, A_S_cfg_host_mac,
    A_S_cfg_keepalive_ms, A_S_cfg_max_body, A_S_cfg_max_cmds, A_S_cfg_max_retries, A_S_cfg_offline_ms,
    A_S_cfg_sum_mode, A_S_cfg_wake_timeout_ms, A_S_desk_counter, A_S_desk_counter_valid, A_S_desk_known,
    A_S_desk_mac, A_S_display_sent, A_S_e1_named_us, A_S_foreign, A_S_host_counter, A_S_inflight,
    A_S_inflight_counter, A_S_inflight_frame, A_S_inflight_len, A_S_inflight_retries, A_S_inflight_sent_us,
    A_S_io_ctx, A_S_io_now_us, A_S_io_recv, A_S_io_send, A_S_last_display_us, A_S_last_rx_us,
    A_S_next_keepalive_us, A_S_notify, A_S_notify_ctx, A_S_personality, A_S_queue_bytes, A_S_queue_display,
    A_S_queue_key, A_S_queue_len, A_S_queued, A_S_state, A_S_stats_ack_lost, A_S_stats_coalesced,
    A_S_stats_refused, A_S_stats_rx_data, A_S_stats_rx_desk_retries, A_S_stats_rx_duplicates, A_S_stats_rx_frames,
    A_S_stats_rx_ignored, A_S_stats_tx_acks, A_S_stats_tx_data, A_S_stats_tx_frames, A_S_stats_tx_keepalives,
    A_S_stats_tx_retransmits, A_S_stats_tx_wakes, A_S_wake_acked, A_S_wake_sent_us, CMDS_MAX, DIGINET_ETH_HDR_LEN,
    OFF_GOT, OFF_M, OFF_OW, OFF_g_cfg, OFF_g_cmd, OFF_g_fail_next, OFF_g_last_counter, OFF_g_ncmd, OFF_g_now,
    OFF_g_nq, OFF_g_q, OFF_g_raw, OFF_g_rx, OFF_g_rx_fail, OFF_g_rx_len, OFF_g_rx_send, OFF_g_rx_times, OFF_g_s,
    QUEUE_MAX, SPEC_MAX_FRAME, S_queue_N, TRANS_MAX, W_LEN in *.

Lemma ri_wlen : forall (B0 X : list byte), length B0 = Z.to_nat W_LEN -> length X = length B0 ->
  Z.of_nat (length X) = W_LEN.
Proof. intros B0 X HL0 L. rewrite L, HL0. apply Z2Nat.id. unfold W_LEN. lia. Qed.

(* ri_q from equal reads (a PENDING command of Y is one of X) *)
Lemma ri_q_same : forall X Y,
  S_queued Y = S_queued X -> g_ncmd Y = g_ncmd X ->
  S_cfg_max_cmds Y = S_cfg_max_cmds X -> S_cfg_max_body Y = S_cfg_max_body X ->
  (forall i, 0 <= i < QUEUE_MAX -> S_queue_len Y i = S_queue_len X i) ->
  (forall s, 0 <= s < CMDS_MAX -> Cmd_st Y s = PENDING -> Cmd_st X s = PENDING) ->
  (forall s, 0 <= s < CMDS_MAX -> Cmd_len Y s = Cmd_len X s) ->
  ri_q X -> ri_q Y.
Proof.
  intros X Y E1 E2 E3 E4 E5 E6 E7 (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
  unfold ri_q. rewrite E1, E2, E3, E4.
  refine (conj _ (conj _ (conj Q3 (conj Q4 (conj Q5 Q6))))).
  - intros i Hi. rewrite E5 by lia. apply Q1. exact Hi.
  - intros s Hs Hst. rewrite E7 by lia. apply Q2; [exact Hs|]. apply E6; [lia | exact Hst].
Qed.

Lemma ri_q_upd : forall X k v, Z.of_nat (length X) = W_LEN -> 0 <= k -> k + Z.of_nat (length v) <= W_LEN ->
  outRq k (Z.of_nat (length v)) -> ri_q X -> ri_q (upd X k v).
Proof.
  intros X k v HX Hk Hl Ho Q.
  assert (Hl' : k + Z.of_nat (length v) <= Z.of_nat (length X)) by lia.
  apply (ri_q_same X (upd X k v)); [ | | | | intros i Hi | intros s Hs | intros s Hs | exact Q ].
  - unfold S_queued. apply u_at_upd_out; [exact Hk | ri_num; lia | ri_num; lia | exact Hl'].
  - unfold g_ncmd. apply u_at_upd_out; [exact Hk | ri_num; lia | ri_num; lia | exact Hl'].
  - unfold S_cfg_max_cmds. apply u_at_upd_out; [exact Hk | ri_num; lia | ri_num; lia | exact Hl'].
  - unfold S_cfg_max_body. apply u_at_upd_out; [exact Hk | ri_num; lia | ri_num; lia | exact Hl'].
  - unfold S_queue_len. apply u_at_upd_out; [exact Hk | ri_num; lia | ri_num; lia | exact Hl'].
  - unfold Cmd_st. rewrite s32_at_upd_out; [exact (fun h => h) | exact Hk | ri_num; lia | ri_num; lia | exact Hl'].
  - unfold Cmd_len. apply u_at_upd_out; [exact Hk | ri_num; lia | ri_num; lia | exact Hl'].
Qed.

Lemma rk_upd : forall B0 X k v, length B0 = Z.to_nat W_LEN -> rk B0 X -> 0 <= k ->
  k + Z.of_nat (length v) <= W_LEN -> outR k (Z.of_nat (length v)) -> rk B0 (upd X k v).
Proof.
  intros B0 X k v HL0 (L & G & F & Q) Hk Hl Ho.
  pose proof (ri_wlen B0 X HL0 L) as HX.
  assert (Hl' : k + Z.of_nat (length v) <= Z.of_nat (length X)) by lia.
  assert (Hq : outRq k (Z.of_nat (length v))) by (ri_num; lia).
  split; [rewrite length_upd by lia; exact L|].
  split; [unfold g_rx; rewrite u_at_upd_out; [exact G | exact Hk | ri_num; lia | ri_num; lia | exact Hl']|].
  split.
  - intros H0. specialize (F H0). unfold ri_f, M_fly_on, M_fly_len in *.
    rewrite s32_at_upd_out; [| exact Hk | ri_num; lia | ri_num; lia | exact Hl'].
    rewrite u_at_upd_out; [exact F | exact Hk | ri_num; lia | ri_num; lia | exact Hl'].
  - intros H0. exact (ri_q_upd X k v HX Hk Hl Hq (Q H0)).
Qed.

Lemma rq_upd : forall B0 X k v, length B0 = Z.to_nat W_LEN -> rq B0 X -> 0 <= k ->
  k + Z.of_nat (length v) <= W_LEN -> outRq k (Z.of_nat (length v)) -> rq B0 (upd X k v).
Proof.
  intros B0 X k v HL0 (L & G & Q) Hk Hl Ho.
  pose proof (ri_wlen B0 X HL0 L) as HX.
  assert (Hl' : k + Z.of_nat (length v) <= Z.of_nat (length X)) by lia.
  split; [rewrite length_upd by lia; exact L|].
  split; [unfold g_rx; rewrite u_at_upd_out; [exact G | exact Hk | ri_num; lia | ri_num; lia | exact Hl']|].
  intros H0. exact (ri_q_upd X k v HX Hk Hl Ho (Q H0)).
Qed.

(* M.fly.on := 0 (m_lost :212, notice's N_ACK_LOST :957, m_rx's ACK :337) *)
Lemma rk_fly_off : forall B0 X, length B0 = Z.to_nat W_LEN -> rk B0 X -> rk B0 (upd X A_M_fly_on (put 4 0)).
Proof.
  intros B0 X HL0 K.
  pose proof (ri_wlen B0 X HL0 (rk_len B0 X K)) as HX.
  assert (R : rq B0 (upd X A_M_fly_on (put 4 0))).
  { apply rq_upd; [exact HL0 | exact (rk_rq B0 X K) | ri_num; lia | rewrite length_put; ri_num; lia
    | rewrite length_put; ri_num; lia]. }
  destruct R as (L & G & Q). refine (conj L (conj G (conj _ Q))).
  intros _. unfold ri_f, M_fly_on. rewrite s32_at_upd_put by (ri_num; lia).
  intros C. exfalso. apply C. reflexivity.
Qed.

(* the frame in flight of io_send (fuzz_transport.c:883-889): M.fly.len := flen <= SPEC_MAX_FRAME, then M.fly.frame *)
Lemma rk_fly_end : forall B0 Y fl fr, length B0 = Z.to_nat W_LEN -> rq B0 Y -> 0 <= fl <= 1514 ->
  (length fr <= 1514)%nat -> rk B0 (upd (upd Y A_M_fly_len (put 8 fl)) A_M_fly_frame fr).
Proof.
  intros B0 Y fl fr HL0 K Hfl Hfr.
  pose proof (ri_wlen B0 Y HL0 (proj1 K)) as HY.
  assert (K1 : rq B0 (upd Y A_M_fly_len (put 8 fl))).
  { apply rq_upd; [exact HL0 | exact K | ri_num; lia | rewrite length_put; ri_num; lia
    | rewrite length_put; ri_num; lia]. }
  assert (K2 : rq B0 (upd (upd Y A_M_fly_len (put 8 fl)) A_M_fly_frame fr)).
  { apply rq_upd; [exact HL0 | exact K1 | unfold A_M_fly_frame; ri_num; lia | unfold A_M_fly_frame; ri_num; lia
    | unfold A_M_fly_frame; ri_num; lia]. }
  pose proof (ri_wlen B0 _ HL0 (proj1 K1)) as HY1.
  destruct K2 as (L & G & Q). refine (conj L (conj G (conj _ Q))).
  intros _. unfold ri_f, M_fly_len. intros _.
  rewrite u_at_upd_out by (unfold A_M_fly_frame; ri_num; lia).
  rewrite u_at_upd_put by (ri_num; lia).
  rewrite Z.mod_small by (split; [lia | apply (Z.le_lt_trans _ 1514); [lia | reflexivity]]).
  unfold SPEC_MAX_FRAME. lia.
Qed.

(* a command marked SENT (check_latest_sent, fuzz_transport.c:639) *)
Lemma rk_cmd_sent : forall B0 X s, length B0 = Z.to_nat W_LEN -> rk B0 X -> 0 <= s < CMDS_MAX ->
  rk B0 (upd X (A_Cmd_st s) (put 4 SENT)).
Proof.
  intros B0 X s HL0 (L & G & F & Q) Hs.
  pose proof (ri_wlen B0 X HL0 L) as HX.
  assert (Hl : A_Cmd_st s + Z.of_nat (length (put 4 SENT)) <= Z.of_nat (length X))
    by (rewrite length_put; ri_num; lia).
  assert (Hk : 0 <= A_Cmd_st s) by (ri_num; lia).
  split; [rewrite length_upd by lia; exact L|].
  split; [unfold g_rx; rewrite u_at_upd_out; [exact G | exact Hk | ri_num; lia | rewrite length_put; ri_num; lia
    | exact Hl]|].
  split.
  - intros H0. specialize (F H0). unfold ri_f, M_fly_on, M_fly_len in *.
    rewrite s32_at_upd_out; [| exact Hk | ri_num; lia | rewrite length_put; ri_num; lia | exact Hl].
    rewrite u_at_upd_out; [exact F | exact Hk | ri_num; lia | rewrite length_put; ri_num; lia | exact Hl].
  - intros H0. apply (ri_q_same X); [ | | | | intros i Hi | intros s' Hs' Hst | intros s' Hs' | exact (Q H0) ].
    + unfold S_queued. apply u_at_upd_out; [exact Hk | ri_num; lia | rewrite length_put; ri_num; lia | exact Hl].
    + unfold g_ncmd. apply u_at_upd_out; [exact Hk | ri_num; lia | rewrite length_put; ri_num; lia | exact Hl].
    + unfold S_cfg_max_cmds. apply u_at_upd_out; [exact Hk | ri_num; lia | rewrite length_put; ri_num; lia | exact Hl].
    + unfold S_cfg_max_body. apply u_at_upd_out; [exact Hk | ri_num; lia | rewrite length_put; ri_num; lia | exact Hl].
    + unfold S_queue_len. apply u_at_upd_out; [exact Hk | ri_num; lia | rewrite length_put; ri_num; lia | exact Hl].
    + destruct (Z.eq_dec s' s) as [->|Hne].
      * exfalso. unfold Cmd_st in Hst. rewrite s32_at_upd_put in Hst by (ri_num; lia).
        unfold SENT, PENDING in Hst. discriminate Hst.
      * unfold Cmd_st in *. rewrite s32_at_upd_out in Hst;
          [exact Hst | exact Hk | ri_num; lia | rewrite length_put; ri_num; lia | exact Hl].
    + unfold Cmd_len. apply u_at_upd_out; [exact Hk | ri_num; lia | rewrite length_put; ri_num; lia | exact Hl].
Qed.

(* ------------------------------------------------------------------ *)
(* Tactics                                                            *)
(* ------------------------------------------------------------------ *)

Ltac ri_set :=
  unfold
    set_Cfg_ack_timeout_ms, set_Cfg_auto_wake, set_Cfg_backoff_ms, set_Cfg_desk_mac, set_Cfg_desk_mac_set,
    set_Cfg_display_gap_us, set_Cfg_host_mac, set_Cfg_keepalive_ms, set_Cfg_max_body, set_Cfg_max_cmds,
    set_Cfg_max_retries, set_Cfg_offline_ms, set_Cfg_sum_mode, set_Cfg_wake_timeout_ms, set_Cmd_bytes,
    set_Cmd_display, set_Cmd_key, set_Cmd_len, set_Cmd_st, set_GOT_acked, set_GOT_acks, set_GOT_desk, set_GOT_e2,
    set_GOT_e3, set_GOT_foreign, set_GOT_n, set_GOT_ndata, set_GOT_t_old, set_GOT_t_reason, set_GOT_t_state,
    set_M_backoff_until, set_M_desk, set_M_desk_counter, set_M_desk_counter_valid, set_M_desk_known,
    set_M_display_sent, set_M_e1_us, set_M_e2_acked, set_M_fail, set_M_fly_cmd, set_M_fly_counter, set_M_fly_frame,
    set_M_fly_len, set_M_fly_on, set_M_fly_retries, set_M_fly_sent, set_M_foreign, set_M_host_counter,
    set_M_last_display, set_M_last_rx, set_M_next_ka, set_M_state, set_M_wake_sent, set_OW_acked,
    set_OW_acked_counter, set_OW_acked_retry, set_OW_acks, set_OW_desk, set_OW_desk_body, set_OW_desk_off,
    set_OW_desk_p, set_OW_dn_body, set_OW_dn_counter, set_OW_dn_len, set_OW_dn_retry, set_OW_e2, set_OW_e3,
    set_OW_foreign, set_OW_n, set_OW_ndata, set_OW_t_old, set_OW_t_reason, set_OW_t_state, set_Q_at,
    set_S_backoff_until_us, set_S_cfg_ack_timeout_ms, set_S_cfg_auto_wake, set_S_cfg_backoff_ms,
    set_S_cfg_desk_mac, set_S_cfg_desk_mac_set, set_S_cfg_display_gap_us, set_S_cfg_host_mac,
    set_S_cfg_keepalive_ms, set_S_cfg_max_body, set_S_cfg_max_cmds, set_S_cfg_max_retries, set_S_cfg_offline_ms,
    set_S_cfg_sum_mode, set_S_cfg_wake_timeout_ms, set_S_desk_counter, set_S_desk_counter_valid, set_S_desk_known,
    set_S_desk_mac, set_S_display_sent, set_S_e1_named_us, set_S_foreign, set_S_host_counter, set_S_inflight,
    set_S_inflight_counter, set_S_inflight_frame, set_S_inflight_len, set_S_inflight_retries,
    set_S_inflight_sent_us, set_S_io_ctx, set_S_io_now_us, set_S_io_recv, set_S_io_send, set_S_last_display_us,
    set_S_last_rx_us, set_S_next_keepalive_us, set_S_notify, set_S_notify_ctx, set_S_personality,
    set_S_queue_bytes, set_S_queue_display, set_S_queue_key, set_S_queue_len, set_S_queued, set_S_state,
    set_S_stats_ack_lost, set_S_stats_coalesced, set_S_stats_refused, set_S_stats_rx_data,
    set_S_stats_rx_desk_retries, set_S_stats_rx_duplicates, set_S_stats_rx_frames, set_S_stats_rx_ignored,
    set_S_stats_tx_acks, set_S_stats_tx_data, set_S_stats_tx_frames, set_S_stats_tx_keepalives,
    set_S_stats_tx_retransmits, set_S_stats_tx_wakes, set_S_wake_acked, set_S_wake_sent_us, set_g_fail_next,
    set_g_last_counter, set_g_ncmd, set_g_now, set_g_nq, set_g_raw, set_g_rx, set_g_rx_fail, set_g_rx_len,
    set_g_rx_send, set_g_rx_times in *.

Ltac ri_bools :=
  repeat match goal with
  | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
  | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
  | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
  | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
  end.

Lemma ri_fr_src_len : forall b, (length (fr_src b) <= 6)%nat.
Proof. intros b. unfold fr_src. rewrite length_firstn. lia. Qed.

Lemma ri_lib_frame_len : forall dst src send ack retry cmd ncmds body mode,
  (length dst <= 6)%nat -> (length src <= 6)%nat -> (length body <= 1484)%nat ->
  (length (lib_frame dst src send ack retry cmd ncmds body mode) <= 1514)%nat.
Proof.
  intros dst src send ack retry cmd ncmds body mode Hd Hs Hb. unfold lib_frame.
  rewrite !length_app, !length_put16, !length_put32, repeat_length. cbn [length].
  unfold frame_len. lia.
Qed.

Lemma ri_mac_len : forall B, (length (S_desk_mac B) <= 6)%nat /\ (length (S_cfg_host_mac B) <= 6)%nat.
Proof. intros B. unfold S_desk_mac, S_cfg_host_mac. split; apply length_sub_le. Qed.

(* the lengths of the values written: put, firstn, sub, fr_src and the frames the session builds *)
Ltac ri_len :=
  repeat match goal with
  | |- context [length (put ?n ?w)] => rewrite (length_put n w)
  | |- context [length (firstn ?n ?l)] => rewrite (length_firstn n l)
  | |- context [length (sub ?bs ?k ?n)] =>
      let H := fresh "Hls" in pose proof (length_sub_le bs k n) as H; revert H;
      generalize (length (sub bs k n)); intros ? ?
  | |- context [length (fr_src ?b)] =>
      let H := fresh "Hls" in pose proof (ri_fr_src_len b) as H; revert H;
      generalize (length (fr_src b)); intros ? ?
  | |- context [length (lib_frame ?d ?s ?a ?b ?c ?e ?g ?bd ?m)] =>
      let H := fresh "Hls" in
      assert (H : (length (lib_frame d s a b c e g bd m) <= 1514)%nat)
        by (apply ri_lib_frame_len;
            first [ apply length_sub_le | apply (proj1 (ri_mac_len _)) | apply (proj2 (ri_mac_len _))
                  | assumption | (cbn [length]; lia) ]);
      revert H; generalize (length (lib_frame d s a b c e g bd m)); intros ? ?
  end.

(* a test left in a written value (gk_split stops once its hypothesis is Some _ = Some _) is split here *)
Ltac rk_side :=
  repeat (match goal with |- context [if ?c then _ else _] => let E := fresh "Es" in destruct c eqn:E end);
  ri_bools; ri_len; ri_num; lia.

Ltac rk_go :=
  lazymatch goal with
  | |- rk ?B0 (upd (upd ?Y A_M_fly_len (put 8 ?fl)) A_M_fly_frame ?fr) =>
      apply (rk_fly_end B0 Y fl fr); [assumption | rq_go | rk_side | rk_side]
  | |- rk ?B0 (upd ?X A_M_fly_on (put 4 0)) => apply (rk_fly_off B0 X); [assumption | rk_go]
  | |- rk ?B0 (upd ?X (A_Cmd_st ?s) (put 4 SENT)) => apply (rk_cmd_sent B0 X s); [assumption | rk_go | rk_side]
  | |- rk ?B0 (upd ?X ?k ?v) => apply (rk_upd B0 X k v); [assumption | rk_go | rk_side | rk_side | rk_side]
  | |- rk ?B0 (if ?c then _ else _) => let E := fresh "Ew" in destruct c eqn:E; rk_go
  | |- rk ?B0 ?X => first [ assumption | apply rk_refl ]
  end
with rq_go :=
  lazymatch goal with
  | |- rq ?B0 (upd ?X ?k ?v) => apply (rq_upd B0 X k v); [assumption | rq_go | rk_side | rk_side | rk_side]
  | |- rq ?B0 (if ?c then _ else _) => let E := fresh "Ew" in destruct c eqn:E; rq_go
  | |- rq ?B0 ?X => first [ assumption | (apply rk_rq; first [ assumption | apply rk_refl ]) ]
  end.

(* rk B0 Z from the call E : f .. = Some (Z, ..) by the lemma L of f, its argument world by rk_go *)
Ltac ri_call B0 HL0 E Z L :=
  let K := fresh "K" in
  assert (K : rk B0 Z) by (eapply (L B0 HL0); [ | exact E ]; ri_set; rk_go);
  clear E.

(* the checks of io_send return their world (TIoSendFail.v) *)
Ltac ri_chk :=
  match goal with
  | E : check_sent_frame_m _ _ = Some (?Z, _) |- _ => apply isf_sent in E; subst Z
  | E : check_ack_frame_m _ _ = Some (?Z, _) |- _ => apply isf_ack in E; subst Z
  | E : check_latest_control_m _ _ = Some (?Z, _) |- _ => apply isf_ctl in E; subst Z
  | E : check_inflight_retry_m _ _ = Some (?Z, _) |- _ => apply isf_retry in E; subst Z
  | E : check_state_wake_m _ = Some (?Z, _) |- _ => apply isf_wake in E; subst Z
  | E : check_inflight_new_m _ = Some (?Z, _) |- _ => apply isf_new in E; subst Z
  | E : check_latest_frame_m _ _ _ = Some (?Z, _) |- _ => apply isf_frame in E; subst Z
  | E : check_keepalive_due_m _ = Some (?Z, _) |- _ => apply isf_ka in E; subst Z
  | E : check_latest_display_m _ = Some (?Z, _) |- _ => apply isf_disp in E; subst Z
  end.

(* ------------------------------------------------------------------ *)
(* The harness: notice (fuzz_transport.c:937-973)                     *)
(* ------------------------------------------------------------------ *)

Lemma notice_rk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall I F B n B' u, rk B0 B -> notice_m I F B n = Some (B', u) -> rk B0 B'.
Proof.
  intros B0 HL0 I F B n B' u K H.
  unfold notice_m, check_state_online_m, check_inflight_acked_m, check_inflight_lost_m, check_state_desk_m,
    check_state_data_m in H.
  gk_split H.
  all: apply some_pair_inv in H as [<- _]; ri_set; rk_go.
Qed.

Lemma call_notify_rk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall I F B n B' u, rk B0 B -> call_notify I F B n = Some (B', u) -> rk B0 B'.
Proof.
  intros B0 HL0 I F B n B' u K H. unfold call_notify in H.
  destruct (S_notify B =? ti_notice I); [exact (notice_rk B0 HL0 I F B n B' u K H) | discriminate H].
Qed.

(* ------------------------------------------------------------------ *)
(* The harness: io_send (fuzz_transport.c:823-899)                    *)
(* ------------------------------------------------------------------ *)

(* q_remove's loop writes g_q[k], k <= i < CMDS_MAX (:619-623) *)
Lemma q_loop_rk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall fuel X s nq i k Y k', rk B0 X -> 0 <= k <= i -> q_remove_loop fuel X s nq i k = Some (Y, k') -> rk B0 Y.
Proof.
  intros B0 HL0. induction fuel as [|fuel IH]; intros X s nq i k Y k' K Hk H; cbn [q_remove_loop] in H;
    [discriminate H|].
  revert H. destruct (Z.ltb_spec i nq) as [Hi|Hi]; intros H; cbv beta iota in H;
    [|injection H as <- _; exact K].
  revert H. destruct (Z.leb_spec CMDS_MAX i) as [Hc|Hc]; intros H; cbv beta iota in H; [discriminate H|].
  revert H. destruct (Q_at X i =? s); intros H; cbv beta iota in H.
  - exact (IH X s nq (i + 1) k Y k' K ltac:(lia) H).
  - refine (IH _ s nq (i + 1) (k + 1) Y k' _ ltac:(lia) H). unfold set_Q_at. rk_go.
Qed.

Lemma q_remove_rk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall X s Y u, rk B0 X -> q_remove_m X s = Some (Y, u) -> rk B0 Y.
Proof.
  intros B0 HL0 X s Y u K H. unfold q_remove_m in H.
  match type of H with match ?x with _ => _ end = _ => destruct x as [[X1 k]|] eqn:EL end;
    cbv beta iota in H; [|discriminate H].
  injection H as <- _. pose proof (q_loop_rk B0 HL0 _ X s _ 0 0 X1 k K ltac:(lia) EL) as K1.
  unfold set_g_nq. rk_go.
Qed.

Lemma ls_loop_rk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall fuel X body len pos disp Y d, rk B0 X -> latest_sent_loop fuel X body len pos disp = Some (Y, d) ->
  rk B0 Y.
Proof.
  intros B0 HL0. induction fuel as [|fuel IH]; intros X body len pos disp Y d K H; cbn [latest_sent_loop] in H;
    [discriminate H|].
  cbv zeta in H. revert H.
  destruct (pos <? len); intros H; cbv beta iota in H; [|injection H as <- _; exact K].
  match type of H with match ?x with _ => _ end = _ => destruct x as [[X0 t]|] eqn:ET end;
    cbv beta iota in H; [|discriminate H].
  destruct t as [s|]; cbv beta iota in H; [|discriminate H].
  pose proof (isf_tagged _ _ _ _ _ ET) as Hs.
  match type of H with (if ?c then _ else _) = _ => destruct c end; cbv beta iota in H; [discriminate H|].
  match type of H with match ?x with _ => _ end = _ => destruct x as [[X2 u2]|] eqn:EQ end;
    cbv beta iota in H; [|discriminate H].
  refine (IH X2 body len _ _ Y d _ H).
  apply (q_remove_rk B0 HL0 (set_Cmd_st X s SENT) s X2 u2); [|exact EQ].
  unfold set_Cmd_st. rk_go.
Qed.

Lemma latest_sent_rk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall X body len Y d, rk B0 X -> check_latest_sent_m X body len = Some (Y, d) -> rk B0 Y.
Proof. intros B0 HL0 X body len Y d K H. unfold check_latest_sent_m in H. exact (ls_loop_rk B0 HL0 _ _ _ _ _ _ _ _ K H). Qed.

Lemma io_send_rk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall I B frame B' r, rk B0 B -> io_send_m I B frame = Some (B', r) -> rk B0 B'.
Proof.
  intros B0 HL0 I B frame B' r K H.
  assert (K0 : rk B0 (set_g_fail_next B 0)) by (unfold set_g_fail_next; rk_go).
  unfold io_send_m in H. cbv zeta in H.
  set (Bz := set_g_fail_next B 0) in *. clearbody Bz.
  gk_split H.
  all: apply some_pair_inv in H as [<- _];
       repeat first [ ri_chk | match goal with
                               | E : check_latest_sent_m _ _ _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z latest_sent_rk
                               end ];
       ri_set; rk_go.
Qed.

(* ------------------------------------------------------------------ *)
(* The harness model: m_set .. m_rx (fuzz_transport.c:196-375), io_recv (:906-929) *)
(* ------------------------------------------------------------------ *)

Lemma m_set_rk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall B st why B' u, rk B0 B -> m_set_m B st why = Some (B', u) -> rk B0 B'.
Proof.
  intros B0 HL0 B st why B' u K H. unfold m_set_m in H. gk_split H.
  all: first [apply some_pair_inv in H as [<- _] | idtac];
       ri_set; rk_go.
Qed.

Lemma m_lost_rk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall B why B' u, rk B0 B -> m_lost_m B why = Some (B', u) -> rk B0 B'.
Proof.
  intros B0 HL0 B why B' u K H. unfold m_lost_m in H.
  eapply (m_set_rk B0 HL0); [|exact H]. ri_set; rk_go.
Qed.

Lemma m_maybe_online_rk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall B B' u, rk B0 B -> m_maybe_online_m B = Some (B', u) -> rk B0 B'.
Proof.
  intros B0 HL0 B B' u K H. unfold m_maybe_online_m in H. gk_split H.
  all: first [apply some_pair_inv in H as [<- _] | idtac];
       repeat match goal with
       | E : m_set_m _ _ _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z m_set_rk
       end;
       ri_set; rk_go.
Qed.

Lemma m_tick_rk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall B B' u, rk B0 B -> m_tick_m B = Some (B', u) -> rk B0 B'.
Proof.
  intros B0 HL0 B B' u K H. unfold m_tick_m in H. gk_split H.
  all: first [apply some_pair_inv in H as [<- _] | idtac];
       repeat match goal with
       | E : m_lost_m _ _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z m_lost_rk
       end;
       ri_set; rk_go.
Qed.

Lemma m_wake_rk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall B B' r, rk B0 B -> m_wake_m B = Some (B', r) -> rk B0 B'.
Proof.
  intros B0 HL0 B B' r K H. unfold m_wake_m in H. gk_split H.
  all: first [apply some_pair_inv in H as [<- _] | idtac];
       repeat match goal with
       | E : m_set_m _ _ _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z m_set_rk
       end;
       ri_set; rk_go.
Qed.

(* m_rx (fuzz_transport.c:280-375); its export is mrx_m_run_inv below *)
Lemma m_rx_rk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall I F B n B' r, rk B0 B -> m_rx_m I F B n = Some (B', r) -> rk B0 B'.
Proof.
  intros B0 HL0 I F B n B' r K H. unfold m_rx_m in H.
  destruct F as [fr|]; [|discriminate H].
  gk_split H.
  all: first [apply some_pair_inv in H as [<- _] | idtac];
       repeat match goal with
       | E : m_set_m _ _ _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z m_set_rk
       | E : m_lost_m _ _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z m_lost_rk
       | E : m_maybe_online_m _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z m_maybe_online_rk
       | E : m_tick_m _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z m_tick_rk
       | E : m_wake_m _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z m_wake_rk
       end;
       ri_set; rk_go.
Qed.

Lemma io_recv_rk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall I F B cap B' r got, rk B0 B -> io_recv_m I F B cap = Some (B', r, got) -> rk B0 B'.
Proof.
  intros B0 HL0 I F B cap B' r got K H. unfold io_recv_m in H. gk_split H.
  all: apply some_triple_inv in H as [<- _];
       repeat match goal with
       | E : m_tick_m _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z m_tick_rk
       | E : m_rx_m _ _ _ _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z m_rx_rk
       end;
       ri_set; rk_go.
Qed.

(* ------------------------------------------------------------------ *)
(* take (diginet_session.c:353-386): the queue compaction             *)
(* ------------------------------------------------------------------ *)

Lemma ri_ql_out : forall Bc kept v x, length Bc = WN -> 0 <= kept < S_queue_N -> length v = 32%nat -> 0 <= x ->
  x <> kept -> S_queue_len (upd Bc (A_S_queue_bytes kept) v) x = S_queue_len Bc x.
Proof.
  intros Bc kept v x HB Hk Hv Hx Hne. unfold S_queue_len. apply u_at_upd_out.
  - unfold A_S_queue_bytes, OFF_g_s. lia.
  - unfold A_S_queue_len, OFF_g_s. lia.
  - rewrite Hv. unfold A_S_queue_len, A_S_queue_bytes. lia.
  - rewrite HB, Hv. unfold WN, W_LEN, A_S_queue_bytes, OFF_g_s, S_queue_N in *. lia.
Qed.

Lemma ri_ql_copy : forall Bc kept j, length Bc = WN -> 0 <= kept < S_queue_N -> 0 <= j < S_queue_N ->
  S_queue_len (upd Bc (A_S_queue_bytes kept) (sub Bc (A_S_queue_bytes j) 32)) kept = S_queue_len Bc j.
Proof.
  intros Bc kept j HB Hk Hj.
  rewrite (S_queue_len_ent _ kept ltac:(lia)), (S_queue_len_ent Bc j ltac:(lia)).
  change (sub Bc (A_S_queue_bytes j) 32) with (sq_ent Bc j).
  rewrite (sq_ent_upd Bc kept kept (sq_ent Bc j) HB Hk Hk (sq_ent_length Bc j HB Hj)).
  rewrite Z.eqb_refl. reflexivity.
Qed.

(* the length bounds of the entries below k and of the entries of X from i on, in B *)
Definition qb (X B : list byte) (k i : Z) : Prop :=
  (forall x, 0 <= x < k -> S_queue_len B x <= DIGINET_CMD_MAX_LEN) /\
  (forall x, i <= x < S_queued X -> S_queue_len B x <= DIGINET_CMD_MAX_LEN).

(* :378-379 the tail copy: entries j .. move down to kept .. *)
Lemma ri_tail : forall fuel Bc kept j Bf kf, length Bc = WN -> 0 <= kept <= j ->
  take_tail_m Bc kept j fuel = Some (Bf, kf) ->
  wframe Rq Bc Bf /\ kept <= kf <= kept + Z.of_nat fuel /\
  ((forall x, 0 <= x < kept -> S_queue_len Bc x <= DIGINET_CMD_MAX_LEN) ->
   (forall x, j <= x < j + Z.of_nat fuel -> S_queue_len Bc x <= DIGINET_CMD_MAX_LEN) ->
   forall x, 0 <= x < kf -> S_queue_len Bf x <= DIGINET_CMD_MAX_LEN).
Proof.
  induction fuel as [|f IH]; intros Bc kept j Bf kf HB Hk H; cbn [take_tail_m] in H.
  - injection H as <- <-. split; [apply wframe_refl|]. split; [lia|]. intros H1 _ x Hx. exact (H1 x Hx).
  - revert H. destruct (Z.leb_spec S_queue_N j) as [Ej|Ej]; cbn [orb]; [intros H; discriminate H|].
    destruct (Z.leb_spec S_queue_N kept) as [Ek|Ek]; cbn [orb]; [intros H; discriminate H|].
    intros H.
    set (v := sub Bc (A_S_queue_bytes j) 32) in H.
    assert (Hv : length v = 32%nat) by exact (sq_ent_length Bc j HB ltac:(lia)).
    assert (W1 : wframe Rq Bc (upd Bc (A_S_queue_bytes kept) v)) by exact (Rq_upd Bc kept v HB ltac:(lia) Hv).
    assert (HB1 : length (upd Bc (A_S_queue_bytes kept) v) = WN) by (rewrite (proj1 W1); exact HB).
    destruct (IH _ (kept + 1) (j + 1) Bf kf HB1 ltac:(lia) H) as (W2 & Hkf & Hb).
    split; [exact (wframe_trans _ _ _ _ W1 W2)|]. split; [lia|].
    intros H1 H2. apply Hb.
    + intros x Hx. destruct (Z.eq_dec x kept) as [->|Hne].
      * unfold v. rewrite (ri_ql_copy Bc kept j HB ltac:(lia) ltac:(lia)). apply H2. lia.
      * rewrite (ri_ql_out Bc kept v x HB ltac:(lia) Hv ltac:(lia) Hne). apply H1. lia.
    + intros x Hx. rewrite (ri_ql_out Bc kept v x HB ltac:(lia) Hv ltac:(lia) ltac:(lia)). apply H2. lia.
Qed.

(* the end of one turn of take's loop (:377-382): the break into the tail copy, or the next turn *)
Lemma ri_cont : forall X allow f Bc B1 i kept k1 taken1 len1 hd1 body1 (c : bool) Bf b l h t kf,
  (forall Bc' i' taken' kept' len' hd' body' Bf' b' l' h' t' kf',
     length X = WN -> wframe Rq X Bc' -> 0 <= kept' <= i' -> i' + Z.of_nat f = S_queued X ->
     take_loop_m Bc' allow i' taken' kept' len' hd' body' f = Some (Bf', (b', l', h', t', kf')) ->
     wframe Rq X Bf' /\ kept' <= kf' <= S_queued X /\
     (qb X Bc' kept' i' -> forall x, 0 <= x < kf' -> S_queue_len Bf' x <= DIGINET_CMD_MAX_LEN)) ->
  length X = WN -> wframe Rq X B1 -> kept <= k1 -> 0 <= k1 <= i + 1 -> i + 1 + Z.of_nat f = S_queued X ->
  (qb X Bc kept i -> qb X B1 k1 (i + 1)) ->
  (if c then
     match take_tail_m B1 k1 (i + 1) (Z.to_nat (S_queued B1 - (i + 1))) with
     | None => None
     | Some (B2, kept2) => Some (B2, (body1, len1, hd1, taken1, kept2))
     end
   else take_loop_m B1 allow (i + 1) taken1 k1 len1 hd1 body1 f) = Some (Bf, (b, l, h, t, kf)) ->
  wframe Rq X Bf /\ kept <= kf <= S_queued X /\
  (qb X Bc kept i -> forall x, 0 <= x < kf -> S_queue_len Bf x <= DIGINET_CMD_MAX_LEN).
Proof.
  intros X allow f Bc B1 i kept k1 taken1 len1 hd1 body1 c Bf b l h t kf IH HX W1 Hk1 Hk1' Hf Hst H.
  assert (HB1 : length B1 = WN) by (rewrite (proj1 W1); exact HX).
  destruct (rq_getters X B1 W1) as (_ & _ & Eq1).
  destruct c.
  - revert H. rewrite Eq1. replace (Z.to_nat (S_queued X - (i + 1))) with f by lia.
    destruct (take_tail_m B1 k1 (i + 1) f) as [[B2 k2]|] eqn:ET; intros H; [|discriminate H].
    apply some_pair_inv in H as [<- Hr].
    assert (Ek : k2 = kf) by exact (f_equal snd Hr). subst kf.
    destruct (ri_tail f B1 k1 (i + 1) B2 k2 HB1 ltac:(lia) ET) as (W2 & Hk2 & Hb).
    split; [exact (wframe_trans _ _ _ _ W1 W2)|]. split; [lia|].
    intros Q x Hx. destruct (Hst Q) as [Q1 Q2]. apply (Hb Q1); [|exact Hx].
    intros y Hy. apply Q2. lia.
  - destruct (IH B1 (i + 1) taken1 k1 len1 hd1 body1 Bf b l h t kf HX W1 ltac:(lia) Hf H) as (W2 & Hk2 & Hb).
    split; [exact W2|]. split; [lia|]. intros Q. exact (Hb (Hst Q)).
Qed.

(* :358-382 the loop: entries [0, kept) are kept ones, entries [i, s->queued) are X's, only s->queue[] is written *)
Lemma ri_loop : forall X allow fuel Bc i taken kept len hd body Bf b l h t kf,
  length X = WN -> wframe Rq X Bc -> 0 <= kept <= i -> i + Z.of_nat fuel = S_queued X ->
  take_loop_m Bc allow i taken kept len hd body fuel = Some (Bf, (b, l, h, t, kf)) ->
  wframe Rq X Bf /\ kept <= kf <= S_queued X /\
  (qb X Bc kept i -> forall x, 0 <= x < kf -> S_queue_len Bf x <= DIGINET_CMD_MAX_LEN).
Proof.
  intros X allow fuel. induction fuel as [|f IH]; intros Bc i taken kept len hd body Bf b l h t kf HX W Hk Hi H;
    cbn [take_loop_m] in H.
  - apply some_pair_inv in H as [<- Hr]. assert (Ek : kept = kf) by exact (f_equal snd Hr). subst kf.
    split; [exact W|]. split; [lia|]. intros (Q1 & _). exact Q1.
  - assert (HBc : length Bc = WN) by (rewrite (proj1 W); exact HX).
    cbv zeta in H. revert H.
    destruct (Z.leb_spec S_queue_N i) as [Hn|Hn]; cbv beta iota; [intros H; discriminate H|]. intros H.
    match type of H with (if ?c then _ else _) = _ => destruct c end; cbv beta iota in H; [discriminate H|].
    match type of H with (match (if ?c then _ else _) with _ => _ end) = _ => destruct c end; cbv beta iota in H.
    + refine (ri_cont X allow f Bc Bc i kept kept _ _ _ _ _ Bf b l h t kf IH HX W ltac:(lia) ltac:(lia) ltac:(lia)
                _ H).
      intros (Q1 & Q2). split; [exact Q1|]. intros x Hx. apply Q2. lia.
    + revert H. destruct (Z.eqb_spec kept i) as [Eki|Eki]; cbv beta iota; intros H.
      * subst kept.
        refine (ri_cont X allow f Bc Bc i i (i + 1) _ _ _ _ _ Bf b l h t kf IH HX W ltac:(lia) ltac:(lia)
                  ltac:(lia) _ H).
        intros (Q1 & Q2). split; [|intros x Hx; apply Q2; lia].
        intros x Hx. destruct (Z.eq_dec x i) as [->|Hne]; [apply Q2; lia | apply Q1; lia].
      * set (v := sub Bc (A_S_queue_bytes i) 32) in H.
        assert (Hv : length v = 32%nat) by exact (sq_ent_length Bc i HBc ltac:(lia)).
        assert (W1 : wframe Rq X (upd Bc (A_S_queue_bytes kept) v))
          by exact (wframe_trans _ _ _ _ W (Rq_upd Bc kept v HBc ltac:(lia) Hv)).
        refine (ri_cont X allow f Bc _ i kept (kept + 1) _ _ _ _ _ Bf b l h t kf IH HX W1 ltac:(lia) ltac:(lia)
                  ltac:(lia) _ H).
        intros (Q1 & Q2). split.
        -- intros x Hx. destruct (Z.eq_dec x kept) as [->|Hne].
           ++ unfold v. rewrite (ri_ql_copy Bc kept i HBc ltac:(lia) ltac:(lia)). apply Q2. lia.
           ++ rewrite (ri_ql_out Bc kept v x HBc ltac:(lia) Hv ltac:(lia) Hne). apply Q1. lia.
        -- intros x Hx. rewrite (ri_ql_out Bc kept v x HBc ltac:(lia) Hv ltac:(lia) ltac:(lia)). apply Q2. lia.
Qed.

Lemma take_rk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall X allow X' res, rk B0 X -> take_m X allow = Some (X', res) -> rk B0 X'.
Proof.
  intros B0 HL0 X allow X' res K H. unfold take_m in H.
  match type of H with match ?x with _ => _ end = _ => destruct x as [[Bf [[[[b l] h] t] kf]]|] eqn:EL end;
    cbv beta iota in H; [|discriminate H].
  apply some_pair_inv in H as [<- _].
  destruct K as (L & G & F & Q).
  assert (HX : length X = WN) by (unfold WN; rewrite L; exact HL0).
  assert (Hq0 : 0 <= S_queued X) by (unfold S_queued; apply u_at_nonneg).
  destruct (ri_loop X allow _ X 0 0 0 0 0 [] Bf b l h t kf HX (wframe_refl Rq X) ltac:(lia)
              ltac:(rewrite Z2Nat.id by exact Hq0; lia) EL) as (W & Hkf & Hb).
  assert (HBf : length Bf = WN) by (rewrite (proj1 W); exact HX).
  assert (HZ : Z.of_nat (length Bf) = W_LEN) by (rewrite HBf; unfold WN; apply Z2Nat.id; unfold W_LEN; lia).
  (* reads outside s->queue[] are X's *)
  assert (RX : forall j n, 0 <= j -> (j + Z.of_nat n <= A_S_queue_bytes 0 \/ A_S_queue_bytes S_queue_N <= j) ->
                 u_at Bf j n = u_at X j n).
  { intros j n Hj Hd. apply (wframe_u_at Rq X Bf j n W Hj). intros a Ha HR. unfold Rq in HR. lia. }
  assert (Hw : 0 <= A_S_queued) by (ri_num; lia).
  assert (Hwl : A_S_queued + Z.of_nat (length (put 4 kf)) <= Z.of_nat (length Bf))
    by (rewrite length_put, HZ; ri_num; lia).
  (* reads other than s->queued are Bf's *)
  assert (R2 : forall j n, 0 <= j -> (j + Z.of_nat n <= A_S_queued \/ A_S_queued + 4 <= j) ->
                 u_at (upd Bf A_S_queued (put 4 kf)) j n = u_at Bf j n).
  { intros j n Hj Hd. apply u_at_upd_out; [exact Hw | exact Hj | rewrite length_put; exact Hd | exact Hwl]. }
  unfold set_S_queued.
  split; [rewrite length_upd by lia; rewrite (proj1 W); exact L|].
  split; [unfold g_rx; rewrite R2, RX by (ri_num; lia); exact G|].
  split.
  { intros H0. specialize (F H0). unfold ri_f, M_fly_on, M_fly_len, s32_at in *.
    rewrite !R2, !RX by (ri_num; lia). exact F. }
  intros H0. specialize (Q H0). destruct Q as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
  assert (EQ : S_queued (upd Bf A_S_queued (put 4 kf)) = kf).
  { unfold S_queued. rewrite u_at_upd_put by (rewrite ?HZ; ri_num; lia).
    apply Z.mod_small. split; [lia|]. apply (Z.le_lt_trans _ 512); [unfold QUEUE_MAX in Q6; lia | reflexivity]. }
  assert (QB : qb X X 0 0) by (split; [intros y Hy; lia | exact Q1]).
  unfold ri_q. rewrite EQ.
  unfold g_ncmd, S_cfg_max_cmds, S_cfg_max_body in *.
  rewrite !R2, !RX by (ri_num; lia).
  refine (conj _ (conj _ (conj Q3 (conj Q4 (conj Q5 _))))).
  - intros x Hx. unfold S_queue_len. rewrite R2 by (unfold QUEUE_MAX in Q6; ri_num; lia).
    exact (Hb QB x Hx).
  - intros s Hs Hst. unfold Cmd_st, Cmd_len, s32_at in *.
    rewrite R2, RX in Hst by (unfold CMDS_MAX in Q5; ri_num; lia).
    rewrite R2, RX by (unfold CMDS_MAX in Q5; ri_num; lia).
    exact (Q2 s Hs Hst).
  - unfold QUEUE_MAX in *. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The session (transport/src/diginet_session.c)                      *)
(* ------------------------------------------------------------------ *)

(* the frame send_control builds (:99-105): [] or 60 bytes *)
Lemma send_control_frame_len : forall I F B cmd ack B' r f,
  send_control_m I F B cmd ack = Some (B', (r, f)) -> (length f <= 1514)%nat.
Proof.
  intros I F B cmd ack B' r f H. unfold send_control_m in H. cbv zeta in H.
  match type of H with (if ?c then _ else _) = _ => destruct c end; cbv beta iota in H.
  - injection H as _ _ <-. cbn [length]. lia.
  - match type of H with match ?x with _ => _ end = _ => destruct x as [[B1 r1]|] end;
      cbv beta iota in H; [|discriminate H].
    injection H as _ _ <-. apply ri_lib_frame_len; [apply (proj1 (ri_mac_len B)) | apply (proj2 (ri_mac_len B))
      | cbn [length]; lia].
Qed.

(* a build code >= 0 (:101, :393) means a body of at most 1484 bytes *)
Lemma ri_build_body : forall body cap mode, (diginet_frame_build_code body cap mode <? 0) = false ->
  (length body <= 1484)%nat.
Proof.
  intros body cap mode H. unfold diginet_frame_build_code, lib_build_code in H.
  revert H. destruct (negb ((mode =? 0) || (mode =? 1))); [intros H; discriminate H|].
  destruct (Z.ltb_spec 1484 (Z.of_nat (length body))) as [Hb|Hb]; [intros H; discriminate H|].
  intros _. lia.
Qed.

(* the length facts the writes of the session's frames need, from the calls in the context *)
Ltac ri_pre :=
  repeat match goal with
  | E : send_control_m _ _ _ _ _ = Some (_, (_, ?f)) |- _ =>
      lazymatch goal with
      | _ : (length f <= 1514)%nat |- _ => fail
      | _ => pose proof (send_control_frame_len _ _ _ _ _ _ _ _ E)
      end
  | E : (diginet_frame_build_code ?bd _ _ <? 0) = false |- _ =>
      lazymatch goal with
      | _ : (length bd <= 1484)%nat |- _ => fail
      | _ => pose proof (ri_build_body _ _ _ E)
      end
  end.

(* set_state (:79-86) *)
Lemma set_state_rk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall I F B st why B' u, rk B0 B -> set_state_m I F B st why = Some (B', u) -> rk B0 B'.
Proof.
  intros B0 HL0 I F B st why B' u K H. unfold set_state_m in H. gk_split H.
  all: first [apply some_pair_inv in H as [<- _] | idtac];
       repeat match goal with
       | E : call_notify _ _ _ _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z call_notify_rk
       end;
       ri_set; rk_go.
Qed.

(* send_raw (:88-94) *)
Lemma send_raw_rk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall I F B frame B' r, rk B0 B -> send_raw_m I F B frame = Some (B', r) -> rk B0 B'.
Proof.
  intros B0 HL0 I F B frame B' r K H. unfold send_raw_m, call_send in H. gk_split H.
  all: first [apply some_pair_inv in H as [<- _] | idtac];
       repeat match goal with
       | E : io_send_m _ _ _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z io_send_rk
       end;
       ri_set; rk_go.
Qed.

(* send_control (:97-109) *)
Lemma send_control_rk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall I F B cmd ack B' R, rk B0 B -> send_control_m I F B cmd ack = Some (B', R) -> rk B0 B'.
Proof.
  intros B0 HL0 I F B cmd ack B' R K H. unfold send_control_m in H. gk_split H.
  all: first [apply some_pair_inv in H as [<- _] | idtac];
       repeat match goal with
       | E : send_raw_m _ _ _ _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z send_raw_rk
       end;
       ri_set; rk_go.
Qed.

(* session_lost (:160-165) *)
Lemma session_lost_rk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall I F B why B' u, rk B0 B -> session_lost_m I F B why = Some (B', u) -> rk B0 B'.
Proof.
  intros B0 HL0 I F B why B' u K H. unfold session_lost_m in H. gk_split H.
  all: first [apply some_pair_inv in H as [<- _] | idtac];
       repeat match goal with
       | E : set_state_m _ _ _ _ _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z set_state_rk
       end;
       ri_set; rk_go.
Qed.

(* diginet_session_wake (:119-145) *)
Lemma wake_rk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall I F B now B' r, rk B0 B -> diginet_session_wake_m I F B now = Some (B', r) -> rk B0 B'.
Proof.
  intros B0 HL0 I F B now B' r K H. unfold diginet_session_wake_m, inflight_start_m in H. gk_split H.
  all: first [apply some_pair_inv in H as [<- _] | idtac]; ri_pre;
       repeat match goal with
       | E : send_control_m _ _ _ _ _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z send_control_rk
       | E : set_state_m _ _ _ _ _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z set_state_rk
       end;
       ri_set; rk_go.
Qed.

(* maybe_online (:176-182) *)
Lemma maybe_online_rk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall I F B B' u, rk B0 B -> maybe_online_m I F B = Some (B', u) -> rk B0 B'.
Proof.
  intros B0 HL0 I F B B' u K H. unfold maybe_online_m in H. gk_split H.
  all: first [apply some_pair_inv in H as [<- _] | idtac];
       repeat match goal with
       | E : set_state_m _ _ _ _ _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z set_state_rk
       end;
       ri_set; rk_go.
Qed.

(* on_announce (:184-221) *)
Lemma on_announce_rk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall I F B buf now B' u, rk B0 B -> on_announce_m I F B buf now = Some (B', u) -> rk B0 B'.
Proof.
  intros B0 HL0 I F B buf now B' u K H. unfold on_announce_m in H. gk_split H.
  all: first [apply some_pair_inv in H as [<- _] | idtac];
       repeat match goal with
       | E : call_notify _ _ _ _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z call_notify_rk
       | E : session_lost_m _ _ _ _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z session_lost_rk
       | E : diginet_session_wake_m _ _ _ _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z wake_rk
       | E : maybe_online_m _ _ _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z maybe_online_rk
       end;
       ri_set; rk_go.
Qed.

(* on_ack (:223-237) *)
Lemma on_ack_rk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall I F B buf B' u, rk B0 B -> on_ack_m I F B buf = Some (B', u) -> rk B0 B'.
Proof.
  intros B0 HL0 I F B buf B' u K H. unfold on_ack_m in H. gk_split H.
  all: first [apply some_pair_inv in H as [<- _] | idtac];
       repeat match goal with
       | E : call_notify _ _ _ _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z call_notify_rk
       | E : maybe_online_m _ _ _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z maybe_online_rk
       end;
       ri_set; rk_go.
Qed.

(* on_data (:239-261) *)
Lemma on_data_rk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall I F B buf now B' u, rk B0 B -> on_data_m I F B buf now = Some (B', u) -> rk B0 B'.
Proof.
  intros B0 HL0 I F B buf now B' u K H. unfold on_data_m in H. gk_split H.
  all: first [apply some_pair_inv in H as [<- _] | idtac];
       repeat match goal with
       | E : send_control_m _ _ _ _ _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z send_control_rk
       | E : call_notify _ _ _ _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z call_notify_rk
       end;
       ri_set; rk_go.
Qed.

(* retransmit (:403-412) *)
Lemma retransmit_rk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall I F B now B' r, rk B0 B -> retransmit_m I F B now = Some (B', r) -> rk B0 B'.
Proof.
  intros B0 HL0 I F B now B' r K H. unfold retransmit_m, inflight_bytes in H. gk_split H.
  all: first [apply some_pair_inv in H as [<- _] | idtac];
       repeat match goal with
       | E : send_raw_m _ _ _ _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z send_raw_rk
       end;
       ri_set; rk_go.
Qed.

(* send_data (:388-401) *)
Lemma send_data_rk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall I F B body ncmds now B' r, rk B0 B -> send_data_m I F B body ncmds now = Some (B', r) -> rk B0 B'.
Proof.
  intros B0 HL0 I F B body ncmds now B' r K H. unfold send_data_m, inflight_start_m, inflight_bytes in H. gk_split H.
  all: first [apply some_pair_inv in H as [<- _] | idtac]; ri_pre;
       repeat match goal with
       | E : send_raw_m _ _ _ _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z send_raw_rk
       end;
       ri_set; rk_go.
Qed.

(* diginet_session_tick (:414-472) *)
Lemma tick_rk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall I F B now B' r, rk B0 B -> diginet_session_tick_m I F B now = Some (B', r) -> rk B0 B'.
Proof.
  intros B0 HL0 I F B now B' r K H. unfold diginet_session_tick_m in H. gk_split H.
  all: first [apply some_pair_inv in H as [<- _] | idtac];
       repeat match goal with
       | E : session_lost_m _ _ _ _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z session_lost_rk
       | E : retransmit_m _ _ _ _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z retransmit_rk
       | E : call_notify _ _ _ _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z call_notify_rk
       | E : take_m _ _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z take_rk
       | E : send_data_m _ _ _ _ _ _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z send_data_rk
       end;
       ri_set; rk_go.
Qed.

(* diginet_session_rx (:263-318) *)
Lemma rx_rk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall I F B buf now B' r, rk B0 B -> diginet_session_rx_m I F B buf now = Some (B', r) -> rk B0 B'.
Proof.
  intros B0 HL0 I F B buf now B' r K H. unfold diginet_session_rx_m in H. gk_split H.
  all: first [apply some_pair_inv in H as [<- _] | idtac];
       repeat match goal with
       | E : on_announce_m _ _ _ _ _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z on_announce_rk
       | E : on_ack_m _ _ _ _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z on_ack_rk
       | E : on_data_m _ _ _ _ _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z on_data_rk
       | E : session_lost_m _ _ _ _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z session_lost_rk
       | E : diginet_session_tick_m _ _ _ _ = Some (?Z, _) |- _ => ri_call B0 HL0 E Z tick_rk
       end;
       ri_set; rk_go.
Qed.

(* the drain loop of diginet_session_poll (:524-526) *)
Lemma poll_drain_rk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall I F fuel B B' r, rk B0 B -> poll_drain_m I F B fuel = Some (B', r) -> rk B0 B'.
Proof.
  intros B0 HL0 I F fuel. induction fuel as [|f IH]; intros B B' r K H;
    destruct (TPoll.poll_drain_cases I F B _ B' r H)
      as (B1 & r1 & got & CR & [(_ & -> & _) | (_ & f' & now & B2 & r2 & Ef & _ & RX & PD)]);
    apply TPoll.call_recv_inv in CR as [_ CR];
    assert (K1 : rk B0 B1) by (eapply (io_recv_rk B0 HL0); [exact K | exact CR]).
  - exact K1.
  - discriminate Ef.
  - exact K1.
  - injection Ef as <-. apply (IH B2 B' r); [|exact PD]. eapply (rx_rk B0 HL0); [exact K1 | exact RX].
Qed.

(* diginet_session_poll (:505-527) *)
Lemma poll_rk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall I F w B B' r, rk B0 B -> diginet_session_poll_m I F B w = Some (B', r) -> rk B0 B'.
Proof.
  intros B0 HL0 I F w B B' r K H.
  destruct (TPoll.poll_cases I F B w B' r H) as [(_ & -> & _) | (_ & _ & now & due & B1 & r1 & got & _ & _ & CR & C)];
    [exact K|].
  apply TPoll.call_recv_inv in CR as [_ CR].
  assert (K1 : rk B0 B1) by (eapply (io_recv_rk B0 HL0); [exact K | exact CR]).
  destruct C as [(_ & -> & _) | (_ & now2 & B2 & B3 & r3 & _ & HRX & TK & PD)]; [exact K1|].
  assert (K2 : rk B0 B2).
  { destruct HRX as [(_ & ->) | (_ & r2 & RX)]; [exact K1|]. eapply (rx_rk B0 HL0); [exact K1 | exact RX]. }
  assert (K3 : rk B0 B3) by (eapply (tick_rk B0 HL0); [exact K2 | exact TK]).
  eapply (poll_drain_rk B0 HL0); [exact K3 | exact PD].
Qed.

(* ------------------------------------------------------------------ *)
(* The lemmas the walks use                                           *)
(* ------------------------------------------------------------------ *)

(* (H3) *)
Lemma tick_m_run_inv : forall I F Bx now B2 r, length Bx = Z.to_nat TW.W_LEN -> run_inv Bx ->
  TSS.diginet_session_tick_m I F Bx now = Some (B2, r) -> length B2 = Z.to_nat TW.W_LEN /\ run_inv B2.
Proof.
  intros I F Bx now B2 r HL R H. apply (rk_out Bx B2 HL R).
  eapply (tick_rk Bx HL); [apply rk_refl | exact H].
Qed.

(* (H5) *)
Lemma tick_m_g_rx : forall I F Bx now B2 r, length Bx = Z.to_nat TW.W_LEN ->
  TSS.diginet_session_tick_m I F Bx now = Some (B2, r) -> TW.g_rx B2 = TW.g_rx Bx.
Proof.
  intros I F Bx now B2 r HL H. apply (rk_g_rx Bx B2).
  eapply (tick_rk Bx HL); [apply rk_refl | exact H].
Qed.

(* m_rx, the harness model of a received frame (receive's by_poll = 0 path) *)
Lemma mrx_m_run_inv : forall I F Bx n B2 r, length Bx = Z.to_nat TW.W_LEN -> run_inv Bx ->
  TC.m_rx_m I F Bx n = Some (B2, r) -> length B2 = Z.to_nat TW.W_LEN /\ run_inv B2.
Proof.
  intros I F Bx n B2 r HL R H. apply (rk_out Bx B2 HL R).
  eapply (m_rx_rk Bx HL); [apply rk_refl | exact H].
Qed.

(* (H6): io_recv runs m_rx (m_rx_rk, the relation mrx_m_run_inv reads) or m_tick *)
Lemma iorecv_m_run_inv : forall I F Bx cap B1 r got, length Bx = Z.to_nat TW.W_LEN -> run_inv Bx ->
  TC.io_recv_m I F Bx cap = Some (B1, r, got) -> length B1 = Z.to_nat TW.W_LEN /\ run_inv B1.
Proof.
  intros I F Bx cap B1 r got HL R H. apply (rk_out Bx B1 HL R).
  eapply (io_recv_rk Bx HL); [apply rk_refl | exact H].
Qed.

(* (H7) *)
Lemma iorecv_m_g_rx : forall I F Bx cap B1 r got, length Bx = Z.to_nat TW.W_LEN ->
  TC.io_recv_m I F Bx cap = Some (B1, r, got) -> TW.g_rx B1 = TW.g_rx Bx.
Proof.
  intros I F Bx cap B1 r got HL H. apply (rk_g_rx Bx B1).
  eapply (io_recv_rk Bx HL); [apply rk_refl | exact H].
Qed.

(* (H4) *)
Lemma rx_m_g_rx : forall I F Bx b now B2 r, length Bx = Z.to_nat TW.W_LEN ->
  TSS.diginet_session_rx_m I F Bx b now = Some (B2, r) -> TW.g_rx B2 = TW.g_rx Bx.
Proof.
  intros I F Bx b now B2 r HL H. apply (rk_g_rx Bx B2).
  eapply (rx_rk Bx HL); [apply rk_refl | exact H].
Qed.

(* (H2) *)
Lemma rx_m_run_inv : forall I F Bx b now B2 r, length Bx = Z.to_nat TW.W_LEN -> run_inv Bx ->
  TSS.diginet_session_rx_m I F Bx b now = Some (B2, r) -> length B2 = Z.to_nat TW.W_LEN /\ run_inv B2.
Proof.
  intros I F Bx b now B2 r HL R H. apply (rk_out Bx B2 HL R).
  eapply (rx_rk Bx HL); [apply rk_refl | exact H].
Qed.

Lemma poll_m_run_inv : forall I F Bw max_wait_ms Bw' r, length Bw = Z.to_nat TW.W_LEN -> run_inv Bw ->
  TSS.diginet_session_poll_m I F Bw max_wait_ms = Some (Bw', r) -> length Bw' = Z.to_nat TW.W_LEN /\ run_inv Bw'.
Proof.
  intros I F Bw max_wait_ms Bw' r HL R H. apply (rk_out Bw Bw' HL R).
  eapply (poll_rk Bw HL); [apply rk_refl | exact H].
Qed.

Lemma poll_m_g_rx : forall I F Bw max_wait_ms Bw' r, length Bw = Z.to_nat TW.W_LEN ->
  TSS.diginet_session_poll_m I F Bw max_wait_ms = Some (Bw', r) -> TW.g_rx Bw' = TW.g_rx Bw.
Proof.
  intros I F Bw max_wait_ms Bw' r HL H. apply (rk_g_rx Bw Bw').
  eapply (poll_rk Bw HL); [apply rk_refl | exact H].
Qed.
