(* Setting: op 3 after op_begin; B1 in agree_core at ops (already counted), the new
   time now' with g_now B1 <= now' <= the bound of C, B2 := set_g_now B1 now'. The model's m_tick (FT:246-252) runs
   first on B2, then the library's diginet_session_tick (DS:414-472; TickDefs.tick_unfold).
   - front_lost_ok: a timeout (WAKING past wake_timeout, or ONLINE past offline): m_lost (FT:210-215) and the library's
     session_lost (DS:160-165) take the same branch and end in agree_core, IDLE, nothing in flight, OW and GOT
     holding the one transition (IDLE, st, why).
   - front_quiet_ok: no timeout: m_tick changes nothing and the library's tick is its in-flight step, then its tail.
   - front_step_ok: the in-flight step (DS:430-443): nothing overdue (B2 itself), a retransmission (DS:403-412 and
     io_send's retry branch FT:840-843), or the drop with N_ACK_LOST (DS:436-441, FT:955-957).
   Discipline of SimLib (no rewrite on goals with reads: wrw; no shared Ltac metavariables; reads opaque). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import
  TWorld TWorldLemmas TImg TNeed TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree Links SendOk SettleOk SimLib
  Deadline TickDefs TickFrontW.
Import ListNotations.
Open Scope Z_scope.

Local Opaque sub upd u_at s32_at put.

(* the bytes front_lost_ok may write besides R_tick: OW.n, OW.t[0], GOT.n, GOT.t[0] *)
Definition R_lost (a : Z) : Prop := R_tick a \/ (OFF_OW <= a < OFF_OW + 16) \/ (OFF_GOT <= a < OFF_GOT + 16).

(* ---- closed facts ---- *)
Lemma ns_state : (DIGINET_N_STATE =? N_STATE) = true.
Proof. reflexivity. Qed.
Lemma ns_idle_online : (DIGINET_S_IDLE =? S_ONLINE) = false.
Proof. reflexivity. Qed.
Lemma nal_state : (DIGINET_N_ACK_LOST =? N_STATE) = false.
Proof. reflexivity. Qed.
Lemma nal_acked : (DIGINET_N_ACK_LOST =? N_ACKED) = false.
Proof. reflexivity. Qed.
Lemma nal_lost : (DIGINET_N_ACK_LOST =? N_ACK_LOST) = true.
Proof. reflexivity. Qed.
Lemma idle_range : 0 <= S_IDLE <= 3.
Proof. unfold S_IDLE. lia. Qed.
Lemma eio_ne0 : (- EIO =? 0) = false.
Proof. reflexivity. Qed.

Lemma gnow_nonneg : forall B, 0 <= g_now B.
Proof. intros B. exact (proj1 (u_at_range B OFF_g_now 8)). Qed.

(* ---- g_now written ---- *)
Lemma gnow_step : forall B now', length B = Z.to_nat W_LEN -> 0 <= now' < 2 ^ 64 ->
  length (set_g_now B now') = Z.to_nat W_LEN /\ wsame B (set_g_now B now') [(OFF_g_now, 8)] /\
  g_now (set_g_now B now') = now'.
Proof. intros B now' HB Hn. split; [wlen|]. split; [wsame_tac|]. wsimp. Qed.

(* ---- m_lost (FT:210-215) from OW.n = 0 ---- *)
Definition rs_ml : list (Z * Z) := [(A_M_fly_on, 4); (A_M_desk_counter_valid, 4); (OFF_OW, 16); (A_M_state, 4)].

Lemma m_lost_step : forall B st why, length B = Z.to_nat W_LEN -> OW_n B = 0 -> M_state B = st -> st <> S_IDLE ->
  - 2 ^ 31 <= st < 2 ^ 31 -> 0 <= why <= 8 ->
  exists B', m_lost_m B why = Some (B', tt) /\ length B' = Z.to_nat W_LEN /\ wsame B B' rs_ml /\
    M_state B' = S_IDLE /\ M_fly_on B' = 0 /\ M_desk_counter_valid B' = 0 /\ OW_n B' = 1 /\
    OW_t_state B' 0 = S_IDLE /\ OW_t_old B' 0 = st /\ OW_t_reason B' 0 = why.
Proof.
  intros B st why HB Hn Hst Hs Hr Hw.
  assert (E1 : M_state (set_M_desk_counter_valid (set_M_fly_on B 0) 0) = st) by (wsimp; exact Hst).
  assert (E2 : OW_n (set_M_desk_counter_valid (set_M_fly_on B 0) 0) = 0) by (wsimp; exact Hn).
  unfold m_lost_m, m_set_m. cbv zeta. wrw E1. wrw E2.
  destruct (Z.eqb_spec st S_IDLE) as [Hs'|_]; [exfalso; exact (Hs Hs')|].
  wrw ltb_0_TM. wrw ltb_0_0. cbv beta iota. wrw int_inc_0. cbv beta iota.
  eexists. split; [reflexivity|].
  split; [wlen|]. split; [wsame_tac|].
  split; [wsimp|]. split; [wsimp|]. split; [wsimp|]. split; [wsimp|].
  split; [wsimp|]. split; [wsimp|]. wsimp.
Qed.

(* ---- session_lost (DS:160-165) from GOT.n = 0: set_state's N_STATE notice (DS:79-86, FT:941-949) ---- *)
Definition rs_sl : list (Z * Z) := [(A_S_inflight, 4); (A_S_desk_counter_valid, 4); (A_S_state, 4); (OFF_GOT, 16)].

Lemma s_lost_step : forall I F B st why, length B = Z.to_nat W_LEN -> GOT_n B = 0 -> S_state B = st ->
  st <> DIGINET_S_IDLE -> - 2 ^ 31 <= st < 2 ^ 31 -> S_notify B = ti_notice I -> 0 <= why <= 8 ->
  exists B', session_lost_m I F B why = Some (B', tt) /\ length B' = Z.to_nat W_LEN /\ wsame B B' rs_sl /\
    S_state B' = DIGINET_S_IDLE /\ S_inflight B' = 0 /\ S_desk_counter_valid B' = 0 /\ GOT_n B' = 1 /\
    GOT_t_state B' 0 = DIGINET_S_IDLE /\ GOT_t_old B' 0 = st /\ GOT_t_reason B' 0 = why.
Proof.
  intros I F B st why HB Hn Hst Hs Hr Hno Hw.
  assert (E1 : S_state (set_S_desk_counter_valid (set_S_inflight B 0) 0) = st) by (wsimp; exact Hst).
  assert (E2 : S_notify (set_S_state (set_S_desk_counter_valid (set_S_inflight B 0) 0) DIGINET_S_IDLE) = ti_notice I)
    by (wsimp; exact Hno).
  assert (E3 : GOT_n (set_S_state (set_S_desk_counter_valid (set_S_inflight B 0) 0) DIGINET_S_IDLE) = 0)
    by (wsimp; exact Hn).
  unfold session_lost_m, set_state_m. cbv zeta. wrw E1.
  destruct (Z.eqb_spec st DIGINET_S_IDLE) as [Hs'|_]; [exfalso; exact (Hs Hs')|].
  cbv beta iota. unfold call_notify. wrw E2. wrw (Z.eqb_refl (ti_notice I)). cbv beta iota.
  unfold notice_m. cbv zeta. cbn [n_kind n_state n_old n_reason].
  wrw ns_state. cbv beta iota. wrw E3. wrw ltb_0_TM. wrw ltb_0_0. cbv beta iota.
  wrw int_inc_0. cbv beta iota. wrw ns_idle_online. cbv beta iota.
  eexists. split; [reflexivity|].
  split; [wlen|]. split; [wsame_tac|].
  split; [wsimp|]. split; [wsimp|]. split; [wsimp|]. split; [wsimp|].
  split; [wsimp|]. split; [wsimp|]. wsimp.
Qed.

Lemma rs_lost_R : forall a, in_ranges (rs_ml ++ rs_sl) a -> R_lost a.
Proof.
  intros a Ha. unfold rs_ml, rs_sl in Ha. wranges_in Ha. unfold R_lost, R_tick.
  revert Ha. wunfold_addr. intros Ha. lia.
Qed.

Lemma rs_rt_R : forall a, in_ranges rs_rt a -> R_tick a.
Proof. intros a Ha. unfold rs_rt in Ha. wranges_in Ha. unfold R_tick. revert Ha. wunfold_addr. intros Ha. lia. Qed.

Definition rs_al : list (Z * Z) := [(A_S_inflight, 4); (A_S_stats_ack_lost, 8); (A_M_fly_on, 4)].

Lemma rs_al_R : forall a, in_ranges rs_al a -> R_tick a.
Proof. intros a Ha. unfold rs_al in Ha. wranges_in Ha. unfold R_tick. revert Ha. wunfold_addr. intros Ha. lia. Qed.

(* ---- agree_core after the tick's front, one lemma per outcome ---- *)

(* nothing overdue: only g_now moved *)
Lemma agree_quiet : forall I ops B B' now', agree_core I ops B -> g_now B <= now' <= 1000000 + ops * 65535000000 ->
  (M_state B = S_WAKING -> now' - M_wake_sent B < 1000 * Cfg_wake_timeout_ms B) ->
  (M_state B = S_ONLINE -> now' - M_last_rx B < 1000 * Cfg_offline_ms B) ->
  (M_fly_on B = 1 -> now' - M_fly_sent B < 1000 * Cfg_ack_timeout_ms B) ->
  wsame B B' [(OFF_g_now, 8)] -> length B' = Z.to_nat W_LEN -> g_now B' = now' -> agree_core I ops B'.
Proof.
  intros I ops B B' now' HC Hn Hwk Hon Hfl HW HL' Eg.
  pose proof (ac_st _ _ _ HC) as HS. pose proof (ac_fly _ _ _ HC) as HF.
  pose proof (ac_time _ _ _ HC) as HT. pose proof (ac_misc _ _ _ HC) as HM.
  tf_sames HW B B'.
  apply (agree_core_x I ops B B' HC (wsame_weaken_b B B' [(OFF_g_now, 8)] rs_x HW ltac:(vm_compute; reflexivity)) HL').
  - constructor; tf_rw B'.
    + exact (b1_state _ HS).
    + exact (b1_state_range _ HS).
    + exact (b2_desk_known _ HS).
    + exact (b2_desk_known01 _ HS).
    + exact (b2_desk_mac _ HS).
    + exact (b3_foreign _ HS).
    + exact (b3_foreign01 _ HS).
    + exact (b3_e1 _ HS).
    + exact (b3_e1_01 _ HS).
    + exact (b3_e2 _ HS).
    + exact (b3_e2_01 _ HS).
    + exact (b4_wake_sent _ HS).
    + exact (b4_last_rx _ HS).
    + exact (b4_backoff _ HS).
    + exact (b5_next_ka _ HS).
    + exact (b5_display_sent _ HS).
    + exact (b5_display_sent01 _ HS).
    + exact (b5_last_display _ HS).
    + exact (b6_valid _ HS).
    + exact (b6_valid01 _ HS).
    + exact (b6_counter _ HS).
    + exact (b7_host_counter _ HS).
    + exact (b9_idle _ HS).
    + exact (b9_known _ HS).
  - constructor; tf_rw B'.
    + exact (b8_on _ HF).
    + exact (b8_on01 _ HF).
    + exact (b8_state _ HF).
    + exact (b8_counter _ HF).
    + exact (b8_counter_host _ HF).
    + exact (b8_retries _ HF).
    + exact (b8_retries_le _ HF).
    + exact (b8_sent _ HF).
    + exact (b8_len _ HF).
    + exact (b8_cmd _ HF).
    + intros Hfo. destruct (b8_frames _ HF Hfo) as (body & ncmds & Hl & Hbc & Hnc & Hlen & Hm & Hs).
      assert (Hn15 : (Z.to_nat (M_fly_len B) <= 1514)%nat) by (wrw Hlen; clear - Hl; unfold frame_len; lia).
      wrw (wsame_sub_le B B' [(OFF_g_now, 8)] A_M_fly_frame (Z.to_nat (M_fly_len B)) 1514 HW ltac:(wle) Hn15 ltac:(vm_compute; reflexivity)).
      wrw (wsame_sub_le B B' [(OFF_g_now, 8)] A_S_inflight_frame (Z.to_nat (M_fly_len B)) 1514 HW ltac:(wle) Hn15 ltac:(vm_compute; reflexivity)).
      exists body, ncmds. exact (conj Hl (conj Hbc (conj Hnc (conj Hlen (conj Hm Hs))))).
  - constructor; tf_rw B'.
    + clear - Hn; lia.
    + pose proof (c1_last_rx _ _ HT) as Hx; clear - Hx Hn; lia.
    + pose proof (c1_wake_sent _ _ HT) as Hx; clear - Hx Hn; lia.
    + intros Hf. pose proof (c1_fly_sent _ _ HT Hf) as Hx; clear - Hx Hn; lia.
    + intros Hd. pose proof (c1_last_display _ _ HT Hd) as Hx; clear - Hx Hn; lia.
    + pose proof (c1_backoff _ _ HT) as Hx; clear - Hx Hn; lia.
    + intros Hr. pose proof (c1_next_ka _ _ HT Hr) as Hx; clear - Hx Hn; lia.
    + exact Hwk.
    + exact Hon.
    + exact Hfl.
  - tf_rw B'. exact (e1_fail_next _ _ HM).
Qed.

(* a timeout: m_lost and session_lost (front_lost_ok) *)
Definition rs_lost : list (Z * Z) := ([(OFF_g_now, 8)] ++ rs_ml) ++ rs_sl.

Lemma agree_lost : forall I ops B B' now', agree_core I ops B -> g_now B <= now' <= 1000000 + ops * 65535000000 ->
  wsame B B' rs_lost -> length B' = Z.to_nat W_LEN -> g_now B' = now' ->
  M_state B' = S_IDLE -> S_state B' = DIGINET_S_IDLE -> M_fly_on B' = 0 -> S_inflight B' = 0 ->
  M_desk_counter_valid B' = 0 -> S_desk_counter_valid B' = 0 -> agree_core I ops B'.
Proof.
  intros I ops B B' now' HC Hn HW HL' Eg E1 E2 E3 E4 E5 E6.
  pose proof (ac_st _ _ _ HC) as HS. pose proof (ac_fly _ _ _ HC) as HF.
  pose proof (ac_time _ _ _ HC) as HT. pose proof (ac_misc _ _ _ HC) as HM.
  tf_sames HW B B'.
  apply (agree_core_x I ops B B' HC (wsame_weaken_b B B' rs_lost rs_x HW ltac:(vm_compute; reflexivity)) HL').
  - constructor; tf_rw B'.
    + reflexivity.
    + exact idle_range.
    + exact (b2_desk_known _ HS).
    + exact (b2_desk_known01 _ HS).
    + exact (b2_desk_mac _ HS).
    + exact (b3_foreign _ HS).
    + exact (b3_foreign01 _ HS).
    + exact (b3_e1 _ HS).
    + exact (b3_e1_01 _ HS).
    + exact (b3_e2 _ HS).
    + exact (b3_e2_01 _ HS).
    + exact (b4_wake_sent _ HS).
    + exact (b4_last_rx _ HS).
    + exact (b4_backoff _ HS).
    + exact (b5_next_ka _ HS).
    + exact (b5_display_sent _ HS).
    + exact (b5_display_sent01 _ HS).
    + exact (b5_last_display _ HS).
    + reflexivity.
    + left; reflexivity.
    + intros Hx; discriminate Hx.
    + exact (b7_host_counter _ HS).
    + intros _; reflexivity.
    + tf_unconst; intros [Hx|Hx]; discriminate Hx.
  - constructor; tf_rw B'.
    + reflexivity.
    + left; reflexivity.
    + intros Hx; discriminate Hx.
    + intros Hx; discriminate Hx.
    + intros Hx; discriminate Hx.
    + intros Hx; discriminate Hx.
    + intros Hx; discriminate Hx.
    + intros Hx; discriminate Hx.
    + intros Hx; discriminate Hx.
    + intros Hx; discriminate Hx.
    + intros Hx; discriminate Hx.
  - constructor; tf_rw B'.
    + clear - Hn; lia.
    + pose proof (c1_last_rx _ _ HT) as Hx; clear - Hx Hn; lia.
    + pose proof (c1_wake_sent _ _ HT) as Hx; clear - Hx Hn; lia.
    + intros Hx; discriminate Hx.
    + intros Hd. pose proof (c1_last_display _ _ HT Hd) as Hx; clear - Hx Hn; lia.
    + pose proof (c1_backoff _ _ HT) as Hx; clear - Hx Hn; lia.
    + intros Hr. pose proof (c1_next_ka _ _ HT Hr) as Hx; clear - Hx Hn; lia.
    + tf_unconst; intros Hx; discriminate Hx.
    + tf_unconst; intros Hx; discriminate Hx.
    + intros Hx; discriminate Hx.
  - tf_rw B'. exact (e1_fail_next _ _ HM).
Qed.

(* the drop with N_ACK_LOST: inflight and M.fly.on cleared *)
Lemma agree_acklost : forall I ops B B' now', agree_core I ops B -> g_now B <= now' <= 1000000 + ops * 65535000000 ->
  (M_state B = S_WAKING -> now' - M_wake_sent B < 1000 * Cfg_wake_timeout_ms B) ->
  (M_state B = S_ONLINE -> now' - M_last_rx B < 1000 * Cfg_offline_ms B) ->
  wsame B B' ([(OFF_g_now, 8)] ++ rs_al) -> length B' = Z.to_nat W_LEN -> g_now B' = now' ->
  S_inflight B' = 0 -> M_fly_on B' = 0 -> agree_core I ops B'.
Proof.
  intros I ops B B' now' HC Hn Hwk Hon HW HL' Eg E1 E2.
  pose proof (ac_st _ _ _ HC) as HS. pose proof (ac_fly _ _ _ HC) as HF.
  pose proof (ac_time _ _ _ HC) as HT. pose proof (ac_misc _ _ _ HC) as HM.
  tf_sames HW B B'.
  apply (agree_core_x I ops B B' HC (wsame_weaken_b B B' ([(OFF_g_now, 8)] ++ rs_al) rs_x HW
           ltac:(vm_compute; reflexivity)) HL').
  - constructor; tf_rw B'.
    + exact (b1_state _ HS).
    + exact (b1_state_range _ HS).
    + exact (b2_desk_known _ HS).
    + exact (b2_desk_known01 _ HS).
    + exact (b2_desk_mac _ HS).
    + exact (b3_foreign _ HS).
    + exact (b3_foreign01 _ HS).
    + exact (b3_e1 _ HS).
    + exact (b3_e1_01 _ HS).
    + exact (b3_e2 _ HS).
    + exact (b3_e2_01 _ HS).
    + exact (b4_wake_sent _ HS).
    + exact (b4_last_rx _ HS).
    + exact (b4_backoff _ HS).
    + exact (b5_next_ka _ HS).
    + exact (b5_display_sent _ HS).
    + exact (b5_display_sent01 _ HS).
    + exact (b5_last_display _ HS).
    + exact (b6_valid _ HS).
    + exact (b6_valid01 _ HS).
    + exact (b6_counter _ HS).
    + exact (b7_host_counter _ HS).
    + intros _; reflexivity.
    + exact (b9_known _ HS).
  - constructor; tf_rw B'.
    + reflexivity.
    + left; reflexivity.
    + intros Hx; discriminate Hx.
    + intros Hx; discriminate Hx.
    + intros Hx; discriminate Hx.
    + intros Hx; discriminate Hx.
    + intros Hx; discriminate Hx.
    + intros Hx; discriminate Hx.
    + intros Hx; discriminate Hx.
    + intros Hx; discriminate Hx.
    + intros Hx; discriminate Hx.
  - constructor; tf_rw B'.
    + clear - Hn; lia.
    + pose proof (c1_last_rx _ _ HT) as Hx; clear - Hx Hn; lia.
    + pose proof (c1_wake_sent _ _ HT) as Hx; clear - Hx Hn; lia.
    + intros Hx; discriminate Hx.
    + intros Hd. pose proof (c1_last_display _ _ HT Hd) as Hx; clear - Hx Hn; lia.
    + pose proof (c1_backoff _ _ HT) as Hx; clear - Hx Hn; lia.
    + intros Hr. pose proof (c1_next_ka _ _ HT Hr) as Hx; clear - Hx Hn; lia.
    + exact Hwk.
    + exact Hon.
    + intros Hx; discriminate Hx.
  - tf_rw B'. exact (e1_fail_next _ _ HM).
Qed.

(* a retransmission: retries + 1 on both sides, the retry field of the frame in flight, sent at now' *)
Lemma agree_retx : forall I ops B B' now', agree_core I ops B -> g_now B <= now' <= 1000000 + ops * 65535000000 ->
  (M_state B = S_WAKING -> now' - M_wake_sent B < 1000 * Cfg_wake_timeout_ms B) ->
  (M_state B = S_ONLINE -> now' - M_last_rx B < 1000 * Cfg_offline_ms B) ->
  M_fly_on B = 1 -> M_fly_retries B + 1 <= Cfg_max_retries B ->
  wsame B B' ([(OFF_g_now, 8)] ++ rs_rt) -> length B' = Z.to_nat W_LEN -> g_now B' = now' ->
  S_inflight_retries B' = M_fly_retries B + 1 -> M_fly_retries B' = M_fly_retries B + 1 ->
  S_inflight_sent_us B' = now' -> M_fly_sent B' = now' -> g_fail_next B' = 0 ->
  sub B' A_S_inflight_frame (Z.to_nat (M_fly_len B)) =
    firstn 26 (sub B A_S_inflight_frame (Z.to_nat (M_fly_len B))) ++ put16 (M_fly_retries B + 1) ++
    skipn 28 (sub B A_S_inflight_frame (Z.to_nat (M_fly_len B))) ->
  agree_core I ops B'.
Proof.
  intros I ops B B' now' HC Hn Hwk Hon Hf1 Hle HW HL' Eg E1 E2 E3 E4 E5 Hfr.
  pose proof (ac_len _ _ _ HC) as HB.
  pose proof (ac_st _ _ _ HC) as HS. pose proof (ac_fly _ _ _ HC) as HF.
  pose proof (ac_time _ _ _ HC) as HT. pose proof (ac_misc _ _ _ HC) as HM.
  pose proof (a1_max_retries _ (ac_cfg _ _ _ HC)) as Hmx.
  assert (Hmr : 0 <= M_fly_retries B) by exact (proj1 (u_at_range B A_M_fly_retries 4)).
  tf_sames HW B B'.
  apply (agree_core_x I ops B B' HC (wsame_weaken_b B B' ([(OFF_g_now, 8)] ++ rs_rt) rs_x HW
           ltac:(vm_compute; reflexivity)) HL').
  - constructor; tf_rw B'.
    + exact (b1_state _ HS).
    + exact (b1_state_range _ HS).
    + exact (b2_desk_known _ HS).
    + exact (b2_desk_known01 _ HS).
    + exact (b2_desk_mac _ HS).
    + exact (b3_foreign _ HS).
    + exact (b3_foreign01 _ HS).
    + exact (b3_e1 _ HS).
    + exact (b3_e1_01 _ HS).
    + exact (b3_e2 _ HS).
    + exact (b3_e2_01 _ HS).
    + exact (b4_wake_sent _ HS).
    + exact (b4_last_rx _ HS).
    + exact (b4_backoff _ HS).
    + exact (b5_next_ka _ HS).
    + exact (b5_display_sent _ HS).
    + exact (b5_display_sent01 _ HS).
    + exact (b5_last_display _ HS).
    + exact (b6_valid _ HS).
    + exact (b6_valid01 _ HS).
    + exact (b6_counter _ HS).
    + exact (b7_host_counter _ HS).
    + exact (b9_idle _ HS).
    + exact (b9_known _ HS).
  - constructor; tf_rw B'.
    + exact (b8_on _ HF).
    + exact (b8_on01 _ HF).
    + exact (b8_state _ HF).
    + exact (b8_counter _ HF).
    + exact (b8_counter_host _ HF).
    + intros _; reflexivity.
    + intros _; exact Hle.
    + intros _; reflexivity.
    + exact (b8_len _ HF).
    + exact (b8_cmd _ HF).
    + intros Hfo. destruct (b8_frames _ HF Hfo) as (body & ncmds & Hl & Hbc & Hnc & Hlen & Hm & Hs).
      assert (Hn15 : (Z.to_nat (M_fly_len B) <= 1514)%nat) by (wrw Hlen; clear - Hl; unfold frame_len; lia).
      wrw (wsame_sub_le B B' ([(OFF_g_now, 8)] ++ rs_rt) A_M_fly_frame (Z.to_nat (M_fly_len B)) 1514 HW ltac:(wle) Hn15 ltac:(vm_compute; reflexivity)).
      wrw Hfr. wrw Hs.
      assert (Hd6 : length (M_desk B) = 6%nat) by (unfold M_desk; apply length_sub; [wle | rewrite HB; wle]).
      wrw (lib_frame_retry_set (M_desk B) HOST (M_fly_counter B) 0 (M_fly_retries B) (M_fly_retries B + 1) (M_fly_cmd B)
             ncmds body (Cfg_sum_mode B) Hd6 eq_refl ltac:(clear - Hle Hmr Hmx; lia)).
      exists body, ncmds. exact (conj Hl (conj Hbc (conj Hnc (conj Hlen (conj Hm eq_refl))))).
  - constructor; tf_rw B'.
    + clear - Hn; lia.
    + pose proof (c1_last_rx _ _ HT) as Hx; clear - Hx Hn; lia.
    + pose proof (c1_wake_sent _ _ HT) as Hx; clear - Hx Hn; lia.
    + intros _; apply Z.le_refl.
    + intros Hd. pose proof (c1_last_display _ _ HT Hd) as Hx; clear - Hx Hn; lia.
    + pose proof (c1_backoff _ _ HT) as Hx; clear - Hx Hn; lia.
    + intros Hr. pose proof (c1_next_ka _ _ HT Hr) as Hx; clear - Hx Hn; lia.
    + exact Hwk.
    + exact Hon.
    + intros _. pose proof (a1_ack_timeout _ (ac_cfg _ _ _ HC)) as Hx; clear - Hx; lia.
  - tf_rw B'. left; reflexivity.
Qed.

(* ---- no timeout (front_quiet_ok) ---- *)

(* DS:430 not taken: on to the tail *)
Lemma tick_step_quiet : forall I F B now,
  (negb (S_inflight B =? 0) && (ms_m (S_cfg_ack_timeout_ms B) <=? u64 (now - S_inflight_sent_us B))) = false ->
  tick_step_m I F B now = Some (inr B).
Proof. intros I F B now H. unfold tick_step_m. wrw H. reflexivity. Qed.

Lemma front_quiet_ok : forall (HL : links) I F ops B1 now', agree_core I ops B1 ->
  g_now B1 <= now' <= 1000000 + ops * 65535000000 ->
  (M_state B1 = S_WAKING -> now' - M_wake_sent B1 < 1000 * Cfg_wake_timeout_ms B1) ->
  (M_state B1 = S_ONLINE -> now' - M_last_rx B1 < 1000 * Cfg_offline_ms B1) ->
  let B2 := set_g_now B1 now' in
  m_tick_m B2 = Some (B2, tt) /\
  diginet_session_tick_m I F B2 now' =
    match tick_step_m I F B2 now' with
    | None => None
    | Some (inl (B, r)) => Some (B, r)
    | Some (inr B) => tick_tail_m I F B now'
    end.
Proof.
  intros HL I F ops B1 now' HC Hn Hwk Hon. cbv zeta.
  pose proof (ac_len _ _ _ HC) as HB1.
  pose proof (d3_ops _ _ (ac_q _ _ _ HC)) as Hops.
  pose proof (gnow_nonneg B1) as Hg0.
  assert (Hn64 : 0 <= now' < 2 ^ 64) by (unfold OPS_MAX in Hops; clear - Hn Hops Hg0; lia).
  destruct (gnow_step B1 now' HB1 Hn64) as (HL2 & HW2 & HG2).
  set (B2 := set_g_now B1 now') in *. clearbody B2.
  pose proof (ac_cfg _ _ _ HC) as HA. pose proof (ac_st _ _ _ HC) as HS. pose proof (ac_fly _ _ _ HC) as HF.
  pose proof (ac_time _ _ _ HC) as HT.
  pose proof (a1_wake_timeout _ HA) as Hwt. pose proof (a1_offline _ HA) as Hof.
  pose proof (c1_wake_sent _ _ HT) as Hws. pose proof (c1_last_rx _ _ HT) as Hlr.
  assert (Rw : 0 <= now' - M_wake_sent B1 < 18446744073709551616) by (clear - Hws Hn Hn64; wrange; lia).
  assert (Rl : 0 <= now' - M_last_rx B1 < 18446744073709551616) by (clear - Hlr Hn Hn64; wrange; lia).
  tf_sames HW2 B1 B2.
  split.
  - unfold m_tick_m. tf_rw B2.
    wrw (h_ms_small (Cfg_wake_timeout_ms B1) ltac:(clear - Hwt; lia)).
    wrw (h_ms_small (Cfg_offline_ms B1) ltac:(clear - Hof; lia)).
    wrw (u64_small (now' - M_wake_sent B1) Rw). wrw (u64_small (now' - M_last_rx B1) Rl).
    destruct (Z.eqb_spec (M_state B1) S_WAKING) as [Hw|Hw]; cbn [andb].
    + wrw (proj2 (Z.leb_gt _ _) (Hwk Hw)). cbn [andb].
      destruct (Z.eqb_spec (M_state B1) S_ONLINE) as [Ho|_]; [tf_cl Ho Hw|]. cbn [andb]. reflexivity.
    + destruct (Z.eqb_spec (M_state B1) S_ONLINE) as [Ho|_]; cbn [andb]; [|reflexivity].
      wrw (proj2 (Z.leb_gt _ _) (Hon Ho)). cbn [andb]. reflexivity.
  - assert (Hstep0 : M_fly_on B1 = 0 -> tick_step_m I F B2 now' = Some (inr B2)).
    { intros Hf0. apply tick_step_quiet. tf_rw B2. wrw (b8_on _ HF). wrw Hf0. wrw (Z.eqb_refl 0). reflexivity. }
    assert (Htail0 : M_state B1 <> S_ONLINE -> tick_tail_m I F B2 now' = Some (B2, DIGINET_OK)).
    { intros Hno. unfold tick_tail_m. tf_rw B2. wrw (b1_state _ HS).
      destruct (Z.eqb_spec (M_state B1) DIGINET_S_ONLINE) as [Ho|_]; [exfalso; exact (Hno Ho)|].
      cbn [negb orb]. reflexivity. }
    wrw (tick_unfold I F B2 now'). tf_rw B2.
    wrw (b1_state _ HS). wrw (a2_wake_timeout _ HA). wrw (a2_offline _ HA).
    wrw (b4_wake_sent _ HS). wrw (b4_last_rx _ HS).
    wrw (ms_small (Cfg_wake_timeout_ms B1) ltac:(clear - Hwt; lia)).
    wrw (ms_small (Cfg_offline_ms B1) ltac:(clear - Hof; lia)).
    wrw (u64_small (now' - M_wake_sent B1) Rw). wrw (u64_small (now' - M_last_rx B1) Rl).
    destruct (Z.eqb_spec (M_state B1) DIGINET_S_CLOSED) as [Hc|Hc]; cbn [orb].
    + wrw (Hstep0 (b9_idle _ HS (or_intror Hc))). cbv beta iota.
      wrw (Htail0 ltac:(intros Hx; tf_cl Hx Hc)). reflexivity.
    + destruct (Z.eqb_spec (M_state B1) DIGINET_S_IDLE) as [Hi|Hi]; cbn [orb].
      * wrw (Hstep0 (b9_idle _ HS (or_introl Hi))). cbv beta iota.
        wrw (Htail0 ltac:(intros Hx; tf_cl Hx Hi)). reflexivity.
      * destruct (Z.eqb_spec (M_state B1) DIGINET_S_WAKING) as [Hw|Hw]; cbn [andb].
        -- wrw (proj2 (Z.leb_gt _ _) (Hwk Hw)). cbn [andb].
           destruct (Z.eqb_spec (M_state B1) DIGINET_S_ONLINE) as [Ho|_]; [tf_cl Ho Hw|]. cbn [andb]. reflexivity.
        -- destruct (Z.eqb_spec (M_state B1) DIGINET_S_ONLINE) as [Ho|_]; cbn [andb]; [|reflexivity].
           wrw (proj2 (Z.leb_gt _ _) (Hon Ho)). cbn [andb]. reflexivity.
Qed.

(* ---- a timeout (front_lost_ok) ---- *)
Lemma front_lost_ok : forall (HL : links) I F ops B1 now' st why,
  agree_core I ops B1 -> g_now B1 <= now' <= 1000000 + ops * 65535000000 -> OW_n B1 = 0 -> GOT_n B1 = 0 ->
  ((st = S_WAKING /\ why = R_WAKE_TIMEOUT /\ M_state B1 = S_WAKING /\
    1000 * Cfg_wake_timeout_ms B1 <= now' - M_wake_sent B1) \/
   (st = S_ONLINE /\ why = R_SILENCE /\ M_state B1 = S_ONLINE /\
    1000 * Cfg_offline_ms B1 <= now' - M_last_rx B1)) ->
  let B2 := set_g_now B1 now' in
  exists B3 B4, m_tick_m B2 = Some (B3, tt) /\ g_now B3 = now' /\
    diginet_session_tick_m I F B3 now' = Some (B4, DIGINET_OK) /\
    agree_core I ops B4 /\ M_state B4 = S_IDLE /\ M_fly_on B4 = 0 /\ OW_n B4 = 1 /\ GOT_n B4 = 1 /\
    GOT_t_state B4 0 = OW_t_state B4 0 /\ GOT_t_old B4 0 = OW_t_old B4 0 /\ GOT_t_reason B4 0 = OW_t_reason B4 0 /\
    wframe R_lost B2 B4 /\ g_fail_next B4 = g_fail_next B1.
Proof.
  intros HL I F ops B1 now' st why HC Hn HOW HGOT Hcase. cbv zeta.
  pose proof (ac_len _ _ _ HC) as HB1.
  pose proof (d3_ops _ _ (ac_q _ _ _ HC)) as Hops.
  pose proof (gnow_nonneg B1) as Hg0.
  assert (Hn64 : 0 <= now' < 2 ^ 64) by (unfold OPS_MAX in Hops; clear - Hn Hops Hg0; lia).
  destruct (gnow_step B1 now' HB1 Hn64) as (HL2 & HW2 & HG2).
  set (B2 := set_g_now B1 now') in *. clearbody B2.
  pose proof (ac_cfg _ _ _ HC) as HA. pose proof (ac_st _ _ _ HC) as HS.
  pose proof (ac_time _ _ _ HC) as HT. pose proof (ac_io _ _ _ HC) as HI.
  pose proof (a1_wake_timeout _ HA) as Hwt. pose proof (a1_offline _ HA) as Hof.
  pose proof (c1_wake_sent _ _ HT) as Hws. pose proof (c1_last_rx _ _ HT) as Hlr.
  assert (Rw : 0 <= now' - M_wake_sent B1 < 18446744073709551616) by (clear - Hws Hn Hn64; wrange; lia).
  assert (Rl : 0 <= now' - M_last_rx B1 < 18446744073709551616) by (clear - Hlr Hn Hn64; wrange; lia).
  tf_sames HW2 B1 B2.
  assert (Hms : M_state B1 = st) by (destruct Hcase as [(E1 & _ & E3 & _)|(E1 & _ & E3 & _)]; wrw E1; exact E3).
  assert (Hst : (st = S_WAKING /\ why = R_WAKE_TIMEOUT) \/ (st = S_ONLINE /\ why = R_SILENCE))
    by (destruct Hcase as [(E1 & E2 & _)|(E1 & E2 & _)]; [left|right]; exact (conj E1 E2)).
  assert (Hst0 : st <> S_IDLE) by (clear - Hst; destruct Hst as [(-> & _)|(-> & _)]; tf_unconst; discriminate).
  assert (Hstr : - 2 ^ 31 <= st < 2 ^ 31) by (clear - Hst; destruct Hst as [(-> & _)|(-> & _)]; tf_unconst; lia).
  assert (Hw8 : 0 <= why <= 8) by (clear - Hst; destruct Hst as [(_ & ->)|(_ & ->)]; tf_unconst; lia).
  (* the model's m_tick (FT:246-252) takes m_lost *)
  assert (HT1 : m_tick_m B2 = m_lost_m B2 why).
  { unfold m_tick_m. tf_rw B2.
    wrw (h_ms_small (Cfg_wake_timeout_ms B1) ltac:(clear - Hwt; lia)).
    wrw (h_ms_small (Cfg_offline_ms B1) ltac:(clear - Hof; lia)).
    wrw (u64_small (now' - M_wake_sent B1) Rw). wrw (u64_small (now' - M_last_rx B1) Rl).
    destruct Hcase as [(-> & -> & Hs & Hle)|(-> & -> & Hs & Hle)].
    - destruct (Z.eqb_spec (M_state B1) S_WAKING) as [_|Hx]; [|exfalso; exact (Hx Hs)].
      wrw (proj2 (Z.leb_le _ _) Hle). cbn [andb]. reflexivity.
    - destruct (Z.eqb_spec (M_state B1) S_WAKING) as [Hx|_]; [tf_cl Hx Hs|]. cbn [andb].
      destruct (Z.eqb_spec (M_state B1) S_ONLINE) as [_|Hx]; [|exfalso; exact (Hx Hs)].
      wrw (proj2 (Z.leb_le _ _) Hle). cbn [andb]. reflexivity. }
  assert (HOW2 : OW_n B2 = 0) by (tf_rw B2; exact HOW).
  assert (Hms2 : M_state B2 = st) by (tf_rw B2; exact Hms).
  destruct (m_lost_step B2 st why HL2 HOW2 Hms2 Hst0 Hstr Hw8)
    as (B3 & HM3 & HL3 & HW3 & M1 & M2 & M3 & M4 & M5 & M6 & M7).
  pose proof (wsame_trans B1 B2 B3 _ _ HW2 HW3) as HW13.
  assert (G3 : g_now B3 = now') by (assert (X : g_now B3 = g_now B2) by tf_same HW3; wrw X; exact HG2).
  exists B3.
  tf_sames HW13 B1 B3.
  (* the library's tick (DS:418-427) takes session_lost *)
  assert (HD : diginet_session_tick_m I F B3 now' =
               match session_lost_m I F B3 why with None => None | Some (B, _) => Some (B, DIGINET_OK) end).
  { wrw (tick_unfold I F B3 now'). tf_rw B3.
    wrw (b1_state _ HS). wrw (a2_wake_timeout _ HA). wrw (a2_offline _ HA).
    wrw (b4_wake_sent _ HS). wrw (b4_last_rx _ HS).
    wrw (ms_small (Cfg_wake_timeout_ms B1) ltac:(clear - Hwt; lia)).
    wrw (ms_small (Cfg_offline_ms B1) ltac:(clear - Hof; lia)).
    wrw (u64_small (now' - M_wake_sent B1) Rw). wrw (u64_small (now' - M_last_rx B1) Rl).
    destruct Hcase as [(-> & -> & Hs & Hle)|(-> & -> & Hs & Hle)].
    - destruct (Z.eqb_spec (M_state B1) DIGINET_S_CLOSED) as [Hx|_]; [tf_cl Hx Hs|].
      destruct (Z.eqb_spec (M_state B1) DIGINET_S_IDLE) as [Hx|_]; [tf_cl Hx Hs|]. cbn [orb].
      destruct (Z.eqb_spec (M_state B1) DIGINET_S_WAKING) as [_|Hx]; [|exfalso; exact (Hx Hs)].
      wrw (proj2 (Z.leb_le _ _) Hle). cbn [andb]. reflexivity.
    - destruct (Z.eqb_spec (M_state B1) DIGINET_S_CLOSED) as [Hx|_]; [tf_cl Hx Hs|].
      destruct (Z.eqb_spec (M_state B1) DIGINET_S_IDLE) as [Hx|_]; [tf_cl Hx Hs|]. cbn [orb].
      destruct (Z.eqb_spec (M_state B1) DIGINET_S_WAKING) as [Hx|_]; [tf_cl Hx Hs|]. cbn [andb].
      destruct (Z.eqb_spec (M_state B1) DIGINET_S_ONLINE) as [_|Hx]; [|exfalso; exact (Hx Hs)].
      wrw (proj2 (Z.leb_le _ _) Hle). cbn [andb]. reflexivity. }
  assert (HGOT3 : GOT_n B3 = 0) by (tf_rw B3; exact HGOT).
  assert (HSS3 : S_state B3 = st) by (tf_rw B3; wrw (b1_state _ HS); exact Hms).
  assert (Hst1 : st <> DIGINET_S_IDLE) by exact Hst0.
  assert (HN3 : S_notify B3 = ti_notice I) by (tf_rw B3; exact (a3_notify _ _ HI)).
  destruct (s_lost_step I F B3 st why HL3 HGOT3 HSS3 Hst1 Hstr HN3 Hw8)
    as (B4 & HS4 & HL4 & HW4 & S1 & S2 & S3 & S4 & S5 & S6 & S7).
  exists B4.
  pose proof (wsame_trans B1 B3 B4 _ _ HW13 HW4) as HW14.
  pose proof (wsame_trans B2 B3 B4 _ _ HW3 HW4) as HW24.
  assert (F1 : M_state B4 = S_IDLE)
    by (assert (X : M_state B4 = M_state B3) by tf_same HW4; wrw X; exact M1).
  assert (F2 : M_fly_on B4 = 0)
    by (assert (X : M_fly_on B4 = M_fly_on B3) by tf_same HW4; wrw X; exact M2).
  assert (F3 : M_desk_counter_valid B4 = 0)
    by (assert (X : M_desk_counter_valid B4 = M_desk_counter_valid B3) by tf_same HW4; wrw X; exact M3).
  assert (F4 : OW_n B4 = 1)
    by (assert (X : OW_n B4 = OW_n B3) by tf_same HW4; wrw X; exact M4).
  assert (F5 : OW_t_state B4 0 = S_IDLE)
    by (assert (X : OW_t_state B4 0 = OW_t_state B3 0) by tf_same HW4; wrw X; exact M5).
  assert (F6 : OW_t_old B4 0 = st)
    by (assert (X : OW_t_old B4 0 = OW_t_old B3 0) by tf_same HW4; wrw X; exact M6).
  assert (F7 : OW_t_reason B4 0 = why)
    by (assert (X : OW_t_reason B4 0 = OW_t_reason B3 0) by tf_same HW4; wrw X; exact M7).
  assert (F8 : g_now B4 = now')
    by (assert (X : g_now B4 = g_now B2) by tf_same HW24; wrw X; exact HG2).
  assert (F9 : g_fail_next B4 = g_fail_next B1) by tf_same HW14.
  split; [wrw HT1; exact HM3|].
  split; [exact G3|].
  split; [wrw HD; wrw HS4; reflexivity|].
  split; [exact (agree_lost I ops B1 B4 now' HC Hn HW14 HL4 F8 F1 S1 F2 S2 F3 S3)|].
  split; [exact F1|]. split; [exact F2|]. split; [exact F4|]. split; [exact S4|].
  split; [wrw S5; wrw F5; reflexivity|].
  split; [wrw S6; wrw F6; reflexivity|].
  split; [wrw S7; wrw F7; reflexivity|].
  split; [exact (wframe_weaken _ _ B2 B4 rs_lost_R HW24)|].
  exact F9.
Qed.

(* ---- the drop with N_ACK_LOST (DS:436-441; notice FT:955-957) ---- *)
Lemma acklost_step : forall I F B now,
  (negb (S_inflight B =? 0) && (ms_m (S_cfg_ack_timeout_ms B) <=? u64 (now - S_inflight_sent_us B))) = true ->
  (S_inflight_retries B <? S_cfg_max_retries B) = false ->
  length B = Z.to_nat W_LEN -> S_notify B = ti_notice I -> M_fly_on B = 1 ->
  S_inflight_counter B = M_fly_counter B -> S_inflight_retries B = M_fly_retries B ->
  M_fly_retries B = Cfg_max_retries B -> 0 <= M_fly_retries B <= 7 ->
  exists W, tick_step_m I F B now = Some (inr W) /\ length W = Z.to_nat W_LEN /\ wsame B W rs_al /\
    S_inflight W = 0 /\ M_fly_on W = 0.
Proof.
  intros I F B now T1 T2 HB Hno Hf Hc Hr Hm Hb.
  unfold tick_step_m. wrw T1. wrw T2. cbv beta iota zeta.
  match goal with |- context [call_notify I F ?X _] =>
    assert (E1 : S_notify X = ti_notice I) by (wsimp; exact Hno);
    assert (E2 : S_inflight_counter X = M_fly_counter B) by (wsimp; exact Hc);
    assert (E3 : S_inflight_retries X = M_fly_retries B) by (wsimp; exact Hr);
    assert (E4 : M_fly_on X = 1) by (wsimp; exact Hf);
    assert (E5 : M_fly_counter X = M_fly_counter B) by wsimp;
    assert (E6 : M_fly_retries X = M_fly_retries B) by wsimp;
    assert (E7 : Cfg_max_retries X = Cfg_max_retries B) by wsimp
  end.
  unfold call_notify. wrw E1. wrw (Z.eqb_refl (ti_notice I)). cbv beta iota.
  unfold notice_m. cbv zeta. cbn [n_kind n_counter n_retry].
  wrw nal_state. cbv beta iota. wrw nal_acked. cbv beta iota. wrw nal_lost. cbv beta iota.
  unfold check_inflight_lost_m. cbn [n_counter n_retry].
  wrw E4. wrw truth_1. wrw E2. wrw E5. wrw (Z.eqb_refl (M_fly_counter B)). wrw E3. wrw E6. wrw E7.
  wrw (u16_small (M_fly_retries B) ltac:(clear - Hb; lia)).
  destruct (Z.eqb_spec (M_fly_retries B) (Cfg_max_retries B)) as [_|Hx]; [|exfalso; exact (Hx Hm)].
  cbn [negb orb]. cbv beta iota.
  eexists. split; [reflexivity|].
  split; [wlen|]. split; [wsame_tac|]. split; [wsimp|]. wsimp.
Qed.

(* ---- a retransmission (DS:431-434, :403-412; io_send's retry branch FT:826-843) ---- *)
Lemma tick_step_retx : forall I F B now,
  (negb (S_inflight B =? 0) && (ms_m (S_cfg_ack_timeout_ms B) <=? u64 (now - S_inflight_sent_us B))) = true ->
  (S_inflight_retries B <? S_cfg_max_retries B) = true ->
  tick_step_m I F B now =
    match retransmit_m I F B now with
    | None => None
    | Some (B', r) => if r <? 0 then Some (inl (B', r)) else Some (inr B')
    end.
Proof. intros I F B now H1 H2. unfold tick_step_m. wrw H1. wrw H2. reflexivity. Qed.

(* the world retransmit hands to send_raw (DS:405-410) *)
Definition rt_world (B : list byte) (now : Z) : list byte :=
  let B := set_S_inflight_retries B (u32 (S_inflight_retries B + 1)) in
  let retry := u16 (S_inflight_retries B) in
  let B := upd B (A_S_inflight_frame + DIGINET_ETH_HDR_LEN + 12) (put 1 (u8 (Z.shiftr retry 8))) in
  let B := upd B (A_S_inflight_frame + DIGINET_ETH_HDR_LEN + 13) (put 1 (u8 retry)) in
  let B := set_S_inflight_sent_us B now in
  set_S_stats_tx_retransmits B (u64 (S_stats_tx_retransmits B + 1)).

Lemma retransmit_eq : forall I F B now, retransmit_m I F B now =
  match inflight_bytes (rt_world B now) with None => None | Some fr => send_raw_m I F (rt_world B now) fr end.
Proof. intros I F B now. reflexivity. Qed.

Definition rs_rw : list (Z * Z) :=
  [(A_S_inflight_retries, 4); (A_S_inflight_frame + 26, 2); (A_S_inflight_sent_us, 8);
   (A_S_stats_tx_retransmits, 8)].

Lemma rt_world_ok : forall B now r, length B = Z.to_nat W_LEN -> S_inflight_retries B = r -> 0 <= r ->
  r + 1 < 2 ^ 16 -> 0 <= now < 2 ^ 64 ->
  length (rt_world B now) = Z.to_nat W_LEN /\ wsame B (rt_world B now) rs_rw /\
  S_inflight_retries (rt_world B now) = r + 1 /\ S_inflight_sent_us (rt_world B now) = now /\
  forall n, (28 <= n <= 1514)%nat ->
    sub (rt_world B now) A_S_inflight_frame n =
      firstn 26 (sub B A_S_inflight_frame n) ++ put16 (r + 1) ++ skipn 28 (sub B A_S_inflight_frame n).
Proof.
  intros B now r HB Hr Hr0 Hr16 Hn64. unfold rt_world. cbv zeta.
  wrw Hr. wrw (u32_small (r + 1) ltac:(clear - Hr0 Hr16; lia)).
  assert (E : S_inflight_retries (set_S_inflight_retries B (r + 1)) = r + 1) by wsimp.
  wrw E. wrw (u16_small (r + 1) ltac:(clear - Hr0 Hr16; lia)).
  match goal with |- context [set_S_stats_tx_retransmits _ ?v] => generalize v; intros w end.
  split; [wlen|]. split; [wsame_tac|]. split; [wsimp|]. split; [wsimp|].
  intros n Hn. wsimp.
  match goal with |- context [sub (upd (upd ?X ?j1 (put 1 ?x)) ?j2 (put 1 ?y)) A_S_inflight_frame n] =>
    assert (HX : length X = Z.to_nat W_LEN) by wlen;
    wrw (sub_two X A_S_inflight_frame j1 j2 x y n ltac:(wle) ltac:(vm_compute; reflexivity)
           ltac:(vm_compute; reflexivity) ltac:(clear - Hn; lia)
           ltac:(rewrite HX; clear - Hn; wunfold_addr; lia));
    assert (EX : sub X A_S_inflight_frame n = sub B A_S_inflight_frame n) by wsimp;
    wrw EX
  end.
  wrw (put_be16 (r + 1)). reflexivity.
Qed.

(* io_send (FT:823-899) on a retransmission of the frame in flight: check_sent_frame, then the retry branch
   (FT:840-843: check_inflight_retry, M.fly.retries + 1, M.fly.sent := now) *)
Lemma io_retry_ok : forall (HL : links) I X dst send cmd mode body ncmds r mx ack now sent L,
  length X = Z.to_nat W_LEN -> M_fly_on X = 1 -> M_desk_known X = 1 -> M_desk X = dst -> Cfg_sum_mode X = mode ->
  M_fly_retries X = r -> Cfg_max_retries X = mx -> Cfg_ack_timeout_ms X = ack -> g_now X = now ->
  M_fly_sent X = sent -> M_fly_len X = L ->
  build_ok dst HOST send 0 0 cmd ncmds body mode -> (cmd = SPEC_CMD_E2 \/ cmd = SPEC_CMD_DATA) ->
  0 <= r -> r + 1 <= mx -> mx <= 7 -> 1 <= ack <= 256 -> 0 <= sent -> sent <= now -> now < 2 ^ 64 ->
  1000 * ack <= now - sent -> L = frame_len (length body) ->
  sub X A_M_fly_frame (Z.to_nat L) = lib_frame dst HOST send 0 0 cmd ncmds body mode ->
  io_send_m I X (lib_frame dst HOST send 0 (r + 1) cmd ncmds body mode) =
    Some (set_M_fly_sent (set_M_fly_retries (set_g_fail_next X 0) (r + 1)) now,
          if truth (g_fail_next X) then - EIO else 0).
Proof.
  intros HL I X dst send cmd mode body ncmds r mx ack now sent L HX Hon Hdk Hd Hm Hr Hmx Hack Hg Hs HLf
    Hbo Hcmd Hr0 Hrm Hmx7 Hack1 Hs0 Hsn Hn64 Hov HLb Hfr.
  destruct Hbo as (Hd6 & Hs6 & Hmode & Hsend & Hack0 & Hret0 & Hcm8 & Hnc & Hbl & Hbc).
  assert (Hbo' : build_ok dst HOST send 0 (r + 1) cmd ncmds body mode).
  { refine (conj Hd6 (conj Hs6 (conj Hmode (conj Hsend (conj Hack0 (conj _ (conj Hcm8 (conj Hnc (conj Hbl Hbc))))))))).
    clear - Hr0 Hrm Hmx7. lia. }
  assert (HL1 : 60 <= L <= 1514) by (rewrite HLb; clear - Hbl; unfold frame_len; lia).
  pose proof (rf_lib_frame HL dst HOST send 0 (r + 1) cmd ncmds body mode Hbo') as R. cbv zeta in R.
  destruct R as (Hlenf & Hcode & Hdst0 & Hsrc0 & Hbody0 & Hcmdf & Hsendf & Hackf & Hretf & Hncf & Hblf & Hsubf &
                 Hsd & Hss & Hzf & Hsumf).
  assert (E1 : M_desk_known (set_g_fail_next X 0) = 1) by (wsimp; exact Hdk).
  assert (E2 : M_desk (set_g_fail_next X 0) = dst) by (wsimp; exact Hd).
  assert (E3 : Cfg_sum_mode (set_g_fail_next X 0) = mode) by (wsimp; exact Hm).
  assert (E4 : M_fly_on (set_g_fail_next X 0) = 1) by (wsimp; exact Hon).
  assert (E5 : M_fly_len (set_g_fail_next X 0) = L) by (wsimp; exact HLf).
  assert (E6 : M_fly_retries (set_g_fail_next X 0) = r) by (wsimp; exact Hr).
  assert (E7 : Cfg_max_retries (set_g_fail_next X 0) = mx) by (wsimp; exact Hmx).
  assert (E8 : g_now (set_g_fail_next X 0) = now) by (wsimp; exact Hg).
  assert (E9 : M_fly_sent (set_g_fail_next X 0) = sent) by (wsimp; exact Hs).
  assert (E10 : Cfg_ack_timeout_ms (set_g_fail_next X 0) = ack) by (wsimp; exact Hack).
  assert (E11 : sub (set_g_fail_next X 0) A_M_fly_frame 26 = sub X A_M_fly_frame 26) by wsimp.
  assert (E12 : sub (set_g_fail_next X 0) (A_M_fly_frame + 26 + 2) (Z.to_nat (L - 26 - 2)) =
                sub X (A_M_fly_frame + 26 + 2) (Z.to_nat (L - 26 - 2))) by wsimp.
  assert (Tr : truth (r + 1) = true)
    by (unfold truth; destruct (Z.eqb_spec (r + 1) 0) as [Hx|_]; [clear - Hx Hr0; lia | reflexivity]).
  assert (HCR : check_inflight_retry_m (set_g_fail_next X 0) (lib_frame dst HOST send 0 (r + 1) cmd ncmds body mode) =
                Some (set_g_fail_next X 0, tt)).
  { unfold check_inflight_retry_m. cbv zeta. wrw (eq_refl : RETRY_AT = 26).
    wrw E4. wrw truth_1. wrw Hlenf. wrw E5. wrw (eq_sym HLb). wrw (Z.eqb_refl L).
    wrw (proj2 (Z.ltb_ge L (26 + 2)) ltac:(clear - HL1; lia)). cbn [negb orb]. cbv beta iota.
    wrw (proj2 (Z.ltb_ge W_LEN (A_M_fly_frame + L)) ltac:(clear - HL1; wunfold_addr; lia)). cbv beta iota.
    wrw (eq_refl : Z.to_nat 26 = 26%nat). wrw (eq_refl : Z.to_nat (26 + 2) = 28%nat).
    wrw (lib_frame_retry_head dst HOST send 0 (r + 1) cmd ncmds body mode Hd6 Hs6).
    wrw (lib_frame_retry_tail dst HOST send 0 (r + 1) cmd ncmds body mode Hd6 Hs6).
    wrw E11. wrw E12.
    wrw (eq_sym (sub_firstn_le X A_M_fly_frame 26 (Z.to_nat L) ltac:(clear - HL1; lia))).
    wrw (sub_skip28 X A_M_fly_frame L ltac:(wle) ltac:(clear - HL1; lia)).
    wrw Hfr.
    wrw (lib_frame_retry_head dst HOST send 0 0 cmd ncmds body mode Hd6 Hs6).
    wrw (lib_frame_retry_tail dst HOST send 0 0 cmd ncmds body mode Hd6 Hs6).
    wrw (beq_bytes_refl (lib_head dst HOST send 0 body mode)). wrw (beq_bytes_refl (lib_tail cmd ncmds body)).
    cbn [negb orb]. cbv beta iota.
    wrw Hretf. wrw E6. wrw (u32_small (r + 1) ltac:(clear - Hr0 Hrm Hmx7; lia)). wrw (Z.eqb_refl (r + 1)).
    wrw E7. wrw (proj2 (Z.ltb_ge mx (r + 1)) Hrm). cbn [negb orb]. cbv beta iota.
    wrw E8. wrw E9. wrw E10.
    wrw (u64_small (now - sent) ltac:(clear - Hs0 Hsn Hn64; lia)). wrw (h_ms_small ack ltac:(clear - Hack1; lia)).
    wrw (proj2 (Z.ltb_ge (now - sent) (1000 * ack)) Hov). cbv beta iota. reflexivity. }
  unfold io_send_m. cbv zeta.
  wrw (sent_frame_ok HL (set_g_fail_next X 0) dst HOST send 0 (r + 1) cmd ncmds body mode Hbo' eq_refl E1 E2 E3).
  cbv beta iota. wrw Hcmdf. wrw Hretf.
  destruct Hcmd as [-> | ->].
  - tf_ceq SPEC_CMD_E2 SPEC_CMD_ACK. cbv beta iota. tf_ceq SPEC_CMD_E2 SPEC_CMD_E2. cbn [orb]. cbv beta iota.
    wrw Tr. cbv beta iota. wrw HCR. cbv beta iota.
    wrw E6. wrw (u32_small (r + 1) ltac:(clear - Hr0 Hrm Hmx7; lia)). wrw E8. reflexivity.
  - tf_ceq SPEC_CMD_DATA SPEC_CMD_ACK. cbv beta iota. tf_ceq SPEC_CMD_DATA SPEC_CMD_E2.
    tf_ceq SPEC_CMD_DATA SPEC_CMD_DATA. cbn [orb]. cbv beta iota.
    wrw Tr. cbv beta iota. wrw HCR. cbv beta iota.
    wrw E6. wrw (u32_small (r + 1) ltac:(clear - Hr0 Hrm Hmx7; lia)). wrw E8. reflexivity.
Qed.

(* retransmit_m end to end: the world, the code (0, or -EIO when the harness fails the send, FT:826-829, :898) *)
Lemma retx_step : forall (HL : links) I F B now body ncmds r,
  length B = Z.to_nat W_LEN -> S_inflight_retries B = r -> M_fly_retries B = r -> 0 <= r ->
  r + 1 <= Cfg_max_retries B -> Cfg_max_retries B <= 7 ->
  M_fly_on B = 1 -> M_desk_known B = 1 -> (M_fly_cmd B = SPEC_CMD_E2 \/ M_fly_cmd B = SPEC_CMD_DATA) ->
  build_ok (M_desk B) HOST (M_fly_counter B) 0 0 (M_fly_cmd B) ncmds body (Cfg_sum_mode B) ->
  S_inflight_len B = M_fly_len B -> M_fly_len B = frame_len (length body) -> S_io_send B = ti_io_send I ->
  g_now B = now -> M_fly_sent B <= now -> now < 2 ^ 64 -> 1 <= Cfg_ack_timeout_ms B <= 256 ->
  1000 * Cfg_ack_timeout_ms B <= now - M_fly_sent B ->
  sub B A_M_fly_frame (Z.to_nat (M_fly_len B)) =
    lib_frame (M_desk B) HOST (M_fly_counter B) 0 0 (M_fly_cmd B) ncmds body (Cfg_sum_mode B) ->
  sub B A_S_inflight_frame (Z.to_nat (M_fly_len B)) =
    lib_frame (M_desk B) HOST (M_fly_counter B) 0 r (M_fly_cmd B) ncmds body (Cfg_sum_mode B) ->
  exists W rv, retransmit_m I F B now = Some (W, rv) /\ (rv = 0 \/ rv = - EIO) /\ length W = Z.to_nat W_LEN /\
    wsame B W rs_rt /\ S_inflight_retries W = r + 1 /\ M_fly_retries W = r + 1 /\ S_inflight_sent_us W = now /\
    M_fly_sent W = now /\ g_fail_next W = 0 /\
    sub W A_S_inflight_frame (Z.to_nat (M_fly_len B)) =
      firstn 26 (sub B A_S_inflight_frame (Z.to_nat (M_fly_len B))) ++ put16 (r + 1) ++
      skipn 28 (sub B A_S_inflight_frame (Z.to_nat (M_fly_len B))).
Proof.
  intros HL I F B now body ncmds r HB Hsr Hmr Hr0 Hle Hmx Hon Hdk Hcmd Hbo Hsl Hfl Hio Hg Hsn Hn64 Hack Hov Hm Hs.
  pose proof Hbo as Hbo2. destruct Hbo2 as (Hd6 & _ & _ & _ & _ & _ & _ & _ & Hbl & _).
  assert (HL60 : 60 <= M_fly_len B <= 1514) by (wrw Hfl; clear - Hbl; unfold frame_len; lia).
  assert (Hn : (28 <= Z.to_nat (M_fly_len B) <= 1514)%nat) by (clear - HL60; lia).
  assert (Hnow0 : 0 <= now) by exact (eq_ind (g_now B) (fun x => 0 <= x) (gnow_nonneg B) now Hg).
  assert (Hs0 : 0 <= M_fly_sent B) by exact (proj1 (u_at_range B A_M_fly_sent 8)).
  destruct (rt_world_ok B now r HB Hsr Hr0 ltac:(clear - Hle Hmx; lia) ltac:(clear - Hnow0 Hn64; lia))
    as (HRL & HRW & HR1 & HR2 & HRF).
  specialize (HRF (Z.to_nat (M_fly_len B)) Hn).
  wrw (retransmit_eq I F B now).
  assert (E1 : S_inflight_len (rt_world B now) = M_fly_len B)
    by (assert (X : S_inflight_len (rt_world B now) = S_inflight_len B) by tf_same HRW; wrw X; exact Hsl).
  unfold inflight_bytes. wrw E1.
  destruct (Z.ltb_spec 1514 (M_fly_len B)) as [Hx|_]; [exfalso; clear - HL60 Hx; lia|].
  cbv beta iota.
  assert (Efr : sub (rt_world B now) A_S_inflight_frame (Z.to_nat (M_fly_len B)) =
                lib_frame (M_desk B) HOST (M_fly_counter B) 0 (r + 1) (M_fly_cmd B) ncmds body (Cfg_sum_mode B)).
  { wrw HRF. wrw Hs.
    exact (lib_frame_retry_set (M_desk B) HOST (M_fly_counter B) 0 r (r + 1) (M_fly_cmd B) ncmds body (Cfg_sum_mode B)
             Hd6 eq_refl ltac:(clear - Hr0 Hle Hmx; lia)). }
  wrw Efr.
  unfold send_raw_m, call_send.
  assert (E2 : S_io_send (rt_world B now) = ti_io_send I)
    by (assert (X : S_io_send (rt_world B now) = S_io_send B) by tf_same HRW; wrw X; exact Hio).
  wrw E2. wrw (Z.eqb_refl (ti_io_send I)). cbv beta iota.
  assert (E3 : M_fly_on (rt_world B now) = 1)
    by (assert (X : M_fly_on (rt_world B now) = M_fly_on B) by tf_same HRW; wrw X; exact Hon).
  assert (E4 : M_desk_known (rt_world B now) = 1)
    by (assert (X : M_desk_known (rt_world B now) = M_desk_known B) by tf_same HRW; wrw X; exact Hdk).
  assert (E5 : M_desk (rt_world B now) = M_desk B) by tf_same HRW.
  assert (E6 : Cfg_sum_mode (rt_world B now) = Cfg_sum_mode B) by tf_same HRW.
  assert (E7 : M_fly_retries (rt_world B now) = r)
    by (assert (X : M_fly_retries (rt_world B now) = M_fly_retries B) by tf_same HRW; wrw X; exact Hmr).
  assert (E8 : Cfg_max_retries (rt_world B now) = Cfg_max_retries B) by tf_same HRW.
  assert (E9 : Cfg_ack_timeout_ms (rt_world B now) = Cfg_ack_timeout_ms B) by tf_same HRW.
  assert (E10 : g_now (rt_world B now) = now)
    by (assert (X : g_now (rt_world B now) = g_now B) by tf_same HRW; wrw X; exact Hg).
  assert (E11 : M_fly_sent (rt_world B now) = M_fly_sent B) by tf_same HRW.
  assert (E12 : M_fly_len (rt_world B now) = M_fly_len B) by tf_same HRW.
  assert (Em : sub (rt_world B now) A_M_fly_frame (Z.to_nat (M_fly_len B)) =
               lib_frame (M_desk B) HOST (M_fly_counter B) 0 0 (M_fly_cmd B) ncmds body (Cfg_sum_mode B)).
  { wrw (wsame_sub_le B (rt_world B now) rs_rw A_M_fly_frame (Z.to_nat (M_fly_len B)) 1514 HRW ltac:(wle)
           ltac:(clear - Hn; lia) ltac:(vm_compute; reflexivity)).
    exact Hm. }
  wrw (io_retry_ok HL I (rt_world B now) (M_desk B) (M_fly_counter B) (M_fly_cmd B) (Cfg_sum_mode B) body ncmds r
         (Cfg_max_retries B) (Cfg_ack_timeout_ms B) now (M_fly_sent B) (M_fly_len B)
         HRL E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 Hbo Hcmd Hr0 Hle Hmx Hack Hs0 Hsn Hn64 Hov Hfl Em).
  cbv beta iota.
  destruct (truth (g_fail_next (rt_world B now))).
  - cbv beta iota. wrw eio_ne0. cbv beta iota.
    eexists. eexists. split; [reflexivity|]. split; [right; reflexivity|].
    split; [wlen|].
    split; [apply (wsame_weaken_b B _ (rs_rw ++ [(OFF_g_fail_next, 1); (A_M_fly_retries, 4); (A_M_fly_sent, 8)]) rs_rt);
            [apply (wsame_trans B (rt_world B now) _ rs_rw [(OFF_g_fail_next, 1); (A_M_fly_retries, 4); (A_M_fly_sent, 8)]); [exact HRW | wsame_tac] | vm_compute; reflexivity]|].
    split; [wsimp; exact HR1|].
    split; [wsimp|].
    split; [wsimp; exact HR2|].
    split; [wsimp|].
    split; [wsimp|].
    wsimp. exact HRF.
  - cbv beta iota. wrw (Z.eqb_refl 0). cbv beta iota.
    match goal with |- context [set_S_stats_tx_frames _ ?v] => generalize v; intros v' end.
    eexists. eexists. split; [reflexivity|]. split; [left; reflexivity|].
    split; [wlen|].
    split; [apply (wsame_weaken_b B _ (rs_rw ++ [(OFF_g_fail_next, 1); (A_M_fly_retries, 4); (A_M_fly_sent, 8); (A_S_stats_tx_frames, 8)]) rs_rt);
            [apply (wsame_trans B (rt_world B now) _ rs_rw [(OFF_g_fail_next, 1); (A_M_fly_retries, 4); (A_M_fly_sent, 8); (A_S_stats_tx_frames, 8)]); [exact HRW | wsame_tac] | vm_compute; reflexivity]|].
    split; [wsimp; exact HR1|].
    split; [wsimp|].
    split; [wsimp; exact HR2|].
    split; [wsimp|].
    split; [wsimp|].
    wsimp. exact HRF.
Qed.

(* ---- the in-flight step (front_step_ok) ---- *)
Lemma front_step_ok : forall (HL : links) I F ops B1 now',
  agree_core I ops B1 -> g_now B1 <= now' <= 1000000 + ops * 65535000000 ->
  (M_state B1 = S_WAKING -> now' - M_wake_sent B1 < 1000 * Cfg_wake_timeout_ms B1) ->
  (M_state B1 = S_ONLINE -> now' - M_last_rx B1 < 1000 * Cfg_offline_ms B1) ->
  let B2 := set_g_now B1 now' in
  exists res, tick_step_m I F B2 now' = Some res /\
    match res with
    | inl (W, r) => tick_post I ops B2 W
    | inr W => agree_core I ops W /\ wframe R_tick B2 W /\
               (g_fail_next W = g_fail_next B2 \/ g_fail_next W = 0) /\ g_now W = now'
    end.
Proof.
  intros HL I F ops B1 now' HC Hn Hwk Hon. cbv zeta.
  pose proof (ac_len _ _ _ HC) as HB1.
  pose proof (d3_ops _ _ (ac_q _ _ _ HC)) as Hops.
  pose proof (gnow_nonneg B1) as Hg0.
  assert (Hn64 : 0 <= now' < 2 ^ 64) by (unfold OPS_MAX in Hops; clear - Hn Hops Hg0; lia).
  destruct (gnow_step B1 now' HB1 Hn64) as (HL2 & HW2 & HG2).
  set (B2 := set_g_now B1 now') in *. clearbody B2.
  pose proof (ac_cfg _ _ _ HC) as HA. pose proof (ac_st _ _ _ HC) as HS. pose proof (ac_fly _ _ _ HC) as HF.
  pose proof (ac_time _ _ _ HC) as HT. pose proof (ac_io _ _ _ HC) as HI.
  pose proof (a1_ack_timeout _ HA) as Hack. pose proof (a1_max_retries _ HA) as Hmx.
  tf_sames HW2 B1 B2.
  destruct (b8_on01 _ HF) as [Hf0|Hf1].
  - (* nothing in flight: on to the tail *)
    assert (T1 : (negb (S_inflight B2 =? 0) && (ms_m (S_cfg_ack_timeout_ms B2) <=? u64 (now' - S_inflight_sent_us B2)))
                 = false)
      by (tf_rw B2; wrw (b8_on _ HF); wrw Hf0; wrw (Z.eqb_refl 0); reflexivity).
    exists (inr B2). split; [exact (tick_step_quiet I F B2 now' T1)|].
    split; [exact (agree_quiet I ops B1 B2 now' HC Hn Hwk Hon ltac:(intros Hx; tf_cl Hx Hf0) HW2 HL2 HG2)|].
    split; [exact (wframe_refl R_tick B2)|]. split; [left; reflexivity|]. exact HG2.
  - pose proof (b8_retries _ HF Hf1) as Hsr. pose proof (b8_retries_le _ HF Hf1) as Hrle.
    pose proof (b8_sent _ HF Hf1) as Hss. pose proof (c1_fly_sent _ _ HT Hf1) as Hfs.
    assert (Hfs0 : 0 <= M_fly_sent B1) by exact (proj1 (u_at_range B1 A_M_fly_sent 8)).
    assert (Hr0 : 0 <= M_fly_retries B1) by exact (proj1 (u_at_range B1 A_M_fly_retries 4)).
    assert (Rf : 0 <= now' - M_fly_sent B1 < 18446744073709551616) by (clear - Hfs Hn Hn64 Hfs0; lia).
    assert (Ev : (ms_m (S_cfg_ack_timeout_ms B2) <=? u64 (now' - S_inflight_sent_us B2)) =
                 (1000 * Cfg_ack_timeout_ms B1 <=? now' - M_fly_sent B1)).
    { tf_rw B2. wrw (a2_ack_timeout _ HA). wrw Hss.
      wrw (ms_small (Cfg_ack_timeout_ms B1) ltac:(clear - Hack; lia)). wrw (u64_small (now' - M_fly_sent B1) Rf).
      reflexivity. }
    destruct (Z.leb_spec (1000 * Cfg_ack_timeout_ms B1) (now' - M_fly_sent B1)) as [Hov|Hnov].
    + (* overdue (DS:430) *)
      assert (T1 : (negb (S_inflight B2 =? 0) && (ms_m (S_cfg_ack_timeout_ms B2) <=? u64 (now' - S_inflight_sent_us B2)))
                   = true).
      { wrw Ev. tf_rw B2. wrw (b8_on _ HF). wrw Hf1. wrw eqb_1_0. wrw (proj2 (Z.leb_le _ _) Hov). reflexivity. }
      destruct (Z.ltb_spec (M_fly_retries B1) (Cfg_max_retries B1)) as [Hlt|Hge].
      * (* retries left: retransmit (DS:431-434) *)
        assert (T2 : (S_inflight_retries B2 <? S_cfg_max_retries B2) = true)
          by (tf_rw B2; wrw Hsr; wrw (a2_max_retries _ HA); wrw (proj2 (Z.ltb_lt _ _) Hlt); reflexivity).
        destruct (fly_frames_ok B1 HB1 HA HS HF Hf1) as (Hdk1 & body & ncmds & Hbo0 & _ & Hfl1 & Hm1 & Hs1).
        assert (Hn15 : (Z.to_nat (M_fly_len B1) <= 1514)%nat).
        { destruct Hbo0 as (_ & _ & _ & _ & _ & _ & _ & _ & Hbl & _). wrw Hfl1. clear - Hbl. unfold frame_len. lia. }
        assert (X1 : S_inflight_retries B2 = M_fly_retries B1) by (tf_rw B2; exact Hsr).
        assert (X2 : M_fly_retries B2 = M_fly_retries B1) by tf_same HW2.
        assert (X3 : M_fly_retries B1 + 1 <= Cfg_max_retries B2) by (tf_rw B2; clear - Hlt; lia).
        assert (X4 : Cfg_max_retries B2 <= 7) by (tf_rw B2; exact Hmx).
        assert (X5 : M_fly_on B2 = 1) by (tf_rw B2; exact Hf1).
        assert (X6 : M_desk_known B2 = 1) by (tf_rw B2; exact Hdk1).
        assert (X7 : M_fly_cmd B2 = SPEC_CMD_E2 \/ M_fly_cmd B2 = SPEC_CMD_DATA) by (tf_rw B2; exact (b8_cmd _ HF Hf1)).
        assert (X8 : build_ok (M_desk B2) HOST (M_fly_counter B2) 0 0 (M_fly_cmd B2) ncmds body (Cfg_sum_mode B2))
          by (tf_rw B2; exact Hbo0).
        assert (Efl : M_fly_len B2 = M_fly_len B1) by tf_same HW2.
        assert (X9 : S_inflight_len B2 = M_fly_len B2) by (tf_rw B2; exact (b8_len _ HF Hf1)).
        assert (X10 : M_fly_len B2 = frame_len (length body)) by (tf_rw B2; exact Hfl1).
        assert (X11 : S_io_send B2 = ti_io_send I) by (tf_rw B2; exact (a3_io_send _ _ HI)).
        assert (X12 : M_fly_sent B2 <= now') by (tf_rw B2; clear - Hfs Hn; lia).
        assert (X13 : 1 <= Cfg_ack_timeout_ms B2 <= 256) by (tf_rw B2; exact Hack).
        assert (X14 : 1000 * Cfg_ack_timeout_ms B2 <= now' - M_fly_sent B2) by (tf_rw B2; exact Hov).
        assert (X15 : sub B2 A_M_fly_frame (Z.to_nat (M_fly_len B2)) =
                      lib_frame (M_desk B2) HOST (M_fly_counter B2) 0 0 (M_fly_cmd B2) ncmds body (Cfg_sum_mode B2)).
        { wrw Efl. tf_rw B2.
          wrw (wsame_sub_le B1 B2 [(OFF_g_now, 8)] A_M_fly_frame (Z.to_nat (M_fly_len B1)) 1514 HW2 ltac:(wle) Hn15
                 ltac:(vm_compute; reflexivity)).
          exact Hm1. }
        assert (X16 : sub B2 A_S_inflight_frame (Z.to_nat (M_fly_len B2)) =
                      lib_frame (M_desk B2) HOST (M_fly_counter B2) 0 (M_fly_retries B1) (M_fly_cmd B2) ncmds body
                        (Cfg_sum_mode B2)).
        { wrw Efl. tf_rw B2.
          wrw (wsame_sub_le B1 B2 [(OFF_g_now, 8)] A_S_inflight_frame (Z.to_nat (M_fly_len B1)) 1514 HW2 ltac:(wle) Hn15
                 ltac:(vm_compute; reflexivity)).
          exact Hs1. }
        destruct (retx_step HL I F B2 now' body ncmds (M_fly_retries B1) HL2 X1 X2 Hr0 X3 X4 X5 X6 X7 X8 X9 X10 X11
                    HG2 X12 (proj2 Hn64) X13 X14 X15 X16)
          as (W & rv & HR & Hrv & HLW & HWW & W1 & W2 & W3 & W4 & W5 & W6).
        pose proof (wsame_trans B1 B2 W _ _ HW2 HWW) as HW1W.
        assert (GW : g_now W = now') by (assert (X : g_now W = g_now B2) by tf_same HWW; wrw X; exact HG2).
        assert (W6' : sub W A_S_inflight_frame (Z.to_nat (M_fly_len B1)) =
                      firstn 26 (sub B1 A_S_inflight_frame (Z.to_nat (M_fly_len B1))) ++ put16 (M_fly_retries B1 + 1) ++
                      skipn 28 (sub B1 A_S_inflight_frame (Z.to_nat (M_fly_len B1)))).
        { wrw (eq_sym (wsame_sub_le B1 B2 [(OFF_g_now, 8)] A_S_inflight_frame (Z.to_nat (M_fly_len B1)) 1514 HW2
                         ltac:(wle) Hn15 ltac:(vm_compute; reflexivity))).
          wrw (eq_sym Efl). exact W6. }
        assert (HA1 : agree_core I ops W)
          by exact (agree_retx I ops B1 W now' HC Hn Hwk Hon Hf1 ltac:(clear - Hlt; lia) HW1W HLW GW W1 W2 W3 W4 W5 W6').
        assert (Hfw : M_fly_on W = 1)
          by (assert (X : M_fly_on W = M_fly_on B1) by tf_same HW1W; wrw X; exact Hf1).
        destruct Hrv as [-> | ->].
        -- (* sent: on to the tail *)
           exists (inr W). split; [wrw (tick_step_retx I F B2 now' T1 T2); wrw HR; reflexivity|].
           split; [exact HA1|]. split; [exact (wframe_weaken _ _ B2 W rs_rt_R HWW)|].
           split; [right; exact W5|]. exact GW.
        -- (* the harness failed the send: the tick returns -EIO (DS:433-434) *)
           exists (inl (W, - EIO)). split; [wrw (tick_step_retx I F B2 now' T1 T2); wrw HR; reflexivity|].
           constructor.
           ++ exact HA1.
           ++ unfold c2_keepalive. intros _ _ Hx. exfalso. clear - Hx Hfw. lia.
           ++ unfold drain_fact. intros _ _ Hx. exfalso. clear - Hx Hfw. lia.
           ++ exact (wframe_weaken _ _ B2 W rs_rt_R HWW).
           ++ right. exact W5.
      * (* retries spent: drop and N_ACK_LOST (DS:436-441) *)
        assert (Heq : M_fly_retries B1 = Cfg_max_retries B1) by (clear - Hge Hrle; lia).
        assert (T2 : (S_inflight_retries B2 <? S_cfg_max_retries B2) = false)
          by (tf_rw B2; wrw Hsr; wrw (a2_max_retries _ HA); wrw (proj2 (Z.ltb_ge _ _) Hge); reflexivity).
        assert (X1 : S_notify B2 = ti_notice I) by (tf_rw B2; exact (a3_notify _ _ HI)).
        assert (X2 : M_fly_on B2 = 1) by (tf_rw B2; exact Hf1).
        assert (X3 : S_inflight_counter B2 = M_fly_counter B2) by (tf_rw B2; exact (b8_counter _ HF Hf1)).
        assert (X4 : S_inflight_retries B2 = M_fly_retries B2) by (tf_rw B2; exact Hsr).
        assert (X5 : M_fly_retries B2 = Cfg_max_retries B2) by (tf_rw B2; exact Heq).
        assert (X6 : 0 <= M_fly_retries B2 <= 7) by (tf_rw B2; clear - Hr0 Hrle Hmx; lia).
        destruct (acklost_step I F B2 now' T1 T2 HL2 X1 X2 X3 X4 X5 X6) as (W & HR & HLW & HWW & W1 & W2).
        pose proof (wsame_trans B1 B2 W _ _ HW2 HWW) as HW1W.
        assert (GW : g_now W = now') by (assert (X : g_now W = g_now B2) by tf_same HWW; wrw X; exact HG2).
        exists (inr W). split; [exact HR|].
        split; [exact (agree_acklost I ops B1 W now' HC Hn Hwk Hon HW1W HLW GW W1 W2)|].
        split; [exact (wframe_weaken _ _ B2 W rs_al_R HWW)|].
        split; [left; tf_same HWW|]. exact GW.
    + (* not overdue: on to the tail *)
      assert (T1 : (negb (S_inflight B2 =? 0) && (ms_m (S_cfg_ack_timeout_ms B2) <=? u64 (now' - S_inflight_sent_us B2)))
                   = false).
      { wrw Ev. wrw (proj2 (Z.leb_gt _ _) Hnov). exact (andb_false_r _). }
      exists (inr B2). split; [exact (tick_step_quiet I F B2 now' T1)|].
      split; [exact (agree_quiet I ops B1 B2 now' HC Hn Hwk Hon (fun _ => Hnov) HW2 HL2 HG2)|].
      split; [exact (wframe_refl R_tick B2)|]. split; [left; reflexivity|]. exact HG2.
Qed.
