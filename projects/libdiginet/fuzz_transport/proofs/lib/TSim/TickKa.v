(* tick_ka_m (TickDefs.v; diginet_session.c:449-456) run in a world B in agree_core at its current time g_now B,
   the session ONLINE with nothing in flight, the back-off passed and the keepalive due:
   - DS:451-453 the deadline moves to next_keepalive + ms keepalive, clamped to now + ms keepalive (ka_nk);
     DS:454 the stats (ka_prefix);
   - send_data (DS:388-400) of the body {0}, one command: host_counter + 1, the frame diginet_frame_build makes
     (lib_frame, 60 bytes) in s->inflight_frame, inflight_start, the stats, send_raw (ka_send_data);
   - io_send (fuzz_transport.c:823-899) on that frame: g_fail_next cleared, check_sent_frame (SendOk.v),
     check_inflight_new, check_latest_frame, M.host_counter / g_last_counter, in tagged mode check_keepalive_due
     and the harness's own next keepalive (the same ka_nk), then M.fly (ka_io);
   - send_raw's tx_frames when io_send returned 0 (DS:91-92).
   The world after satisfies every clause of agree_core (the changed fields: B5 next keepalive, B7, B8 with the
   body {0} and one command, C1 / C2 of the frame in flight, E1), C2's keepalive clause and the drain fact hold
   because a frame is in flight, the writes lie inside R_tick, and g_fail_next is 0 (ka_post).
   tick_ka_keep: the same, and the writes lie inside ka_W (ka_W_trans), which misses world bytes 0..15
   (M.desk_known, M.desk, M.state: ka_W_low); tick_ka_ok is its tick_post part. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TNeed TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree Links SendOk SimLib Deadline SettleOk TickDefs.
Import ListNotations.
Open Scope Z_scope.

(* ---------------------------------------------------------------- reads and writes of a world of W_LEN bytes
   (over TWorldLemmas / SimLib; a world X has length X = Z.to_nat W_LEN, every write lies inside it) *)

Lemma ka_wl : forall X k v, length X = Z.to_nat W_LEN -> 0 <= k -> k + Z.of_nat (length v) <= W_LEN ->
  length (upd X k v) = Z.to_nat W_LEN.
Proof. intros X k v HX Hk Hv. rewrite (length_upd X v k Hk); [exact HX|]. rewrite HX. lia. Qed.

Lemma ka_ua_out : forall X k v j n, length X = Z.to_nat W_LEN -> 0 <= k -> 0 <= j ->
  k + Z.of_nat (length v) <= W_LEN -> (j + Z.of_nat n <= k \/ k + Z.of_nat (length v) <= j) ->
  u_at (upd X k v) j n = u_at X j n.
Proof. intros X k v j n HX Hk Hj Hv Hd. apply (u_at_upd_out X v k j n Hk Hj Hd). rewrite HX. lia. Qed.

Lemma ka_s32_out : forall X k v j, length X = Z.to_nat W_LEN -> 0 <= k -> 0 <= j ->
  k + Z.of_nat (length v) <= W_LEN -> (j + 4 <= k \/ k + Z.of_nat (length v) <= j) ->
  s32_at (upd X k v) j = s32_at X j.
Proof. intros X k v j HX Hk Hj Hv Hd. apply (s32_at_upd_out X v k j Hk Hj Hd). rewrite HX. lia. Qed.

Lemma ka_sb_out : forall X k v j n, length X = Z.to_nat W_LEN -> 0 <= k -> 0 <= j ->
  k + Z.of_nat (length v) <= W_LEN -> (j + Z.of_nat n <= k \/ k + Z.of_nat (length v) <= j) ->
  sub (upd X k v) j n = sub X j n.
Proof. intros X k v j n HX Hk Hj Hv Hd. apply (sub_upd_out X v k j n Hk Hj Hd). rewrite HX. lia. Qed.

Lemma ka_sb_same : forall X k v n, length X = Z.to_nat W_LEN -> 0 <= k -> length v = n ->
  k + Z.of_nat n <= W_LEN -> sub (upd X k v) k n = v.
Proof. intros X k v n HX Hk Hl Hv. apply (sub_upd_eq X v k n Hk Hl). rewrite HX, Hl. lia. Qed.

Lemma ka_ua_same8 : forall X k x, length X = Z.to_nat W_LEN -> 0 <= k -> k + 8 <= W_LEN ->
  u_at (upd X k (put 8 x)) k 8 = x mod 2 ^ 64.
Proof. intros X k x HX Hk Hv. rewrite (u_at_upd_put X k 8 x Hk); [reflexivity|]. rewrite HX. lia. Qed.

Lemma ka_ua_same4 : forall X k x, length X = Z.to_nat W_LEN -> 0 <= k -> k + 4 <= W_LEN ->
  u_at (upd X k (put 4 x)) k 4 = x mod 2 ^ 32.
Proof. intros X k x HX Hk Hv. rewrite (u_at_upd_put X k 4 x Hk); [reflexivity|]. rewrite HX. lia. Qed.

Lemma ka_ua_same1 : forall X k x, length X = Z.to_nat W_LEN -> 0 <= k -> k + 1 <= W_LEN ->
  u_at (upd X k (put 1 x)) k 1 = x mod 2 ^ 8.
Proof. intros X k x HX Hk Hv. rewrite (u_at_upd_put X k 1 x Hk); [reflexivity|]. rewrite HX. lia. Qed.

Lemma ka_s32_same : forall X k x, length X = Z.to_nat W_LEN -> 0 <= k -> k + 4 <= W_LEN ->
  - 2 ^ 31 <= x < 2 ^ 31 -> s32_at (upd X k (put 4 x)) k = x.
Proof. intros X k x HX Hk Hv Hx. apply (s32_at_upd_same X k x Hk); [rewrite HX; lia | exact Hx]. Qed.

Lemma ka_wf_upd : forall (R : Z -> Prop) B X k v, wframe R B X -> length X = Z.to_nat W_LEN -> 0 <= k ->
  k + Z.of_nat (length v) <= W_LEN -> (forall a, k <= a < k + Z.of_nat (length v) -> R a) ->
  wframe R B (upd X k v).
Proof.
  intros R B X k v HW HX Hk Hv HR. apply (wframe_trans R B X (upd X k v) HW).
  apply (wframe_upd R X k v Hk); [rewrite HX; lia | exact HR].
Qed.

Lemma ka_u32_mod : forall x, u32 x mod 2 ^ 32 = u32 x.
Proof. intros x. unfold u32. apply Z.mod_mod. lia. Qed.

Lemma ka_u64_mod : forall x, u64 x mod 2 ^ 64 = u64 x.
Proof. intros x. unfold u64. apply Z.mod_mod. lia. Qed.

Lemma ka_ua_mod8 : forall X j, u_at X j 8 mod 2 ^ 64 = u_at X j 8.
Proof. intros X j. apply Z.mod_small. exact (u_at_range X j 8). Qed.

Lemma ka_hms : forall v, h_ms_m v = ms_m v.
Proof. intros v. reflexivity. Qed.

(* the keepalive deadline after DS:451-453 (and the harness's FT:871-873): x + ms ka, clamped to now + ms ka *)
Definition ka_nk (x ka now : Z) : Z :=
  if u64 (x + ms_m ka) <=? now then u64 (now + ms_m ka) else u64 (x + ms_m ka).

Lemma ka_nk_le : forall x ka now, 0 <= x <= now -> 1 <= ka <= 65536 -> now + 65536000 < 2 ^ 64 ->
  ka_nk x ka now <= now + 65536000.
Proof.
  intros x ka now Hx Hka Hn. change (2 ^ 64) with 18446744073709551616 in Hn.
  unfold ka_nk. rewrite (ms_small ka) by lia.
  rewrite (u64_small (x + 1000 * ka)) by lia. rewrite (u64_small (now + 1000 * ka)) by lia.
  destruct (Z.leb_spec (x + 1000 * ka) now); lia.
Qed.

(* the keepalive body (DS:449 ka[1] = {0}) passes diginet_body_check *)
Lemma ka_bc : body_check [b8 0] = DIGINET_OK.
Proof. vm_compute. reflexivity. Qed.

(* ---------------------------------------------------------------- the bytes each piece writes *)

(* tick_ka_m's prefix (DS:451-454): s->next_keepalive_us and the stats *)
Definition ka_Wpre (a : Z) : Prop :=
  (A_S_next_keepalive_us <= a < A_S_next_keepalive_us + 8) \/ (A_S_stats_rx_frames <= a < OFF_g_s + SZ_g_s).
(* the library's writes (DS:391-399 too): host_counter, next_keepalive_us, inflight .. inflight_sent_us, stats *)
Definition ka_Wlib (a : Z) : Prop :=
  (A_S_host_counter <= a < A_S_host_counter + 4) \/ (A_S_next_keepalive_us <= a < A_S_next_keepalive_us + 8) \/
  (A_S_inflight <= a < A_S_queue_bytes 0) \/ (A_S_stats_rx_frames <= a < OFF_g_s + SZ_g_s).
(* io_send's writes (FT:829, :867-873, :883-889): M.next_ka, M.host_counter, M.fly, g_fail_next, g_last_counter *)
Definition ka_Wio (a : Z) : Prop :=
  (A_M_next_ka <= a < A_M_next_ka + 8) \/ (A_M_host_counter <= a < A_M_host_counter + 4) \/
  (A_M_fly_on <= a < OFF_M + SZ_M) \/ (OFF_g_fail_next <= a < OFF_g_fail_next + 1) \/
  (OFF_g_last_counter <= a < OFF_g_last_counter + 4).
(* send_raw's stats (DS:91-92) *)
Definition ka_Wst (a : Z) : Prop := A_S_stats_rx_frames <= a < OFF_g_s + SZ_g_s.
Definition ka_W (a : Z) : Prop := ka_Wlib a \/ ka_Wio a.

(* ---------------------------------------------------------------- tactics (the address unfoldings run A_ first, then the OFF_ / SZ_ they expose)
   No tactic here lets the unifier compare two reads (SimLib.v's SAFETY note): a getter is unfolded to
   s32_at / u_at / sub of a chain of upd, and each read through a write is rewritten by a fully applied
   instance of a ka_ lemma whose left side Ltac's syntactic matching found in the goal; side conditions are
   offsets (lia on the unfolded numbers) and lengths (length_put, or a hypothesis length v = n). *)

Local Ltac ka_ua := unfold A_M_desk_known, A_M_desk, A_M_state, A_M_e2_acked, A_M_e1_us, A_M_foreign, A_M_last_rx, A_M_wake_sent, A_M_next_ka, A_M_backoff_until, A_M_last_display, A_M_display_sent, A_M_desk_counter_valid, A_M_desk_counter, A_M_host_counter, A_M_fail, A_M_fly_on, A_M_fly_cmd, A_M_fly_counter, A_M_fly_retries, A_M_fly_sent, A_M_fly_frame, A_M_fly_len, A_S_cfg_host_mac, A_S_cfg_desk_mac, A_S_cfg_desk_mac_set, A_S_cfg_auto_wake, A_S_cfg_sum_mode, A_S_cfg_keepalive_ms, A_S_cfg_ack_timeout_ms, A_S_cfg_max_retries, A_S_cfg_backoff_ms, A_S_cfg_offline_ms, A_S_cfg_wake_timeout_ms, A_S_cfg_display_gap_us, A_S_cfg_max_cmds, A_S_cfg_max_body, A_S_io_ctx, A_S_io_send, A_S_io_recv, A_S_io_now_us, A_S_notify, A_S_notify_ctx, A_S_state, A_S_desk_known, A_S_desk_mac, A_S_personality, A_S_foreign, A_S_e1_named_us, A_S_wake_acked, A_S_wake_sent_us, A_S_host_counter, A_S_desk_counter, A_S_desk_counter_valid, A_S_last_rx_us, A_S_next_keepalive_us, A_S_backoff_until_us, A_S_last_display_us, A_S_display_sent, A_S_inflight, A_S_inflight_frame, A_S_inflight_len, A_S_inflight_counter, A_S_inflight_retries, A_S_inflight_sent_us, A_S_queue_bytes, A_S_queue_len, A_S_queue_display, A_S_queue_key, A_S_queued, A_S_stats_rx_frames, A_S_stats_rx_data, A_S_stats_rx_duplicates, A_S_stats_rx_desk_retries, A_S_stats_rx_ignored, A_S_stats_tx_frames, A_S_stats_tx_data, A_S_stats_tx_acks, A_S_stats_tx_keepalives, A_S_stats_tx_wakes, A_S_stats_tx_retransmits, A_S_stats_ack_lost, A_S_stats_coalesced, A_S_stats_refused, A_Cfg_host_mac, A_Cfg_desk_mac, A_Cfg_desk_mac_set, A_Cfg_auto_wake, A_Cfg_sum_mode, A_Cfg_keepalive_ms, A_Cfg_ack_timeout_ms, A_Cfg_max_retries, A_Cfg_backoff_ms, A_Cfg_offline_ms, A_Cfg_wake_timeout_ms, A_Cfg_display_gap_us, A_Cfg_max_cmds, A_Cfg_max_body, A_Cmd_st, A_Cmd_key, A_Cmd_display, A_Cmd_bytes, A_Cmd_len;
  unfold W_LEN, OFF_M, SZ_M, OFF_g_s, SZ_g_s, OFF_g_cmd, SZ_g_cmd, OFF_g_q, SZ_g_q, OFF_g_fail_next, SZ_g_fail_next, OFF_g_raw, SZ_g_raw, OFF_g_last_counter, SZ_g_last_counter, OFF_g_nq, SZ_g_nq, OFF_g_ncmd, SZ_g_ncmd, OFF_g_rx_send, SZ_g_rx_send, OFF_g_rx_fail, SZ_g_rx_fail, OFF_g_rx_times, SZ_g_rx_times, OFF_g_now, SZ_g_now, OFF_g_rx, SZ_g_rx, OFF_g_rx_len, SZ_g_rx_len, OFF_g_cfg, SZ_g_cfg, OFF_GOT, SZ_GOT, OFF_OW, SZ_OW.
Local Ltac ka_uaa := unfold A_M_desk_known, A_M_desk, A_M_state, A_M_e2_acked, A_M_e1_us, A_M_foreign, A_M_last_rx, A_M_wake_sent, A_M_next_ka, A_M_backoff_until, A_M_last_display, A_M_display_sent, A_M_desk_counter_valid, A_M_desk_counter, A_M_host_counter, A_M_fail, A_M_fly_on, A_M_fly_cmd, A_M_fly_counter, A_M_fly_retries, A_M_fly_sent, A_M_fly_frame, A_M_fly_len, A_S_cfg_host_mac, A_S_cfg_desk_mac, A_S_cfg_desk_mac_set, A_S_cfg_auto_wake, A_S_cfg_sum_mode, A_S_cfg_keepalive_ms, A_S_cfg_ack_timeout_ms, A_S_cfg_max_retries, A_S_cfg_backoff_ms, A_S_cfg_offline_ms, A_S_cfg_wake_timeout_ms, A_S_cfg_display_gap_us, A_S_cfg_max_cmds, A_S_cfg_max_body, A_S_io_ctx, A_S_io_send, A_S_io_recv, A_S_io_now_us, A_S_notify, A_S_notify_ctx, A_S_state, A_S_desk_known, A_S_desk_mac, A_S_personality, A_S_foreign, A_S_e1_named_us, A_S_wake_acked, A_S_wake_sent_us, A_S_host_counter, A_S_desk_counter, A_S_desk_counter_valid, A_S_last_rx_us, A_S_next_keepalive_us, A_S_backoff_until_us, A_S_last_display_us, A_S_display_sent, A_S_inflight, A_S_inflight_frame, A_S_inflight_len, A_S_inflight_counter, A_S_inflight_retries, A_S_inflight_sent_us, A_S_queue_bytes, A_S_queue_len, A_S_queue_display, A_S_queue_key, A_S_queued, A_S_stats_rx_frames, A_S_stats_rx_data, A_S_stats_rx_duplicates, A_S_stats_rx_desk_retries, A_S_stats_rx_ignored, A_S_stats_tx_frames, A_S_stats_tx_data, A_S_stats_tx_acks, A_S_stats_tx_keepalives, A_S_stats_tx_wakes, A_S_stats_tx_retransmits, A_S_stats_ack_lost, A_S_stats_coalesced, A_S_stats_refused, A_Cfg_host_mac, A_Cfg_desk_mac, A_Cfg_desk_mac_set, A_Cfg_auto_wake, A_Cfg_sum_mode, A_Cfg_keepalive_ms, A_Cfg_ack_timeout_ms, A_Cfg_max_retries, A_Cfg_backoff_ms, A_Cfg_offline_ms, A_Cfg_wake_timeout_ms, A_Cfg_display_gap_us, A_Cfg_max_cmds, A_Cfg_max_body, A_Cmd_st, A_Cmd_key, A_Cmd_display, A_Cmd_bytes, A_Cmd_len in *;
  unfold W_LEN, OFF_M, SZ_M, OFF_g_s, SZ_g_s, OFF_g_cmd, SZ_g_cmd, OFF_g_q, SZ_g_q, OFF_g_fail_next, SZ_g_fail_next, OFF_g_raw, SZ_g_raw, OFF_g_last_counter, SZ_g_last_counter, OFF_g_nq, SZ_g_nq, OFF_g_ncmd, SZ_g_ncmd, OFF_g_rx_send, SZ_g_rx_send, OFF_g_rx_fail, SZ_g_rx_fail, OFF_g_rx_times, SZ_g_rx_times, OFF_g_now, SZ_g_now, OFF_g_rx, SZ_g_rx, OFF_g_rx_len, SZ_g_rx_len, OFF_g_cfg, SZ_g_cfg, OFF_GOT, SZ_GOT, OFF_OW, SZ_OW in *.
Local Ltac ka_ar := ka_ua; lia.
Local Ltac ka_us := unfold set_S_next_keepalive_us, set_S_stats_tx_keepalives, set_S_host_counter, set_S_inflight_frame, set_S_inflight_len, set_S_inflight, set_S_inflight_counter, set_S_inflight_retries, set_S_inflight_sent_us, set_S_stats_tx_data, set_S_stats_tx_frames, set_g_fail_next, set_M_host_counter, set_g_last_counter, set_M_next_ka, set_M_fly_on, set_M_fly_cmd, set_M_fly_counter, set_M_fly_retries, set_M_fly_sent, set_M_fly_len, set_M_fly_frame.

Local Ltac ka_vl :=
  repeat match goal with
  | |- context [length (put ?n ?x)] => rewrite (length_put n x)
  | H : length ?w = _ |- context [length ?v] => constr_eq w v; rewrite H
  end; ka_ar.

Local Ltac ka_vle :=
  first [ exact (length_put _ _)
        | match goal with H : length ?w = _ |- length ?v = _ => constr_eq w v; exact H end ].

Local Ltac ka_wlen HB :=
  lazymatch goal with
  | |- length (upd ?X ?k ?v) = Z.to_nat W_LEN => apply (ka_wl X k v); [ka_wlen HB | ka_ar | ka_vl]
  | |- _ => exact HB
  end.

Local Ltac ka_peel HB :=
  lazymatch goal with
  | |- context [s32_at (upd ?X ?k ?v) ?j] =>
      tryif constr_eq k j then
        lazymatch v with
        | put 4 ?x => rewrite (ka_s32_same X k x); [ka_peel HB | ka_wlen HB | ka_ar | ka_ar | ka_ar]
        end
      else (rewrite (ka_s32_out X k v j); [ka_peel HB | ka_wlen HB | ka_ar | ka_ar | ka_vl | ka_vl])
  | |- context [u_at (upd ?X ?k ?v) ?j ?n] =>
      tryif constr_eq k j then
        lazymatch v with
        | put 8 ?x => rewrite (ka_ua_same8 X k x); [ka_peel HB | ka_wlen HB | ka_ar | ka_ar]
        | put 4 ?x => rewrite (ka_ua_same4 X k x); [ka_peel HB | ka_wlen HB | ka_ar | ka_ar]
        | put 1 ?x => rewrite (ka_ua_same1 X k x); [ka_peel HB | ka_wlen HB | ka_ar | ka_ar]
        end
      else (rewrite (ka_ua_out X k v j n); [ka_peel HB | ka_wlen HB | ka_ar | ka_ar | ka_vl | ka_vl])
  | |- context [sub (upd ?X ?k ?v) ?j ?n] =>
      tryif constr_eq k j then
        (rewrite (ka_sb_same X k v n); [ka_peel HB | ka_wlen HB | ka_ar | ka_vle | ka_ar])
      else (rewrite (ka_sb_out X k v j n); [ka_peel HB | ka_wlen HB | ka_ar | ka_ar | ka_vl | ka_vl])
  | |- _ => idtac
  end.

(* a getter (unfolded by the caller) of a chain of writes over the world HB names, equal to its base read *)
Local Ltac ka_kp HB := ka_us; ka_peel HB; reflexivity.

Local Ltac ka_rg :=
  let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha;
  repeat match type of Ha with
  | context [length (put ?n ?x)] => rewrite (length_put n x) in Ha
  | context [length ?v] => match goal with H : length ?w = _ |- _ => constr_eq w v; rewrite H in Ha end
  end;
  unfold ka_W, ka_Wlib, ka_Wio, ka_Wst, ka_Wpre; clear - Ha; ka_uaa; lia.

(* wframe R B0 (chain of upd over X0), from H0 : wframe R B0 X0 and HB : length X0 = Z.to_nat W_LEN *)
Local Ltac ka_wf H0 HB :=
  lazymatch goal with
  | |- wframe ?R ?B0 (upd ?X ?k ?v) =>
      apply (ka_wf_upd R B0 X k v); [ka_wf H0 HB | ka_wlen HB | ka_ar | ka_vl | ka_rg]
  | |- _ => exact H0
  end.

Local Ltac ka_kside :=
  let a := fresh "a" in let Ha := fresh "Ha" in let Hr := fresh "Hr" in
  intros a Ha Hr; unfold ka_W, ka_Wlib, ka_Wio, ka_Wst, ka_Wpre in Hr; clear - Ha Hr; ka_uaa; lia.

Local Ltac ka_ksidei Hi :=
  let a := fresh "a" in let Ha := fresh "Ha" in let Hr := fresh "Hr" in
  intros a Ha Hr; unfold ka_W, ka_Wlib, ka_Wio, ka_Wst, ka_Wpre in Hr; clear - Hi Ha Hr; ka_uaa; lia.

(* a read outside the region of HW : wframe R B0 B1 is the same in B1 and B0 *)
Local Ltac ka_keep HW :=
  lazymatch goal with
  | |- s32_at ?B1 ?j = s32_at ?B0 ?j => apply (wframe_s32_at _ B0 B1 j HW); [ka_ar | ka_kside]
  | |- u_at ?B1 ?j ?n = u_at ?B0 ?j ?n => apply (wframe_u_at _ B0 B1 j n HW); [ka_ar | ka_kside]
  | |- sub ?B1 ?j ?n = sub ?B0 ?j ?n => apply (wframe_sub _ B0 B1 j n HW); [ka_ar | ka_kside]
  end.

Local Ltac ka_keepi HW Hi :=
  lazymatch goal with
  | |- s32_at ?B1 ?j = s32_at ?B0 ?j => apply (wframe_s32_at _ B0 B1 j HW); [ka_ar | ka_ksidei Hi]
  | |- u_at ?B1 ?j ?n = u_at ?B0 ?j ?n => apply (wframe_u_at _ B0 B1 j n HW); [ka_ar | ka_ksidei Hi]
  | |- sub ?B1 ?j ?n = sub ?B0 ?j ?n => apply (wframe_sub _ B0 B1 j n HW); [ka_ar | ka_ksidei Hi]
  end.

(* ---------------------------------------------------------------- DS:451-454: the deadline moves on, the stats *)

Lemma ka_prefix : forall I F B now, length B = Z.to_nat W_LEN ->
  exists Bc, tick_ka_m I F B now = send_data_m I F Bc [b8 0] 1 now /\ length Bc = Z.to_nat W_LEN /\
    wframe ka_Wpre B Bc /\ S_next_keepalive_us Bc = ka_nk (S_next_keepalive_us B) (S_cfg_keepalive_ms B) now.
Proof.
  intros I F B now HB. unfold tick_ka_m.
  remember (set_S_next_keepalive_us B (u64 (S_next_keepalive_us B + ms_m (S_cfg_keepalive_ms B)))) as Ba eqn:EBa.
  cbv zeta.
  assert (HBa : length Ba = Z.to_nat W_LEN) by (rewrite EBa; ka_us; ka_wlen HB).
  assert (HWa : wframe ka_Wpre B Ba) by (rewrite EBa; ka_us; ka_wf (wframe_refl ka_Wpre B) HB).
  assert (E1 : S_next_keepalive_us Ba = u64 (S_next_keepalive_us B + ms_m (S_cfg_keepalive_ms B))).
  { rewrite EBa. unfold S_next_keepalive_us. ka_us. ka_peel HB. apply ka_u64_mod. }
  assert (E2 : S_cfg_keepalive_ms Ba = S_cfg_keepalive_ms B).
  { rewrite EBa. unfold S_cfg_keepalive_ms. ka_kp HB. }
  rewrite E1. rewrite E2.
  destruct (Z.leb_spec (u64 (S_next_keepalive_us B + ms_m (S_cfg_keepalive_ms B))) now) as [Hle|Hgt];
    cbv beta iota.
  - eexists. split; [reflexivity|].
    split; [ka_us; ka_wlen HBa|].
    split; [ka_us; ka_wf HWa HBa|].
    transitivity (u64 (now + ms_m (S_cfg_keepalive_ms B))).
    + unfold S_next_keepalive_us. ka_us. ka_peel HBa. apply ka_u64_mod.
    + unfold ka_nk.
      destruct (Z.leb_spec (u64 (S_next_keepalive_us B + ms_m (S_cfg_keepalive_ms B))) now) as [_|X];
        [reflexivity | lia].
  - eexists. split; [reflexivity|].
    split; [ka_us; ka_wlen HBa|].
    split; [ka_us; ka_wf HWa HBa|].
    transitivity (S_next_keepalive_us Ba).
    + unfold S_next_keepalive_us. ka_kp HBa.
    + rewrite E1. unfold ka_nk.
      destruct (Z.leb_spec (u64 (S_next_keepalive_us B + ms_m (S_cfg_keepalive_ms B))) now) as [X|_];
        [lia | reflexivity].
Qed.

(* ---------------------------------------------------------------- DS:388-400: send_data up to send_raw *)

Lemma ka_send_data : forall I F Bc now dst src h mode fr, length Bc = Z.to_nat W_LEN ->
  S_desk_mac Bc = dst -> S_cfg_host_mac Bc = src -> S_host_counter Bc = h -> S_cfg_sum_mode Bc = mode ->
  diginet_frame_build_code [b8 0] DIGINET_MAX_FRAME_LEN mode = 60 ->
  fr = lib_frame dst src (u32 (h + 1)) 0 0 DIGINET_CMD_DATA (u8 1) [b8 0] mode -> length fr = 60%nat ->
  exists Bh, send_data_m I F Bc [b8 0] 1 now = send_raw_m I F Bh fr /\ length Bh = Z.to_nat W_LEN /\
    wframe ka_Wlib Bc Bh /\ S_host_counter Bh = u32 (h + 1) /\
    S_next_keepalive_us Bh = S_next_keepalive_us Bc /\ S_inflight Bh = 1 /\
    S_inflight_counter Bh = u32 (h + 1) /\ S_inflight_retries Bh = 0 /\
    S_inflight_sent_us Bh = now mod 2 ^ 64 /\ S_inflight_len Bh = 60 /\ sub Bh A_S_inflight_frame 60 = fr.
Proof.
  intros I F Bc now dst src h mode fr HB Hd Hs Hh Hm Hbc Hfr Hfl.
  unfold send_data_m.
  remember (set_S_host_counter Bc (u32 (S_host_counter Bc + 1))) as Bd eqn:EBd.
  cbv zeta.
  assert (HBd : length Bd = Z.to_nat W_LEN) by (rewrite EBd; ka_us; ka_wlen HB).
  assert (HWd : wframe ka_Wlib Bc Bd) by (rewrite EBd; ka_us; ka_wf (wframe_refl ka_Wlib Bc) HB).
  assert (Ed1 : S_host_counter Bd = u32 (h + 1)).
  { rewrite <- Hh. rewrite EBd. unfold S_host_counter. ka_us. ka_peel HB. apply ka_u32_mod. }
  assert (Ed2 : S_cfg_sum_mode Bd = mode).
  { rewrite <- Hm. rewrite EBd. unfold S_cfg_sum_mode. ka_kp HB. }
  assert (Ed3 : S_desk_mac Bd = dst).
  { rewrite <- Hd. rewrite EBd. unfold S_desk_mac. ka_kp HB. }
  assert (Ed4 : S_cfg_host_mac Bd = src).
  { rewrite <- Hs. rewrite EBd. unfold S_cfg_host_mac. ka_kp HB. }
  rewrite Ed2. rewrite Hbc.
  destruct (Z.ltb_spec 60 0) as [Hx|_]; [lia|].
  cbv beta iota.
  rewrite Ed1. rewrite Ed3. rewrite Ed4. rewrite <- Hfr.
  assert (Ef : S_host_counter (set_S_inflight_len (set_S_inflight_frame Bd fr) 60) = u32 (h + 1)).
  { rewrite <- Ed1. unfold S_host_counter. ka_kp HBd. }
  rewrite Ef.
  unfold inflight_start_m. cbv beta iota zeta.
  match goal with |- context [inflight_bytes ?T] => remember T as Bh eqn:EBh end.
  assert (HBh : length Bh = Z.to_nat W_LEN) by (rewrite EBh; ka_us; ka_wlen HBd).
  assert (El : S_inflight_len Bh = 60).
  { rewrite EBh. unfold S_inflight_len. ka_us. ka_peel HBd. reflexivity. }
  assert (Efr : sub Bh A_S_inflight_frame 60 = fr).
  { rewrite EBh. ka_us. ka_peel HBd. reflexivity. }
  unfold inflight_bytes. rewrite El.
  destruct (Z.ltb_spec 1514 60) as [Hx|_]; [revert Hx; ka_ar|].
  cbv beta iota.
  change (Z.to_nat 60) with 60%nat. rewrite Efr.
  exists Bh. split; [reflexivity|].
  split; [exact HBh|].
  split; [rewrite EBh; ka_us; ka_wf HWd HBd|].
  split; [rewrite <- Ed1; rewrite EBh; unfold S_host_counter; ka_kp HBd|].
  split.
  { rewrite EBh. unfold S_next_keepalive_us. ka_us. ka_peel HBd. rewrite EBd. ka_us. ka_peel HB. reflexivity. }
  split; [rewrite EBh; unfold S_inflight; ka_us; ka_peel HBd; reflexivity|].
  split; [rewrite EBh; unfold S_inflight_counter; ka_us; ka_peel HBd; apply ka_u32_mod|].
  split; [rewrite EBh; unfold S_inflight_retries; ka_us; ka_peel HBd; reflexivity|].
  split; [rewrite EBh; unfold S_inflight_sent_us; ka_us; ka_peel HBd; reflexivity|].
  split; [exact El | exact Efr].
Qed.

(* ---------------------------------------------------------------- FT:823-899: io_send on the keepalive frame *)

Lemma ka_io : forall (HL : links) I Bh fr dst send mode,
  length Bh = Z.to_nat W_LEN ->
  build_ok dst HOST send 0 0 DIGINET_CMD_DATA (u8 1) [b8 0] mode ->
  fr = lib_frame dst HOST send 0 0 DIGINET_CMD_DATA (u8 1) [b8 0] mode ->
  M_desk_known Bh = 1 -> M_desk Bh = dst -> Cfg_sum_mode Bh = mode ->
  M_state Bh = S_ONLINE -> M_fly_on Bh = 0 -> M_backoff_until Bh <= g_now Bh ->
  send = u32 (M_host_counter Bh + 1) -> 1 <= Cfg_max_body Bh -> 1 <= Cfg_max_cmds Bh ->
  (g_raw Bh = 0 -> M_next_ka Bh <= g_now Bh) ->
  exists Bz, io_send_m I Bh fr = Some (Bz, if truth (g_fail_next Bh) then - EIO else 0) /\
    length Bz = Z.to_nat W_LEN /\ wframe ka_Wio Bh Bz /\ g_fail_next Bz = 0 /\ M_host_counter Bz = send /\
    (g_raw Bh = 0 -> M_next_ka Bz = ka_nk (M_next_ka Bh) (Cfg_keepalive_ms Bh) (g_now Bh)) /\
    M_fly_on Bz = 1 /\ M_fly_cmd Bz = DIGINET_CMD_DATA /\ M_fly_counter Bz = send /\
    M_fly_retries Bz = 0 /\ M_fly_sent Bz = g_now Bh /\ M_fly_len Bz = 60 /\ sub Bz A_M_fly_frame 60 = fr.
Proof.
  intros HL I Bh fr dst send mode HB Hok Hfr Hkn Hdesk Hmode Hst Hon Hbo Hsend Hmb Hmc Hnk.
  pose proof (rf_lib_frame HL dst HOST send 0 0 DIGINET_CMD_DATA (u8 1) [b8 0] mode Hok) as R. cbv zeta in R.
  rewrite <- Hfr in R.
  destruct R as (Hlen & _ & _ & _ & Hb30 & Hcmd & Hse & _ & Hre & Hnc & Hbl & Hsub & _).
  assert (Hfl : length fr = 60%nat) by (change (frame_len (length [b8 0])) with 60 in Hlen; lia).
  assert (Hff : firstn 60 fr = fr) by (apply firstn_all2; rewrite Hfl; lia).
  assert (Hat : at8 (skipn (Z.to_nat SPEC_BODY_AT) fr) 0 = 0).
  { revert Hsub. unfold sub. change (length [b8 0]) with 1%nat.
    destruct (skipn (Z.to_nat SPEC_BODY_AT) fr) as [|x l]; cbn [firstn]; intros Hs.
    - discriminate Hs.
    - injection Hs as Hx. unfold at8. cbn [nth]. rewrite Hx. vm_compute. reflexivity. }
  unfold io_send_m. cbv beta zeta.
  remember (set_g_fail_next Bh 0) as B0 eqn:E0.
  assert (HB0 : length B0 = Z.to_nat W_LEN) by (rewrite E0; ka_us; ka_wlen HB).
  assert (A0kn : M_desk_known B0 = M_desk_known Bh) by (rewrite E0; unfold M_desk_known; ka_kp HB).
  assert (A0d : M_desk B0 = M_desk Bh) by (rewrite E0; unfold M_desk; ka_kp HB).
  assert (A0m : Cfg_sum_mode B0 = Cfg_sum_mode Bh) by (rewrite E0; unfold Cfg_sum_mode; ka_kp HB).
  assert (A0st : M_state B0 = M_state Bh) by (rewrite E0; unfold M_state; ka_kp HB).
  assert (A0on : M_fly_on B0 = M_fly_on Bh) by (rewrite E0; unfold M_fly_on; ka_kp HB).
  assert (A0now : g_now B0 = g_now Bh) by (rewrite E0; unfold g_now; ka_kp HB).
  assert (A0bo : M_backoff_until B0 = M_backoff_until Bh) by (rewrite E0; unfold M_backoff_until; ka_kp HB).
  assert (A0mb : Cfg_max_body B0 = Cfg_max_body Bh) by (rewrite E0; unfold Cfg_max_body; ka_kp HB).
  assert (A0mc : Cfg_max_cmds B0 = Cfg_max_cmds Bh) by (rewrite E0; unfold Cfg_max_cmds; ka_kp HB).
  assert (A0hc : M_host_counter B0 = M_host_counter Bh) by (rewrite E0; unfold M_host_counter; ka_kp HB).
  (* check_sent_frame (FT:831) *)
  assert (Hsent : check_sent_frame_m B0 fr = Some (B0, tt)).
  { rewrite Hfr. apply (sent_frame_ok HL B0 dst HOST send 0 0 DIGINET_CMD_DATA (u8 1) [b8 0] mode Hok eq_refl).
    - rewrite A0kn. exact Hkn.
    - rewrite A0d. exact Hdesk.
    - rewrite A0m. exact Hmode. }
  (* check_inflight_new (FT:857) *)
  assert (Hin : check_inflight_new_m B0 = Some (B0, tt)).
  { unfold check_inflight_new_m. rewrite A0st. rewrite A0on. rewrite A0now. rewrite A0bo. rewrite Hst. rewrite Hon.
    change (negb (S_ONLINE =? S_ONLINE) || truth 0) with false.
    destruct (Z.ltb_spec (g_now Bh) (M_backoff_until Bh)) as [X|_]; [lia|].
    reflexivity. }
  (* check_latest_frame (FT:866), cmds = f.num_commands = 1 (FT:863-865) *)
  assert (Hlf : check_latest_frame_m B0 fr (u8 1) = Some (B0, tt)).
  { unfold check_latest_frame_m. cbv zeta.
    rewrite Hbl. rewrite Hnc. rewrite Hse. rewrite A0mb. rewrite A0mc. rewrite A0hc.
    change (Z.of_nat (length [b8 0])) with 1. change (u8 1) with 1.
    destruct (Z.ltb_spec (Cfg_max_body Bh) 1) as [X|_]; [lia|].
    destruct (Z.ltb_spec (Cfg_max_cmds Bh) 1) as [X|_]; [lia|].
    rewrite (Z.eqb_refl 1). change (negb true) with false.
    rewrite (andb_false_r (negb (truth (g_raw B0)))).
    rewrite <- Hsend. rewrite (Z.eqb_refl send).
    reflexivity. }
  rewrite Hsent. cbv beta iota.
  rewrite Hcmd. rewrite Hse. rewrite Hre. rewrite Hb30. rewrite Hbl. rewrite Hnc. rewrite Hat.
  change (DIGINET_CMD_DATA =? SPEC_CMD_ACK) with false.
  change ((DIGINET_CMD_DATA =? SPEC_CMD_E2) || (DIGINET_CMD_DATA =? SPEC_CMD_DATA)) with true.
  change (truth 0) with false.
  change (DIGINET_CMD_DATA =? SPEC_CMD_E2) with false.
  change ((Z.of_nat (length [b8 0]) =? 1) && (0 =? 0) && (u8 1 =? 1)) with true.
  cbv beta iota.
  rewrite Hin. cbv beta iota.
  change (negb true) with false. rewrite (andb_false_r (negb (truth (g_raw B0)))). cbv beta iota.
  rewrite Hlf. cbv beta iota.
  remember (set_g_last_counter (set_M_host_counter B0 send) send) as B5 eqn:E5.
  assert (A5raw : g_raw B5 = g_raw Bh) by (rewrite E5; rewrite E0; unfold g_raw; ka_kp HB).
  assert (A5st : M_state B5 = M_state Bh) by (rewrite E5; rewrite E0; unfold M_state; ka_kp HB).
  assert (A5on : M_fly_on B5 = M_fly_on Bh) by (rewrite E5; rewrite E0; unfold M_fly_on; ka_kp HB).
  assert (A5now : g_now B5 = g_now Bh) by (rewrite E5; rewrite E0; unfold g_now; ka_kp HB).
  assert (A5bo : M_backoff_until B5 = M_backoff_until Bh) by (rewrite E5; rewrite E0; unfold M_backoff_until; ka_kp HB).
  assert (A5nk : M_next_ka B5 = M_next_ka Bh) by (rewrite E5; rewrite E0; unfold M_next_ka; ka_kp HB).
  assert (A5ka : Cfg_keepalive_ms B5 = Cfg_keepalive_ms Bh) by (rewrite E5; rewrite E0; unfold Cfg_keepalive_ms; ka_kp HB).
  rewrite (andb_true_r (negb (truth (g_raw B5)))). rewrite A5raw.
  destruct (Z.eqb_spec (g_raw Bh) 0) as [Er|Er].
  - (* tagged: check_keepalive_due and the harness's next keepalive (FT:869-873) *)
    assert (Tr : truth (g_raw Bh) = false) by (unfold truth; rewrite Er; reflexivity).
    rewrite Tr. change (negb false) with true. cbv beta iota.
    assert (Hkd : check_keepalive_due_m B5 = Some (B5, tt)).
    { unfold check_keepalive_due_m. rewrite A5st. rewrite A5on. rewrite A5now. rewrite A5bo. rewrite A5nk.
      rewrite Hst. rewrite Hon.
      change (negb (S_ONLINE =? S_ONLINE) || truth 0) with false.
      destruct (Z.ltb_spec (g_now Bh) (M_backoff_until Bh)) as [X|_]; [lia|].
      destruct (Z.ltb_spec (g_now Bh) (M_next_ka Bh)) as [X|_]; [specialize (Hnk Er); lia|].
      reflexivity. }
    rewrite Hkd. cbv beta iota.
    rewrite A5nk. rewrite A5ka. rewrite (ka_hms (Cfg_keepalive_ms Bh)).
    remember (set_M_next_ka B5 (u64 (M_next_ka Bh + ms_m (Cfg_keepalive_ms Bh)))) as Bk1 eqn:Ek1.
    assert (Ak1now : g_now Bk1 = g_now Bh) by (rewrite Ek1; rewrite E5; rewrite E0; unfold g_now; ka_kp HB).
    assert (Ak1ka : Cfg_keepalive_ms Bk1 = Cfg_keepalive_ms Bh)
      by (rewrite Ek1; rewrite E5; rewrite E0; unfold Cfg_keepalive_ms; ka_kp HB).
    rewrite Ak1now. rewrite Ak1ka. rewrite (ka_hms (Cfg_keepalive_ms Bh)).
    destruct (Z.leb_spec (u64 (M_next_ka Bh + ms_m (Cfg_keepalive_ms Bh))) (g_now Bh)) as [Hl|Hl];
      cbv beta iota.
    + (* clamped (FT:872-873) *)
      assert (A6 : g_now (set_M_next_ka Bk1 (u64 (g_now Bh + ms_m (Cfg_keepalive_ms Bh)))) = g_now Bh)
        by (rewrite Ek1; rewrite E5; rewrite E0; unfold g_now; ka_kp HB).
      rewrite A6. rewrite Hfl.
      change (if Z.of_nat 60 <? SPEC_MAX_FRAME then Z.of_nat 60 else SPEC_MAX_FRAME) with 60.
      change (Z.to_nat 60) with 60%nat. rewrite Hff. cbv beta iota.
      eexists. split; [reflexivity|].
      split; [rewrite Ek1; rewrite E5; rewrite E0; ka_us; ka_wlen HB|].
      split; [rewrite Ek1; rewrite E5; rewrite E0; ka_us; ka_wf (wframe_refl ka_Wio Bh) HB|].
      split; [rewrite Ek1; rewrite E5; rewrite E0; unfold g_fail_next; ka_us; ka_peel HB; reflexivity|].
      split; [rewrite Ek1; rewrite E5; rewrite E0; unfold M_host_counter; ka_us; ka_peel HB; rewrite Hsend; apply ka_u32_mod|].
      split; [intros _; transitivity (u64 (g_now Bh + ms_m (Cfg_keepalive_ms Bh)));
        [ rewrite Ek1; rewrite E5; rewrite E0; unfold M_next_ka; ka_us; ka_peel HB; apply ka_u64_mod
        | unfold ka_nk;
          destruct (Z.leb_spec (u64 (M_next_ka Bh + ms_m (Cfg_keepalive_ms Bh))) (g_now Bh)) as [_|X];
          [reflexivity | lia] ]|].
      split; [rewrite Ek1; rewrite E5; rewrite E0; unfold M_fly_on; ka_us; ka_peel HB; reflexivity|].
      split; [rewrite Ek1; rewrite E5; rewrite E0; unfold M_fly_cmd; ka_us; ka_peel HB; reflexivity|].
      split; [rewrite Ek1; rewrite E5; rewrite E0; unfold M_fly_counter; ka_us; ka_peel HB; rewrite Hsend; apply ka_u32_mod|].
      split; [rewrite Ek1; rewrite E5; rewrite E0; unfold M_fly_retries; ka_us; ka_peel HB; reflexivity|].
      split; [rewrite Ek1; rewrite E5; rewrite E0; unfold M_fly_sent; ka_us; ka_peel HB; unfold g_now; apply ka_ua_mod8|].
      split; [rewrite Ek1; rewrite E5; rewrite E0; unfold M_fly_len; ka_us; ka_peel HB; reflexivity|].
      rewrite Ek1; rewrite E5; rewrite E0; ka_us; ka_peel HB; reflexivity.
    + rewrite Ak1now. rewrite Hfl.
      change (if Z.of_nat 60 <? SPEC_MAX_FRAME then Z.of_nat 60 else SPEC_MAX_FRAME) with 60.
      change (Z.to_nat 60) with 60%nat. rewrite Hff. cbv beta iota.
      eexists. split; [reflexivity|].
      split; [rewrite Ek1; rewrite E5; rewrite E0; ka_us; ka_wlen HB|].
      split; [rewrite Ek1; rewrite E5; rewrite E0; ka_us; ka_wf (wframe_refl ka_Wio Bh) HB|].
      split; [rewrite Ek1; rewrite E5; rewrite E0; unfold g_fail_next; ka_us; ka_peel HB; reflexivity|].
      split; [rewrite Ek1; rewrite E5; rewrite E0; unfold M_host_counter; ka_us; ka_peel HB; rewrite Hsend; apply ka_u32_mod|].
      split; [intros _; transitivity (u64 (M_next_ka Bh + ms_m (Cfg_keepalive_ms Bh)));
        [ rewrite Ek1; rewrite E5; rewrite E0; unfold M_next_ka; ka_us; ka_peel HB; apply ka_u64_mod
        | unfold ka_nk;
          destruct (Z.leb_spec (u64 (M_next_ka Bh + ms_m (Cfg_keepalive_ms Bh))) (g_now Bh)) as [X|_];
          [lia | reflexivity] ]|].
      split; [rewrite Ek1; rewrite E5; rewrite E0; unfold M_fly_on; ka_us; ka_peel HB; reflexivity|].
      split; [rewrite Ek1; rewrite E5; rewrite E0; unfold M_fly_cmd; ka_us; ka_peel HB; reflexivity|].
      split; [rewrite Ek1; rewrite E5; rewrite E0; unfold M_fly_counter; ka_us; ka_peel HB; rewrite Hsend; apply ka_u32_mod|].
      split; [rewrite Ek1; rewrite E5; rewrite E0; unfold M_fly_retries; ka_us; ka_peel HB; reflexivity|].
      split; [rewrite Ek1; rewrite E5; rewrite E0; unfold M_fly_sent; ka_us; ka_peel HB; unfold g_now; apply ka_ua_mod8|].
      split; [rewrite Ek1; rewrite E5; rewrite E0; unfold M_fly_len; ka_us; ka_peel HB; reflexivity|].
      rewrite Ek1; rewrite E5; rewrite E0; ka_us; ka_peel HB; reflexivity.
  - (* raw: no keepalive bookkeeping (FT:869, :874) *)
    assert (Tr : truth (g_raw Bh) = true).
    { unfold truth. destruct (Z.eqb_spec (g_raw Bh) 0) as [X|_]; [exfalso; exact (Er X) | reflexivity]. }
    rewrite Tr. change (negb true) with false. cbv beta iota.
    rewrite A5now. rewrite Hfl.
    change (if Z.of_nat 60 <? SPEC_MAX_FRAME then Z.of_nat 60 else SPEC_MAX_FRAME) with 60.
    change (Z.to_nat 60) with 60%nat. rewrite Hff. cbv beta iota.
    eexists. split; [reflexivity|].
    split; [rewrite E5; rewrite E0; ka_us; ka_wlen HB|].
    split; [rewrite E5; rewrite E0; ka_us; ka_wf (wframe_refl ka_Wio Bh) HB|].
    split; [rewrite E5; rewrite E0; unfold g_fail_next; ka_us; ka_peel HB; reflexivity|].
    split; [rewrite E5; rewrite E0; unfold M_host_counter; ka_us; ka_peel HB; rewrite Hsend; apply ka_u32_mod|].
    split; [intros X; exfalso; exact (Er X)|].
    split; [rewrite E5; rewrite E0; unfold M_fly_on; ka_us; ka_peel HB; reflexivity|].
    split; [rewrite E5; rewrite E0; unfold M_fly_cmd; ka_us; ka_peel HB; reflexivity|].
    split; [rewrite E5; rewrite E0; unfold M_fly_counter; ka_us; ka_peel HB; rewrite Hsend; apply ka_u32_mod|].
    split; [rewrite E5; rewrite E0; unfold M_fly_retries; ka_us; ka_peel HB; reflexivity|].
    split; [rewrite E5; rewrite E0; unfold M_fly_sent; ka_us; ka_peel HB; unfold g_now; apply ka_ua_mod8|].
    split; [rewrite E5; rewrite E0; unfold M_fly_len; ka_us; ka_peel HB; reflexivity|].
    rewrite E5; rewrite E0; ka_us; ka_peel HB; reflexivity.
Qed.

(* ---------------------------------------------------------------- the world after: tick_post *)

(* the writes of the whole path: the library's, io_send's, send_raw's stats *)
Lemma ka_W_trans : forall B Bh Bz B', wframe ka_Wlib B Bh -> wframe ka_Wio Bh Bz -> wframe ka_Wst Bz B' ->
  wframe ka_W B B'.
Proof.
  intros B Bh Bz B' HW1 HW2 HW3. apply (wframe_trans ka_W B Bh B').
  - apply (wframe_weaken ka_Wlib ka_W B Bh); [|exact HW1]. intros a Ha. left. exact Ha.
  - apply (wframe_trans ka_W Bh Bz B').
    + apply (wframe_weaken ka_Wio ka_W Bh Bz); [|exact HW2]. intros a Ha. right. exact Ha.
    + apply (wframe_weaken ka_Wst ka_W Bz B'); [|exact HW3]. intros a Ha. left. unfold ka_Wlib.
      right. right. right. exact Ha.
Qed.

(* ka_W misses M.desk_known, M.desk, M.state (world bytes 0..15) *)
Lemma ka_W_low : forall a, 0 <= a < 16 -> ~ ka_W a.
Proof. ka_kside. Qed.

Lemma ka_post : forall I ops B Bh Bz B' fr nk,
  agree_core I ops B -> S_state B = DIGINET_S_ONLINE -> S_next_keepalive_us B <= g_now B ->
  wframe ka_Wlib B Bh -> wframe ka_Wio Bh Bz -> wframe ka_Wst Bz B' ->
  fr = lib_frame (M_desk B) HOST (u32 (S_host_counter B + 1)) 0 0 DIGINET_CMD_DATA (u8 1) [b8 0] (Cfg_sum_mode B) ->
  nk = ka_nk (S_next_keepalive_us B) (Cfg_keepalive_ms B) (g_now B) ->
  S_host_counter Bh = u32 (S_host_counter B + 1) -> S_next_keepalive_us Bh = nk -> S_inflight Bh = 1 ->
  S_inflight_counter Bh = u32 (S_host_counter B + 1) -> S_inflight_retries Bh = 0 ->
  S_inflight_sent_us Bh = g_now B -> S_inflight_len Bh = 60 -> sub Bh A_S_inflight_frame 60 = fr ->
  g_fail_next Bz = 0 -> M_host_counter Bz = u32 (S_host_counter B + 1) -> (g_raw B = 0 -> M_next_ka Bz = nk) ->
  M_fly_on Bz = 1 -> M_fly_cmd Bz = DIGINET_CMD_DATA -> M_fly_counter Bz = u32 (S_host_counter B + 1) ->
  M_fly_retries Bz = 0 -> M_fly_sent Bz = g_now B -> M_fly_len Bz = 60 -> sub Bz A_M_fly_frame 60 = fr ->
  tick_post I ops B B'.
Proof.
  intros I ops B Bh Bz B' fr nk HC Hst Hnk HW1 HW2 HW3 Hfr Hnkv S1 S2 S3 S4 S5 S6 S7 S8
    M0 M1 M2 M3 M4 M5 M6 M7 M8 M9.
  pose proof (ac_cfg _ _ _ HC) as HA. pose proof (ac_io _ _ _ HC) as HI. pose proof (ac_st _ _ _ HC) as HS.
  pose proof (ac_fly _ _ _ HC) as HF. pose proof (ac_time _ _ _ HC) as HT. pose proof (ac_q _ _ _ HC) as HQ.
  pose proof (ac_misc _ _ _ HC) as HM.
  assert (HMst : M_state B = S_ONLINE) by (rewrite <- (b1_state _ HS); exact Hst).
  (* B -> B' *)
  pose proof (ka_W_trans B Bh Bz B' HW1 HW2 HW3) as HW.
  (* what the library wrote, at B' *)
  assert (T1 : S_host_counter B' = u32 (S_host_counter B + 1)).
  { transitivity (S_host_counter Bz); [unfold S_host_counter; ka_keep HW3|].
    refine (eq_trans _ S1). unfold S_host_counter. ka_keep HW2. }
  assert (T2 : S_next_keepalive_us B' = nk).
  { transitivity (S_next_keepalive_us Bz); [unfold S_next_keepalive_us; ka_keep HW3|].
    refine (eq_trans _ S2). unfold S_next_keepalive_us. ka_keep HW2. }
  assert (T3 : S_inflight B' = 1).
  { transitivity (S_inflight Bz); [unfold S_inflight; ka_keep HW3|].
    refine (eq_trans _ S3). unfold S_inflight. ka_keep HW2. }
  assert (T4 : S_inflight_counter B' = u32 (S_host_counter B + 1)).
  { transitivity (S_inflight_counter Bz); [unfold S_inflight_counter; ka_keep HW3|].
    refine (eq_trans _ S4). unfold S_inflight_counter. ka_keep HW2. }
  assert (T5 : S_inflight_retries B' = 0).
  { transitivity (S_inflight_retries Bz); [unfold S_inflight_retries; ka_keep HW3|].
    refine (eq_trans _ S5). unfold S_inflight_retries. ka_keep HW2. }
  assert (T6 : S_inflight_sent_us B' = g_now B).
  { transitivity (S_inflight_sent_us Bz); [unfold S_inflight_sent_us; ka_keep HW3|].
    refine (eq_trans _ S6). unfold S_inflight_sent_us. ka_keep HW2. }
  assert (T7 : S_inflight_len B' = 60).
  { transitivity (S_inflight_len Bz); [unfold S_inflight_len; ka_keep HW3|].
    refine (eq_trans _ S7). unfold S_inflight_len. ka_keep HW2. }
  assert (T8 : sub B' A_S_inflight_frame 60 = fr).
  { transitivity (sub Bz A_S_inflight_frame 60); [ka_keep HW3|].
    refine (eq_trans _ S8). ka_keep HW2. }
  (* what the harness wrote, at B' *)
  assert (U0 : g_fail_next B' = 0) by (refine (eq_trans _ M0); unfold g_fail_next; ka_keep HW3).
  assert (U1 : M_host_counter B' = u32 (S_host_counter B + 1))
    by (refine (eq_trans _ M1); unfold M_host_counter; ka_keep HW3).
  assert (U2 : g_raw B = 0 -> M_next_ka B' = nk)
    by (intros Er; refine (eq_trans _ (M2 Er)); unfold M_next_ka; ka_keep HW3).
  assert (U3 : M_fly_on B' = 1) by (refine (eq_trans _ M3); unfold M_fly_on; ka_keep HW3).
  assert (U4 : M_fly_cmd B' = DIGINET_CMD_DATA) by (refine (eq_trans _ M4); unfold M_fly_cmd; ka_keep HW3).
  assert (U5 : M_fly_counter B' = u32 (S_host_counter B + 1))
    by (refine (eq_trans _ M5); unfold M_fly_counter; ka_keep HW3).
  assert (U6 : M_fly_retries B' = 0) by (refine (eq_trans _ M6); unfold M_fly_retries; ka_keep HW3).
  assert (U7 : M_fly_sent B' = g_now B) by (refine (eq_trans _ M7); unfold M_fly_sent; ka_keep HW3).
  assert (U8 : M_fly_len B' = 60) by (refine (eq_trans _ M8); unfold M_fly_len; ka_keep HW3).
  assert (U9 : sub B' A_M_fly_frame 60 = fr) by (refine (eq_trans _ M9); ka_keep HW3).
  (* every other read is the same in B' and B *)
  assert (Kmr : Cfg_max_retries B' = Cfg_max_retries B) by (unfold Cfg_max_retries; ka_keep HW).
  assert (Kack : Cfg_ack_timeout_ms B' = Cfg_ack_timeout_ms B) by (unfold Cfg_ack_timeout_ms; ka_keep HW).
  assert (Kka : Cfg_keepalive_ms B' = Cfg_keepalive_ms B) by (unfold Cfg_keepalive_ms; ka_keep HW).
  assert (Kbk : Cfg_backoff_ms B' = Cfg_backoff_ms B) by (unfold Cfg_backoff_ms; ka_keep HW).
  assert (Koff : Cfg_offline_ms B' = Cfg_offline_ms B) by (unfold Cfg_offline_ms; ka_keep HW).
  assert (Kwt : Cfg_wake_timeout_ms B' = Cfg_wake_timeout_ms B) by (unfold Cfg_wake_timeout_ms; ka_keep HW).
  assert (Kgap : Cfg_display_gap_us B' = Cfg_display_gap_us B) by (unfold Cfg_display_gap_us; ka_keep HW).
  assert (Kmc : Cfg_max_cmds B' = Cfg_max_cmds B) by (unfold Cfg_max_cmds; ka_keep HW).
  assert (Kmb : Cfg_max_body B' = Cfg_max_body B) by (unfold Cfg_max_body; ka_keep HW).
  assert (Khm : Cfg_host_mac B' = Cfg_host_mac B) by (unfold Cfg_host_mac; ka_keep HW).
  assert (Kdm : Cfg_desk_mac B' = Cfg_desk_mac B) by (unfold Cfg_desk_mac; ka_keep HW).
  assert (Kdms : Cfg_desk_mac_set B' = Cfg_desk_mac_set B) by (unfold Cfg_desk_mac_set; ka_keep HW).
  assert (Kaw : Cfg_auto_wake B' = Cfg_auto_wake B) by (unfold Cfg_auto_wake; ka_keep HW).
  assert (Kmode : Cfg_sum_mode B' = Cfg_sum_mode B) by (unfold Cfg_sum_mode; ka_keep HW).
  assert (Kraw : g_raw B' = g_raw B) by (unfold g_raw; ka_keep HW).
  assert (Kioc : S_io_ctx B' = S_io_ctx B) by (unfold S_io_ctx; ka_keep HW).
  assert (Kios : S_io_send B' = S_io_send B) by (unfold S_io_send; ka_keep HW).
  assert (Kior : S_io_recv B' = S_io_recv B) by (unfold S_io_recv; ka_keep HW).
  assert (Kion : S_io_now_us B' = S_io_now_us B) by (unfold S_io_now_us; ka_keep HW).
  assert (Kno : S_notify B' = S_notify B) by (unfold S_notify; ka_keep HW).
  assert (Knoc : S_notify_ctx B' = S_notify_ctx B) by (unfold S_notify_ctx; ka_keep HW).
  assert (KSst : S_state B' = S_state B) by (unfold S_state; ka_keep HW).
  assert (KMst : M_state B' = M_state B) by (unfold M_state; ka_keep HW).
  assert (KSdk : S_desk_known B' = S_desk_known B) by (unfold S_desk_known; ka_keep HW).
  assert (KMdk : M_desk_known B' = M_desk_known B) by (unfold M_desk_known; ka_keep HW).
  assert (KSdm : S_desk_mac B' = S_desk_mac B) by (unfold S_desk_mac; ka_keep HW).
  assert (KMd : M_desk B' = M_desk B) by (unfold M_desk; ka_keep HW).
  assert (KSfo : S_foreign B' = S_foreign B) by (unfold S_foreign; ka_keep HW).
  assert (KMfo : M_foreign B' = M_foreign B) by (unfold M_foreign; ka_keep HW).
  assert (KSe1 : S_e1_named_us B' = S_e1_named_us B) by (unfold S_e1_named_us; ka_keep HW).
  assert (KMe1 : M_e1_us B' = M_e1_us B) by (unfold M_e1_us; ka_keep HW).
  assert (KSwa : S_wake_acked B' = S_wake_acked B) by (unfold S_wake_acked; ka_keep HW).
  assert (KMe2 : M_e2_acked B' = M_e2_acked B) by (unfold M_e2_acked; ka_keep HW).
  assert (KSws : S_wake_sent_us B' = S_wake_sent_us B) by (unfold S_wake_sent_us; ka_keep HW).
  assert (KMws : M_wake_sent B' = M_wake_sent B) by (unfold M_wake_sent; ka_keep HW).
  assert (KSlr : S_last_rx_us B' = S_last_rx_us B) by (unfold S_last_rx_us; ka_keep HW).
  assert (KMlr : M_last_rx B' = M_last_rx B) by (unfold M_last_rx; ka_keep HW).
  assert (KSbo : S_backoff_until_us B' = S_backoff_until_us B) by (unfold S_backoff_until_us; ka_keep HW).
  assert (KMbo : M_backoff_until B' = M_backoff_until B) by (unfold M_backoff_until; ka_keep HW).
  assert (KSds : S_display_sent B' = S_display_sent B) by (unfold S_display_sent; ka_keep HW).
  assert (KMds : M_display_sent B' = M_display_sent B) by (unfold M_display_sent; ka_keep HW).
  assert (KSld : S_last_display_us B' = S_last_display_us B) by (unfold S_last_display_us; ka_keep HW).
  assert (KMld : M_last_display B' = M_last_display B) by (unfold M_last_display; ka_keep HW).
  assert (KSdv : S_desk_counter_valid B' = S_desk_counter_valid B) by (unfold S_desk_counter_valid; ka_keep HW).
  assert (KMdv : M_desk_counter_valid B' = M_desk_counter_valid B) by (unfold M_desk_counter_valid; ka_keep HW).
  assert (KSdc : S_desk_counter B' = S_desk_counter B) by (unfold S_desk_counter; ka_keep HW).
  assert (KMdc : M_desk_counter B' = M_desk_counter B) by (unfold M_desk_counter; ka_keep HW).
  assert (Know : g_now B' = g_now B) by (unfold g_now; ka_keep HW).
  assert (Kqd : S_queued B' = S_queued B) by (unfold S_queued; ka_keep HW).
  assert (Knq : g_nq B' = g_nq B) by (unfold g_nq; ka_keep HW).
  assert (Kncmd : g_ncmd B' = g_ncmd B) by (unfold g_ncmd; ka_keep HW).
  assert (KSp : S_personality B' = S_personality B) by (unfold S_personality; ka_keep HW).
  assert (KQ : forall i, 0 <= i < 1024 -> Q_at B' i = Q_at B i) by (intros i Hi; unfold Q_at; ka_keepi HW Hi).
  assert (KCst : forall i, 0 <= i < 1024 -> Cmd_st B' i = Cmd_st B i) by (intros i Hi; unfold Cmd_st; ka_keepi HW Hi).
  assert (KCb : forall i, 0 <= i < 1024 -> Cmd_bytes B' i = Cmd_bytes B i) by (intros i Hi; unfold Cmd_bytes; ka_keepi HW Hi).
  assert (KCl : forall i, 0 <= i < 1024 -> Cmd_len B' i = Cmd_len B i) by (intros i Hi; unfold Cmd_len; ka_keepi HW Hi).
  assert (KCk : forall i, 0 <= i < 1024 -> Cmd_key B' i = Cmd_key B i) by (intros i Hi; unfold Cmd_key; ka_keepi HW Hi).
  assert (KCd : forall i, 0 <= i < 1024 -> Cmd_display B' i = Cmd_display B i) by (intros i Hi; unfold Cmd_display; ka_keepi HW Hi).
  assert (KSqb : forall i, 0 <= i < 512 -> S_queue_bytes B' i = S_queue_bytes B i) by (intros i Hi; unfold S_queue_bytes; ka_keepi HW Hi).
  assert (KSql : forall i, 0 <= i < 512 -> S_queue_len B' i = S_queue_len B i) by (intros i Hi; unfold S_queue_len; ka_keepi HW Hi).
  assert (KSqk : forall i, 0 <= i < 512 -> S_queue_key B' i = S_queue_key B i) by (intros i Hi; unfold S_queue_key; ka_keepi HW Hi).
  assert (KSqd : forall i, 0 <= i < 512 -> S_queue_display B' i = S_queue_display B i) by (intros i Hi; unfold S_queue_display; ka_keepi HW Hi).
  assert (Ka2a : sub B' A_S_cfg_host_mac 60 = sub B A_S_cfg_host_mac 60) by ka_keep HW.
  assert (Ka2b : sub B' OFF_g_cfg 60 = sub B OFF_g_cfg 60) by ka_keep HW.
  (* bounds *)
  pose proof (d3_ncmd _ _ HQ) as Hn3. pose proof (d3_ops _ _ HQ) as Hops. unfold OPS_MAX in Hops.
  assert (Hnow : g_now B + 65536000 < 2 ^ 64).
  { pose proof (c_now _ _ HT) as Hc. change (2 ^ 64) with 18446744073709551616. lia. }
  assert (Hnk0 : 0 <= S_next_keepalive_us B).
  { unfold S_next_keepalive_us. exact (proj1 (u_at_range B A_S_next_keepalive_us 8)). }
  constructor.
  - (* tp_core *)
    constructor.
    + exact (ac_img _ _ _ HC).
    + rewrite (proj1 HW). exact (ac_len _ _ _ HC).
    + (* A *)
      constructor.
      * rewrite Kmr. exact (a1_max_retries _ HA).
      * rewrite Kack. exact (a1_ack_timeout _ HA).
      * rewrite Kka. exact (a1_keepalive _ HA).
      * rewrite Kbk. exact (a1_backoff _ HA).
      * rewrite Koff. exact (a1_offline _ HA).
      * rewrite Kwt. exact (a1_wake_timeout _ HA).
      * rewrite Kgap. exact (a1_display_gap _ HA).
      * rewrite Kmc. exact (a1_max_cmds _ HA).
      * rewrite Kmb. exact (a1_max_body _ HA).
      * rewrite Khm. exact (a1_host_mac _ HA).
      * rewrite Kdm. exact (a1_desk_mac _ HA).
      * rewrite Kdms. exact (a1_desk_mac_set _ HA).
      * rewrite Kaw. exact (a1_auto_wake _ HA).
      * rewrite Kmode. exact (a1_sum_mode _ HA).
      * rewrite Ka2a. rewrite Ka2b. exact (a2_cfg _ HA).
      * rewrite Kraw. exact (a4_raw _ HA).
    + (* A3 *)
      constructor.
      * rewrite Kioc. exact (a3_io_ctx _ _ HI).
      * rewrite Kios. exact (a3_io_send _ _ HI).
      * rewrite Kior. exact (a3_io_recv _ _ HI).
      * rewrite Kion. exact (a3_io_now _ _ HI).
      * rewrite Kno. exact (a3_notify _ _ HI).
      * rewrite Knoc. exact (a3_notify_ctx _ _ HI).
    + (* B1-B7, B9 *)
      constructor.
      * rewrite KSst. rewrite KMst. exact (b1_state _ HS).
      * rewrite KMst. exact (b1_state_range _ HS).
      * rewrite KSdk. rewrite KMdk. exact (b2_desk_known _ HS).
      * rewrite KMdk. exact (b2_desk_known01 _ HS).
      * rewrite KMdk. rewrite KSdm. rewrite KMd. exact (b2_desk_mac _ HS).
      * rewrite KSfo. rewrite KMfo. exact (b3_foreign _ HS).
      * rewrite KMfo. exact (b3_foreign01 _ HS).
      * rewrite KSe1. rewrite KMe1. exact (b3_e1 _ HS).
      * rewrite KMe1. exact (b3_e1_01 _ HS).
      * rewrite KSwa. rewrite KMe2. exact (b3_e2 _ HS).
      * rewrite KMe2. exact (b3_e2_01 _ HS).
      * rewrite KSws. rewrite KMws. exact (b4_wake_sent _ HS).
      * rewrite KSlr. rewrite KMlr. exact (b4_last_rx _ HS).
      * rewrite KSbo. rewrite KMbo. exact (b4_backoff _ HS).
      * rewrite Kraw. intros Er. rewrite T2. rewrite (U2 Er). reflexivity.
      * rewrite Kraw. rewrite KSds. rewrite KMds. exact (b5_display_sent _ HS).
      * rewrite Kraw. rewrite KMds. exact (b5_display_sent01 _ HS).
      * rewrite Kraw. rewrite KSld. rewrite KMld. exact (b5_last_display _ HS).
      * rewrite KSdv. rewrite KMdv. exact (b6_valid _ HS).
      * rewrite KMdv. exact (b6_valid01 _ HS).
      * rewrite KMdv. rewrite KSdc. rewrite KMdc. exact (b6_counter _ HS).
      * rewrite T1. rewrite U1. reflexivity.
      * rewrite KMst. rewrite HMst. intros [X|X]; unfold S_ONLINE, S_IDLE, S_CLOSED in X; discriminate X.
      * rewrite KMst. rewrite KMdk. exact (b9_known _ HS).
    + (* B8 *)
      constructor.
      * rewrite T3. rewrite U3. reflexivity.
      * rewrite U3. right. reflexivity.
      * intros _. right. rewrite KMst. exact HMst.
      * intros _. rewrite T4. rewrite U5. reflexivity.
      * intros _. rewrite T4. rewrite T1. reflexivity.
      * intros _. rewrite T5. rewrite U6. reflexivity.
      * intros _. rewrite U6. unfold Cfg_max_retries. exact (proj1 (u_at_range B' A_Cfg_max_retries 4)).
      * intros _. rewrite T6. rewrite U7. reflexivity.
      * intros _. rewrite T7. rewrite U8. reflexivity.
      * intros _. rewrite U4. right. reflexivity.
      * intros _. exists [b8 0], (u8 1).
        refine (conj _ (conj ka_bc (conj _ (conj _ (conj _ _))))).
        -- cbn [length]. lia.
        -- change (u8 1) with 1. lia.
        -- rewrite U8. reflexivity.
        -- rewrite U8. change (Z.to_nat 60) with 60%nat. rewrite U9.
           rewrite KMd. rewrite U5. rewrite U4. rewrite Kmode. exact Hfr.
        -- rewrite U8. change (Z.to_nat 60) with 60%nat. rewrite T8.
           rewrite KMd. rewrite U5. rewrite U6. rewrite U4. rewrite Kmode. exact Hfr.
    + (* C *)
      constructor.
      * rewrite Know. exact (c_now _ _ HT).
      * rewrite KMlr. rewrite Know. exact (c1_last_rx _ _ HT).
      * rewrite KMws. rewrite Know. exact (c1_wake_sent _ _ HT).
      * intros _. rewrite U7. rewrite Know. lia.
      * rewrite KMds. rewrite KMld. rewrite Know. exact (c1_last_display _ _ HT).
      * rewrite KMbo. rewrite Know. exact (c1_backoff _ _ HT).
      * rewrite Kraw. intros Er. rewrite (U2 Er). rewrite Know. rewrite Hnkv.
        apply ka_nk_le; [lia | exact (a1_keepalive _ HA) | exact Hnow].
      * rewrite KMst. rewrite HMst. intros X. unfold S_ONLINE, S_WAKING in X. discriminate X.
      * rewrite KMst. rewrite Know. rewrite KMlr. rewrite Koff. exact (c2_online _ _ HT).
      * intros _. rewrite Know. rewrite U7. rewrite Kack. pose proof (a1_ack_timeout _ HA). lia.
    + (* D *)
      constructor.
      * rewrite Kraw. rewrite Kqd. rewrite Knq. exact (d1_queued _ _ HQ).
      * rewrite Kraw. rewrite Knq. exact (d1_nq _ _ HQ).
      * rewrite Kraw. intros Er i Hi. rewrite Knq in Hi.
        pose proof (d1_nq _ _ HQ Er) as Hnq. unfold QUEUE_MAX in Hnq.
        destruct (d1_entry _ _ HQ Er i Hi) as (E1 & E2 & E3 & E4 & E5 & E6).
        assert (Hi1 : 0 <= i < 1024) by lia. assert (Hi2 : 0 <= i < 512) by lia.
        assert (Hk : 0 <= Q_at B i < 1024) by lia.
        rewrite (KQ i Hi1). rewrite Kncmd. rewrite (KCst _ Hk). rewrite (KSqb i Hi2). rewrite (KCb _ Hk).
        rewrite (KSql i Hi2). rewrite (KCl _ Hk). rewrite (KSqk i Hi2). rewrite (KCk _ Hk).
        rewrite (KSqd i Hi2). rewrite (KCd _ Hk).
        exact (conj E1 (conj E2 (conj E3 (conj E4 (conj E5 E6))))).
      * rewrite Kraw. intros Er i j Hi Hj Hq. rewrite Knq in Hi. rewrite Knq in Hj.
        pose proof (d1_nq _ _ HQ Er) as Hnq. unfold QUEUE_MAX in Hnq.
        rewrite (KQ i ltac:(lia)) in Hq. rewrite (KQ j ltac:(lia)) in Hq.
        exact (d1_nodup _ _ HQ Er i j Hi Hj Hq).
      * rewrite Kraw. intros Er k Hk. rewrite Kncmd in Hk.
        pose proof (d1_nq _ _ HQ Er) as Hnq. unfold QUEUE_MAX in Hnq.
        rewrite (KCst k ltac:(lia)). rewrite Knq.
        destruct (d1_pending _ _ HQ Er k Hk) as [P1 P2]. split.
        -- intros Hp. destruct (P1 Hp) as (i & Hi & Hq). exists i. split; [exact Hi|].
           rewrite (KQ i ltac:(lia)). exact Hq.
        -- intros (i & Hi & Hq). apply P2. exists i. split; [exact Hi|].
           rewrite (KQ i ltac:(lia)) in Hq. exact Hq.
      * intros k Hk Hst0. rewrite Kncmd in Hk. rewrite (KCst k ltac:(lia)) in Hst0.
        rewrite (KCb k ltac:(lia)). rewrite (KCl k ltac:(lia)). rewrite (KCd k ltac:(lia)).
        exact (d2_cmd _ _ HQ k Hk Hst0).
      * rewrite Kncmd. exact Hn3.
      * exact (d3_ops _ _ HQ).
      * rewrite Kraw. rewrite Kqd. exact (d4_queued _ _ HQ).
      * rewrite Kraw. intros Er i Hi. rewrite Kqd in Hi.
        pose proof (d4_queued _ _ HQ Er) as Hq4. unfold QUEUE_MAX in Hq4.
        rewrite (KSql i ltac:(lia)). rewrite (KSqb i ltac:(lia)).
        exact (d4_entry _ _ HQ Er i Hi).
    + (* E *)
      constructor.
      * rewrite U0. left. reflexivity.
      * rewrite KSp. exact (e2_personality _ _ HM).
  - (* C2's keepalive clause: something is in flight *)
    unfold c2_keepalive. intros _ _ X. rewrite U3 in X. discriminate X.
  - (* the drain fact: likewise *)
    unfold drain_fact. intros _ _ X. rewrite U3 in X. discriminate X.
  - (* the frame *)
    apply (wframe_weaken ka_W R_tick B B'); [|exact HW].
    intros a Ha. unfold ka_W, ka_Wlib, ka_Wio in Ha. unfold R_tick. clear - Ha. ka_uaa. lia.
  - right. exact U0.
Qed.

(* ---------------------------------------------------------------- the keepalive path of the tick *)

Lemma tick_ka_keep : forall (HL : links) I F ops B,
  agree_core I ops B -> S_state B = DIGINET_S_ONLINE -> S_inflight B = 0 ->
  S_backoff_until_us B <= g_now B -> S_next_keepalive_us B <= g_now B ->
  exists B' r, tick_ka_m I F B (g_now B) = Some (B', r) /\ tick_post I ops B B' /\ wframe ka_W B B'.
Proof.
  intros HL I F ops B HC Hst Hinf Hbo Hnk.
  pose proof (ac_len _ _ _ HC) as HB.
  pose proof (ac_cfg _ _ _ HC) as HA. pose proof (ac_io _ _ _ HC) as HI. pose proof (ac_st _ _ _ HC) as HS.
  pose proof (ac_fly _ _ _ HC) as HF. pose proof (ac_time _ _ _ HC) as HT.
  assert (HMst : M_state B = S_ONLINE) by (rewrite <- (b1_state _ HS); exact Hst).
  assert (HMon : M_fly_on B = 0) by (rewrite <- (b8_on _ HF); exact Hinf).
  assert (HMbo : M_backoff_until B <= g_now B) by (rewrite <- (b4_backoff _ HS); exact Hbo).
  assert (HMkn : M_desk_known B = 1) by (apply (b9_known _ HS); right; exact HMst).
  pose proof (b2_desk_mac _ HS HMkn) as Hdesk.
  pose proof (a2_host_mac B HA) as Hhost. pose proof (a2_sum_mode B HA) as Hmode.
  pose proof (a2_keepalive B HA) as Hka.
  (* the keepalive frame (DS:393-394: diginet_frame_build of the body {0}, one command) *)
  remember (lib_frame (M_desk B) HOST (u32 (S_host_counter B + 1)) 0 0 DIGINET_CMD_DATA (u8 1) [b8 0]
              (Cfg_sum_mode B)) as fr eqn:Hfr.
  assert (Hok : build_ok (M_desk B) HOST (u32 (S_host_counter B + 1)) 0 0 DIGINET_CMD_DATA (u8 1) [b8 0]
                  (Cfg_sum_mode B)).
  { refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ ka_bc))))))))).
    - unfold M_desk. apply length_sub; [ka_ar|]. rewrite HB. ka_ua. lia.
    - reflexivity.
    - exact (a1_sum_mode _ HA).
    - unfold u32. apply Z.mod_pos_bound. lia.
    - lia.
    - lia.
    - unfold DIGINET_CMD_DATA. lia.
    - change (u8 1) with 1. lia.
    - cbn [length]. lia. }
  assert (Hfl : length fr = 60%nat).
  { pose proof (rf_lib_frame HL _ _ _ _ _ _ _ _ _ Hok) as R. cbv zeta in R. destruct R as (Hlen & _).
    rewrite <- Hfr in Hlen. change (frame_len (length [b8 0])) with 60 in Hlen. lia. }
  pose proof (build_code_ok HL _ _ _ _ _ _ _ _ _ DIGINET_MAX_FRAME_LEN Hok ltac:(cbv; discriminate)) as Hbc.
  change (frame_len (length [b8 0])) with 60 in Hbc.
  (* DS:451-454 *)
  destruct (ka_prefix I F B (g_now B) HB) as (Bc & E1 & HBc & HWc & Hnkc).
  assert (Kc1 : S_desk_mac Bc = M_desk B) by (refine (eq_trans _ Hdesk); unfold S_desk_mac; ka_keep HWc).
  assert (Kc2 : S_cfg_host_mac Bc = HOST) by (refine (eq_trans _ Hhost); unfold S_cfg_host_mac; ka_keep HWc).
  assert (Kc3 : S_host_counter Bc = S_host_counter B) by (unfold S_host_counter; ka_keep HWc).
  assert (Kc4 : S_cfg_sum_mode Bc = Cfg_sum_mode B) by (refine (eq_trans _ Hmode); unfold S_cfg_sum_mode; ka_keep HWc).
  (* DS:390-400 *)
  destruct (ka_send_data I F Bc (g_now B) (M_desk B) HOST (S_host_counter B) (Cfg_sum_mode B) fr
              HBc Kc1 Kc2 Kc3 Kc4 Hbc Hfr Hfl)
    as (Bh & E2 & HBh & HWh & S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
  assert (HWBh : wframe ka_Wlib B Bh).
  { apply (wframe_trans ka_Wlib B Bc Bh); [|exact HWh].
    apply (wframe_weaken ka_Wpre ka_Wlib B Bc); [|exact HWc].
    intros a Ha. unfold ka_Wpre in Ha. unfold ka_Wlib. clear - Ha. lia. }
  rewrite E1. rewrite E2. unfold send_raw_m, call_send.
  assert (Kio : S_io_send Bh = ti_io_send I)
    by (refine (eq_trans _ (a3_io_send _ _ HI)); unfold S_io_send; ka_keep HWBh).
  rewrite Kio. rewrite (Z.eqb_refl (ti_io_send I)). cbv beta iota.
  (* io_send's view of Bh *)
  assert (H1 : M_desk_known Bh = 1) by (refine (eq_trans _ HMkn); unfold M_desk_known; ka_keep HWBh).
  assert (H2 : M_desk Bh = M_desk B) by (unfold M_desk; ka_keep HWBh).
  assert (H3 : Cfg_sum_mode Bh = Cfg_sum_mode B) by (unfold Cfg_sum_mode; ka_keep HWBh).
  assert (H4 : M_state Bh = S_ONLINE) by (refine (eq_trans _ HMst); unfold M_state; ka_keep HWBh).
  assert (H5 : M_fly_on Bh = 0) by (refine (eq_trans _ HMon); unfold M_fly_on; ka_keep HWBh).
  assert (Kn : g_now Bh = g_now B) by (unfold g_now; ka_keep HWBh).
  assert (Kbo : M_backoff_until Bh = M_backoff_until B) by (unfold M_backoff_until; ka_keep HWBh).
  assert (H6 : M_backoff_until Bh <= g_now Bh) by (rewrite Kbo; rewrite Kn; exact HMbo).
  assert (Khc : M_host_counter Bh = M_host_counter B) by (unfold M_host_counter; ka_keep HWBh).
  assert (H7 : u32 (S_host_counter B + 1) = u32 (M_host_counter Bh + 1)).
  { rewrite Khc. rewrite (b7_host_counter _ HS). reflexivity. }
  assert (Kmb : Cfg_max_body Bh = Cfg_max_body B) by (unfold Cfg_max_body; ka_keep HWBh).
  assert (Kmc : Cfg_max_cmds Bh = Cfg_max_cmds B) by (unfold Cfg_max_cmds; ka_keep HWBh).
  assert (H8 : 1 <= Cfg_max_body Bh) by (rewrite Kmb; pose proof (a1_max_body _ HA); lia).
  assert (H9 : 1 <= Cfg_max_cmds Bh) by (rewrite Kmc; pose proof (a1_max_cmds _ HA); lia).
  assert (Kraw : g_raw Bh = g_raw B) by (unfold g_raw; ka_keep HWBh).
  assert (Knk : M_next_ka Bh = M_next_ka B) by (unfold M_next_ka; ka_keep HWBh).
  assert (Kka : Cfg_keepalive_ms Bh = Cfg_keepalive_ms B) by (unfold Cfg_keepalive_ms; ka_keep HWBh).
  assert (H10 : g_raw Bh = 0 -> M_next_ka Bh <= g_now Bh).
  { intros Er. rewrite Kraw in Er. rewrite Knk. rewrite Kn. rewrite <- (b5_next_ka _ HS Er). exact Hnk. }
  (* FT:823-899 *)
  destruct (ka_io HL I Bh fr (M_desk B) (u32 (S_host_counter B + 1)) (Cfg_sum_mode B)
              HBh Hok Hfr H1 H2 H3 H4 H5 H6 H7 H8 H9 H10)
    as (Bz & E3 & HBz & HWz & M0 & M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9).
  rewrite E3. cbv beta iota.
  (* the facts ka_post reads *)
  assert (S2n : S_next_keepalive_us Bh = ka_nk (S_next_keepalive_us B) (Cfg_keepalive_ms B) (g_now B)).
  { rewrite S2. rewrite Hnkc. rewrite Hka. reflexivity. }
  assert (S6n : S_inflight_sent_us Bh = g_now B).
  { rewrite S6. unfold g_now. apply ka_ua_mod8. }
  assert (M2n : g_raw B = 0 -> M_next_ka Bz = ka_nk (S_next_keepalive_us B) (Cfg_keepalive_ms B) (g_now B)).
  { intros Er. assert (Erh : g_raw Bh = 0) by (rewrite Kraw; exact Er).
    rewrite (M2 Erh). rewrite Knk. rewrite Kka. rewrite Kn. rewrite <- (b5_next_ka _ HS Er). reflexivity. }
  assert (M7n : M_fly_sent Bz = g_now B) by (rewrite M7; exact Kn).
  destruct (truth (g_fail_next Bh)); cbv beta iota.
  - (* io_send returned -EIO (FT:898): send_raw counts nothing (DS:91-93) *)
    change (- EIO =? 0) with false. cbv beta iota.
    exists Bz, (- EIO). split; [reflexivity|]. split.
    + exact (ka_post I ops B Bh Bz Bz fr _ HC Hst Hnk HWBh HWz (wframe_refl ka_Wst Bz) Hfr eq_refl
               S1 S2n S3 S4 S5 S6n S7 S8 M0 M1 M2n M3 M4 M5 M6 M7n M8 M9).
    + exact (ka_W_trans B Bh Bz Bz HWBh HWz (wframe_refl ka_Wst Bz)).
  - (* io_send returned 0: send_raw counts the frame (DS:91-92) *)
    change (0 =? 0) with true. cbv beta iota.
    eexists. eexists. split; [reflexivity|].
    match goal with |- _ /\ wframe _ _ ?X =>
      assert (HW3 : wframe ka_Wst Bz X) by (ka_us; ka_wf (wframe_refl ka_Wst Bz) HBz) end.
    split.
    + exact (ka_post I ops B Bh Bz _ fr _ HC Hst Hnk HWBh HWz HW3 Hfr eq_refl
               S1 S2n S3 S4 S5 S6n S7 S8 M0 M1 M2n M3 M4 M5 M6 M7n M8 M9).
    + exact (ka_W_trans B Bh Bz _ HWBh HWz HW3).
Qed.

Lemma tick_ka_ok : forall (HL : links) I F ops B,
  agree_core I ops B -> S_state B = DIGINET_S_ONLINE -> S_inflight B = 0 ->
  S_backoff_until_us B <= g_now B -> S_next_keepalive_us B <= g_now B ->
  exists B' r, tick_ka_m I F B (g_now B) = Some (B', r) /\ tick_post I ops B B'.
Proof.
  intros HL I F ops B HC Hst Hinf Hbo Hnk.
  destruct (tick_ka_keep HL I F ops B HC Hst Hinf Hbo Hnk) as (B' & r & E & Hp & _). exists B', r. exact (conj E Hp).
Qed.
