(* A getter of TWorld.v / TCb.v (s32_at, u_at or sub at a literal offset) applied to a chain of setters (upd ..
   (put n v)): rewrite the read through each write it misses, and read back the write it hits. The tactics
   only rewrite with fully applied lemmas whose left side is in the goal (no rewrite falls back to conversion:
   one such rewrite once grew a build to 209 GB), and decide offsets on the unfolded numbers.
   Use: `assert (E : M_state X = M_state B) by wget.` (X a setter chain over B with length B = WN in the
   context), `assert (E : S_state X = 2) by wget.`; wget unfolds the getters and setters of its goal only.
   lib_start's frame: `rs_get` reads a getter through lib_start (RxBase.v) when its range misses R_start. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TNeed TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree SimLib QueueFacts RxBase.
Import ListNotations.
Open Scope Z_scope.

(* ---- the reads through one write ---- *)

Lemma rw_sub_d : forall B k v j n, length B = WN -> 0 <= k -> 0 <= j -> k + Z.of_nat (length v) <= W_LEN ->
  (j + Z.of_nat n <= k \/ k + Z.of_nat (length v) <= j) -> sub (upd B k v) j n = sub B j n.
Proof. intros B k v j n HB Hk Hj Hv Hd. apply sub_upd_out; try assumption. rewrite HB. unfold WN. lia. Qed.

Lemma rw_u_d : forall B k v j n, length B = WN -> 0 <= k -> 0 <= j -> k + Z.of_nat (length v) <= W_LEN ->
  (j + Z.of_nat n <= k \/ k + Z.of_nat (length v) <= j) -> u_at (upd B k v) j n = u_at B j n.
Proof. intros. unfold u_at. f_equal. apply rw_sub_d; assumption. Qed.

Lemma rw_s_d : forall B k v j, length B = WN -> 0 <= k -> 0 <= j -> k + Z.of_nat (length v) <= W_LEN ->
  (j + 4 <= k \/ k + Z.of_nat (length v) <= j) -> s32_at (upd B k v) j = s32_at B j.
Proof. intros. unfold s32_at. f_equal. apply rw_u_d; assumption. Qed.

Lemma rw_sub_p : forall B k v n, length B = WN -> 0 <= k -> k + Z.of_nat n <= W_LEN -> length v = n ->
  sub (upd B k v) k n = v.
Proof.
  intros B k v n HB Hk Hn Hv. apply sub_upd_eq; [exact Hk | exact Hv | rewrite HB; unfold WN; lia].
Qed.

Lemma rw_u_p : forall B k n x, length B = WN -> 0 <= k -> k + Z.of_nat n <= W_LEN ->
  u_at (upd B k (put n x)) k n = x mod 2 ^ (8 * Z.of_nat n).
Proof.
  intros B k n x HB Hk Hn. unfold u_at. rewrite rw_sub_p; [apply bytes_le_to_Z_put | exact HB | exact Hk | exact Hn |].
  apply length_put.
Qed.

Lemma rw_s_p : forall B k x, length B = WN -> 0 <= k -> k + 4 <= W_LEN ->
  s32_at (upd B k (put 4 x)) k = bv_swrap 32 (x mod 2 ^ 32).
Proof. intros B k x HB Hk Hn. unfold s32_at. rewrite rw_u_p by assumption. reflexivity. Qed.

Lemma rw_len : forall B k v, length B = WN -> 0 <= k -> k + Z.of_nat (length v) <= W_LEN ->
  length (upd B k v) = WN.
Proof. intros B k v HB Hk Hv. rewrite length_upd; [exact HB | exact Hk | rewrite HB; unfold WN; lia]. Qed.

(* the value a write leaves, back in range *)
Lemma rw_swrap_id : forall x, - 2 ^ 31 <= x < 2 ^ 31 -> bv_swrap 32 (x mod 2 ^ 32) = x.
Proof.
  intros x Hx. change (x mod 2 ^ 32) with (bv_wrap 32 x). rewrite bv_swrap_wrap. apply bv_swrap_small.
  unfold bv_half_modulus, bv_modulus. cbn. lia.
Qed.

Lemma rw_mod_id : forall x n, 0 <= x < 2 ^ (8 * Z.of_nat n) -> x mod 2 ^ (8 * Z.of_nat n) = x.
Proof. intros x n H. apply Z.mod_small. exact H. Qed.

(* the ranges of the reads *)
Lemma rw_u_range : forall B j n, 0 <= u_at B j n < 2 ^ (8 * Z.of_nat n).
Proof. intros. split; [apply u_at_nonneg | apply u_at_bound]. Qed.

Lemma rw_s_range : forall B j, - 2 ^ 31 <= s32_at B j < 2 ^ 31.
Proof.
  intros B j. unfold s32_at, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 `div` 2) with (2 ^ 31).
  pose proof (Z.mod_pos_bound (u_at B j 4 + 2 ^ 31) (2 ^ 32) ltac:(lia)). lia.
Qed.

(* ---- offsets ---- *)

Ltac wunf_off := unfold
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
  A_S_io_ctx, A_S_io_now_us, A_S_io_recv, A_S_io_send, A_S_last_display_us, A_S_last_rx_us, A_S_next_keepalive_us,
  A_S_notify, A_S_notify_ctx, A_S_personality, A_S_queue_bytes, A_S_queue_display, A_S_queue_key, A_S_queue_len,
  A_S_queued, A_S_state, A_S_stats_ack_lost, A_S_stats_coalesced, A_S_stats_refused, A_S_stats_rx_data,
  A_S_stats_rx_desk_retries, A_S_stats_rx_duplicates, A_S_stats_rx_frames, A_S_stats_rx_ignored, A_S_stats_tx_acks,
  A_S_stats_tx_data, A_S_stats_tx_frames, A_S_stats_tx_keepalives, A_S_stats_tx_retransmits, A_S_stats_tx_wakes,
  A_S_wake_acked, A_S_wake_sent_us, OFF_GOT, OFF_M, OFF_OW, OFF_g_cfg, OFF_g_cmd, OFF_g_fail_next,
  OFF_g_last_counter, OFF_g_ncmd, OFF_g_now, OFF_g_nq, OFF_g_q, OFF_g_raw, OFF_g_rx, OFF_g_rx_fail, OFF_g_rx_len,
  OFF_g_rx_send, OFF_g_rx_times, OFF_g_s, SZ_GOT, SZ_M, SZ_OW, SZ_g_cfg, SZ_g_cmd, SZ_g_fail_next,
  SZ_g_last_counter, SZ_g_ncmd, SZ_g_now, SZ_g_nq, SZ_g_q, SZ_g_raw, SZ_g_rx, SZ_g_rx_fail, SZ_g_rx_len,
  SZ_g_rx_send, SZ_g_rx_times, SZ_g_s, W_LEN, WN.

Ltac wunf_get := unfold
  M_desk_known, M_desk, M_state, M_e2_acked, M_e1_us, M_foreign, M_last_rx, M_wake_sent, M_next_ka,
  M_backoff_until, M_last_display, M_display_sent, M_desk_counter_valid, M_desk_counter, M_host_counter, M_fail,
  M_fly_on, M_fly_cmd, M_fly_counter, M_fly_retries, M_fly_sent, M_fly_frame, M_fly_len, OW_n, OW_t_state,
  OW_t_old, OW_t_reason, OW_e2, OW_e3, OW_acks, OW_desk, OW_foreign, OW_acked, OW_ndata, OW_acked_counter,
  OW_acked_retry, OW_desk_off, OW_desk_p, OW_desk_body, GOT_n, GOT_t_state, GOT_t_old, GOT_t_reason, GOT_e2,
  GOT_e3, GOT_acks, GOT_desk, GOT_foreign, GOT_acked, GOT_ndata, S_cfg_host_mac, S_cfg_desk_mac,
  S_cfg_desk_mac_set, S_cfg_auto_wake, S_cfg_sum_mode, S_cfg_keepalive_ms, S_cfg_ack_timeout_ms, S_cfg_max_retries,
  S_cfg_backoff_ms, S_cfg_offline_ms, S_cfg_wake_timeout_ms, S_cfg_display_gap_us, S_cfg_max_cmds, S_cfg_max_body,
  S_io_ctx, S_io_send, S_io_recv, S_io_now_us, S_notify, S_notify_ctx, S_state, S_desk_known, S_desk_mac,
  S_personality, S_foreign, S_e1_named_us, S_wake_acked, S_wake_sent_us, S_host_counter, S_desk_counter,
  S_desk_counter_valid, S_last_rx_us, S_next_keepalive_us, S_backoff_until_us, S_last_display_us, S_display_sent,
  S_inflight, S_inflight_frame, S_inflight_len, S_inflight_counter, S_inflight_retries, S_inflight_sent_us,
  S_queue_bytes, S_queue_len, S_queue_display, S_queue_key, S_queued, S_stats_rx_frames, S_stats_rx_data,
  S_stats_rx_duplicates, S_stats_rx_desk_retries, S_stats_rx_ignored, S_stats_tx_frames, S_stats_tx_data,
  S_stats_tx_acks, S_stats_tx_keepalives, S_stats_tx_wakes, S_stats_tx_retransmits, S_stats_ack_lost,
  S_stats_coalesced, S_stats_refused, Cfg_host_mac, Cfg_desk_mac, Cfg_desk_mac_set, Cfg_auto_wake, Cfg_sum_mode,
  Cfg_keepalive_ms, Cfg_ack_timeout_ms, Cfg_max_retries, Cfg_backoff_ms, Cfg_offline_ms, Cfg_wake_timeout_ms,
  Cfg_display_gap_us, Cfg_max_cmds, Cfg_max_body, Cmd_st, Cmd_key, Cmd_display, Cmd_bytes, Cmd_len, Q_at, g_now,
  g_raw, g_last_counter, g_rx_send, g_ncmd, g_nq, g_rx, g_rx_len, g_rx_fail, g_rx_times, g_fail_next, OW_dn_body,
  OW_dn_len, OW_dn_counter, OW_dn_retry.

Ltac wunf_set := unfold
  set_M_desk_known, set_M_desk, set_M_state, set_M_e2_acked, set_M_e1_us, set_M_foreign, set_M_last_rx,
  set_M_wake_sent, set_M_next_ka, set_M_backoff_until, set_M_last_display, set_M_display_sent,
  set_M_desk_counter_valid, set_M_desk_counter, set_M_host_counter, set_M_fail, set_M_fly_on, set_M_fly_cmd,
  set_M_fly_counter, set_M_fly_retries, set_M_fly_sent, set_M_fly_frame, set_M_fly_len, set_OW_n, set_OW_t_state,
  set_OW_t_old, set_OW_t_reason, set_OW_e2, set_OW_e3, set_OW_acks, set_OW_desk, set_OW_foreign, set_OW_acked,
  set_OW_ndata, set_OW_acked_counter, set_OW_acked_retry, set_OW_desk_off, set_OW_desk_p, set_OW_desk_body,
  set_GOT_n, set_GOT_t_state, set_GOT_t_old, set_GOT_t_reason, set_GOT_e2, set_GOT_e3, set_GOT_acks, set_GOT_desk,
  set_GOT_foreign, set_GOT_acked, set_GOT_ndata, set_S_cfg_host_mac, set_S_cfg_desk_mac, set_S_cfg_desk_mac_set,
  set_S_cfg_auto_wake, set_S_cfg_sum_mode, set_S_cfg_keepalive_ms, set_S_cfg_ack_timeout_ms, set_S_cfg_max_retries,
  set_S_cfg_backoff_ms, set_S_cfg_offline_ms, set_S_cfg_wake_timeout_ms, set_S_cfg_display_gap_us,
  set_S_cfg_max_cmds, set_S_cfg_max_body, set_S_io_ctx, set_S_io_send, set_S_io_recv, set_S_io_now_us,
  set_S_notify, set_S_notify_ctx, set_S_state, set_S_desk_known, set_S_desk_mac, set_S_personality, set_S_foreign,
  set_S_e1_named_us, set_S_wake_acked, set_S_wake_sent_us, set_S_host_counter, set_S_desk_counter,
  set_S_desk_counter_valid, set_S_last_rx_us, set_S_next_keepalive_us, set_S_backoff_until_us,
  set_S_last_display_us, set_S_display_sent, set_S_inflight, set_S_inflight_frame, set_S_inflight_len,
  set_S_inflight_counter, set_S_inflight_retries, set_S_inflight_sent_us, set_S_queue_bytes, set_S_queue_len,
  set_S_queue_display, set_S_queue_key, set_S_queued, set_S_stats_rx_frames, set_S_stats_rx_data,
  set_S_stats_rx_duplicates, set_S_stats_rx_desk_retries, set_S_stats_rx_ignored, set_S_stats_tx_frames,
  set_S_stats_tx_data, set_S_stats_tx_acks, set_S_stats_tx_keepalives, set_S_stats_tx_wakes,
  set_S_stats_tx_retransmits, set_S_stats_ack_lost, set_S_stats_coalesced, set_S_stats_refused, set_Cfg_host_mac,
  set_Cfg_desk_mac, set_Cfg_desk_mac_set, set_Cfg_auto_wake, set_Cfg_sum_mode, set_Cfg_keepalive_ms,
  set_Cfg_ack_timeout_ms, set_Cfg_max_retries, set_Cfg_backoff_ms, set_Cfg_offline_ms, set_Cfg_wake_timeout_ms,
  set_Cfg_display_gap_us, set_Cfg_max_cmds, set_Cfg_max_body, set_Cmd_st, set_Cmd_key, set_Cmd_display,
  set_Cmd_bytes, set_Cmd_len, set_Q_at, set_g_now, set_g_raw, set_g_last_counter, set_g_rx_send, set_g_ncmd,
  set_g_nq, set_g_rx, set_g_rx_len, set_g_rx_fail, set_g_rx_times, set_g_fail_next, set_OW_dn_body, set_OW_dn_len,
  set_OW_dn_counter, set_OW_dn_retry.

(* a closed arithmetic side condition by computation, else lia *)
Ltac wcl := lazymatch goal with
  | |- _ \/ _ => first [left; wcl | right; wcl]
  | |- _ /\ _ => split; wcl
  | |- _ <= _ => apply Z.leb_le; vm_compute; reflexivity
  | |- _ < _ => apply Z.ltb_lt; vm_compute; reflexivity
  end.

Ltac wlenput := repeat match goal with
  | |- context [length (put ?n ?x)] => rewrite (length_put n x)
  | |- context [length (repeat ?x ?n)] => rewrite (repeat_length x n)
  end.

(* lia on an offset goal, after dropping the hypotheses lia would case-split on or that cannot help *)
Ltac wclear := repeat match goal with
  | H : _ \/ _ |- _ => clear H
  | H : _ -> _ |- _ => clear H
  | H : forall _, _ |- _ => clear H
  end.
Ltac wnum := wlenput; wunf_off; first [wcl | (wclear; lia)].

Ltac wlen_go := lazymatch goal with
  | |- length (upd ?B ?k ?v) = WN => apply rw_len; [wlen_go | wnum | wnum]
  | |- length ?B = WN => assumption
  end.
Ltac wlen := wunf_set; wlen_go.

Ltac wsd := first [ wlen
                  | lazymatch goal with |- length _ = _ => wlenput; first [reflexivity | assumption] end
                  | wnum ].

(* b is syntactically a (a pattern without metavariables matches syntactically; a metavariable shared between
   two patterns would be compared by conversion, which unfolds reads: never use one) *)
Ltac wis a b := lazymatch b with a => idtac end.

(* one read through one write; same offset decided syntactically *)
Ltac wr1 := match goal with
  | |- context [s32_at (upd ?B ?k ?v) ?j] =>
      first [ wis k j; lazymatch v with put 4 ?x => rewrite (rw_s_p B k x) by wsd end
            | rewrite (rw_s_d B k v j) by wsd ]
  | |- context [u_at (upd ?B ?k ?v) ?j ?n] =>
      first [ wis k j; lazymatch v with put ?m ?x => wis m n; rewrite (rw_u_p B k n x) by wsd end
            | rewrite (rw_u_d B k v j n) by wsd ]
  | |- context [sub (upd ?B ?k ?v) ?j ?n] =>
      first [ wis k j; rewrite (rw_sub_p B k v n) by wsd
            | rewrite (rw_sub_d B k v j n) by wsd ]
  end.

Ltac wsyn := lazymatch goal with |- ?a = ?b => wis a b; exact eq_refl end.
Ltac wget := wunf_get; wunf_set; repeat wr1;
  first [ wsyn
        | rewrite rw_swrap_id; [wsyn | wclear; lia]
        | rewrite rw_mod_id; [wsyn | first [apply rw_u_range | wclear; cbn; lia]]
        | idtac ].

(* ---- reads through lib_start (RxBase.v) ---- *)

Definition disj_rs (j n : Z) (rs : list (Z * Z)) : bool :=
  forallb (fun '(k, m) => (j + n <=? k) || (k + m <=? j)) rs.

Lemma disj_rs_ok : forall j n rs, disj_rs j n rs = true -> forall a, j <= a < j + n -> ~ in_rs rs a.
Proof.
  intros j n rs H a Ha Hin. unfold in_rs in Hin. induction Hin as [[k m] rs' Hx | x rs' Hx IH].
  - cbn in H. apply andb_prop in H as [H _]. apply orb_prop in H as [H|H]; apply Z.leb_le in H; lia.
  - cbn in H. destruct x as [k m]. apply andb_prop in H as [_ H]. exact (IH H).
Qed.

Lemma rs_sub : forall Bm W buf j n, lib_start Bm W buf -> 0 <= j -> disj_rs j (Z.of_nat n) R_start = true ->
  sub W j n = sub Bm j n.
Proof.
  intros Bm W buf j n [Hf _] Hj Hd. eapply (wframe_sub (in_rs R_start)); [exact Hf | exact Hj |].
  intros a Ha. exact (disj_rs_ok j (Z.of_nat n) R_start Hd a Ha).
Qed.

Lemma rs_u : forall Bm W buf j n, lib_start Bm W buf -> 0 <= j -> disj_rs j (Z.of_nat n) R_start = true ->
  u_at W j n = u_at Bm j n.
Proof. intros. unfold u_at. f_equal. eapply rs_sub; eassumption. Qed.

Lemma rs_s : forall Bm W buf j, lib_start Bm W buf -> 0 <= j -> disj_rs j 4 R_start = true ->
  s32_at W j = s32_at Bm j.
Proof. intros. unfold s32_at. f_equal. eapply (rs_u _ _ _ _ 4); eassumption. Qed.

(* `G W = G Bm` for a getter G whose range misses R_start, given H : lib_start Bm W buf *)
Ltac rs_get H := wunf_get;
  lazymatch goal with
  | |- s32_at _ _ = s32_at _ _ => apply (rs_s _ _ _ _ H)
  | |- u_at _ _ _ = u_at _ _ _ => apply (rs_u _ _ _ _ _ H)
  | |- sub _ _ _ = sub _ _ _ => apply (rs_sub _ _ _ _ _ H)
  end;
  [ wnum | unfold R_start; vm_compute; reflexivity ].

(* ---- frames over a list of ranges (in_rs, RxBase.v) ---- *)

Lemma fr_sub : forall rs X Y j n, wframe (in_rs rs) X Y -> 0 <= j -> disj_rs j (Z.of_nat n) rs = true ->
  sub Y j n = sub X j n.
Proof.
  intros rs X Y j n H Hj Hd. eapply wframe_sub; [exact H | exact Hj |].
  intros a Ha. exact (disj_rs_ok j (Z.of_nat n) rs Hd a Ha).
Qed.

Lemma fr_u : forall rs X Y j n, wframe (in_rs rs) X Y -> 0 <= j -> disj_rs j (Z.of_nat n) rs = true ->
  u_at Y j n = u_at X j n.
Proof. intros. unfold u_at. f_equal. eapply fr_sub; eassumption. Qed.

Lemma fr_s : forall rs X Y j, wframe (in_rs rs) X Y -> 0 <= j -> disj_rs j 4 rs = true ->
  s32_at Y j = s32_at X j.
Proof. intros. unfold s32_at. f_equal. eapply (fr_u _ _ _ _ 4); eassumption. Qed.

(* `G Y = G X` for a getter G whose range misses rs, given H : wframe (in_rs rs) X Y *)
Ltac fget H := wunf_get;
  lazymatch goal with
  | |- s32_at _ _ = s32_at _ _ => apply (fr_s _ _ _ _ H)
  | |- u_at _ _ _ = u_at _ _ _ => apply (fr_u _ _ _ _ _ H)
  | |- sub _ _ _ = sub _ _ _ => apply (fr_sub _ _ _ _ _ H)
  end;
  [ wnum | vm_compute; reflexivity ].

(* [k, k + m) lies inside one range of rs *)
Definition rs_has (k m : Z) (rs : list (Z * Z)) : bool :=
  existsb (fun '(k', m') => (k' <=? k) && (k + m <=? k' + m')) rs.

Lemma rs_has_in : forall k m rs a, rs_has k m rs = true -> k <= a < k + m -> in_rs rs a.
Proof.
  intros k m rs a H Ha. unfold rs_has in H. apply existsb_exists in H. destruct H as [[k' m'] [Hin Hb]].
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1, H2. unfold in_rs. apply Exists_exists.
  exists (k', m'). split; [exact Hin | cbn; lia].
Qed.

Lemma wframe_upd_rs : forall rs X Y k v, wframe (in_rs rs) X Y -> length Y = WN -> 0 <= k ->
  k + Z.of_nat (length v) <= W_LEN -> rs_has k (Z.of_nat (length v)) rs = true -> wframe (in_rs rs) X (upd Y k v).
Proof.
  intros rs X Y k v H HY Hk Hv Hh. eapply wframe_trans; [exact H|].
  apply wframe_upd; [exact Hk | rewrite HY; unfold WN; lia |].
  intros a Ha. exact (rs_has_in _ _ _ a Hh Ha).
Qed.

(* every range of rs1 inside a range of rs2 *)
Definition rs_incl (rs1 rs2 : list (Z * Z)) : bool := forallb (fun '(k, m) => rs_has k m rs2) rs1.

Lemma wframe_rs_incl : forall rs1 rs2 X Y, rs_incl rs1 rs2 = true -> wframe (in_rs rs1) X Y -> wframe (in_rs rs2) X Y.
Proof.
  intros rs1 rs2 X Y Hs H. eapply wframe_weaken; [|exact H]. clear H. intros a Ha. unfold in_rs in Ha.
  induction Ha as [[k m] rs' Hx | x rs' Hx IH].
  - cbn in Hs. apply andb_prop in Hs as [Hs _]. exact (rs_has_in k m rs2 a Hs Hx).
  - cbn in Hs. destruct x as [k m]. apply andb_prop in Hs as [_ Hs]. exact (IH Hs).
Qed.

Lemma wframe_app_l : forall rs1 rs2 X Y, wframe (in_rs rs1) X Y -> wframe (in_rs (rs1 ++ rs2)) X Y.
Proof.
  intros rs1 rs2 X Y H. eapply wframe_weaken; [|exact H]. intros a Ha. unfold in_rs in *.
  apply Exists_app. left. exact Ha.
Qed.

Lemma wframe_app_r : forall rs1 rs2 X Y, wframe (in_rs rs2) X Y -> wframe (in_rs (rs1 ++ rs2)) X Y.
Proof.
  intros rs1 rs2 X Y H. eapply wframe_weaken; [|exact H]. intros a Ha. unfold in_rs in *.
  apply Exists_app. right. exact Ha.
Qed.

Lemma wframe_trans_rs : forall rs1 rs2 X Y Z, wframe (in_rs rs1) X Y -> wframe (in_rs rs2) Y Z ->
  wframe (in_rs (rs1 ++ rs2)) X Z.
Proof.
  intros rs1 rs2 X Y Z H1 H2. eapply wframe_trans; [apply wframe_app_l, H1 | apply wframe_app_r, H2].
Qed.

Lemma wframe_len : forall R X Y, wframe R X Y -> length X = WN -> length Y = WN.
Proof. intros R X Y [H _] HX. rewrite H. exact HX. Qed.

(* the lengths of the lists written, from the context *)
Ltac wlenhyp := repeat match goal with
  | |- context [length ?v] => match goal with H : length ?w = _ |- _ => wis v w; rewrite H end
  end.

(* `wframe (in_rs rs) X (setter chain over X)`, rs a closed list covering every write *)
Ltac wfrs := wunf_set;
  let rec go := lazymatch goal with
    | |- wframe _ ?X ?X => apply wframe_refl
    | |- wframe (in_rs ?rs) ?X (upd ?Y ?k ?v) =>
        apply (wframe_upd_rs rs X Y k v);
        [ go | wlen_go | wnum | wlenput; wlenhyp; wnum | wlenput; wlenhyp; vm_compute; reflexivity ]
    end in go.

Lemma sub_le_eq : forall X Y j m k, sub X j m = sub Y j m -> (k <= m)%nat -> sub X j k = sub Y j k.
Proof.
  intros X Y j m k H Hk.
  assert (E : forall Z0, sub Z0 j k = firstn k (sub Z0 j m)).
  { intros Z0.  unfold sub. rewrite firstn_firstn, Nat.min_l by exact Hk. reflexivity.  }
  rewrite (E X), (E Y), H. reflexivity.
Qed.

(* ---- the desk m_rx learns (FT:296-297) ---- *)

Definition R_learn : list (Z * Z) := [(A_M_desk_known, 4); (A_M_desk, 6)].

Lemma learn_M_frame : forall B buf, length B = WN -> length (fr_src buf) = 6%nat ->
  wframe (in_rs R_learn) B (learn_M B buf) /\ length (learn_M B buf) = WN.
Proof.
  intros B buf HB Hs. unfold learn_M. destruct (M_desk_known B =? 0).
  - split; [wfrs | wlen].
  - split; [apply wframe_refl | exact HB].
Qed.

Lemma learn_M_desk : forall B buf, length B = WN -> length (fr_src buf) = 6%nat ->
  (M_desk_known B = 0 \/ M_desk_known B = 1) -> (M_desk_known B = 1 -> fr_src buf = M_desk B) ->
  M_desk_known (learn_M B buf) = 1 /\ M_desk (learn_M B buf) = fr_src buf.
Proof.
  intros B buf HB Hs H01 Hk. unfold learn_M. destruct (Z.eqb_spec (M_desk_known B) 0) as [E|E].
  - split; wget.
  - destruct H01 as [H0|H1]; [contradiction|]. split; [exact H1 | symmetry; exact (Hk H1)].
Qed.

(* ---- tests ---- *)
Example rw_test1 : forall B, length B = WN -> M_state (set_M_fly_on (set_S_state (set_OW_n B 3) 2) 1) = M_state B.
Proof. intros B HB. wget. Qed.

Example rw_test2 : forall B, length B = WN -> S_state (set_M_fly_on (set_S_state (set_OW_n B 3) 2) 1) = 2.
Proof. intros B HB. wget. Qed.

Example rw_test3 : forall B x, length B = WN -> 0 <= x < 2 ^ 32 ->
  S_host_counter (set_S_inflight (set_S_host_counter (set_GOT_n (set_M_state (set_S_state (set_OW_n
    (set_S_last_rx_us (set_M_last_rx (set_S_desk_known (set_M_desk_known (set_S_foreign B 1) 1) 1) 5) 5) 3) 2) 2) 1) x) 0)
  = x.
Proof. intros B x HB Hx. wget. Qed.
