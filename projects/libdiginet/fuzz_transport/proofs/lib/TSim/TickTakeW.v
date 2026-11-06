(* tick_take_m (TickDefs.v; diginet_session.c:460-471, DS) once the queue is not empty, ONLINE, nothing in flight,
   back-off passed and the keepalive not due. TickTake.v proves it ends in tick_post; this file names the pieces.
   The run, now = g_now B:
     tt_allow     DS:460 the display pacing take is called with
     tt_mask      take as a mask over the queue (TakeOk.take_mask), tt_T / tt_Ts the entries / serials it takes
     tt_body, tt_n, tt_hd   the body, the count and the display flag take returns (TakeOk.take_res)
     tt_send      the counter of the frame (DS:391-392), tt_fr the frame (DS:390-397, lib_frame)
   The worlds after each stage:
     w_dispS      DS:467-470 display_sent / last_display (library), before the send
     w_send, w_fr DS:390-399 send_data up to send_raw: host_counter, the frame built into inflight_frame,
                  inflight_len, inflight_start (DS:111-117), stats.tx_data; the frame
     w_io8        FT:829, :867-868 io_send: g_fail_next := 0; M.host_counter, g_last_counter := the frame's counter
     w_dispM      FT:876-879 the harness's display_sent / last_display
     w_fly        FT:883-889 the frame in flight (harness)
     w_tx         DS:91-92 send_raw's stats.tx_frames
   R_*: the bytes each stage writes; R_tt their union, inside TickDefs.R_tick (R_tt_tick).
   tt_end: the facts of the world after the run that the simulation reads.
   The kit, the tk_ names: reading a getter through a write, the length of a written world, frames.
   TRAP (SettleOk.v): never let the unifier compare two world terms that are not convertible; every rewrite of
   tk_peel is of a subterm Ltac found syntactically; no `rewrite !`/`?`/`repeat rewrite` on world goals. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree Links QueueFacts SimLib SendOk
  SettleOk TickDefs TakeOk.
Import ListNotations.
Open Scope Z_scope.

(* ---------------------------------------------------------------- the world algebra QueueFacts carried
   (same names and statements; SimLib carries wframe*, w_s32_put, w_sub_upd_cover, not these) *)

Lemma w_nth_error_sub : forall B j n t, 0 <= j ->
  nth_error (sub B j n) t = if (t <? n)%nat then nth_error B (Z.to_nat j + t) else None.
Proof.
  intros B j n t Hj. unfold sub. rewrite nth_error_firstn.
  destruct (Nat.ltb_spec t n); [|reflexivity]. rewrite nth_error_skipn. reflexivity.
Qed.

Lemma w_nth_error_upd : forall B k v a, 0 <= k -> (Z.to_nat k + length v <= length B)%nat ->
  nth_error (upd B k v) a =
  if (Z.to_nat k <=? a)%nat && (a <? Z.to_nat k + length v)%nat then nth_error v (a - Z.to_nat k)
  else nth_error B a.
Proof.
  intros B k v a Hk Hl. unfold upd.
  assert (Hf : length (firstn (Z.to_nat k) B) = Z.to_nat k) by (rewrite length_firstn; lia).
  destruct (Nat.ltb_spec a (Z.to_nat k)) as [Ha|Ha].
  - rewrite nth_error_app1 by lia. rewrite nth_error_firstn.
    destruct (Nat.leb_spec (Z.to_nat k) a); [lia|]. cbn [andb].
    destruct (Nat.ltb_spec a (Z.to_nat k)); [reflexivity|lia].
  - rewrite nth_error_app2 by lia. rewrite Hf.
    destruct (Nat.leb_spec (Z.to_nat k) a) as [_|]; [|lia]. cbn [andb].
    destruct (Nat.ltb_spec a (Z.to_nat k + length v)) as [Hb|Hb].
    + rewrite nth_error_app1 by lia. reflexivity.
    + rewrite nth_error_app2 by lia. rewrite nth_error_skipn. f_equal. lia.
Qed.

Lemma w_length_upd : forall B k v, (Z.to_nat k + length v <= length B)%nat -> length (upd B k v) = length B.
Proof. intros B k v H. unfold upd. rewrite !length_app, length_firstn, length_skipn. lia. Qed.

Lemma w_length_sub : forall B j n, (Z.to_nat j + n <= length B)%nat -> length (sub B j n) = n.
Proof. intros B j n H. unfold sub. rewrite length_firstn, length_skipn. lia. Qed.

Lemma w_length_put : forall n v, length (put n v) = n.
Proof. intros. apply length_Z_to_le_bytes. Qed.

Lemma w_sub_upd_disj : forall B k v j n, 0 <= k -> 0 <= j -> (Z.to_nat k + length v <= length B)%nat ->
  (j + Z.of_nat n <= k \/ k + Z.of_nat (length v) <= j) ->
  sub (upd B k v) j n = sub B j n.
Proof.
  intros B k v j n Hk Hj Hl Hd. apply nth_error_ext. intros t.
  rewrite !w_nth_error_sub by exact Hj. destruct (Nat.ltb_spec t n); [|reflexivity].
  rewrite w_nth_error_upd by assumption.
  destruct (Nat.leb_spec (Z.to_nat k) (Z.to_nat j + t)); cbn [andb]; [|reflexivity].
  destruct (Nat.ltb_spec (Z.to_nat j + t) (Z.to_nat k + length v)); [lia|reflexivity].
Qed.

Lemma w_sub_upd_in : forall B k v j n, 0 <= k -> k <= j -> (Z.to_nat k + length v <= length B)%nat ->
  j + Z.of_nat n <= k + Z.of_nat (length v) ->
  sub (upd B k v) j n = sub v (j - k) n.
Proof.
  intros B k v j n Hk Hj Hl Hd. apply nth_error_ext. intros t.
  rewrite !w_nth_error_sub by lia. destruct (Nat.ltb_spec t n); [|reflexivity].
  rewrite w_nth_error_upd by assumption.
  destruct (Nat.leb_spec (Z.to_nat k) (Z.to_nat j + t)); [|lia]. cbn [andb].
  destruct (Nat.ltb_spec (Z.to_nat j + t) (Z.to_nat k + length v)); [|lia]. f_equal. lia.
Qed.

Lemma w_sub_all : forall v, sub v 0 (length v) = v.
Proof. intros v. unfold sub. cbn [Z.to_nat skipn]. apply firstn_all. Qed.

Lemma w_sub_upd_same : forall B k v, 0 <= k -> (Z.to_nat k + length v <= length B)%nat ->
  sub (upd B k v) k (length v) = v.
Proof. intros B k v Hk Hl. rewrite w_sub_upd_in by lia. rewrite Z.sub_diag. apply w_sub_all. Qed.

Lemma w_sub_sub : forall B j n j' n', 0 <= j -> 0 <= j' -> (Z.to_nat j' + n' <= n)%nat ->
  sub (sub B j n) j' n' = sub B (j + j') n'.
Proof.
  intros B j n j' n' Hj Hj' Hn. apply nth_error_ext. intros t.
  rewrite !w_nth_error_sub by lia. destruct (Nat.ltb_spec t n'); [|reflexivity].
  destruct (Nat.ltb_spec (Z.to_nat j' + t) n); [|lia]. f_equal. lia.
Qed.

Lemma w_bytes_put : forall n v, bytes_le_to_Z (put n v) = v mod 2 ^ (8 * Z.of_nat n).
Proof.
  intros n v. unfold put. rewrite <- (Z_to_le_bytes_mod n v (8 * Z.of_nat n)) by lia.
  rewrite bytes_le_to_Z_to_le_bytes by (apply Z.mod_pos_bound; lia).
  apply Z.mod_mod. lia.
Qed.

(* ---------------------------------------------------------------- the run's values *)

Definition tt_allow (B : list byte) : Z :=
  int_of_bool ((S_display_sent B =? 0) || (S_cfg_display_gap_us B <=? u64 (g_now B - S_last_display_us B))).
Definition tt_mask (B : list byte) : list bool :=
  take_mask (S_cfg_max_cmds B) (S_cfg_max_body B) (tt_allow B) 0 0 [] (sq B).
Definition tt_T (B : list byte) (m : list bool) : list (list byte) := pick m (sq B).
Definition tt_Ts (B : list byte) (m : list bool) : list Z := pick m (hq B).
Definition tt_body (B : list byte) (m : list bool) : list byte := concat (map e_bytes (tt_T B m)).
Definition tt_n (B : list byte) (m : list bool) : Z := Z.of_nat (length (tt_T B m)).
Definition tt_hd (B : list byte) (m : list bool) : Z := fold_left Z.lor (map e_disp (tt_T B m)) 0.
Definition tt_send (B : list byte) (m : list bool) : Z := u32 (S_host_counter B + tt_n B m).
Definition tt_fr (B : list byte) (m : list bool) : list byte :=
  lib_frame (M_desk B) HOST (tt_send B m) 0 0 DIGINET_CMD_DATA (u8 (tt_n B m)) (tt_body B m) (Cfg_sum_mode B).

Lemma tt_take_res : forall B, take_res (S_cfg_max_cmds B) (S_cfg_max_body B) (tt_allow B) (sq B) =
  (tt_body B (tt_mask B), Z.of_nat (length (tt_body B (tt_mask B))), tt_hd B (tt_mask B), tt_n B (tt_mask B)).
Proof. intros B. unfold take_res, tt_body, tt_T, tt_hd, tt_n, tt_mask. reflexivity. Qed.

(* ---------------------------------------------------------------- the bytes each stage writes *)

Definition R_qs (a : Z) : Prop := A_S_queue_bytes 0 <= a < A_S_queued + 4.            (* take: queue, queued *)
Definition R_ds (a : Z) : Prop := A_S_last_display_us <= a < A_S_display_sent + 4.    (* DS:467-470 *)
Definition R_ss (a : Z) : Prop :=                                                     (* send_data, send_raw *)
  (A_S_host_counter <= a < A_S_host_counter + 4) \/ (A_S_inflight <= a < A_S_inflight_sent_us + 8) \/
  (A_S_stats_tx_frames <= a < A_S_stats_tx_data + 8).
Definition R_ms (a : Z) : Prop :=                                                     (* io_send's M writes *)
  (A_M_last_display <= a < A_M_display_sent + 4) \/ (A_M_host_counter <= a < A_M_host_counter + 4) \/
  (A_M_fly_on <= a < A_M_fly_len + 8).
Definition R_cs (a : Z) : Prop :=                                                     (* g_cmd[k].st, any k *)
  OFF_g_cmd <= a < OFF_g_cmd + SZ_g_cmd /\ (a - OFF_g_cmd) mod Cmd_ESZ < 4.
Definition R_hq (a : Z) : Prop := (OFF_g_q <= a < OFF_g_q + SZ_g_q) \/ (OFF_g_nq <= a < OFF_g_nq + SZ_g_nq).
Definition R_gs (a : Z) : Prop :=                                                     (* FT:829, :868 *)
  (OFF_g_fail_next <= a < OFF_g_fail_next + 1) \/ (OFF_g_last_counter <= a < OFF_g_last_counter + SZ_g_last_counter).
(* the library's stages; everything but the harness queue model; all *)
Definition R_lib (a : Z) : Prop := R_qs a \/ R_ds a \/ R_ss a.
Definition R_nq (a : Z) : Prop := R_qs a \/ R_ds a \/ R_ss a \/ R_ms a \/ R_gs a.
Definition R_tt (a : Z) : Prop := R_nq a \/ R_cs a \/ R_hq a.
(* w_io8's writes: g_fail_next, M.host_counter, g_last_counter *)
Definition R_io8 (a : Z) : Prop := R_gs a \/ (A_M_host_counter <= a < A_M_host_counter + 4).

(* ---------------------------------------------------------------- the worlds after each stage *)

(* DS:467-470, as tick_take_m writes it *)
Definition w_dispS (B : list byte) (hd now : Z) : list byte :=
  if hd =? 0 then B else set_S_last_display_us (set_S_display_sent B 1) now.

(* the frame send_data builds (DS:390-397) from the world it starts in *)
Definition w_fr (B2 : list byte) (body : list byte) (n : Z) : list byte :=
  lib_frame (S_desk_mac B2) (S_cfg_host_mac B2) (u32 (S_host_counter B2 + n)) 0 0 DIGINET_CMD_DATA (u8 n) body
    (S_cfg_sum_mode B2).

(* send_data (DS:388-401) up to its send_raw: the world send_raw starts in *)
Definition w_send (B2 : list byte) (body : list byte) (n now : Z) : list byte :=
  let B3 := set_S_host_counter B2 (u32 (S_host_counter B2 + n)) in
  let B4 := set_S_inflight_frame B3 (w_fr B2 body n) in
  let B5 := set_S_inflight_len B4 (frame_len (length body)) in
  let B6 := set_S_inflight_sent_us (set_S_inflight_retries (set_S_inflight_counter (set_S_inflight B5 1)
              (u32 (S_host_counter B2 + n))) 0) now in
  set_S_stats_tx_data B6 (u64 (S_stats_tx_data B6 + 1)).

(* io_send (FT:829, :867-868) up to check_latest_sent / the fly, the frame's counter `send` *)
Definition w_io8 (B6 : list byte) (send : Z) : list byte :=
  set_g_last_counter (set_M_host_counter (set_g_fail_next B6 0) send) send.

(* FT:876-879 *)
Definition w_dispM (Bs : list byte) (disp : Z) : list byte :=
  if truth disp then set_M_last_display (set_M_display_sent Bs 1) (g_now Bs) else Bs.

(* FT:883-889, a frame of length <= SPEC_MAX_FRAME *)
Definition w_fly (Bx : list byte) (send : Z) (fr : list byte) : list byte :=
  set_M_fly_frame (set_M_fly_len (set_M_fly_sent (set_M_fly_retries (set_M_fly_counter (set_M_fly_cmd
    (set_M_fly_on Bx 1) SPEC_CMD_DATA) send) 0) (g_now Bx)) (Z.of_nat (length fr))) fr.

(* DS:91-93 *)
Definition w_tx (B9 : list byte) (r : Z) : list byte :=
  if r =? 0 then set_S_stats_tx_frames B9 (u64 (S_stats_tx_frames B9 + 1)) else B9.

(* ---------------------------------------------------------------- the world after the run *)

Record tt_end (B Bf : list byte) (m : list bool) : Prop := {
  te_len : length Bf = WN;
  te_frame : wframe R_tt B Bf;
  te_raw : g_raw B <> 0 -> wframe R_nq B Bf;                 (* raw: the harness queue model untouched *)
  (* the session's queue: the entries not taken, in order *)
  te_queued : S_queued Bf = Z.of_nat (length (unpick m (sq B)));
  te_sq : sq Bf = unpick m (sq B);
  (* tagged: the harness's queue likewise; the serials taken are SENT (FT:639-640) *)
  te_nq : g_raw B = 0 -> g_nq Bf = Z.of_nat (length (unpick m (hq B)));
  te_hq : g_raw B = 0 -> hq Bf = unpick m (hq B);
  te_st_in : g_raw B = 0 -> forall k, In k (tt_Ts B m) -> Cmd_st Bf k = SENT;
  te_st_out : g_raw B = 0 -> forall k, 0 <= k < Cmd_N -> ~ In k (tt_Ts B m) -> Cmd_st Bf k = Cmd_st B k;
  (* display pacing: the library (DS:467-470) and, tagged, the harness (FT:876-879) *)
  te_ds : S_display_sent Bf = if tt_hd B m =? 0 then S_display_sent B else 1;
  te_dl : S_last_display_us Bf = if tt_hd B m =? 0 then S_last_display_us B else g_now B;
  te_ms : M_display_sent Bf = if (g_raw B =? 0) && negb (tt_hd B m =? 0) then 1 else M_display_sent B;
  te_ml : M_last_display Bf = if (g_raw B =? 0) && negb (tt_hd B m =? 0) then g_now B else M_last_display B;
  (* the counter (DS:391, FT:867) and the frame in flight, both sides *)
  te_hc : S_host_counter Bf = tt_send B m;
  te_mhc : M_host_counter Bf = tt_send B m;
  te_on : S_inflight Bf = 1;
  te_mon : M_fly_on Bf = 1;
  te_ctr : S_inflight_counter Bf = tt_send B m;
  te_mctr : M_fly_counter Bf = tt_send B m;
  te_ret : S_inflight_retries Bf = 0;
  te_mret : M_fly_retries Bf = 0;
  te_sent : S_inflight_sent_us Bf = g_now B;
  te_msent : M_fly_sent Bf = g_now B;
  te_flen : S_inflight_len Bf = frame_len (length (tt_body B m));
  te_mflen : M_fly_len Bf = frame_len (length (tt_body B m));
  te_mcmd : M_fly_cmd Bf = SPEC_CMD_DATA;
  te_fr : sub Bf A_S_inflight_frame (Z.to_nat (frame_len (length (tt_body B m)))) = tt_fr B m;
  te_mfr : sub Bf A_M_fly_frame (Z.to_nat (frame_len (length (tt_body B m)))) = tt_fr B m;
  te_fail : g_fail_next Bf = 0;
}.

(* ---------------------------------------------------------------- the kit *)

(* every constant an address or a region is made of; a region before the regions it names *)
Ltac tk_unfold := unfold R_tt, R_nq, R_lib, R_io8, R_qs, R_ds, R_ss, R_ms, R_cs, R_hq, R_gs, R_tick,
  A_S_cfg_host_mac, A_S_cfg_desk_mac, A_S_cfg_desk_mac_set, A_S_cfg_auto_wake, A_S_cfg_sum_mode,
  A_S_cfg_keepalive_ms, A_S_cfg_ack_timeout_ms, A_S_cfg_max_retries, A_S_cfg_backoff_ms, A_S_cfg_offline_ms,
  A_S_cfg_wake_timeout_ms, A_S_cfg_display_gap_us, A_S_cfg_max_cmds, A_S_cfg_max_body,
  A_S_io_ctx, A_S_io_send, A_S_io_recv, A_S_io_now_us, A_S_notify, A_S_notify_ctx, A_S_state, A_S_desk_known,
  A_S_desk_mac, A_S_personality, A_S_foreign, A_S_e1_named_us, A_S_wake_acked, A_S_wake_sent_us,
  A_S_host_counter, A_S_desk_counter, A_S_desk_counter_valid, A_S_last_rx_us, A_S_next_keepalive_us,
  A_S_backoff_until_us, A_S_last_display_us, A_S_display_sent, A_S_inflight, A_S_inflight_frame,
  A_S_inflight_len, A_S_inflight_counter, A_S_inflight_retries, A_S_inflight_sent_us,
  A_S_queue_bytes, A_S_queue_len, A_S_queue_display, A_S_queue_key, A_S_queued,
  A_S_stats_rx_frames, A_S_stats_rx_data, A_S_stats_rx_duplicates, A_S_stats_rx_desk_retries,
  A_S_stats_rx_ignored, A_S_stats_tx_frames, A_S_stats_tx_data, A_S_stats_tx_acks, A_S_stats_tx_keepalives,
  A_S_stats_tx_wakes, A_S_stats_tx_retransmits, A_S_stats_ack_lost, A_S_stats_coalesced, A_S_stats_refused,
  A_M_desk_known, A_M_desk, A_M_state, A_M_e2_acked, A_M_e1_us, A_M_foreign, A_M_last_rx, A_M_wake_sent,
  A_M_next_ka, A_M_backoff_until, A_M_last_display, A_M_display_sent, A_M_desk_counter_valid,
  A_M_desk_counter, A_M_host_counter, A_M_fail, A_M_fly_on, A_M_fly_cmd, A_M_fly_counter, A_M_fly_retries,
  A_M_fly_sent, A_M_fly_frame, A_M_fly_len,
  A_Cfg_host_mac, A_Cfg_desk_mac, A_Cfg_desk_mac_set, A_Cfg_auto_wake, A_Cfg_sum_mode, A_Cfg_keepalive_ms,
  A_Cfg_ack_timeout_ms, A_Cfg_max_retries, A_Cfg_backoff_ms, A_Cfg_offline_ms, A_Cfg_wake_timeout_ms,
  A_Cfg_display_gap_us, A_Cfg_max_cmds, A_Cfg_max_body,
  A_Cmd_st, A_Cmd_key, A_Cmd_display, A_Cmd_bytes, A_Cmd_len,
  OFF_M, SZ_M, OFF_g_s, SZ_g_s, OFF_g_cmd, SZ_g_cmd, OFF_g_q, SZ_g_q, OFF_g_fail_next, SZ_g_fail_next,
  OFF_g_raw, SZ_g_raw, OFF_g_last_counter, SZ_g_last_counter, OFF_g_nq, SZ_g_nq, OFF_g_ncmd, SZ_g_ncmd,
  OFF_g_rx_send, SZ_g_rx_send, OFF_g_rx_fail, SZ_g_rx_fail, OFF_g_rx_times, SZ_g_rx_times, OFF_g_now, SZ_g_now,
  OFF_g_rx, SZ_g_rx, OFF_g_rx_len, SZ_g_rx_len, OFF_g_cfg, SZ_g_cfg, OFF_GOT, SZ_GOT, OFF_OW, SZ_OW,
  WN, W_LEN, S_queue_N, S_queue_ESZ, Cmd_N, Cmd_ESZ, CMDS_MAX, QUEUE_MAX in *.

(* an arithmetic goal over addresses: unfold, the lengths of put / repeat / firstn in the goal, lia *)
Ltac tk_offs := tk_unfold; rewrite ?w_length_put, ?repeat_length; lia.

Lemma tk_len_upd : forall B k v, length B = WN -> 0 <= k -> k + Z.of_nat (length v) <= W_LEN ->
  length (upd B k v) = WN.
Proof. intros B k v HB Hk Hv. rewrite w_length_upd; [exact HB|]. rewrite HB. unfold WN. lia. Qed.

(* length X = WN for X a chain of upd over a world of length WN in the context *)
Ltac tk_len := lazymatch goal with
  | |- length (upd _ _ _) = WN => apply tk_len_upd; [tk_len | tk_offs | tk_offs]
  | |- length _ = WN => assumption
  end.

Ltac tk_side := first [tk_len | tk_offs].

(* ---- one write, read back ---- *)

Lemma tk_sub_disj : forall B k v j n, length B = WN -> 0 <= k -> 0 <= j -> k + Z.of_nat (length v) <= W_LEN ->
  (j + Z.of_nat n <= k \/ k + Z.of_nat (length v) <= j) -> sub (upd B k v) j n = sub B j n.
Proof. intros B k v j n HB Hk Hj Hv Hd. apply w_sub_upd_disj; try assumption. rewrite HB. unfold WN. lia. Qed.

Lemma tk_u_disj : forall B k v j n, length B = WN -> 0 <= k -> 0 <= j -> k + Z.of_nat (length v) <= W_LEN ->
  (j + Z.of_nat n <= k \/ k + Z.of_nat (length v) <= j) -> u_at (upd B k v) j n = u_at B j n.
Proof. intros. unfold u_at. apply (f_equal bytes_le_to_Z). apply tk_sub_disj; assumption. Qed.

Lemma tk_s32_disj : forall B k v j, length B = WN -> 0 <= k -> 0 <= j -> k + Z.of_nat (length v) <= W_LEN ->
  (j + 4 <= k \/ k + Z.of_nat (length v) <= j) -> s32_at (upd B k v) j = s32_at B j.
Proof. intros. unfold s32_at. apply (f_equal (bv_swrap 32)). apply tk_u_disj; assumption. Qed.

Lemma tk_sub_same : forall B k v, length B = WN -> 0 <= k -> k + Z.of_nat (length v) <= W_LEN ->
  sub (upd B k v) k (length v) = v.
Proof. intros B k v HB Hk Hv. apply w_sub_upd_same; [exact Hk|]. rewrite HB. unfold WN. lia. Qed.

Lemma tk_sub_put : forall B k n v, length B = WN -> 0 <= k -> k + Z.of_nat n <= W_LEN ->
  sub (upd B k (put n v)) k n = put n v.
Proof.
  intros B k n v HB Hk Hn. pose proof (tk_sub_same B k (put n v) HB Hk) as E. rewrite w_length_put in E.
  apply E. exact Hn.
Qed.

Lemma tk_u_put : forall B k n v, length B = WN -> 0 <= k -> k + Z.of_nat n <= W_LEN ->
  u_at (upd B k (put n v)) k n = v mod 2 ^ (8 * Z.of_nat n).
Proof. intros B k n v HB Hk Hn. unfold u_at. rewrite (tk_sub_put B k n v HB Hk Hn). apply w_bytes_put. Qed.

Lemma tk_u_put_small : forall B k n v, length B = WN -> 0 <= k -> k + Z.of_nat n <= W_LEN ->
  0 <= v < 2 ^ (8 * Z.of_nat n) -> u_at (upd B k (put n v)) k n = v.
Proof. intros B k n v HB Hk Hn Hv. rewrite (tk_u_put B k n v HB Hk Hn). apply Z.mod_small. exact Hv. Qed.

Lemma tk_s32_put : forall B k v, length B = WN -> 0 <= k -> k + 4 <= W_LEN -> - 2 ^ 31 <= v < 2 ^ 31 ->
  s32_at (upd B k (put 4 v)) k = v.
Proof.
  intros B k v HB Hk Hn Hv. unfold s32_at, u_at. rewrite (tk_sub_put B k 4 v HB Hk Hn). apply w_s32_put. exact Hv.
Qed.

(* peel one write a read misses: the subterm is found by Ltac, so the rewrite's left side is in the goal *)
Ltac tk_peel := match goal with
  | |- context [u_at (upd ?B ?k ?v) ?j ?n] => rewrite (tk_u_disj B k v j n) by tk_side
  | |- context [s32_at (upd ?B ?k ?v) ?j] => rewrite (tk_s32_disj B k v j) by tk_side
  | |- context [sub (upd ?B ?k ?v) ?j ?n] => rewrite (tk_sub_disj B k v j n) by tk_side
  end.

(* ---- frames ---- *)

Lemma tk_frame_upd : forall (R : Z -> Prop) B X k v, wframe R B X -> length X = WN -> 0 <= k ->
  k + Z.of_nat (length v) <= W_LEN -> (forall a, k <= a < k + Z.of_nat (length v) -> R a) ->
  wframe R B (upd X k v).
Proof.
  intros R B X k v H HX Hk Hv HR. eapply wframe_trans; [exact H|].
  apply wframe_upd; [exact Hk | rewrite HX; unfold WN; lia | exact HR].
Qed.

(* wframe R B (a chain of upd over B), each write inside R *)
Ltac tk_fr := lazymatch goal with
  | |- wframe _ ?B ?B => apply wframe_refl
  | |- wframe _ _ (upd _ _ _) =>
      apply tk_frame_upd; [tk_fr | tk_len | tk_offs | tk_offs
      | let a := fresh "a" in let Ha := fresh "Ha" in
        intros a Ha; cbv beta; rewrite ?w_length_put, ?repeat_length in Ha; tk_offs]
  end.

Lemma tk_frame_comb : forall (R1 R2 R : Z -> Prop) B1 B2 B3, (forall a, R1 a -> R a) -> (forall a, R2 a -> R a) ->
  wframe R1 B1 B2 -> wframe R2 B2 B3 -> wframe R B1 B3.
Proof.
  intros R1 R2 R B1 B2 B3 H1 H2 F1 F2. eapply wframe_trans.
  - eapply wframe_weaken; [exact H1 | exact F1].
  - eapply wframe_weaken; [exact H2 | exact F2].
Qed.

Lemma tk_frame_len : forall (R : Z -> Prop) B B', wframe R B B' -> length B = WN -> length B' = WN.
Proof. intros R B B' [L _] HB. rewrite L. exact HB. Qed.

(* an address range outside the region of a frame *)
Ltac tk_notR := let a := fresh "a" in let Ha := fresh "Ha" in let HR := fresh "HR" in
  intros a Ha HR; cbv beta in HR; tk_offs.

(* a getter (unfolded to u_at / s32_at / sub) outside the region of the frame H keeps its value *)
Ltac tk_get H := match goal with
  | |- u_at _ _ _ = u_at _ _ _ => apply (wframe_u_at _ _ _ _ _ H); [tk_offs | tk_notR]
  | |- s32_at _ _ = s32_at _ _ => apply (wframe_s32_at _ _ _ _ H); [tk_offs | tk_notR]
  | |- sub _ _ _ = sub _ _ _ => apply (wframe_sub _ _ _ _ _ H); [tk_offs | tk_notR]
  end.

Lemma R_tt_tick : forall a, R_tt a -> R_tick a.
Proof. intros a H. tk_offs. Qed.

Lemma R_lib_nq : forall a, R_lib a -> R_nq a.
Proof. intros a H. tk_offs. Qed.

Lemma R_nq_tt : forall a, R_nq a -> R_tt a.
Proof. intros a H. unfold R_tt. left. exact H. Qed.

(* ---------------------------------------------------------------- the queue views *)

Lemma tk_sq_length : forall B, length (sq B) = Z.to_nat (S_queued B).
Proof. intros B. unfold sq. rewrite length_map. apply length_zseq. Qed.

Lemma tk_hq_length : forall B, length (hq B) = Z.to_nat (g_nq B).
Proof. intros B. unfold hq. rewrite length_map. apply length_zseq. Qed.

Lemma tk_sq_nth : forall B i d, 0 <= i < S_queued B -> nth (Z.to_nat i) (sq B) d = sq_ent B i.
Proof.
  intros B i d Hi. unfold sq.
  rewrite nth_indep with (d' := sq_ent B 0) by (rewrite length_map, length_zseq; lia).
  rewrite map_nth. rewrite (nth_zseq (Z.to_nat (S_queued B)) (Z.to_nat i) 0) by lia.
  rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma tk_hq_nth : forall B i d, 0 <= i < g_nq B -> nth (Z.to_nat i) (hq B) d = Q_at B i.
Proof.
  intros B i d Hi. unfold hq.
  rewrite nth_indep with (d' := Q_at B 0) by (rewrite length_map, length_zseq; lia).
  rewrite map_nth. rewrite (nth_zseq (Z.to_nat (g_nq B)) (Z.to_nat i) 0) by lia.
  rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma tk_In_sq : forall B e, In e (sq B) <-> exists i, 0 <= i < S_queued B /\ e = sq_ent B i.
Proof.
  intros B e. pose proof (u_at_nonneg B A_S_queued 4) as H0. fold (S_queued B) in H0.
  unfold sq. rewrite in_map_iff. split.
  - intros [i [<- Hi]]. apply in_zseq in Hi. exists i. split; [lia | reflexivity].
  - intros [i [Hi ->]]. exists i. split; [reflexivity|]. apply in_zseq. lia.
Qed.

Lemma tk_In_hq : forall B k, In k (hq B) <-> exists i, 0 <= i < g_nq B /\ k = Q_at B i.
Proof.
  intros B k. pose proof (u_at_nonneg B OFF_g_nq 4) as H0. fold (g_nq B) in H0.
  unfold hq. rewrite in_map_iff. split.
  - intros [i [<- Hi]]. apply in_zseq in Hi. exists i. split; [lia | reflexivity].
  - intros [i [Hi ->]]. exists i. split; [reflexivity|]. apply in_zseq. lia.
Qed.

(* ---------------------------------------------------------------- A2: the session's config is g_cfg *)

Lemma tk_cfg_sub : forall B o n, agree_cfg B -> 0 <= o -> o + Z.of_nat n <= 60 ->
  sub B (A_S_cfg_host_mac + o) n = sub B (OFF_g_cfg + o) n.
Proof.
  intros B o n HC Ho Hn.
  rewrite <- (w_sub_sub B A_S_cfg_host_mac 60 o n) by (unfold A_S_cfg_host_mac, OFF_g_s; lia).
  rewrite <- (w_sub_sub B OFF_g_cfg 60 o n) by (unfold OFF_g_cfg; lia).
  rewrite (a2_cfg B HC). reflexivity.
Qed.

Lemma tk_cfg_u : forall B o n, agree_cfg B -> 0 <= o -> o + Z.of_nat n <= 60 ->
  u_at B (A_S_cfg_host_mac + o) n = u_at B (OFF_g_cfg + o) n.
Proof. intros. unfold u_at. apply (f_equal bytes_le_to_Z). apply tk_cfg_sub; assumption. Qed.

Lemma tk_cfg_host_mac : forall B, agree_cfg B -> S_cfg_host_mac B = Cfg_host_mac B.
Proof. intros B HC. exact (tk_cfg_sub B 0 6 HC ltac:(lia) ltac:(lia)). Qed.
Lemma tk_cfg_sum_mode : forall B, agree_cfg B -> S_cfg_sum_mode B = Cfg_sum_mode B.
Proof. intros B HC. unfold S_cfg_sum_mode, Cfg_sum_mode, s32_at. apply (f_equal (bv_swrap 32)).
  exact (tk_cfg_u B 20 4 HC ltac:(lia) ltac:(lia)). Qed.
Lemma tk_cfg_max_cmds : forall B, agree_cfg B -> S_cfg_max_cmds B = Cfg_max_cmds B.
Proof. intros B HC. exact (tk_cfg_u B 52 4 HC ltac:(lia) ltac:(lia)). Qed.
Lemma tk_cfg_max_body : forall B, agree_cfg B -> S_cfg_max_body B = Cfg_max_body B.
Proof. intros B HC. exact (tk_cfg_u B 56 4 HC ltac:(lia) ltac:(lia)). Qed.
Lemma tk_cfg_display_gap : forall B, agree_cfg B -> S_cfg_display_gap_us B = Cfg_display_gap_us B.
Proof. intros B HC. exact (tk_cfg_u B 48 4 HC ltac:(lia) ltac:(lia)). Qed.
Lemma tk_cfg_ack_timeout : forall B, agree_cfg B -> S_cfg_ack_timeout_ms B = Cfg_ack_timeout_ms B.
Proof. intros B HC. exact (tk_cfg_u B 28 4 HC ltac:(lia) ltac:(lia)). Qed.
Lemma tk_cfg_keepalive : forall B, agree_cfg B -> S_cfg_keepalive_ms B = Cfg_keepalive_ms B.
Proof. intros B HC. exact (tk_cfg_u B 24 4 HC ltac:(lia) ltac:(lia)). Qed.

(* ---------------------------------------------------------------- w_dispS (the kit at work) *)

Lemma tk_dispS_len : forall B hd now, length B = WN -> length (w_dispS B hd now) = WN.
Proof.
  intros B hd now HB. unfold w_dispS. destruct (hd =? 0); [exact HB|].
  unfold set_S_last_display_us, set_S_display_sent. tk_len.
Qed.

Lemma tk_dispS_frame : forall B hd now, length B = WN -> wframe R_ds B (w_dispS B hd now).
Proof.
  intros B hd now HB. unfold w_dispS. destruct (hd =? 0); [apply wframe_refl|].
  unfold set_S_last_display_us, set_S_display_sent. tk_fr.
Qed.

Lemma tk_dispS_ds : forall B hd now, length B = WN ->
  S_display_sent (w_dispS B hd now) = if hd =? 0 then S_display_sent B else 1.
Proof.
  intros B hd now HB. unfold w_dispS. destruct (hd =? 0); [reflexivity|].
  unfold S_display_sent, set_S_last_display_us, set_S_display_sent. tk_peel.
  apply tk_s32_put; [tk_len | tk_offs | tk_offs | lia].
Qed.

Lemma tk_dispS_dl : forall B hd now, length B = WN -> 0 <= now < 2 ^ 64 ->
  S_last_display_us (w_dispS B hd now) = if hd =? 0 then S_last_display_us B else now.
Proof.
  intros B hd now HB Hn. unfold w_dispS. destruct (hd =? 0); [reflexivity|].
  unfold S_last_display_us, set_S_last_display_us, set_S_display_sent.
  apply tk_u_put_small; [tk_len | tk_offs | tk_offs | exact Hn].
Qed.

Lemma tk_io8_frame : forall B6 send, length B6 = WN -> wframe R_io8 B6 (w_io8 B6 send).
Proof.
  intros B6 send HB6. unfold w_io8, set_g_last_counter, set_M_host_counter, set_g_fail_next. tk_fr.
Qed.
