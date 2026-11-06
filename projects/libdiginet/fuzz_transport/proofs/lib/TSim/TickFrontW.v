(* On SimLib (wsimp, wlen, wsame, wsame_tac, wrw) and its discipline: no rewrite on a goal holding reads (wrw is
   `pattern` + eq_ind_r), no Ltac metavariable shared between two patterns (Ltac compares those by conversion;
   terms are compared syntactically by SimLib's wis), the read primitives opaque below.
   - world-free list lemmas for the retransmission's retry bytes (DS:405-408): put_be16, sub_upd_mid, upd_upd_next,
     sub_two, lib_frame_retry_set, sub_firstn_le, sub_skip28;
   - tf_same / tf_sames: G B' = G B for every getter outside a frame wsame B B' rs; tf_rw W: rewrite the reads of
     W that equations G W = _ of the context name;
   - the parts of agree_core no step of the tick's front writes (cfg, io, queues, personality): x_cfg, x_io, x_q,
     agree_core_x. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import
  TWorld TWorldLemmas TImg TNeed TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree Links SendOk SimLib.
Import ListNotations.
Open Scope Z_scope.

(* ---- world-free list facts ---- *)

(* DS:407-408 write the retry big-endian: the two bytes are put16 of it *)
Lemma put_be16 : forall t, put 1 (u8 (Z.shiftr t 8)) ++ put 1 (u8 t) = put16 t.
Proof.
  intros t. unfold put, put16, u8, b8. cbn [Z_to_le_bytes app].
  rewrite (Z_to_bv8_mod (Z.shiftr t 8 mod 256) (t / 2 ^ 8)).
  2: { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. apply Z.mod_mod. lia. }
  rewrite (Z_to_bv8_mod (t mod 256) t). 2: { change (2 ^ 8) with 256. apply Z.mod_mod. lia. }
  reflexivity.
Qed.

(* a frame with its retry field (bytes 26-27) replaced *)
Lemma lib_frame_retry_set : forall dst src send ack r1 r2 cmd ncmds body mode,
  length dst = 6%nat -> length src = 6%nat -> 0 <= r2 < 2 ^ 16 ->
  firstn 26 (lib_frame dst src send ack r1 cmd ncmds body mode) ++ put16 r2 ++
  skipn 28 (lib_frame dst src send ack r1 cmd ncmds body mode) = lib_frame dst src send ack r2 cmd ncmds body mode.
Proof.
  intros dst src send ack r1 r2 cmd ncmds body mode Hd Hs Hr.
  rewrite (lib_frame_retry_head dst src send ack r1 cmd ncmds body mode Hd Hs).
  rewrite (lib_frame_retry_tail dst src send ack r1 cmd ncmds body mode Hd Hs).
  rewrite (lib_frame_split dst src send ack r2 cmd ncmds body mode).
  rewrite (Z.mod_small r2 (2 ^ 16) Hr). reflexivity.
Qed.

(* a write inside a read *)
Lemma sub_upd_mid : forall B k d v n, 0 <= k -> 0 <= d -> (Z.to_nat d + length v <= n)%nat ->
  (Z.to_nat k + n <= length B)%nat ->
  sub (upd B (k + d) v) k n = firstn (Z.to_nat d) (sub B k n) ++ v ++ skipn (Z.to_nat d + length v) (sub B k n).
Proof.
  intros B k d v n Hk Hd Hn Hb.
  assert (HS : length (sub B k n) = n) by (unfold sub; rewrite length_firstn, length_skipn; lia).
  assert (Hl1 : length (firstn (Z.to_nat d) (sub B k n)) = Z.to_nat d) by (rewrite length_firstn; lia).
  apply nth_error_ext. intros t.
  rewrite (ne_sub (upd B (k + d) v) k n t Hk).
  rewrite (ne_upd B v (k + d) (Z.to_nat k + t)) by lia.
  replace (Z.to_nat (k + d)) with (Z.to_nat k + Z.to_nat d)%nat by lia.
  destruct (Nat.ltb_spec t (Z.to_nat d)) as [H1|H1].
  - rewrite nth_error_app1 by lia. rewrite ne_firstn.
    destruct (Nat.ltb_spec t (Z.to_nat d)) as [_|H2]; [|lia].
    rewrite (ne_sub B k n t Hk).
    destruct (Nat.ltb_spec t n) as [H3|H3]; [|lia].
    destruct (Nat.leb_spec (Z.to_nat k + Z.to_nat d) (Z.to_nat k + t)) as [H4|H4]; [lia|]. reflexivity.
  - rewrite nth_error_app2 by lia. rewrite Hl1.
    destruct (Nat.ltb_spec (t - Z.to_nat d) (length v)) as [H2|H2].
    + rewrite nth_error_app1 by lia.
      destruct (Nat.ltb_spec t n) as [H3|H3]; [|lia].
      destruct (Nat.leb_spec (Z.to_nat k + Z.to_nat d) (Z.to_nat k + t)) as [H4|H4]; [|lia].
      destruct (Nat.ltb_spec (Z.to_nat k + t) (Z.to_nat k + Z.to_nat d + length v)) as [H5|H5]; [|lia].
      cbn [andb]. f_equal. lia.
    + rewrite nth_error_app2 by lia. rewrite nth_skipn.
      rewrite (ne_sub B k n _ Hk).
      replace (Z.to_nat d + length v + (t - Z.to_nat d - length v))%nat with t by lia.
      destruct (Nat.ltb_spec t n) as [H3|H3]; [|reflexivity].
      destruct (Nat.leb_spec (Z.to_nat k + Z.to_nat d) (Z.to_nat k + t)) as [H4|H4]; cbn [andb]; [|reflexivity].
      destruct (Nat.ltb_spec (Z.to_nat k + t) (Z.to_nat k + Z.to_nat d + length v)) as [H5|H5]; [lia|reflexivity].
Qed.

(* two writes side by side are one write *)
Lemma upd_upd_next : forall X j a b, 0 <= j -> length a = 1%nat -> (Z.to_nat j + 1 + length b <= length X)%nat ->
  upd (upd X j a) (j + 1) b = upd X j (a ++ b).
Proof.
  intros X j a b Hj Ha Hl.
  assert (L1 : length (upd X j a) = length X) by (apply length_upd; [lia | rewrite Ha; lia]).
  apply nth_error_ext. intros t.
  rewrite (ne_upd (upd X j a) b (j + 1) t) by (try lia; rewrite L1; lia).
  rewrite (ne_upd X (a ++ b) j t) by (try lia; rewrite length_app, Ha; lia).
  rewrite (ne_upd X a j t) by (try lia; rewrite Ha; lia).
  replace (Z.to_nat (j + 1)) with (Z.to_nat j + 1)%nat by lia.
  rewrite length_app, Ha.
  destruct (Nat.leb_spec (Z.to_nat j + 1) t) as [H1|H1].
  - destruct (Nat.ltb_spec t (Z.to_nat j + 1 + length b)) as [H2|H2]; cbn [andb].
    + destruct (Nat.leb_spec (Z.to_nat j) t) as [H3|H3]; [|lia].
      destruct (Nat.ltb_spec t (Z.to_nat j + (1 + length b))) as [H4|H4]; [|lia]. cbn [andb].
      rewrite nth_error_app2 by lia. rewrite Ha. f_equal. lia.
    + destruct (Nat.leb_spec (Z.to_nat j) t) as [H3|H3]; cbn [andb]; [|lia].
      destruct (Nat.ltb_spec t (Z.to_nat j + (1 + length b))) as [H4|H4]; [lia|].
      destruct (Nat.ltb_spec t (Z.to_nat j + 1)) as [H5|H5]; [lia|]. cbn [andb]. reflexivity.
  - cbn [andb].
    destruct (Nat.leb_spec (Z.to_nat j) t) as [H3|H3]; cbn [andb].
    + destruct (Nat.ltb_spec t (Z.to_nat j + (1 + length b))) as [H4|H4]; [|lia].
      destruct (Nat.ltb_spec t (Z.to_nat j + 1)) as [H5|H5]; [|lia].
      rewrite nth_error_app1 by lia. reflexivity.
    + reflexivity.
Qed.

(* the read of a frame whose bytes 26 and 27 were written one by one *)
Lemma sub_two : forall X k j1 j2 x y n, 0 <= k -> j1 = k + 26 -> j2 = k + 27 -> (28 <= n)%nat ->
  (Z.to_nat k + n <= length X)%nat ->
  sub (upd (upd X j1 (put 1 x)) j2 (put 1 y)) k n =
  firstn 26 (sub X k n) ++ (put 1 x ++ put 1 y) ++ skipn 28 (sub X k n).
Proof.
  intros X k j1 j2 x y n Hk -> -> Hn Hb.
  replace (k + 27) with (k + 26 + 1) by lia.
  rewrite (upd_upd_next X (k + 26) (put 1 x) (put 1 y)) by (try lia; rewrite ?length_put; lia).
  rewrite (sub_upd_mid X k 26 (put 1 x ++ put 1 y) n) by (try lia; rewrite ?length_app, ?length_put; lia).
  rewrite length_app, !length_put. reflexivity.
Qed.

Lemma sub_firstn_le : forall B k m n, (m <= n)%nat -> firstn m (sub B k n) = sub B k m.
Proof. intros B k m n H. unfold sub. rewrite firstn_firstn. f_equal. lia. Qed.

Lemma sub_skip28 : forall B k L, 0 <= k -> 28 <= L ->
  sub B (k + 26 + 2) (Z.to_nat (L - 26 - 2)) = skipn 28 (sub B k (Z.to_nat L)).
Proof.
  intros B k L Hk HL. unfold sub.
  rewrite skipn_firstn_comm, skipn_skipn.
  replace (Z.to_nat (k + 26 + 2)) with (28 + Z.to_nat k)%nat by lia.
  replace (Z.to_nat (L - 26 - 2)) with (Z.to_nat L - 28)%nat by lia.
  reflexivity.
Qed.

Lemma u32_small : forall x, 0 <= x < 2 ^ 32 -> u32 x = x.
Proof. intros x Hx. unfold u32. apply Z.mod_small. exact Hx. Qed.
Lemma u16_small : forall x, 0 <= x < 2 ^ 16 -> u16 x = x.
Proof. intros x Hx. unfold u16. apply Z.mod_small. lia. Qed.

(* ---- from here on the reads are opaque ---- *)
Local Opaque sub upd u_at s32_at put.

(* ---- closed tests ---- *)
Lemma ltb_0_TM : (0 <? TRANS_MAX) = true.
Proof. reflexivity. Qed.
Lemma ltb_0_0 : (0 <? 0) = false.
Proof. reflexivity. Qed.
Lemma int_inc_0 : int_inc 0 = Some 1.
Proof. reflexivity. Qed.
Lemma truth_1 : truth 1 = true.
Proof. reflexivity. Qed.
Lemma eqb_1_0 : (1 =? 0) = false.
Proof. reflexivity. Qed.

Ltac tf_unconst := cbv beta delta [
    S_IDLE S_WAKING S_ONLINE S_CLOSED R_NONE R_WAKE R_ONLINE R_DESK_OFFLINE R_SILENCE R_FOREIGN
    R_WAKE_TIMEOUT R_DESK_DISCONNECT R_CLOSED N_DESK N_STATE N_DATA N_ACKED N_ACK_LOST N_FOREIGN
    DIGINET_S_IDLE DIGINET_S_WAKING DIGINET_S_ONLINE DIGINET_S_CLOSED DIGINET_R_NONE DIGINET_R_WAKE
    DIGINET_R_ONLINE DIGINET_R_DESK_OFFLINE DIGINET_R_SILENCE DIGINET_R_FOREIGN DIGINET_R_WAKE_TIMEOUT
    DIGINET_R_DESK_DISCONNECT DIGINET_R_CLOSED DIGINET_N_DESK DIGINET_N_STATE DIGINET_N_DATA DIGINET_N_ACKED
    DIGINET_N_ACK_LOST DIGINET_N_FOREIGN DIGINET_OK EIO TRANS_MAX INT_MAX INT_MIN SPEC_CMD_DATA SPEC_CMD_ACK
    SPEC_CMD_E0 SPEC_CMD_E1 SPEC_CMD_E2 SPEC_CMD_E3 DIGINET_CMD_DATA DIGINET_CMD_ACK QUEUE_MAX CMDS_MAX
    OPS_MAX RETRY_AT DIGINET_ETH_HDR_LEN DIGINET_MAX_FRAME_LEN SPEC_MAX_FRAME SPEC_MIN_FRAME
    DIGINET_MIN_FRAME_LEN PENDING SENT REPLACED].

(* two facts on one read that name different constants *)
Ltac tf_cl H1 H2 := exfalso; clear - H1 H2; revert H1 H2; tf_unconst; intros ? ?; lia.

(* x =? y of two closed numbers, by its value *)
Ltac tf_ceq x y := let v := eval vm_compute in (x =? y) in wrw (eq_refl v : (x =? y) = v).

(* G B' = G B for a getter G outside the frame HW : wsame B B' rs *)
Ltac tf_same HW :=
  lazymatch goal with
  | |- ?T = ?Tx =>
      let t := wbody T in
      let tx := wbody Tx in
      change (t = tx);
      lazymatch t with
      | s32_at _ ?j => refine (wsame_s32_at _ _ _ j HW _ _); [wle | wclosed; vm_compute; reflexivity]
      | u_at _ ?j ?n => refine (wsame_u_at _ _ _ j n HW _ _); [wle | wclosed; vm_compute; reflexivity]
      | sub _ ?j ?n => refine (wsame_sub _ _ _ j n HW _ _); [wle | wclosed; vm_compute; reflexivity]
      end
  end.

Ltac tf_same1 HW B B' G := first [ assert (G B' = G B) by (tf_same HW) | idtac ].

(* every unindexed getter agree_core and the front read, where unchanged *)
Ltac tf_sames HW B B' :=
  tf_same1 HW B B' M_desk_known;
  tf_same1 HW B B' M_desk;
  tf_same1 HW B B' M_state;
  tf_same1 HW B B' M_e2_acked;
  tf_same1 HW B B' M_e1_us;
  tf_same1 HW B B' M_foreign;
  tf_same1 HW B B' M_last_rx;
  tf_same1 HW B B' M_wake_sent;
  tf_same1 HW B B' M_next_ka;
  tf_same1 HW B B' M_backoff_until;
  tf_same1 HW B B' M_last_display;
  tf_same1 HW B B' M_display_sent;
  tf_same1 HW B B' M_desk_counter_valid;
  tf_same1 HW B B' M_desk_counter;
  tf_same1 HW B B' M_host_counter;
  tf_same1 HW B B' M_fail;
  tf_same1 HW B B' M_fly_on;
  tf_same1 HW B B' M_fly_cmd;
  tf_same1 HW B B' M_fly_counter;
  tf_same1 HW B B' M_fly_retries;
  tf_same1 HW B B' M_fly_sent;
  tf_same1 HW B B' M_fly_len;
  tf_same1 HW B B' OW_n;
  tf_same1 HW B B' GOT_n;
  tf_same1 HW B B' S_cfg_sum_mode;
  tf_same1 HW B B' S_cfg_ack_timeout_ms;
  tf_same1 HW B B' S_cfg_max_retries;
  tf_same1 HW B B' S_cfg_offline_ms;
  tf_same1 HW B B' S_cfg_wake_timeout_ms;
  tf_same1 HW B B' S_cfg_keepalive_ms;
  tf_same1 HW B B' S_cfg_display_gap_us;
  tf_same1 HW B B' S_io_ctx;
  tf_same1 HW B B' S_io_send;
  tf_same1 HW B B' S_io_recv;
  tf_same1 HW B B' S_io_now_us;
  tf_same1 HW B B' S_notify;
  tf_same1 HW B B' S_notify_ctx;
  tf_same1 HW B B' S_state;
  tf_same1 HW B B' S_desk_known;
  tf_same1 HW B B' S_desk_mac;
  tf_same1 HW B B' S_personality;
  tf_same1 HW B B' S_foreign;
  tf_same1 HW B B' S_e1_named_us;
  tf_same1 HW B B' S_wake_acked;
  tf_same1 HW B B' S_wake_sent_us;
  tf_same1 HW B B' S_host_counter;
  tf_same1 HW B B' S_desk_counter;
  tf_same1 HW B B' S_desk_counter_valid;
  tf_same1 HW B B' S_last_rx_us;
  tf_same1 HW B B' S_next_keepalive_us;
  tf_same1 HW B B' S_backoff_until_us;
  tf_same1 HW B B' S_last_display_us;
  tf_same1 HW B B' S_display_sent;
  tf_same1 HW B B' S_inflight;
  tf_same1 HW B B' S_inflight_len;
  tf_same1 HW B B' S_inflight_counter;
  tf_same1 HW B B' S_inflight_retries;
  tf_same1 HW B B' S_inflight_sent_us;
  tf_same1 HW B B' S_queued;
  tf_same1 HW B B' Cfg_host_mac;
  tf_same1 HW B B' Cfg_desk_mac;
  tf_same1 HW B B' Cfg_desk_mac_set;
  tf_same1 HW B B' Cfg_auto_wake;
  tf_same1 HW B B' Cfg_sum_mode;
  tf_same1 HW B B' Cfg_keepalive_ms;
  tf_same1 HW B B' Cfg_ack_timeout_ms;
  tf_same1 HW B B' Cfg_max_retries;
  tf_same1 HW B B' Cfg_backoff_ms;
  tf_same1 HW B B' Cfg_offline_ms;
  tf_same1 HW B B' Cfg_wake_timeout_ms;
  tf_same1 HW B B' Cfg_display_gap_us;
  tf_same1 HW B B' Cfg_max_cmds;
  tf_same1 HW B B' Cfg_max_body;
  tf_same1 HW B B' g_now;
  tf_same1 HW B B' g_raw;
  tf_same1 HW B B' g_nq;
  tf_same1 HW B B' g_ncmd;
  tf_same1 HW B B' g_fail_next;
  tf_same1 HW B B' g_rx_send;
  tf_same1 HW B B' g_last_counter;
  tf_same1 HW B B' g_rx.

(* rewrite each read G W of the goal that an equation G W = _ of the context names *)
Ltac tf_rw W := repeat match goal with
  | |- context [?G W] => match goal with H : ?G' W = _ |- _ => wis G' G; wrw H end
  | |- context [?G W ?i] => match goal with H : ?G' W ?i' = _ |- _ => wis G' G; wis i' i; wrw H end
  | |- context [sub W ?j ?n] => match goal with H : sub W ?j' ?n' = _ |- _ => wis j' j; wis n' n; wrw H end
  end.

(* ---- the parts of agree_core no step of the tick's front writes ---- *)
(* every range a step of the front writes: M, g_s from state to the personality and from foreign to the queue,
   the stats, g_fail_next's byte, g_now, GOT and OW *)
Definition rs_x : list (Z * Z) :=
  [(OFF_M, SZ_M); (A_S_state, A_S_personality - A_S_state); (A_S_foreign, A_S_queue_bytes 0 - A_S_foreign);
   (A_S_stats_rx_frames, OFF_g_s + SZ_g_s - A_S_stats_rx_frames); (OFF_g_fail_next, 1); (OFF_g_now, 8);
   (OFF_GOT, OFF_OW + SZ_OW - OFF_GOT)].

Lemma x_cfg : forall B B', wsame B B' rs_x -> agree_cfg B -> agree_cfg B'.
Proof.
  intros B B' HW HA.
  assert (E1 : Cfg_max_retries B' = Cfg_max_retries B) by tf_same HW.
  assert (E2 : Cfg_ack_timeout_ms B' = Cfg_ack_timeout_ms B) by tf_same HW.
  assert (E3 : Cfg_keepalive_ms B' = Cfg_keepalive_ms B) by tf_same HW.
  assert (E4 : Cfg_backoff_ms B' = Cfg_backoff_ms B) by tf_same HW.
  assert (E5 : Cfg_offline_ms B' = Cfg_offline_ms B) by tf_same HW.
  assert (E6 : Cfg_wake_timeout_ms B' = Cfg_wake_timeout_ms B) by tf_same HW.
  assert (E7 : Cfg_display_gap_us B' = Cfg_display_gap_us B) by tf_same HW.
  assert (E8 : Cfg_max_cmds B' = Cfg_max_cmds B) by tf_same HW.
  assert (E9 : Cfg_max_body B' = Cfg_max_body B) by tf_same HW.
  assert (E10 : Cfg_host_mac B' = Cfg_host_mac B) by tf_same HW.
  assert (E11 : Cfg_desk_mac B' = Cfg_desk_mac B) by tf_same HW.
  assert (E12 : Cfg_desk_mac_set B' = Cfg_desk_mac_set B) by tf_same HW.
  assert (E13 : Cfg_auto_wake B' = Cfg_auto_wake B) by tf_same HW.
  assert (E14 : Cfg_sum_mode B' = Cfg_sum_mode B) by tf_same HW.
  assert (E15 : sub B' A_S_cfg_host_mac 60 = sub B A_S_cfg_host_mac 60) by tf_same HW.
  assert (E16 : sub B' OFF_g_cfg 60 = sub B OFF_g_cfg 60) by tf_same HW.
  assert (E17 : g_raw B' = g_raw B) by tf_same HW.
  constructor; tf_rw B'.
  - exact (a1_max_retries _ HA).
  - exact (a1_ack_timeout _ HA).
  - exact (a1_keepalive _ HA).
  - exact (a1_backoff _ HA).
  - exact (a1_offline _ HA).
  - exact (a1_wake_timeout _ HA).
  - exact (a1_display_gap _ HA).
  - exact (a1_max_cmds _ HA).
  - exact (a1_max_body _ HA).
  - exact (a1_host_mac _ HA).
  - exact (a1_desk_mac _ HA).
  - exact (a1_desk_mac_set _ HA).
  - exact (a1_auto_wake _ HA).
  - exact (a1_sum_mode _ HA).
  - exact (a2_cfg _ HA).
  - exact (a4_raw _ HA).
Qed.

Lemma x_io : forall I B B', wsame B B' rs_x -> agree_io I B -> agree_io I B'.
Proof.
  intros I B B' HW HA.
  assert (E1 : S_io_ctx B' = S_io_ctx B) by tf_same HW.
  assert (E2 : S_io_send B' = S_io_send B) by tf_same HW.
  assert (E3 : S_io_recv B' = S_io_recv B) by tf_same HW.
  assert (E4 : S_io_now_us B' = S_io_now_us B) by tf_same HW.
  assert (E5 : S_notify B' = S_notify B) by tf_same HW.
  assert (E6 : S_notify_ctx B' = S_notify_ctx B) by tf_same HW.
  constructor; tf_rw B'.
  - exact (a3_io_ctx _ _ HA).
  - exact (a3_io_send _ _ HA).
  - exact (a3_io_recv _ _ HA).
  - exact (a3_io_now _ _ HA).
  - exact (a3_notify _ _ HA).
  - exact (a3_notify_ctx _ _ HA).
Qed.

(* an indexed read outside rs_x *)
Ltac x_out :=
  let a := fresh "a" in let Ha := fresh "Ha" in let Hin := fresh "Hin" in
  intros a Ha Hin; unfold rs_x in Hin; wranges_in Hin; revert Ha Hin; wunfold_addr; intros Ha Hin; lia.

Lemma x_Q_at : forall B B' i, wsame B B' rs_x -> 0 <= i < 1024 -> Q_at B' i = Q_at B i.
Proof. intros B B' i HW Hi. unfold Q_at. apply (wframe_u_at _ _ _ _ _ HW); [unfold OFF_g_q; lia | x_out]. Qed.
Lemma x_Cmd_st : forall B B' k, wsame B B' rs_x -> 0 <= k < 1024 -> Cmd_st B' k = Cmd_st B k.
Proof. intros B B' k HW Hk. unfold Cmd_st. apply (wframe_s32_at _ _ _ _ HW); [unfold A_Cmd_st, OFF_g_cmd; lia | x_out]. Qed.
Lemma x_Cmd_key : forall B B' k, wsame B B' rs_x -> 0 <= k < 1024 -> Cmd_key B' k = Cmd_key B k.
Proof. intros B B' k HW Hk. unfold Cmd_key. apply (wframe_u_at _ _ _ _ _ HW); [unfold A_Cmd_key, OFF_g_cmd; lia | x_out]. Qed.
Lemma x_Cmd_display : forall B B' k, wsame B B' rs_x -> 0 <= k < 1024 -> Cmd_display B' k = Cmd_display B k.
Proof. intros B B' k HW Hk. unfold Cmd_display. apply (wframe_s32_at _ _ _ _ HW); [unfold A_Cmd_display, OFF_g_cmd; lia | x_out]. Qed.
Lemma x_Cmd_bytes : forall B B' k, wsame B B' rs_x -> 0 <= k < 1024 -> Cmd_bytes B' k = Cmd_bytes B k.
Proof. intros B B' k HW Hk. unfold Cmd_bytes. apply (wframe_sub _ _ _ _ _ HW); [unfold A_Cmd_bytes, OFF_g_cmd; lia | x_out]. Qed.
Lemma x_Cmd_len : forall B B' k, wsame B B' rs_x -> 0 <= k < 1024 -> Cmd_len B' k = Cmd_len B k.
Proof. intros B B' k HW Hk. unfold Cmd_len. apply (wframe_u_at _ _ _ _ _ HW); [unfold A_Cmd_len, OFF_g_cmd; lia | x_out]. Qed.
Lemma x_S_queue_bytes : forall B B' i, wsame B B' rs_x -> 0 <= i < 512 -> S_queue_bytes B' i = S_queue_bytes B i.
Proof. intros B B' i HW Hi. unfold S_queue_bytes. apply (wframe_sub _ _ _ _ _ HW); [unfold A_S_queue_bytes, OFF_g_s; lia | x_out]. Qed.
Lemma x_S_queue_len : forall B B' i, wsame B B' rs_x -> 0 <= i < 512 -> S_queue_len B' i = S_queue_len B i.
Proof. intros B B' i HW Hi. unfold S_queue_len. apply (wframe_u_at _ _ _ _ _ HW); [unfold A_S_queue_len, OFF_g_s; lia | x_out]. Qed.
Lemma x_S_queue_key : forall B B' i, wsame B B' rs_x -> 0 <= i < 512 -> S_queue_key B' i = S_queue_key B i.
Proof. intros B B' i HW Hi. unfold S_queue_key. apply (wframe_u_at _ _ _ _ _ HW); [unfold A_S_queue_key, OFF_g_s; lia | x_out]. Qed.
Lemma x_S_queue_display : forall B B' i, wsame B B' rs_x -> 0 <= i < 512 -> S_queue_display B' i = S_queue_display B i.
Proof. intros B B' i HW Hi. unfold S_queue_display. apply (wframe_u_at _ _ _ _ _ HW); [unfold A_S_queue_display, OFF_g_s; lia | x_out]. Qed.

Lemma x_q : forall ops B B', wsame B B' rs_x -> agree_q ops B -> agree_q ops B'.
Proof.
  intros ops B B' HW HQ.
  assert (Eq : S_queued B' = S_queued B) by tf_same HW.
  assert (En : g_nq B' = g_nq B) by tf_same HW.
  assert (Ec : g_ncmd B' = g_ncmd B) by tf_same HW.
  assert (Er : g_raw B' = g_raw B) by tf_same HW.
  pose proof (d3_ncmd _ _ HQ) as Hnc. pose proof (d3_ops _ _ HQ) as Hops. unfold OPS_MAX in Hops.
  constructor; tf_rw B'.
  - exact (d1_queued _ _ HQ).
  - exact (d1_nq _ _ HQ).
  - intros Hr i Hi. pose proof (d1_nq _ _ HQ Hr) as Hnq. unfold QUEUE_MAX in Hnq.
    destruct (d1_entry _ _ HQ Hr i Hi) as (Hk & _).
    assert (Hi' : 0 <= i < 1024) by lia. assert (Hi2 : 0 <= i < 512) by lia.
    wrw (x_Q_at B B' i HW Hi').
    assert (Hk' : 0 <= Q_at B i < 1024) by lia.
    wrw (x_Cmd_st B B' (Q_at B i) HW Hk'). wrw (x_S_queue_bytes B B' i HW Hi2).
    wrw (x_Cmd_bytes B B' (Q_at B i) HW Hk'). wrw (x_S_queue_len B B' i HW Hi2).
    wrw (x_Cmd_len B B' (Q_at B i) HW Hk'). wrw (x_S_queue_key B B' i HW Hi2).
    wrw (x_Cmd_key B B' (Q_at B i) HW Hk'). wrw (x_S_queue_display B B' i HW Hi2).
    wrw (x_Cmd_display B B' (Q_at B i) HW Hk').
    exact (d1_entry _ _ HQ Hr i Hi).
  - intros Hr i j Hi Hj Hij. pose proof (d1_nq _ _ HQ Hr) as Hnq. unfold QUEUE_MAX in Hnq.
    assert (Hi' : 0 <= i < 1024) by lia. assert (Hj' : 0 <= j < 1024) by lia.
    exact (d1_nodup _ _ HQ Hr i j Hi Hj
             (eq_trans (eq_sym (x_Q_at B B' i HW Hi')) (eq_trans Hij (x_Q_at B B' j HW Hj')))).
  - intros Hr k Hk. pose proof (d1_nq _ _ HQ Hr) as Hnq. unfold QUEUE_MAX in Hnq.
    assert (Hk' : 0 <= k < 1024) by lia.
    wrw (x_Cmd_st B B' k HW Hk'). split.
    + intros Hp. destruct (proj1 (d1_pending _ _ HQ Hr k Hk) Hp) as (i & Hi & Hqi).
      assert (Hi' : 0 <= i < 1024) by lia.
      exists i. split; [exact Hi|]. exact (eq_trans (x_Q_at B B' i HW Hi') Hqi).
    + intros (i & Hi & Hqi). assert (Hi' : 0 <= i < 1024) by lia.
      apply (proj2 (d1_pending _ _ HQ Hr k Hk)). exists i. split; [exact Hi|].
      exact (eq_trans (eq_sym (x_Q_at B B' i HW Hi')) Hqi).
  - intros k Hk Hs. assert (Hk' : 0 <= k < 1024) by lia.
    assert (Hs' : Cmd_st B k <> 0) by (intros X; apply Hs; exact (eq_trans (x_Cmd_st B B' k HW Hk') X)).
    wrw (x_Cmd_bytes B B' k HW Hk'). wrw (x_Cmd_len B B' k HW Hk'). wrw (x_Cmd_display B B' k HW Hk').
    exact (d2_cmd _ _ HQ k Hk Hs').
  - exact (d3_ncmd _ _ HQ).
  - exact (d3_ops _ _ HQ).
  - exact (d4_queued _ _ HQ).
  - intros Hr i Hi. pose proof (d4_queued _ _ HQ Hr) as Hq4. unfold QUEUE_MAX in Hq4.
    assert (Hi2 : 0 <= i < 512) by lia.
    wrw (x_S_queue_len B B' i HW Hi2). wrw (x_S_queue_bytes B B' i HW Hi2).
    exact (d4_entry _ _ HQ Hr i Hi).
Qed.

Lemma agree_core_x : forall I ops B B', agree_core I ops B -> wsame B B' rs_x -> length B' = Z.to_nat W_LEN ->
  agree_st B' -> agree_fly B' -> agree_time ops B' -> bit01 (g_fail_next B') -> agree_core I ops B'.
Proof.
  intros I ops B B' HC HW HL HS HF HT HE.
  assert (Ep : S_personality B' = S_personality B) by tf_same HW.
  constructor.
  - exact (ac_img _ _ _ HC).
  - exact HL.
  - exact (x_cfg B B' HW (ac_cfg _ _ _ HC)).
  - exact (x_io I B B' HW (ac_io _ _ _ HC)).
  - exact HS.
  - exact HF.
  - exact HT.
  - exact (x_q ops B B' HW (ac_q _ _ _ HC)).
  - constructor; [exact HE|]. wrw Ep. exact (e2_personality _ _ (ac_misc _ _ _ HC)).
Qed.

(* the ranges a retransmission writes: retransmit (DS:403-410: retries, the retry field at frame + 26, sent, the
   count), io_send's retry branch (FT:829 g_fail_next, FT:842-843 M.fly.retries / sent) and send_raw's count
   (DS:91-92) *)
Definition rs_rt : list (Z * Z) :=
  [(A_S_inflight_retries, 4); (A_S_inflight_frame + 26, 2); (A_S_inflight_sent_us, 8);
   (A_S_stats_tx_retransmits, 8); (A_S_stats_tx_frames, 8); (OFF_g_fail_next, 1); (A_M_fly_retries, 4);
   (A_M_fly_sent, 8)].
