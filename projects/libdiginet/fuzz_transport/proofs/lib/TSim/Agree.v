(* The simulation invariant, by clause group A-E (the labels below name its clauses), with the frame facts M1, M2, M13.
   `agree I ops B` holds at the head of the loop of LLVMFuzzerTestOneInput (fuzz_transport.c:1168, FT), ops = the
   operations done so far; it relates the library state g_s, the harness model M, the queues, the config and the
   scalars of the world B (TWorld.v getters). No clause mentions OW, GOT, M_fail or g_rx_send: each operation
   resets or sets them (op_begin FT:388-394, receive FT:1002-1008), so they are per-operation facts.

   Layers. `agree_core` is every clause that also holds where the library calls the harness back in the middle
   of an operation (the library's ticks DS:317 / DS:522 inside receive and poll): it leaves out
   C2's keepalive clause (a tick re-establishes it: it is what the tick of DS:445-456 sends on) and E1's g_rx = 0
   (inside a poll g_rx is the frame's address, FT:1012). `agree` = agree_core + those two.
   Sub-records, one per clause group: A (agree_cfg, agree_io), B1-B7, B9 (agree_st), B8 (agree_fly),
   C (agree_time), D (agree_q: reads only S_queue*, S_queued, g_cmd, g_q, g_nq, g_ncmd, g_raw), E (agree_misc),
   the image addresses (timg_ok).

   Clauses not carried in the record, and why:
   - B2's "unknown: M_desk = DESK, S_desk_mac = 0s": nothing reads either while the desk is unknown (every send
     and every rx path tests desk_known first: DS:122, :152, :278; FT:220, :288, :402-404).
   - B9's third clause (ONLINE -> e2_acked /\ e1_us): false, dropped.
   - D1's "a coalescable key occurs at most once": true but read by nothing.
   - E1's g_rx_fail = 0: the prologue does not write g_rx_fail (FT:1124-1166) and its only reader, io_recv
     (FT:910), runs only inside a poll, after receive wrote it (FT:1015).
   B8 is stated so: the frame in flight, on both sides, IS diginet_frame_build's
   output lib_frame of one body; the B8 frame facts and M1 / M13 follow from it by L2 / L3
   (SendOk.v). *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb.
Import ListNotations.
Open Scope Z_scope.

(* a C int flag that holds 0 or 1 *)
Definition bit01 (x : Z) : Prop := x = 0 \/ x = 1.

(* The image addresses the model stores and compares (TImg.v). diginet_session_init refuses a NULL send or
   notify (DS:58); poll returns E_ARG on a NULL recv or now_us (DS:508); check_state_desk compares the
   personality pointer and OW.desk_p with NULL and tells SPEC_C24 from SPEC_PC by address (FT:534-536,
   TCb spec_desk_at); each is stored in an 8-byte cell (put 8). True of TImgP / TImgU by computation. *)
Record timg_ok (I : timg) : Prop := {
  ti_io_send_ok : 0 < ti_io_send I < 2 ^ 64;
  ti_io_recv_ok : 0 < ti_io_recv I < 2 ^ 64;
  ti_io_now_ok : 0 < ti_io_now I < 2 ^ 64;
  ti_notice_ok : 0 < ti_notice I < 2 ^ 64;
  ti_spec_c24_ok : 0 < ti_spec_c24 I < 2 ^ 64;
  ti_spec_pc_ok : 0 < ti_spec_pc I < 2 ^ 64;
  ti_c24_pc : ti_spec_c24 I <> ti_spec_pc I;
  ti_personalities_ok : 0 < ti_personalities I /\ ti_personalities I + 48 <= 2 ^ 64;
}.

(* ---- A. Fixed by the prologue (FT:1130-1165), never written after ---- *)
Record agree_cfg (B : list byte) : Prop := {
  a1_max_retries : Cfg_max_retries B <= 7;                                       (* FT:1140 *)
  a1_ack_timeout : 1 <= Cfg_ack_timeout_ms B <= 256;                             (* FT:1141 *)
  a1_keepalive : 1 <= Cfg_keepalive_ms B <= 65536;                               (* FT:1142 *)
  a1_backoff : Cfg_backoff_ms B <= 255;                                          (* FT:1143 *)
  a1_offline : 1 <= Cfg_offline_ms B <= 65536;                                   (* FT:1144 *)
  a1_wake_timeout : 1 <= Cfg_wake_timeout_ms B <= 65536;                         (* FT:1145 *)
  a1_display_gap : Cfg_display_gap_us B <= 65535;                                (* FT:1146 *)
  a1_max_cmds : 1 <= Cfg_max_cmds B <= 255;                                      (* FT:1147 *)
  a1_max_body : 24 <= Cfg_max_body B <= 1484;                                    (* FT:1148 *)
  a1_host_mac : Cfg_host_mac B = HOST;                                           (* FT:1135 *)
  a1_desk_mac : Cfg_desk_mac B = DESK;                                           (* FT:1139 *)
  a1_desk_mac_set : bit01 (Cfg_desk_mac_set B);                                  (* FT:1138 *)
  a1_auto_wake : bit01 (Cfg_auto_wake B);                                        (* FT:1136 *)
  a1_sum_mode : Cfg_sum_mode B = DIGINET_SUM_BODY \/ Cfg_sum_mode B = DIGINET_SUM_ZERO;   (* FT:1137 *)
  a2_cfg : sub B A_S_cfg_host_mac 60 = sub B OFF_g_cfg 60;                       (* A2, DS:64 s->cfg = *cfg *)
  a4_raw : bit01 (g_raw B);                                                      (* A4, FT:1150 *)
}.

(* A3 (FT:1127, DS:65-67) *)
Record agree_io (I : timg) (B : list byte) : Prop := {
  a3_io_ctx : S_io_ctx B = 0;
  a3_io_send : S_io_send B = ti_io_send I;
  a3_io_recv : S_io_recv B = ti_io_recv I;
  a3_io_now : S_io_now_us B = ti_io_now I;
  a3_notify : S_notify B = ti_notice I;
  a3_notify_ctx : S_notify_ctx B = 0;
}.

(* ---- B. The session and the harness model agree (B1-B7, B9; B8 is agree_fly) ---- *)
Record agree_st (B : list byte) : Prop := {
  b1_state : S_state B = M_state B;
  b1_state_range : 0 <= M_state B <= 3;                       (* IDLE 0, WAKING 1, ONLINE 2, CLOSED 3 *)
  b2_desk_known : S_desk_known B = M_desk_known B;
  b2_desk_known01 : bit01 (M_desk_known B);
  b2_desk_mac : M_desk_known B = 1 -> S_desk_mac B = M_desk B;
  b3_foreign : S_foreign B = M_foreign B;
  b3_foreign01 : bit01 (M_foreign B);
  b3_e1 : S_e1_named_us B = M_e1_us B;
  b3_e1_01 : bit01 (M_e1_us B);
  b3_e2 : S_wake_acked B = M_e2_acked B;
  b3_e2_01 : bit01 (M_e2_acked B);
  b4_wake_sent : S_wake_sent_us B = M_wake_sent B;
  b4_last_rx : S_last_rx_us B = M_last_rx B;
  b4_backoff : S_backoff_until_us B = M_backoff_until B;
  (* B5, tagged mode only (the raw harness does not track them, FT:869-881; no check reads them in raw mode;
     deadline reads S_next_keepalive_us only on its !inflight path, which ends in the clamp DS:502) *)
  b5_next_ka : g_raw B = 0 -> S_next_keepalive_us B = M_next_ka B;
  b5_display_sent : g_raw B = 0 -> S_display_sent B = M_display_sent B;
  b5_display_sent01 : g_raw B = 0 -> bit01 (M_display_sent B);
  b5_last_display : g_raw B = 0 -> S_last_display_us B = M_last_display B;
  b6_valid : S_desk_counter_valid B = M_desk_counter_valid B;
  b6_valid01 : bit01 (M_desk_counter_valid B);
  b6_counter : M_desk_counter_valid B = 1 -> S_desk_counter B = M_desk_counter B;
  b7_host_counter : S_host_counter B = M_host_counter B;
  b9_idle : M_state B = S_IDLE \/ M_state B = S_CLOSED -> M_fly_on B = 0;
  b9_known : M_state B = S_WAKING \/ M_state B = S_ONLINE -> M_desk_known B = 1;
}.

(* ---- B8. The frame in flight ----
   On: the M_fly_len bytes at M.fly.frame (FT:888-889, the frame as it first went: retry 0) and the
   S_inflight_len bytes at s->inflight_frame (what send_raw resends, DS:400, :411, with the retry count written
   big-endian at 26-27 by DS:405-408) are both lib_frame (diginet_frame_build's bytes, DgnLib.v) of one body
   that diginet_body_check accepts: the wake's E2 (send_control, DS:99-105, :139: body [], ncmds 0) or a data
   frame (send_data, DS:390-397). dst = the desk, src = HOST, send = the counter in flight, ack 0. *)
Record agree_fly (B : list byte) : Prop := {
  b8_on : S_inflight B = M_fly_on B;
  b8_on01 : bit01 (M_fly_on B);
  b8_state : M_fly_on B = 1 -> M_state B = S_WAKING \/ M_state B = S_ONLINE;
  b8_counter : M_fly_on B = 1 -> S_inflight_counter B = M_fly_counter B;
  b8_counter_host : M_fly_on B = 1 -> S_inflight_counter B = S_host_counter B;        (* M2 *)
  b8_retries : M_fly_on B = 1 -> S_inflight_retries B = M_fly_retries B;
  b8_retries_le : M_fly_on B = 1 -> M_fly_retries B <= Cfg_max_retries B;
  b8_sent : M_fly_on B = 1 -> S_inflight_sent_us B = M_fly_sent B;
  b8_len : M_fly_on B = 1 -> S_inflight_len B = M_fly_len B;
  b8_cmd : M_fly_on B = 1 -> M_fly_cmd B = SPEC_CMD_E2 \/ M_fly_cmd B = SPEC_CMD_DATA;
  b8_frames : M_fly_on B = 1 -> exists (body : list byte) (ncmds : Z),
    (length body <= 1484)%nat /\ body_check body = DIGINET_OK /\ 0 <= ncmds < 2 ^ 8 /\
    M_fly_len B = frame_len (length body) /\
    sub B A_M_fly_frame (Z.to_nat (M_fly_len B)) =
      lib_frame (M_desk B) HOST (M_fly_counter B) 0 0 (M_fly_cmd B) ncmds body (Cfg_sum_mode B) /\
    sub B A_S_inflight_frame (Z.to_nat (M_fly_len B)) =
      lib_frame (M_desk B) HOST (M_fly_counter B) 0 (M_fly_retries B) (M_fly_cmd B) ncmds body (Cfg_sum_mode B);
}.

(* ---- C. Time (now = g_now B; u64, never wraps: now <= 1000000 + 1024 * 65535 * 1000000 < 2^47) ----
   C2's keepalive clause is in `agree`, not here (see the header). ms x = 1000 * x. *)
Record agree_time (ops : Z) (B : list byte) : Prop := {
  c_now : g_now B <= 1000000 + ops * 65535000000;            (* FT:1151, :1184: + SCALE <= 10^6 times a u16 *)
  c1_last_rx : M_last_rx B <= g_now B;
  c1_wake_sent : M_wake_sent B <= g_now B;
  c1_fly_sent : M_fly_on B = 1 -> M_fly_sent B <= g_now B;
  c1_last_display : M_display_sent B <> 0 -> M_last_display B <= g_now B;
  c1_backoff : M_backoff_until B <= g_now B + 255000;
  c1_next_ka : g_raw B = 0 -> M_next_ka B <= g_now B + 65536000;
  c2_wake : M_state B = S_WAKING -> g_now B - M_wake_sent B < 1000 * Cfg_wake_timeout_ms B;
  c2_online : M_state B = S_ONLINE -> g_now B - M_last_rx B < 1000 * Cfg_offline_ms B;
  c2_fly : M_fly_on B = 1 -> g_now B - M_fly_sent B < 1000 * Cfg_ack_timeout_ms B;
}.

(* C2's fourth clause (FT:779-782 check_keepalive_settle's guard) *)
Definition c2_keepalive (B : list byte) : Prop :=
  g_raw B = 0 -> M_state B = S_ONLINE -> M_fly_on B = 0 -> M_backoff_until B <= g_now B -> g_now B < M_next_ka B.

(* ---- D. Commands ---- *)
Record agree_q (ops : Z) (B : list byte) : Prop := {
  (* D1, tagged mode: the model's queue g_q[0 .. g_nq) of serials mirrors s->queue (DS:347, FT:1107-1119) *)
  d1_queued : g_raw B = 0 -> S_queued B = g_nq B;
  d1_nq : g_raw B = 0 -> g_nq B <= QUEUE_MAX;
  d1_entry : g_raw B = 0 -> forall i, 0 <= i < g_nq B ->
    0 <= Q_at B i < g_ncmd B /\ Cmd_st B (Q_at B i) = PENDING /\
    S_queue_bytes B i = Cmd_bytes B (Q_at B i) /\ S_queue_len B i = Cmd_len B (Q_at B i) /\
    S_queue_key B i = Cmd_key B (Q_at B i) /\ S_queue_display B i = Cmd_display B (Q_at B i);
  d1_nodup : g_raw B = 0 -> forall i j, 0 <= i < g_nq B -> 0 <= j < g_nq B -> Q_at B i = Q_at B j -> i = j;
  d1_pending : g_raw B = 0 -> forall k, 0 <= k < g_ncmd B ->
    (Cmd_st B k = PENDING <-> exists i, 0 <= i < g_nq B /\ Q_at B i = k);
  (* D2: every command the model made and did not refuse (FT:1089-1094, :1096-1102) *)
  d2_cmd : forall k, 0 <= k < g_ncmd B -> Cmd_st B k <> 0 ->
    at8 (Cmd_bytes B k) 0 = TAG /\ at8 (Cmd_bytes B k) 1 = Z.land k 0x7f /\
    at8 (Cmd_bytes B k) 2 = Z.land (Z.shiftr k 7) 0x7f /\ 3 <= Cmd_len B k <= 24 /\
    bit01 (Cmd_display B k) /\ system_at (firstn (Z.to_nat (Cmd_len B k)) (Cmd_bytes B k)) = false;
  (* D3 (FT:1120, :1168) *)
  d3_ncmd : g_ncmd B <= ops;
  d3_ops : 0 <= ops <= OPS_MAX;
  (* D4, raw mode (DS:330-335, :345-346) *)
  d4_queued : g_raw B <> 0 -> S_queued B <= QUEUE_MAX;
  d4_entry : g_raw B <> 0 -> forall i, 0 <= i < S_queued B ->
    1 <= S_queue_len B i <= 24 /\ system_at (firstn (Z.to_nat (S_queue_len B i)) (S_queue_bytes B i)) = false;
}.

(* ---- E. Small facts (E1's g_rx = 0 is in `agree`; E3 is the absence of OW / GOT / M_fail clauses) ---- *)
Record agree_misc (I : timg) (B : list byte) : Prop := {
  e1_fail_next : bit01 (g_fail_next B);
  e2_personality : S_personality B = 0 \/ S_personality B = ti_personalities I \/
                   S_personality B = ti_personalities I + 24;
}.

(* ---- the two layers ---- *)
Record agree_core (I : timg) (ops : Z) (B : list byte) : Prop := {
  ac_img : timg_ok I;
  ac_len : length B = Z.to_nat W_LEN;
  ac_cfg : agree_cfg B;
  ac_io : agree_io I B;
  ac_st : agree_st B;
  ac_fly : agree_fly B;
  ac_time : agree_time ops B;
  ac_q : agree_q ops B;
  ac_misc : agree_misc I B;
}.

Record agree (I : timg) (ops : Z) (B : list byte) : Prop := {
  ag_core : agree_core I ops B;
  ag_keepalive : c2_keepalive B;            (* C2, fourth clause *)
  ag_rx : g_rx B = 0;                       (* E1 *)
}.
