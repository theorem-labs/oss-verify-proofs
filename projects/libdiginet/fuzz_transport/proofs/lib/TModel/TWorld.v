(* The 17 writable globals of fuzz/fuzz_transport.c lie in one .bss region of 0x10050 bytes, at the same
   offsets in the plain image (base 0x32790) and the ubsan image (base 0x33300). A world is that region as a
   byte list; every global, struct member and array element is read and written at a literal offset.
   Generated from the DWARF of both images; every offset below was checked equal in both. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Mem.
Import ListNotations.
Open Scope Z_scope.

Definition W_LEN : Z := 0x10050.
Definition W_BASE_PLAIN : Z := 0x32790.
Definition W_BASE_UBSAN : Z := 0x33300.

Definition sub (bs : list byte) (k : Z) (n : nat) : list byte := firstn n (skipn (Z.to_nat k) bs).
Definition u_at (bs : list byte) (k : Z) (n : nat) : Z := bytes_le_to_Z (sub bs k n).
Definition s32_at (bs : list byte) (k : Z) : Z := bv_swrap 32 (u_at bs k 4).
Definition upd (bs : list byte) (k : Z) (v : list byte) : list byte :=
  firstn (Z.to_nat k) bs ++ v ++ skipn (Z.to_nat k + length v) bs.
Definition put (n : nat) (v : Z) : list byte := Z_to_le_bytes n v.
Definition zs (l : list byte) : list Z := map bv_unsigned l.
Definition bs (l : list Z) : list byte := map (Z_to_bv 8) l.

(* ---- the globals: offset in the world and size ---- *)
Definition OFF_M : Z := 0x0.  Definition SZ_M : Z := 1648.
Definition OFF_g_s : Z := 0x670.  Definition SZ_g_s : Z := 18264.
Definition OFF_g_cmd : Z := 0x4dc8.  Definition SZ_g_cmd : Z := 40960.
Definition OFF_g_q : Z := 0xedc8.  Definition SZ_g_q : Z := 4096.
Definition OFF_g_fail_next : Z := 0xfdc8.  Definition SZ_g_fail_next : Z := 4.
Definition OFF_g_raw : Z := 0xfdcc.  Definition SZ_g_raw : Z := 4.
Definition OFF_g_last_counter : Z := 0xfdd0.  Definition SZ_g_last_counter : Z := 4.
Definition OFF_g_nq : Z := 0xfdd4.  Definition SZ_g_nq : Z := 4.
Definition OFF_g_ncmd : Z := 0xfdd8.  Definition SZ_g_ncmd : Z := 4.
Definition OFF_g_rx_send : Z := 0xfddc.  Definition SZ_g_rx_send : Z := 4.
Definition OFF_g_rx_fail : Z := 0xfde0.  Definition SZ_g_rx_fail : Z := 4.
Definition OFF_g_rx_times : Z := 0xfde4.  Definition SZ_g_rx_times : Z := 4.
Definition OFF_g_now : Z := 0xfde8.  Definition SZ_g_now : Z := 8.
Definition OFF_g_rx : Z := 0xfdf0.  Definition SZ_g_rx : Z := 8.
Definition OFF_g_rx_len : Z := 0xfdf8.  Definition SZ_g_rx_len : Z := 8.
Definition OFF_g_cfg : Z := 0xfe00.  Definition SZ_g_cfg : Z := 60.
Definition OFF_GOT : Z := 0xfe3c.  Definition SZ_GOT : Z := 224.
Definition OFF_OW : Z := 0xff20.  Definition SZ_OW : Z := 304.

(* ---- M (M) ---- *)
Definition A_M_desk_known : Z := OFF_M + 0.
Definition M_desk_known (B : list byte) : Z := s32_at B (A_M_desk_known).
Definition set_M_desk_known (B : list byte) (v : Z) : list byte := upd B (A_M_desk_known) (put 4 v).
Definition A_M_desk : Z := OFF_M + 4.
Definition M_desk (B : list byte) : list byte := sub B (A_M_desk) 6.
Definition set_M_desk (B : list byte) (v : list byte) : list byte := upd B (A_M_desk) v.
Definition A_M_state : Z := OFF_M + 12.
Definition M_state (B : list byte) : Z := s32_at B (A_M_state).
Definition set_M_state (B : list byte) (v : Z) : list byte := upd B (A_M_state) (put 4 v).
Definition A_M_e2_acked : Z := OFF_M + 16.
Definition M_e2_acked (B : list byte) : Z := s32_at B (A_M_e2_acked).
Definition set_M_e2_acked (B : list byte) (v : Z) : list byte := upd B (A_M_e2_acked) (put 4 v).
Definition A_M_e1_us : Z := OFF_M + 20.
Definition M_e1_us (B : list byte) : Z := s32_at B (A_M_e1_us).
Definition set_M_e1_us (B : list byte) (v : Z) : list byte := upd B (A_M_e1_us) (put 4 v).
Definition A_M_foreign : Z := OFF_M + 24.
Definition M_foreign (B : list byte) : Z := s32_at B (A_M_foreign).
Definition set_M_foreign (B : list byte) (v : Z) : list byte := upd B (A_M_foreign) (put 4 v).
Definition A_M_last_rx : Z := OFF_M + 32.
Definition M_last_rx (B : list byte) : Z := u_at B (A_M_last_rx) 8.
Definition set_M_last_rx (B : list byte) (v : Z) : list byte := upd B (A_M_last_rx) (put 8 v).
Definition A_M_wake_sent : Z := OFF_M + 40.
Definition M_wake_sent (B : list byte) : Z := u_at B (A_M_wake_sent) 8.
Definition set_M_wake_sent (B : list byte) (v : Z) : list byte := upd B (A_M_wake_sent) (put 8 v).
Definition A_M_next_ka : Z := OFF_M + 48.
Definition M_next_ka (B : list byte) : Z := u_at B (A_M_next_ka) 8.
Definition set_M_next_ka (B : list byte) (v : Z) : list byte := upd B (A_M_next_ka) (put 8 v).
Definition A_M_backoff_until : Z := OFF_M + 56.
Definition M_backoff_until (B : list byte) : Z := u_at B (A_M_backoff_until) 8.
Definition set_M_backoff_until (B : list byte) (v : Z) : list byte := upd B (A_M_backoff_until) (put 8 v).
Definition A_M_last_display : Z := OFF_M + 64.
Definition M_last_display (B : list byte) : Z := u_at B (A_M_last_display) 8.
Definition set_M_last_display (B : list byte) (v : Z) : list byte := upd B (A_M_last_display) (put 8 v).
Definition A_M_display_sent : Z := OFF_M + 72.
Definition M_display_sent (B : list byte) : Z := s32_at B (A_M_display_sent).
Definition set_M_display_sent (B : list byte) (v : Z) : list byte := upd B (A_M_display_sent) (put 4 v).
Definition A_M_desk_counter_valid : Z := OFF_M + 76.
Definition M_desk_counter_valid (B : list byte) : Z := s32_at B (A_M_desk_counter_valid).
Definition set_M_desk_counter_valid (B : list byte) (v : Z) : list byte := upd B (A_M_desk_counter_valid) (put 4 v).
Definition A_M_desk_counter : Z := OFF_M + 80.
Definition M_desk_counter (B : list byte) : Z := u_at B (A_M_desk_counter) 4.
Definition set_M_desk_counter (B : list byte) (v : Z) : list byte := upd B (A_M_desk_counter) (put 4 v).
Definition A_M_host_counter : Z := OFF_M + 84.
Definition M_host_counter (B : list byte) : Z := u_at B (A_M_host_counter) 4.
Definition set_M_host_counter (B : list byte) (v : Z) : list byte := upd B (A_M_host_counter) (put 4 v).
Definition A_M_fail : Z := OFF_M + 88.
Definition M_fail (B : list byte) : Z := s32_at B (A_M_fail).
Definition set_M_fail (B : list byte) (v : Z) : list byte := upd B (A_M_fail) (put 4 v).
Definition A_M_fly_on : Z := (OFF_M + 96) + 0.
Definition M_fly_on (B : list byte) : Z := s32_at B (A_M_fly_on).
Definition set_M_fly_on (B : list byte) (v : Z) : list byte := upd B (A_M_fly_on) (put 4 v).
Definition A_M_fly_cmd : Z := (OFF_M + 96) + 4.
Definition M_fly_cmd (B : list byte) : Z := u_at B (A_M_fly_cmd) 1.
Definition set_M_fly_cmd (B : list byte) (v : Z) : list byte := upd B (A_M_fly_cmd) (put 1 v).
Definition A_M_fly_counter : Z := (OFF_M + 96) + 8.
Definition M_fly_counter (B : list byte) : Z := u_at B (A_M_fly_counter) 4.
Definition set_M_fly_counter (B : list byte) (v : Z) : list byte := upd B (A_M_fly_counter) (put 4 v).
Definition A_M_fly_retries : Z := (OFF_M + 96) + 12.
Definition M_fly_retries (B : list byte) : Z := u_at B (A_M_fly_retries) 4.
Definition set_M_fly_retries (B : list byte) (v : Z) : list byte := upd B (A_M_fly_retries) (put 4 v).
Definition A_M_fly_sent : Z := (OFF_M + 96) + 16.
Definition M_fly_sent (B : list byte) : Z := u_at B (A_M_fly_sent) 8.
Definition set_M_fly_sent (B : list byte) (v : Z) : list byte := upd B (A_M_fly_sent) (put 8 v).
Definition A_M_fly_frame : Z := (OFF_M + 96) + 24.
Definition M_fly_frame (B : list byte) : list byte := sub B (A_M_fly_frame) 1514.
Definition set_M_fly_frame (B : list byte) (v : list byte) : list byte := upd B (A_M_fly_frame) v.
Definition A_M_fly_len : Z := (OFF_M + 96) + 1544.
Definition M_fly_len (B : list byte) : Z := u_at B (A_M_fly_len) 8.
Definition set_M_fly_len (B : list byte) (v : Z) : list byte := upd B (A_M_fly_len) (put 8 v).

(* ---- OW (OW) ---- *)
Definition A_OW_n : Z := OFF_OW + 0.
Definition OW_n (B : list byte) : Z := s32_at B (A_OW_n).
Definition set_OW_n (B : list byte) (v : Z) : list byte := upd B (A_OW_n) (put 4 v).
Definition A_OW_t_state (i_t : Z) : Z := (OFF_OW + 4 + 12 * i_t) + 0.
Definition OW_t_state (B : list byte) (i_t : Z) : Z := s32_at B (A_OW_t_state i_t).
Definition set_OW_t_state (B : list byte) (i_t : Z) (v : Z) : list byte := upd B (A_OW_t_state i_t) (put 4 v).
Definition A_OW_t_old (i_t : Z) : Z := (OFF_OW + 4 + 12 * i_t) + 4.
Definition OW_t_old (B : list byte) (i_t : Z) : Z := s32_at B (A_OW_t_old i_t).
Definition set_OW_t_old (B : list byte) (i_t : Z) (v : Z) : list byte := upd B (A_OW_t_old i_t) (put 4 v).
Definition A_OW_t_reason (i_t : Z) : Z := (OFF_OW + 4 + 12 * i_t) + 8.
Definition OW_t_reason (B : list byte) (i_t : Z) : Z := s32_at B (A_OW_t_reason i_t).
Definition set_OW_t_reason (B : list byte) (i_t : Z) (v : Z) : list byte := upd B (A_OW_t_reason i_t) (put 4 v).
Definition OW_t_ESZ : Z := 12.  Definition OW_t_N : Z := 16.
Definition A_OW_e2 : Z := OFF_OW + 196.
Definition OW_e2 (B : list byte) : Z := s32_at B (A_OW_e2).
Definition set_OW_e2 (B : list byte) (v : Z) : list byte := upd B (A_OW_e2) (put 4 v).
Definition A_OW_e3 : Z := OFF_OW + 200.
Definition OW_e3 (B : list byte) : Z := s32_at B (A_OW_e3).
Definition set_OW_e3 (B : list byte) (v : Z) : list byte := upd B (A_OW_e3) (put 4 v).
Definition A_OW_acks : Z := OFF_OW + 204.
Definition OW_acks (B : list byte) : Z := s32_at B (A_OW_acks).
Definition set_OW_acks (B : list byte) (v : Z) : list byte := upd B (A_OW_acks) (put 4 v).
Definition A_OW_desk : Z := OFF_OW + 208.
Definition OW_desk (B : list byte) : Z := s32_at B (A_OW_desk).
Definition set_OW_desk (B : list byte) (v : Z) : list byte := upd B (A_OW_desk) (put 4 v).
Definition A_OW_foreign : Z := OFF_OW + 212.
Definition OW_foreign (B : list byte) : Z := s32_at B (A_OW_foreign).
Definition set_OW_foreign (B : list byte) (v : Z) : list byte := upd B (A_OW_foreign) (put 4 v).
Definition A_OW_acked : Z := OFF_OW + 216.
Definition OW_acked (B : list byte) : Z := s32_at B (A_OW_acked).
Definition set_OW_acked (B : list byte) (v : Z) : list byte := upd B (A_OW_acked) (put 4 v).
Definition A_OW_ndata : Z := OFF_OW + 220.
Definition OW_ndata (B : list byte) : Z := s32_at B (A_OW_ndata).
Definition set_OW_ndata (B : list byte) (v : Z) : list byte := upd B (A_OW_ndata) (put 4 v).
Definition A_OW_acked_counter : Z := OFF_OW + 224.
Definition OW_acked_counter (B : list byte) : Z := u_at B (A_OW_acked_counter) 4.
Definition set_OW_acked_counter (B : list byte) (v : Z) : list byte := upd B (A_OW_acked_counter) (put 4 v).
Definition A_OW_acked_retry : Z := OFF_OW + 228.
Definition OW_acked_retry (B : list byte) : Z := u_at B (A_OW_acked_retry) 4.
Definition set_OW_acked_retry (B : list byte) (v : Z) : list byte := upd B (A_OW_acked_retry) (put 4 v).
Definition A_OW_desk_off : Z := OFF_OW + 232.
Definition OW_desk_off (B : list byte) : Z := s32_at B (A_OW_desk_off).
Definition set_OW_desk_off (B : list byte) (v : Z) : list byte := upd B (A_OW_desk_off) (put 4 v).
Definition A_OW_desk_p : Z := OFF_OW + 240.
Definition OW_desk_p (B : list byte) : Z := u_at B (A_OW_desk_p) 8.
Definition set_OW_desk_p (B : list byte) (v : Z) : list byte := upd B (A_OW_desk_p) (put 8 v).
Definition A_OW_desk_body : Z := OFF_OW + 248.
Definition OW_desk_body (B : list byte) : Z := u_at B (A_OW_desk_body) 8.
Definition set_OW_desk_body (B : list byte) (v : Z) : list byte := upd B (A_OW_desk_body) (put 8 v).
Definition OW_dn_ESZ : Z := 24.  Definition OW_dn_N : Z := 2.

(* ---- GOT (GOT) ---- *)
Definition A_GOT_n : Z := OFF_GOT + 0.
Definition GOT_n (B : list byte) : Z := s32_at B (A_GOT_n).
Definition set_GOT_n (B : list byte) (v : Z) : list byte := upd B (A_GOT_n) (put 4 v).
Definition A_GOT_t_state (i_t : Z) : Z := (OFF_GOT + 4 + 12 * i_t) + 0.
Definition GOT_t_state (B : list byte) (i_t : Z) : Z := s32_at B (A_GOT_t_state i_t).
Definition set_GOT_t_state (B : list byte) (i_t : Z) (v : Z) : list byte := upd B (A_GOT_t_state i_t) (put 4 v).
Definition A_GOT_t_old (i_t : Z) : Z := (OFF_GOT + 4 + 12 * i_t) + 4.
Definition GOT_t_old (B : list byte) (i_t : Z) : Z := s32_at B (A_GOT_t_old i_t).
Definition set_GOT_t_old (B : list byte) (i_t : Z) (v : Z) : list byte := upd B (A_GOT_t_old i_t) (put 4 v).
Definition A_GOT_t_reason (i_t : Z) : Z := (OFF_GOT + 4 + 12 * i_t) + 8.
Definition GOT_t_reason (B : list byte) (i_t : Z) : Z := s32_at B (A_GOT_t_reason i_t).
Definition set_GOT_t_reason (B : list byte) (i_t : Z) (v : Z) : list byte := upd B (A_GOT_t_reason i_t) (put 4 v).
Definition GOT_t_ESZ : Z := 12.  Definition GOT_t_N : Z := 16.
Definition A_GOT_e2 : Z := OFF_GOT + 196.
Definition GOT_e2 (B : list byte) : Z := s32_at B (A_GOT_e2).
Definition set_GOT_e2 (B : list byte) (v : Z) : list byte := upd B (A_GOT_e2) (put 4 v).
Definition A_GOT_e3 : Z := OFF_GOT + 200.
Definition GOT_e3 (B : list byte) : Z := s32_at B (A_GOT_e3).
Definition set_GOT_e3 (B : list byte) (v : Z) : list byte := upd B (A_GOT_e3) (put 4 v).
Definition A_GOT_acks : Z := OFF_GOT + 204.
Definition GOT_acks (B : list byte) : Z := s32_at B (A_GOT_acks).
Definition set_GOT_acks (B : list byte) (v : Z) : list byte := upd B (A_GOT_acks) (put 4 v).
Definition A_GOT_desk : Z := OFF_GOT + 208.
Definition GOT_desk (B : list byte) : Z := s32_at B (A_GOT_desk).
Definition set_GOT_desk (B : list byte) (v : Z) : list byte := upd B (A_GOT_desk) (put 4 v).
Definition A_GOT_foreign : Z := OFF_GOT + 212.
Definition GOT_foreign (B : list byte) : Z := s32_at B (A_GOT_foreign).
Definition set_GOT_foreign (B : list byte) (v : Z) : list byte := upd B (A_GOT_foreign) (put 4 v).
Definition A_GOT_acked : Z := OFF_GOT + 216.
Definition GOT_acked (B : list byte) : Z := s32_at B (A_GOT_acked).
Definition set_GOT_acked (B : list byte) (v : Z) : list byte := upd B (A_GOT_acked) (put 4 v).
Definition A_GOT_ndata : Z := OFF_GOT + 220.
Definition GOT_ndata (B : list byte) : Z := s32_at B (A_GOT_ndata).
Definition set_GOT_ndata (B : list byte) (v : Z) : list byte := upd B (A_GOT_ndata) (put 4 v).

(* ---- g_s (struct diginet_session) ---- *)
Definition A_S_cfg_host_mac : Z := (OFF_g_s + 0) + 0.
Definition S_cfg_host_mac (B : list byte) : list byte := sub B (A_S_cfg_host_mac) 6.
Definition set_S_cfg_host_mac (B : list byte) (v : list byte) : list byte := upd B (A_S_cfg_host_mac) v.
Definition A_S_cfg_desk_mac : Z := (OFF_g_s + 0) + 6.
Definition S_cfg_desk_mac (B : list byte) : list byte := sub B (A_S_cfg_desk_mac) 6.
Definition set_S_cfg_desk_mac (B : list byte) (v : list byte) : list byte := upd B (A_S_cfg_desk_mac) v.
Definition A_S_cfg_desk_mac_set : Z := (OFF_g_s + 0) + 12.
Definition S_cfg_desk_mac_set (B : list byte) : Z := s32_at B (A_S_cfg_desk_mac_set).
Definition set_S_cfg_desk_mac_set (B : list byte) (v : Z) : list byte := upd B (A_S_cfg_desk_mac_set) (put 4 v).
Definition A_S_cfg_auto_wake : Z := (OFF_g_s + 0) + 16.
Definition S_cfg_auto_wake (B : list byte) : Z := s32_at B (A_S_cfg_auto_wake).
Definition set_S_cfg_auto_wake (B : list byte) (v : Z) : list byte := upd B (A_S_cfg_auto_wake) (put 4 v).
Definition A_S_cfg_sum_mode : Z := (OFF_g_s + 0) + 20.
Definition S_cfg_sum_mode (B : list byte) : Z := s32_at B (A_S_cfg_sum_mode).
Definition set_S_cfg_sum_mode (B : list byte) (v : Z) : list byte := upd B (A_S_cfg_sum_mode) (put 4 v).
Definition A_S_cfg_keepalive_ms : Z := (OFF_g_s + 0) + 24.
Definition S_cfg_keepalive_ms (B : list byte) : Z := u_at B (A_S_cfg_keepalive_ms) 4.
Definition set_S_cfg_keepalive_ms (B : list byte) (v : Z) : list byte := upd B (A_S_cfg_keepalive_ms) (put 4 v).
Definition A_S_cfg_ack_timeout_ms : Z := (OFF_g_s + 0) + 28.
Definition S_cfg_ack_timeout_ms (B : list byte) : Z := u_at B (A_S_cfg_ack_timeout_ms) 4.
Definition set_S_cfg_ack_timeout_ms (B : list byte) (v : Z) : list byte := upd B (A_S_cfg_ack_timeout_ms) (put 4 v).
Definition A_S_cfg_max_retries : Z := (OFF_g_s + 0) + 32.
Definition S_cfg_max_retries (B : list byte) : Z := u_at B (A_S_cfg_max_retries) 4.
Definition set_S_cfg_max_retries (B : list byte) (v : Z) : list byte := upd B (A_S_cfg_max_retries) (put 4 v).
Definition A_S_cfg_backoff_ms : Z := (OFF_g_s + 0) + 36.
Definition S_cfg_backoff_ms (B : list byte) : Z := u_at B (A_S_cfg_backoff_ms) 4.
Definition set_S_cfg_backoff_ms (B : list byte) (v : Z) : list byte := upd B (A_S_cfg_backoff_ms) (put 4 v).
Definition A_S_cfg_offline_ms : Z := (OFF_g_s + 0) + 40.
Definition S_cfg_offline_ms (B : list byte) : Z := u_at B (A_S_cfg_offline_ms) 4.
Definition set_S_cfg_offline_ms (B : list byte) (v : Z) : list byte := upd B (A_S_cfg_offline_ms) (put 4 v).
Definition A_S_cfg_wake_timeout_ms : Z := (OFF_g_s + 0) + 44.
Definition S_cfg_wake_timeout_ms (B : list byte) : Z := u_at B (A_S_cfg_wake_timeout_ms) 4.
Definition set_S_cfg_wake_timeout_ms (B : list byte) (v : Z) : list byte := upd B (A_S_cfg_wake_timeout_ms) (put 4 v).
Definition A_S_cfg_display_gap_us : Z := (OFF_g_s + 0) + 48.
Definition S_cfg_display_gap_us (B : list byte) : Z := u_at B (A_S_cfg_display_gap_us) 4.
Definition set_S_cfg_display_gap_us (B : list byte) (v : Z) : list byte := upd B (A_S_cfg_display_gap_us) (put 4 v).
Definition A_S_cfg_max_cmds : Z := (OFF_g_s + 0) + 52.
Definition S_cfg_max_cmds (B : list byte) : Z := u_at B (A_S_cfg_max_cmds) 4.
Definition set_S_cfg_max_cmds (B : list byte) (v : Z) : list byte := upd B (A_S_cfg_max_cmds) (put 4 v).
Definition A_S_cfg_max_body : Z := (OFF_g_s + 0) + 56.
Definition S_cfg_max_body (B : list byte) : Z := u_at B (A_S_cfg_max_body) 4.
Definition set_S_cfg_max_body (B : list byte) (v : Z) : list byte := upd B (A_S_cfg_max_body) (put 4 v).
Definition A_S_io_ctx : Z := (OFF_g_s + 64) + 0.
Definition S_io_ctx (B : list byte) : Z := u_at B (A_S_io_ctx) 8.
Definition set_S_io_ctx (B : list byte) (v : Z) : list byte := upd B (A_S_io_ctx) (put 8 v).
Definition A_S_io_send : Z := (OFF_g_s + 64) + 8.
Definition S_io_send (B : list byte) : Z := u_at B (A_S_io_send) 8.
Definition set_S_io_send (B : list byte) (v : Z) : list byte := upd B (A_S_io_send) (put 8 v).
Definition A_S_io_recv : Z := (OFF_g_s + 64) + 16.
Definition S_io_recv (B : list byte) : Z := u_at B (A_S_io_recv) 8.
Definition set_S_io_recv (B : list byte) (v : Z) : list byte := upd B (A_S_io_recv) (put 8 v).
Definition A_S_io_now_us : Z := (OFF_g_s + 64) + 24.
Definition S_io_now_us (B : list byte) : Z := u_at B (A_S_io_now_us) 8.
Definition set_S_io_now_us (B : list byte) (v : Z) : list byte := upd B (A_S_io_now_us) (put 8 v).
Definition A_S_notify : Z := OFF_g_s + 96.
Definition S_notify (B : list byte) : Z := u_at B (A_S_notify) 8.
Definition set_S_notify (B : list byte) (v : Z) : list byte := upd B (A_S_notify) (put 8 v).
Definition A_S_notify_ctx : Z := OFF_g_s + 104.
Definition S_notify_ctx (B : list byte) : Z := u_at B (A_S_notify_ctx) 8.
Definition set_S_notify_ctx (B : list byte) (v : Z) : list byte := upd B (A_S_notify_ctx) (put 8 v).
Definition A_S_state : Z := OFF_g_s + 112.
Definition S_state (B : list byte) : Z := s32_at B (A_S_state).
Definition set_S_state (B : list byte) (v : Z) : list byte := upd B (A_S_state) (put 4 v).
Definition A_S_desk_known : Z := OFF_g_s + 116.
Definition S_desk_known (B : list byte) : Z := s32_at B (A_S_desk_known).
Definition set_S_desk_known (B : list byte) (v : Z) : list byte := upd B (A_S_desk_known) (put 4 v).
Definition A_S_desk_mac : Z := OFF_g_s + 120.
Definition S_desk_mac (B : list byte) : list byte := sub B (A_S_desk_mac) 6.
Definition set_S_desk_mac (B : list byte) (v : list byte) : list byte := upd B (A_S_desk_mac) v.
Definition A_S_personality : Z := OFF_g_s + 128.
Definition S_personality (B : list byte) : Z := u_at B (A_S_personality) 8.
Definition set_S_personality (B : list byte) (v : Z) : list byte := upd B (A_S_personality) (put 8 v).
Definition A_S_foreign : Z := OFF_g_s + 136.
Definition S_foreign (B : list byte) : Z := s32_at B (A_S_foreign).
Definition set_S_foreign (B : list byte) (v : Z) : list byte := upd B (A_S_foreign) (put 4 v).
Definition A_S_e1_named_us : Z := OFF_g_s + 140.
Definition S_e1_named_us (B : list byte) : Z := s32_at B (A_S_e1_named_us).
Definition set_S_e1_named_us (B : list byte) (v : Z) : list byte := upd B (A_S_e1_named_us) (put 4 v).
Definition A_S_wake_acked : Z := OFF_g_s + 144.
Definition S_wake_acked (B : list byte) : Z := s32_at B (A_S_wake_acked).
Definition set_S_wake_acked (B : list byte) (v : Z) : list byte := upd B (A_S_wake_acked) (put 4 v).
Definition A_S_wake_sent_us : Z := OFF_g_s + 152.
Definition S_wake_sent_us (B : list byte) : Z := u_at B (A_S_wake_sent_us) 8.
Definition set_S_wake_sent_us (B : list byte) (v : Z) : list byte := upd B (A_S_wake_sent_us) (put 8 v).
Definition A_S_host_counter : Z := OFF_g_s + 160.
Definition S_host_counter (B : list byte) : Z := u_at B (A_S_host_counter) 4.
Definition set_S_host_counter (B : list byte) (v : Z) : list byte := upd B (A_S_host_counter) (put 4 v).
Definition A_S_desk_counter : Z := OFF_g_s + 164.
Definition S_desk_counter (B : list byte) : Z := u_at B (A_S_desk_counter) 4.
Definition set_S_desk_counter (B : list byte) (v : Z) : list byte := upd B (A_S_desk_counter) (put 4 v).
Definition A_S_desk_counter_valid : Z := OFF_g_s + 168.
Definition S_desk_counter_valid (B : list byte) : Z := s32_at B (A_S_desk_counter_valid).
Definition set_S_desk_counter_valid (B : list byte) (v : Z) : list byte := upd B (A_S_desk_counter_valid) (put 4 v).
Definition A_S_last_rx_us : Z := OFF_g_s + 176.
Definition S_last_rx_us (B : list byte) : Z := u_at B (A_S_last_rx_us) 8.
Definition set_S_last_rx_us (B : list byte) (v : Z) : list byte := upd B (A_S_last_rx_us) (put 8 v).
Definition A_S_next_keepalive_us : Z := OFF_g_s + 184.
Definition S_next_keepalive_us (B : list byte) : Z := u_at B (A_S_next_keepalive_us) 8.
Definition set_S_next_keepalive_us (B : list byte) (v : Z) : list byte := upd B (A_S_next_keepalive_us) (put 8 v).
Definition A_S_backoff_until_us : Z := OFF_g_s + 192.
Definition S_backoff_until_us (B : list byte) : Z := u_at B (A_S_backoff_until_us) 8.
Definition set_S_backoff_until_us (B : list byte) (v : Z) : list byte := upd B (A_S_backoff_until_us) (put 8 v).
Definition A_S_last_display_us : Z := OFF_g_s + 200.
Definition S_last_display_us (B : list byte) : Z := u_at B (A_S_last_display_us) 8.
Definition set_S_last_display_us (B : list byte) (v : Z) : list byte := upd B (A_S_last_display_us) (put 8 v).
Definition A_S_display_sent : Z := OFF_g_s + 208.
Definition S_display_sent (B : list byte) : Z := s32_at B (A_S_display_sent).
Definition set_S_display_sent (B : list byte) (v : Z) : list byte := upd B (A_S_display_sent) (put 4 v).
Definition A_S_inflight : Z := OFF_g_s + 212.
Definition S_inflight (B : list byte) : Z := s32_at B (A_S_inflight).
Definition set_S_inflight (B : list byte) (v : Z) : list byte := upd B (A_S_inflight) (put 4 v).
Definition A_S_inflight_frame : Z := OFF_g_s + 216.
Definition S_inflight_frame (B : list byte) : list byte := sub B (A_S_inflight_frame) 1514.
Definition set_S_inflight_frame (B : list byte) (v : list byte) : list byte := upd B (A_S_inflight_frame) v.
Definition A_S_inflight_len : Z := OFF_g_s + 1736.
Definition S_inflight_len (B : list byte) : Z := u_at B (A_S_inflight_len) 8.
Definition set_S_inflight_len (B : list byte) (v : Z) : list byte := upd B (A_S_inflight_len) (put 8 v).
Definition A_S_inflight_counter : Z := OFF_g_s + 1744.
Definition S_inflight_counter (B : list byte) : Z := u_at B (A_S_inflight_counter) 4.
Definition set_S_inflight_counter (B : list byte) (v : Z) : list byte := upd B (A_S_inflight_counter) (put 4 v).
Definition A_S_inflight_retries : Z := OFF_g_s + 1748.
Definition S_inflight_retries (B : list byte) : Z := u_at B (A_S_inflight_retries) 4.
Definition set_S_inflight_retries (B : list byte) (v : Z) : list byte := upd B (A_S_inflight_retries) (put 4 v).
Definition A_S_inflight_sent_us : Z := OFF_g_s + 1752.
Definition S_inflight_sent_us (B : list byte) : Z := u_at B (A_S_inflight_sent_us) 8.
Definition set_S_inflight_sent_us (B : list byte) (v : Z) : list byte := upd B (A_S_inflight_sent_us) (put 8 v).
Definition A_S_queue_bytes (i_queue : Z) : Z := (OFF_g_s + 1760 + 32 * i_queue) + 0.
Definition S_queue_bytes (B : list byte) (i_queue : Z) : list byte := sub B (A_S_queue_bytes i_queue) 24.
Definition set_S_queue_bytes (B : list byte) (i_queue : Z) (v : list byte) : list byte := upd B (A_S_queue_bytes i_queue) v.
Definition A_S_queue_len (i_queue : Z) : Z := (OFF_g_s + 1760 + 32 * i_queue) + 24.
Definition S_queue_len (B : list byte) (i_queue : Z) : Z := u_at B (A_S_queue_len i_queue) 1.
Definition set_S_queue_len (B : list byte) (i_queue : Z) (v : Z) : list byte := upd B (A_S_queue_len i_queue) (put 1 v).
Definition A_S_queue_display (i_queue : Z) : Z := (OFF_g_s + 1760 + 32 * i_queue) + 25.
Definition S_queue_display (B : list byte) (i_queue : Z) : Z := u_at B (A_S_queue_display i_queue) 1.
Definition set_S_queue_display (B : list byte) (i_queue : Z) (v : Z) : list byte := upd B (A_S_queue_display i_queue) (put 1 v).
Definition A_S_queue_key (i_queue : Z) : Z := (OFF_g_s + 1760 + 32 * i_queue) + 28.
Definition S_queue_key (B : list byte) (i_queue : Z) : Z := u_at B (A_S_queue_key i_queue) 4.
Definition set_S_queue_key (B : list byte) (i_queue : Z) (v : Z) : list byte := upd B (A_S_queue_key i_queue) (put 4 v).
Definition S_queue_ESZ : Z := 32.  Definition S_queue_N : Z := 512.
Definition A_S_queued : Z := OFF_g_s + 18144.
Definition S_queued (B : list byte) : Z := u_at B (A_S_queued) 4.
Definition set_S_queued (B : list byte) (v : Z) : list byte := upd B (A_S_queued) (put 4 v).
Definition A_S_stats_rx_frames : Z := (OFF_g_s + 18152) + 0.
Definition S_stats_rx_frames (B : list byte) : Z := u_at B (A_S_stats_rx_frames) 8.
Definition set_S_stats_rx_frames (B : list byte) (v : Z) : list byte := upd B (A_S_stats_rx_frames) (put 8 v).
Definition A_S_stats_rx_data : Z := (OFF_g_s + 18152) + 8.
Definition S_stats_rx_data (B : list byte) : Z := u_at B (A_S_stats_rx_data) 8.
Definition set_S_stats_rx_data (B : list byte) (v : Z) : list byte := upd B (A_S_stats_rx_data) (put 8 v).
Definition A_S_stats_rx_duplicates : Z := (OFF_g_s + 18152) + 16.
Definition S_stats_rx_duplicates (B : list byte) : Z := u_at B (A_S_stats_rx_duplicates) 8.
Definition set_S_stats_rx_duplicates (B : list byte) (v : Z) : list byte := upd B (A_S_stats_rx_duplicates) (put 8 v).
Definition A_S_stats_rx_desk_retries : Z := (OFF_g_s + 18152) + 24.
Definition S_stats_rx_desk_retries (B : list byte) : Z := u_at B (A_S_stats_rx_desk_retries) 8.
Definition set_S_stats_rx_desk_retries (B : list byte) (v : Z) : list byte := upd B (A_S_stats_rx_desk_retries) (put 8 v).
Definition A_S_stats_rx_ignored : Z := (OFF_g_s + 18152) + 32.
Definition S_stats_rx_ignored (B : list byte) : Z := u_at B (A_S_stats_rx_ignored) 8.
Definition set_S_stats_rx_ignored (B : list byte) (v : Z) : list byte := upd B (A_S_stats_rx_ignored) (put 8 v).
Definition A_S_stats_tx_frames : Z := (OFF_g_s + 18152) + 40.
Definition S_stats_tx_frames (B : list byte) : Z := u_at B (A_S_stats_tx_frames) 8.
Definition set_S_stats_tx_frames (B : list byte) (v : Z) : list byte := upd B (A_S_stats_tx_frames) (put 8 v).
Definition A_S_stats_tx_data : Z := (OFF_g_s + 18152) + 48.
Definition S_stats_tx_data (B : list byte) : Z := u_at B (A_S_stats_tx_data) 8.
Definition set_S_stats_tx_data (B : list byte) (v : Z) : list byte := upd B (A_S_stats_tx_data) (put 8 v).
Definition A_S_stats_tx_acks : Z := (OFF_g_s + 18152) + 56.
Definition S_stats_tx_acks (B : list byte) : Z := u_at B (A_S_stats_tx_acks) 8.
Definition set_S_stats_tx_acks (B : list byte) (v : Z) : list byte := upd B (A_S_stats_tx_acks) (put 8 v).
Definition A_S_stats_tx_keepalives : Z := (OFF_g_s + 18152) + 64.
Definition S_stats_tx_keepalives (B : list byte) : Z := u_at B (A_S_stats_tx_keepalives) 8.
Definition set_S_stats_tx_keepalives (B : list byte) (v : Z) : list byte := upd B (A_S_stats_tx_keepalives) (put 8 v).
Definition A_S_stats_tx_wakes : Z := (OFF_g_s + 18152) + 72.
Definition S_stats_tx_wakes (B : list byte) : Z := u_at B (A_S_stats_tx_wakes) 8.
Definition set_S_stats_tx_wakes (B : list byte) (v : Z) : list byte := upd B (A_S_stats_tx_wakes) (put 8 v).
Definition A_S_stats_tx_retransmits : Z := (OFF_g_s + 18152) + 80.
Definition S_stats_tx_retransmits (B : list byte) : Z := u_at B (A_S_stats_tx_retransmits) 8.
Definition set_S_stats_tx_retransmits (B : list byte) (v : Z) : list byte := upd B (A_S_stats_tx_retransmits) (put 8 v).
Definition A_S_stats_ack_lost : Z := (OFF_g_s + 18152) + 88.
Definition S_stats_ack_lost (B : list byte) : Z := u_at B (A_S_stats_ack_lost) 8.
Definition set_S_stats_ack_lost (B : list byte) (v : Z) : list byte := upd B (A_S_stats_ack_lost) (put 8 v).
Definition A_S_stats_coalesced : Z := (OFF_g_s + 18152) + 96.
Definition S_stats_coalesced (B : list byte) : Z := u_at B (A_S_stats_coalesced) 8.
Definition set_S_stats_coalesced (B : list byte) (v : Z) : list byte := upd B (A_S_stats_coalesced) (put 8 v).
Definition A_S_stats_refused : Z := (OFF_g_s + 18152) + 104.
Definition S_stats_refused (B : list byte) : Z := u_at B (A_S_stats_refused) 8.
Definition set_S_stats_refused (B : list byte) (v : Z) : list byte := upd B (A_S_stats_refused) (put 8 v).

(* ---- g_cfg (struct diginet_session_config) ---- *)
Definition A_Cfg_host_mac : Z := OFF_g_cfg + 0.
Definition Cfg_host_mac (B : list byte) : list byte := sub B (A_Cfg_host_mac) 6.
Definition set_Cfg_host_mac (B : list byte) (v : list byte) : list byte := upd B (A_Cfg_host_mac) v.
Definition A_Cfg_desk_mac : Z := OFF_g_cfg + 6.
Definition Cfg_desk_mac (B : list byte) : list byte := sub B (A_Cfg_desk_mac) 6.
Definition set_Cfg_desk_mac (B : list byte) (v : list byte) : list byte := upd B (A_Cfg_desk_mac) v.
Definition A_Cfg_desk_mac_set : Z := OFF_g_cfg + 12.
Definition Cfg_desk_mac_set (B : list byte) : Z := s32_at B (A_Cfg_desk_mac_set).
Definition set_Cfg_desk_mac_set (B : list byte) (v : Z) : list byte := upd B (A_Cfg_desk_mac_set) (put 4 v).
Definition A_Cfg_auto_wake : Z := OFF_g_cfg + 16.
Definition Cfg_auto_wake (B : list byte) : Z := s32_at B (A_Cfg_auto_wake).
Definition set_Cfg_auto_wake (B : list byte) (v : Z) : list byte := upd B (A_Cfg_auto_wake) (put 4 v).
Definition A_Cfg_sum_mode : Z := OFF_g_cfg + 20.
Definition Cfg_sum_mode (B : list byte) : Z := s32_at B (A_Cfg_sum_mode).
Definition set_Cfg_sum_mode (B : list byte) (v : Z) : list byte := upd B (A_Cfg_sum_mode) (put 4 v).
Definition A_Cfg_keepalive_ms : Z := OFF_g_cfg + 24.
Definition Cfg_keepalive_ms (B : list byte) : Z := u_at B (A_Cfg_keepalive_ms) 4.
Definition set_Cfg_keepalive_ms (B : list byte) (v : Z) : list byte := upd B (A_Cfg_keepalive_ms) (put 4 v).
Definition A_Cfg_ack_timeout_ms : Z := OFF_g_cfg + 28.
Definition Cfg_ack_timeout_ms (B : list byte) : Z := u_at B (A_Cfg_ack_timeout_ms) 4.
Definition set_Cfg_ack_timeout_ms (B : list byte) (v : Z) : list byte := upd B (A_Cfg_ack_timeout_ms) (put 4 v).
Definition A_Cfg_max_retries : Z := OFF_g_cfg + 32.
Definition Cfg_max_retries (B : list byte) : Z := u_at B (A_Cfg_max_retries) 4.
Definition set_Cfg_max_retries (B : list byte) (v : Z) : list byte := upd B (A_Cfg_max_retries) (put 4 v).
Definition A_Cfg_backoff_ms : Z := OFF_g_cfg + 36.
Definition Cfg_backoff_ms (B : list byte) : Z := u_at B (A_Cfg_backoff_ms) 4.
Definition set_Cfg_backoff_ms (B : list byte) (v : Z) : list byte := upd B (A_Cfg_backoff_ms) (put 4 v).
Definition A_Cfg_offline_ms : Z := OFF_g_cfg + 40.
Definition Cfg_offline_ms (B : list byte) : Z := u_at B (A_Cfg_offline_ms) 4.
Definition set_Cfg_offline_ms (B : list byte) (v : Z) : list byte := upd B (A_Cfg_offline_ms) (put 4 v).
Definition A_Cfg_wake_timeout_ms : Z := OFF_g_cfg + 44.
Definition Cfg_wake_timeout_ms (B : list byte) : Z := u_at B (A_Cfg_wake_timeout_ms) 4.
Definition set_Cfg_wake_timeout_ms (B : list byte) (v : Z) : list byte := upd B (A_Cfg_wake_timeout_ms) (put 4 v).
Definition A_Cfg_display_gap_us : Z := OFF_g_cfg + 48.
Definition Cfg_display_gap_us (B : list byte) : Z := u_at B (A_Cfg_display_gap_us) 4.
Definition set_Cfg_display_gap_us (B : list byte) (v : Z) : list byte := upd B (A_Cfg_display_gap_us) (put 4 v).
Definition A_Cfg_max_cmds : Z := OFF_g_cfg + 52.
Definition Cfg_max_cmds (B : list byte) : Z := u_at B (A_Cfg_max_cmds) 4.
Definition set_Cfg_max_cmds (B : list byte) (v : Z) : list byte := upd B (A_Cfg_max_cmds) (put 4 v).
Definition A_Cfg_max_body : Z := OFF_g_cfg + 56.
Definition Cfg_max_body (B : list byte) : Z := u_at B (A_Cfg_max_body) 4.
Definition set_Cfg_max_body (B : list byte) (v : Z) : list byte := upd B (A_Cfg_max_body) (put 4 v).

(* ---- g_cmd (struct tagged) ---- *)
Definition Cmd_ESZ : Z := 40.  Definition Cmd_N : Z := 1024.
Definition A_Cmd_st (i : Z) : Z := (OFF_g_cmd + 40 * i) + 0.
Definition Cmd_st (B : list byte) (i : Z) : Z := s32_at B (A_Cmd_st i).
Definition set_Cmd_st (B : list byte) (i : Z) (v : Z) : list byte := upd B (A_Cmd_st i) (put 4 v).
Definition A_Cmd_key (i : Z) : Z := (OFF_g_cmd + 40 * i) + 4.
Definition Cmd_key (B : list byte) (i : Z) : Z := u_at B (A_Cmd_key i) 4.
Definition set_Cmd_key (B : list byte) (i : Z) (v : Z) : list byte := upd B (A_Cmd_key i) (put 4 v).
Definition A_Cmd_display (i : Z) : Z := (OFF_g_cmd + 40 * i) + 8.
Definition Cmd_display (B : list byte) (i : Z) : Z := s32_at B (A_Cmd_display i).
Definition set_Cmd_display (B : list byte) (i : Z) (v : Z) : list byte := upd B (A_Cmd_display i) (put 4 v).
Definition A_Cmd_bytes (i : Z) : Z := (OFF_g_cmd + 40 * i) + 12.
Definition Cmd_bytes (B : list byte) (i : Z) : list byte := sub B (A_Cmd_bytes i) 24.
Definition set_Cmd_bytes (B : list byte) (i : Z) (v : list byte) : list byte := upd B (A_Cmd_bytes i) v.
Definition A_Cmd_len (i : Z) : Z := (OFF_g_cmd + 40 * i) + 36.
Definition Cmd_len (B : list byte) (i : Z) : Z := u_at B (A_Cmd_len i) 1.
Definition set_Cmd_len (B : list byte) (i : Z) (v : Z) : list byte := upd B (A_Cmd_len i) (put 1 v).

(* ---- g_q (unsigned[1024]) and the scalars ---- *)
Definition Q_at (B : list byte) (i : Z) : Z := u_at B (OFF_g_q + 4 * i) 4.
Definition set_Q_at (B : list byte) (i v : Z) : list byte := upd B (OFF_g_q + 4 * i) (put 4 v).
Definition g_now (B : list byte) : Z := u_at B OFF_g_now 8.
Definition set_g_now (B : list byte) (v : Z) : list byte := upd B OFF_g_now (put 8 v).
Definition g_raw (B : list byte) : Z := s32_at B OFF_g_raw.
Definition set_g_raw (B : list byte) (v : Z) : list byte := upd B OFF_g_raw (put 4 v).
Definition g_last_counter (B : list byte) : Z := u_at B OFF_g_last_counter 4.
Definition set_g_last_counter (B : list byte) (v : Z) : list byte := upd B OFF_g_last_counter (put 4 v).
Definition g_rx_send (B : list byte) : Z := u_at B OFF_g_rx_send 4.
Definition set_g_rx_send (B : list byte) (v : Z) : list byte := upd B OFF_g_rx_send (put 4 v).
Definition g_ncmd (B : list byte) : Z := u_at B OFF_g_ncmd 4.
Definition set_g_ncmd (B : list byte) (v : Z) : list byte := upd B OFF_g_ncmd (put 4 v).
Definition g_nq (B : list byte) : Z := u_at B OFF_g_nq 4.
Definition set_g_nq (B : list byte) (v : Z) : list byte := upd B OFF_g_nq (put 4 v).
Definition g_rx (B : list byte) : Z := u_at B OFF_g_rx 8.
Definition set_g_rx (B : list byte) (v : Z) : list byte := upd B OFF_g_rx (put 8 v).
Definition g_rx_len (B : list byte) : Z := u_at B OFF_g_rx_len 8.
Definition set_g_rx_len (B : list byte) (v : Z) : list byte := upd B OFF_g_rx_len (put 8 v).
Definition g_rx_fail (B : list byte) : Z := s32_at B OFF_g_rx_fail.
Definition set_g_rx_fail (B : list byte) (v : Z) : list byte := upd B OFF_g_rx_fail (put 4 v).
Definition g_rx_times (B : list byte) : Z := s32_at B OFF_g_rx_times.
Definition set_g_rx_times (B : list byte) (v : Z) : list byte := upd B OFF_g_rx_times (put 4 v).
(* g_fail_next: the int was shrunk by the compiler to ONE byte holding 0 or 1 (DWARF value expression
   DW_OP_deref_size 1 ... stack_value); the model reads and writes that byte. *)
Definition g_fail_next (B : list byte) : Z := u_at B OFF_g_fail_next 1.
Definition set_g_fail_next (B : list byte) (v : Z) : list byte := upd B OFF_g_fail_next (put 1 v).
