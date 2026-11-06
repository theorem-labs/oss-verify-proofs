(* diginet_session_tick (diginet_session.c:414-472, TSess.v diginet_session_tick_m) cut at its C structure:
   tick_step_m = the in-flight step (:430-443: retransmit, or drop and N_ACK_LOST), tick_tail_m = what follows
   (:445-471), itself cut into tick_ka_m (the keepalive, :449-456) and tick_take_m (take and send, :460-471).
   tick_unfold: the model of the tick is these pieces (by conversion).
   R_tick: the bytes a tick may write, library and harness model together: M but M.fail, g_s, g_cmd, g_q,
   g_fail_next (FT:829), g_last_counter and g_nq (FT:623, :850, :868). Outside it: M.fail, g_raw, g_ncmd,
   g_rx_send, g_rx_fail, g_rx_times, g_now, g_rx, g_rx_len, g_cfg, GOT, OW.
   tick_post: what holds after a tick that started in agree_core at the current time. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree SettleOk SimLib.
Import ListNotations.
Open Scope Z_scope.

(* :449-456, once the keepalive is due *)
Definition tick_ka_m (I : timg) (F : option tframe) (B : list byte) (now : Z) : option (list byte * Z) :=
  let B := set_S_next_keepalive_us B (u64 (S_next_keepalive_us B + ms_m (S_cfg_keepalive_ms B))) in
  let B := if S_next_keepalive_us B <=? now
           then set_S_next_keepalive_us B (u64 (now + ms_m (S_cfg_keepalive_ms B))) else B in
  let B := set_S_stats_tx_keepalives B (u64 (S_stats_tx_keepalives B + 1)) in
  send_data_m I F B [b8 0] 1 now.

(* :460-471, once the queue is not empty *)
Definition tick_take_m (I : timg) (F : option tframe) (B : list byte) (now : Z) : option (list byte * Z) :=
  let allow := int_of_bool ((S_display_sent B =? 0) ||
                            (S_cfg_display_gap_us B <=? u64 (now - S_last_display_us B))) in
  match take_m B allow with
  | None => None
  | Some (B, (body, body_len, has_display, n)) =>
      if n =? 0 then Some (B, DIGINET_OK)
      else
        let B := if has_display =? 0 then B
                 else set_S_last_display_us (set_S_display_sent B 1) now in
        send_data_m I F B (firstn (Z.to_nat body_len) body) n now
  end.

(* :445-471 *)
Definition tick_tail_m (I : timg) (F : option tframe) (B : list byte) (now : Z) : option (list byte * Z) :=
  if negb (S_state B =? DIGINET_S_ONLINE) || negb (S_inflight B =? 0) || (now <? S_backoff_until_us B) then
    Some (B, DIGINET_OK)
  else if S_next_keepalive_us B <=? now then tick_ka_m I F B now
  else if S_queued B =? 0 then Some (B, DIGINET_OK)
  else tick_take_m I F B now.

(* :430-443; inl = the return of :434, inr = on to :445 *)
Definition tick_step_m (I : timg) (F : option tframe) (B : list byte) (now : Z)
    : option ((list byte * Z) + list byte) :=
  if negb (S_inflight B =? 0) && (ms_m (S_cfg_ack_timeout_ms B) <=? u64 (now - S_inflight_sent_us B)) then
    if S_inflight_retries B <? S_cfg_max_retries B then
      match retransmit_m I F B now with
      | None => None
      | Some (B, r) => if r <? 0 then Some (inl (B, r)) else Some (inr B)
      end
    else
      let B := set_S_inflight B 0 in
      let B := set_S_stats_ack_lost B (u64 (S_stats_ack_lost B + 1)) in
      let n := Ntc DIGINET_N_ACK_LOST (S_state B) 0 0 (S_inflight_counter B) (u16 (S_inflight_retries B))
                   0 0 None [] 0 in
      match call_notify I F B n with
      | None => None
      | Some (B, _) => Some (inr B)
      end
  else Some (inr B).

Lemma tick_unfold : forall I F B now, diginet_session_tick_m I F B now =
  if (S_state B =? DIGINET_S_CLOSED) || (S_state B =? DIGINET_S_IDLE) then Some (B, DIGINET_OK)
  else if (S_state B =? DIGINET_S_WAKING) && (ms_m (S_cfg_wake_timeout_ms B) <=? u64 (now - S_wake_sent_us B)) then
    match session_lost_m I F B DIGINET_R_WAKE_TIMEOUT with
    | None => None
    | Some (B, _) => Some (B, DIGINET_OK)
    end
  else if (S_state B =? DIGINET_S_ONLINE) && (ms_m (S_cfg_offline_ms B) <=? u64 (now - S_last_rx_us B)) then
    match session_lost_m I F B DIGINET_R_SILENCE with
    | None => None
    | Some (B, _) => Some (B, DIGINET_OK)
    end
  else
    match tick_step_m I F B now with
    | None => None
    | Some (inl (B, r)) => Some (B, r)
    | Some (inr B) => tick_tail_m I F B now
    end.
Proof. intros. reflexivity. Qed.

(* the bytes a tick may write (see the header) *)
Definition R_tick (a : Z) : Prop :=
  (OFF_M <= a < A_M_fail) \/ (A_M_fail + 4 <= a < OFF_g_raw) \/ (OFF_g_last_counter <= a < OFF_g_ncmd).

(* after a tick that started in agree_core at the current time *)
Record tick_post (I : timg) (ops : Z) (B B' : list byte) : Prop := {
  tp_core : agree_core I ops B';
  tp_keepalive : c2_keepalive B';
  tp_drain : drain_fact B';
  tp_frame : wframe R_tick B B';
  tp_fail : g_fail_next B' = g_fail_next B \/ g_fail_next B' = 0;
}.
