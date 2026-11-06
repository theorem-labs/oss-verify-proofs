(* transport/src/diginet_session.c: set_state (:79-86), send_raw (:88-94), send_control (:97-109),
   diginet_session_wake (:119-145), diginet_session_close (:147-158), session_lost (:160-165), find_mac (:168-174),
   maybe_online (:176-182), on_announce (:184-221), on_ack (:223-237), on_data (:239-261),
   diginet_session_rx (:263-318), send_data (:388-401), retransmit (:403-412), diginet_session_tick (:414-472),
   diginet_session_poll (:505-527). The conventions of TSess0.v.

   Every function that can reach a callback takes (I : timg) (F : option tframe) before the world B and hands
   them on (F reaches notice_m and io_recv_m). A call through s->notify, s->io.send, s->io.recv or
   s->io.now_us reads the pointer from the world and is the harness model's (TCb.v) when it equals the timg
   address, else None (the run is then outside the model); the call_ helpers below are that test.
   A struct diginet_frame f that diginet_frame_parse filled from buf (fr_code buf = 0) is given as buf:
   each field is DgnSpec's fr_<field> buf, and f->body points into buf.
   None: everything the callee models are None for (abort() in a check of the harness, a UBSan trap); the
   function-pointer test above; and the cases each definition names. The session's own code here has no other
   UBSan-trapped operation: its integers are unsigned or never overflow, and its fixed indices
   (inflight_frame[26], [27]) are in range. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb.
Import ListNotations.
Open Scope Z_scope.

(* ---- calls through the session's function pointers ---- *)

(* s->notify (s->notify_ctx, &n): the harness's notice (fuzz_transport.c:937) ignores ctx *)
Definition call_notify (I : timg) (F : option tframe) (B : list byte) (n : ntc) : option (list byte * unit) :=
  if S_notify B =? ti_notice I then notice_m I F B n else None.

(* s->io.send (s->io.ctx, frame, length frame): io_send (fuzz_transport.c:823) *)
Definition call_send (I : timg) (B : list byte) (frame : list byte) : option (list byte * Z) :=
  if S_io_send B =? ti_io_send I then io_send_m I B frame else None.

(* s->io.recv (s->io.ctx, buf, cap, timeout): io_recv (fuzz_transport.c:906), which reads neither ctx nor the
   timeout (:908-909); result: the world, the return value, the bytes it copied into buf *)
Definition call_recv (I : timg) (F : option tframe) (B : list byte) (cap : Z) : option (list byte * Z * list byte) :=
  if S_io_recv B =? ti_io_recv I then io_recv_m I F B cap else None.

(* s->io.now_us (s->io.ctx): io_now (fuzz_transport.c:931), which writes nothing *)
Definition call_now (I : timg) (B : list byte) : option Z :=
  if S_io_now_us B =? ti_io_now I then Some (io_now_m B) else None.

(* BROADCAST (diginet_session.c:9) *)
Definition BROADCAST : list byte := bs [0xff; 0xff; 0xff; 0xff; 0xff; 0xff].

(* the s->inflight_len bytes at s->inflight_frame, which send_raw hands to io.send (:400, :411). None when
   s->inflight_len exceeds the array (sizeof inflight_frame = DIGINET_MAX_FRAME_LEN = 1514): the run is then outside
   the model; every value the session stores in inflight_len is a frame length <= 1514 (:140, :397). *)
Definition inflight_bytes (B : list byte) : option (list byte) :=
  if 1514 <? S_inflight_len B then None
  else Some (sub B A_S_inflight_frame (Z.to_nat (S_inflight_len B))).

(* ---- set_state (:79-86) ---- *)
Definition set_state_m (I : timg) (F : option tframe) (B : list byte) (st why : Z) : option (list byte * unit) :=
  if S_state B =? st then Some (B, tt)                                                   (* :81-82 *)
  else
    let n := Ntc DIGINET_N_STATE st (S_state B) why 0 0 0 0 None [] 0 in               (* :83 *)
    call_notify I F (set_S_state B st) n.                                                (* :84-85 *)

(* ---- send_raw (:88-94); frame = the len bytes it sends ---- *)
Definition send_raw_m (I : timg) (F : option tframe) (B : list byte) (frame : list byte) : option (list byte * Z) :=
  match call_send I B frame with                                                         (* :90 *)
  | None => None
  | Some (B1, r) =>
      if r =? 0 then Some (set_S_stats_tx_frames B1 (u64 (S_stats_tx_frames B1 + 1)), r)   (* :91-92 *)
      else Some (B1, r)                                                                  (* :93 *)
  end.

(* ---- send_control (:97-109) ----
   cmd is the uint8_t, ack_counter the uint32_t. f is the local uint8_t[60] (:99). Result R = (the return value,
   the 60 bytes of f once the build succeeded, [] when it failed): what `if (keep) memcpy (keep, f, n)`
   (:104-106) copies, for the one caller that passes keep (diginet_session_wake). *)
Definition send_control_m (I : timg) (F : option tframe) (B : list byte) (cmd ack_counter : Z)
    : option (list byte * (Z * list byte)) :=
  let mode := S_cfg_sum_mode B in
  (* :100 h = { .send_counter = s->host_counter, .ack_counter, .cmd }, the rest 0; :101 the build, no body *)
  let n := diginet_frame_build_code [] DIGINET_MIN_FRAME_LEN mode in
  if n <? 0 then Some (B, (n, []))                                                       (* :102-103 *)
  else
    let f := lib_frame (S_desk_mac B) (S_cfg_host_mac B) (S_host_counter B) ack_counter 0 cmd 0 [] mode in
    match send_raw_m I F B f with                                                        (* :108, (size_t)n bytes *)
    | None => None
    | Some (B1, r) => Some (B1, (r, f))
    end.

(* ---- session_lost (:160-165) ---- *)
Definition session_lost_m (I : timg) (F : option tframe) (B : list byte) (why : Z) : option (list byte * unit) :=
  let B := set_S_inflight B 0 in                                                         (* :162 *)
  let B := set_S_desk_counter_valid B 0 in                                               (* :163 *)
  set_state_m I F B DIGINET_S_IDLE why.                                                  (* :164 *)

(* ---- diginet_session_wake (:119-145), now_us a uint64_t ---- *)
Definition diginet_session_wake_m (I : timg) (F : option tframe) (B : list byte) (now : Z) : option (list byte * Z) :=
  (* :121-122 !s is false *)
  if S_desk_known B =? 0 then Some (B, DIGINET_E_ARG)                                    (* :123-124 *)
  else if negb (S_foreign B =? 0) then
    Some (set_S_stats_refused B (u64 (S_stats_refused B + 1)), DIGINET_E_REFUSED)        (* :125-128 *)
  else
    let B := set_S_e1_named_us B 0 in                                                     (* :129 *)
    let B := set_S_wake_acked B 0 in                                                      (* :130 *)
    let B := set_S_wake_sent_us B now in                                                  (* :131 *)
    (* :134-136: e2[60], e2_len, r = send_control (s, DIGINET_CMD_WAKE, 0, e2, &e2_len) *)
    match send_control_m I F B DIGINET_CMD_WAKE 0 with
    | None => None
    | Some (B, (r, e2)) =>
        if r <? 0 then Some (B, r)                                                        (* :137-138 *)
        else
          let B := set_S_inflight_frame B e2 in                                           (* :139 memcpy, e2_len = 60 *)
          let B := set_S_inflight_len B (Z.of_nat (length e2)) in                         (* :140 *)
          let B := set_S_stats_tx_wakes B (u64 (S_stats_tx_wakes B + 1)) in               (* :141 *)
          match inflight_start_m B (S_host_counter B) now with                            (* :142 *)
          | None => None
          | Some (B, _) =>
              match set_state_m I F B DIGINET_S_WAKING DIGINET_R_WAKE with                (* :143 *)
              | None => None
              | Some (B, _) => Some (B, DIGINET_OK)                                       (* :144 *)
              end
          end
    end.

(* ---- diginet_session_close (:147-158) ---- *)
Definition diginet_session_close_m (I : timg) (F : option tframe) (B : list byte) (now : Z) : option (list byte * Z) :=
  (* :149 (void)now_us; :150-151 !s is false; :152 r = 0 *)
  let sent :=
    if negb (S_desk_known B =? 0) && (S_foreign B =? 0) && negb (S_state B =? DIGINET_S_CLOSED)   (* :153 *)
    then match send_control_m I F B DIGINET_CMD_DISCONNECT 0 with                         (* :154 *)
         | None => None
         | Some (B1, (r, _)) => Some (B1, r)
         end
    else Some (B, 0) in
  match sent with
  | None => None
  | Some (B1, r) =>
      match set_state_m I F (set_S_inflight B1 0) DIGINET_S_CLOSED DIGINET_R_CLOSED with  (* :155-156 *)
      | None => None
      | Some (B2, _) => Some (B2, r)                                                      (* :157 *)
      end
  end.

(* ---- find_mac (:168-174) ----
   a = on_announce's local announce: unknown = the frame body (its first 15 bytes are what the loop reads),
   unknown_len = 15 (src/diginet_frame.c:146-147); given as those bytes and that length. mac = the 6 bytes of
   s->cfg.host_mac. Result: the int i, or -1. No world, no trap: a value. *)

(* :170-172 for (size_t i = 0; i + 6 <= a->unknown_len; i++) if (!memcmp (a->unknown + i, mac, 6)) return (int)i;
   fuel = the turns left, unknown_len - 5 - i *)
Fixpoint find_mac_loop (unknown mac : list byte) (i : Z) (fuel : nat) : Z :=
  match fuel with
  | O => -1                                             (* i + 6 > unknown_len: the test of :170 fails; :173 *)
  | S f =>
      if memeq 6 (skipn (Z.to_nat i) unknown) mac then i                     (* :171-172, (int)i for i <= 9 *)
      else find_mac_loop unknown mac (i + 1) f
  end.

Definition find_mac_m (unknown : list byte) (unknown_len : Z) (mac : list byte) : Z :=
  find_mac_loop unknown mac 0 (Z.to_nat (unknown_len - DIGINET_MAC_LEN + 1)).

(* ---- maybe_online (:176-182) ---- *)
Definition maybe_online_m (I : timg) (F : option tframe) (B : list byte) : option (list byte * unit) :=
  if (S_state B =? DIGINET_S_WAKING) && negb (S_wake_acked B =? 0) && negb (S_e1_named_us B =? 0) then  (* :178 *)
    let B := set_S_next_keepalive_us B (u64 (S_last_rx_us B + ms_m (S_cfg_keepalive_ms B))) in          (* :179 *)
    set_state_m I F B DIGINET_S_ONLINE DIGINET_R_ONLINE                                                 (* :180 *)
  else Some (B, tt).

(* ---- on_announce (:184-221), f given as buf ----
   a = the local struct diginet_announce diginet_announce_parse (src/diginet_frame.c:138-151) fills: unknown =
   f->body, unknown_len = 15, version / name = copy_strz of at most 9 bytes at body + 15 / body + 24 into
   10-byte arrays (:148-149). The notices carry a as notice() reads it (TImg.v tann): each array's string and
   then its NUL, the bytes copy_strz writes (ann_field); the rest of each array is never written and notice()
   reads no byte after the NUL. n.personality is the address of personalities[i] (24-byte entries), 0 = NULL. *)
Definition ann_field (src : list byte) : list byte := firstn (copy_len 10 9 src) src ++ [b8 0].

Definition on_announce_m (I : timg) (F : option tframe) (B : list byte) (buf : list byte) (now : Z)
    : option (list byte * unit) :=
  let cmd := fr_cmd buf in
  let body := fr_body buf in
  if negb (ann_code cmd (fr_body_len buf) =? DIGINET_OK) then                            (* :187 *)
    Some (set_S_stats_rx_ignored B (u64 (S_stats_rx_ignored B + 1)), tt)                 (* :188-189 *)
  else
  let ann := TAnn (ann_field (skipn 15 body)) (ann_field (skipn 24 body)) in
  let name := skipn 24 body in
  let p := diginet_personality_from_name (firstn (copy_len 10 9 name) name) in          (* :191, a.name *)
  let pv := match p with Some i => ti_personalities I + 24 * i | None => 0 end in
  let B := match p with Some _ => set_S_personality B pv | None => B end in              (* :192-193 *)
  let off := if cmd =? DIGINET_CMD_ANNOUNCE_SESSION
             then find_mac_m (ann_unknown body) 15 (S_cfg_host_mac B) else -1 in        (* :194 *)
  let n := Ntc DIGINET_N_DESK (S_state B) 0 0 0 0 off pv (Some ann) [] 0 in             (* :196-197 *)
  match call_notify I F B n with                                                          (* :198 *)
  | None => None
  | Some (B, _) =>
      if cmd =? DIGINET_CMD_ANNOUNCE then                                                 (* :200 *)
        let B := set_S_foreign B 0 in                                                     (* :201 *)
        let lost := if S_state B =? DIGINET_S_ONLINE
                    then session_lost_m I F B DIGINET_R_DESK_OFFLINE else Some (B, tt) in (* :202-203 *)
        match lost with
        | None => None
        | Some (B, _) =>
            if (S_state B =? DIGINET_S_IDLE) && negb (S_cfg_auto_wake B =? 0) then        (* :204 *)
              match diginet_session_wake_m I F B now with                                 (* :205, result unused *)
              | None => None
              | Some (B, _) => Some (B, tt)
              end
            else Some (B, tt)                                                             (* :206 *)
        end
      else if 0 <=? off then                                                              (* :209-210 e1 *)
        let B := set_S_foreign B 0 in                                                     (* :211 *)
        let B := set_S_e1_named_us B 1 in                                                 (* :212 *)
        maybe_online_m I F B                                                              (* :213-214 *)
      else
        let B := set_S_foreign B 1 in                                                     (* :216 *)
        let fn := Ntc DIGINET_N_FOREIGN (S_state B) 0 0 0 0 0 0 (Some ann) [] 0 in        (* :217 *)
        match call_notify I F B fn with                                                   (* :218 *)
        | None => None
        | Some (B, _) =>
            if (S_state B =? DIGINET_S_ONLINE) || (S_state B =? DIGINET_S_WAKING)
            then session_lost_m I F B DIGINET_R_FOREIGN else Some (B, tt)                 (* :219-220 *)
        end
  end.

(* ---- on_ack (:223-237), f given as buf ---- *)
Definition on_ack_m (I : timg) (F : option tframe) (B : list byte) (buf : list byte) : option (list byte * unit) :=
  if (S_inflight B =? 0) || negb (fr_ack buf =? S_inflight_counter B) then               (* :225 *)
    Some (set_S_stats_rx_ignored B (u64 (S_stats_rx_ignored B + 1)), tt)                 (* :226-227 *)
  else
    let B := set_S_inflight B 0 in                                                        (* :229 *)
    let n := Ntc DIGINET_N_ACKED (S_state B) 0 0 (fr_ack buf) (u16 (S_inflight_retries B)) 0 0 None [] 0 in  (* :230-231 *)
    match call_notify I F B n with                                                        (* :232 *)
    | None => None
    | Some (B, _) =>
        if S_state B =? DIGINET_S_WAKING then maybe_online_m I F (set_S_wake_acked B 1)   (* :233-235 *)
        else Some (B, tt)
    end.

(* ---- on_data (:239-261), f given as buf, now a uint64_t ---- *)
Definition on_data_m (I : timg) (F : option tframe) (B : list byte) (buf : list byte) (now : Z)
    : option (list byte * unit) :=
  match send_control_m I F B DIGINET_CMD_ACK (fr_send buf) with                           (* :242 *)
  | None => None
  | Some (B, (r, _)) =>
      let B := if r =? 0 then set_S_stats_tx_acks B (u64 (S_stats_tx_acks B + 1)) else B in    (* :242-243 *)
      let B := set_S_stats_rx_data B (u64 (S_stats_rx_data B + 1)) in                    (* :244 *)
      let retry := fr_retry buf in
      let B := if retry =? 0 then B
               else let B := set_S_stats_rx_desk_retries B (u64 (S_stats_rx_desk_retries B + 1)) in   (* :245-246 *)
                    set_S_backoff_until_us B (u64 (now + ms_m (S_cfg_backoff_ms B))) in   (* :247 *)
      if negb (S_desk_counter_valid B =? 0) && (fr_send buf =? S_desk_counter B) && negb (retry =? 0) then  (* :249 *)
        Some (set_S_stats_rx_duplicates B (u64 (S_stats_rx_duplicates B + 1)), tt)       (* :250-251 *)
      else
        let B := set_S_desk_counter B (fr_send buf) in                                    (* :253 *)
        let B := set_S_desk_counter_valid B 1 in                                          (* :254 *)
        if fr_keepalive buf then Some (B, tt)                                             (* :255-256 *)
        else
          let n := Ntc DIGINET_N_DATA (S_state B) 0 0 (fr_send buf) retry 0 0 None
                       (fr_body buf) (fr_body_len buf) in                                 (* :257-259 *)
          call_notify I F B n                                                             (* :260 *)
  end.

(* ---- send_data (:388-401) ----
   body = the body_len bytes at the caller's body (tick's local body[], or its keepalive byte ka); ncmds the
   unsigned, now the uint64_t. The frame is built into s->inflight_frame (sizeof 1514). *)
Definition send_data_m (I : timg) (F : option tframe) (B : list byte) (body : list byte) (ncmds now : Z)
    : option (list byte * Z) :=
  (* :390 h = { .cmd = DIGINET_CMD_DATA, .num_commands = (uint8_t)ncmds }, the rest 0 *)
  let B := set_S_host_counter B (u32 (S_host_counter B + ncmds)) in                       (* :391 *)
  let send := S_host_counter B in                                                          (* :392 *)
  let mode := S_cfg_sum_mode B in
  let n := diginet_frame_build_code body DIGINET_MAX_FRAME_LEN mode in                     (* :393-394 *)
  if n <? 0 then Some (B, n)                                                               (* :395-396 *)
  else
    let B := set_S_inflight_frame B
               (lib_frame (S_desk_mac B) (S_cfg_host_mac B) send 0 0 DIGINET_CMD_DATA (u8 ncmds) body mode) in
    let B := set_S_inflight_len B n in                                                     (* :397 *)
    match inflight_start_m B (S_host_counter B) now with                                   (* :398 *)
    | None => None
    | Some (B, _) =>
        let B := set_S_stats_tx_data B (u64 (S_stats_tx_data B + 1)) in                    (* :399 *)
        match inflight_bytes B with
        | None => None
        | Some fr => send_raw_m I F B fr                                                    (* :400 *)
        end
    end.

(* ---- retransmit (:403-412), now a uint64_t ---- *)
Definition retransmit_m (I : timg) (F : option tframe) (B : list byte) (now : Z) : option (list byte * Z) :=
  let B := set_S_inflight_retries B (u32 (S_inflight_retries B + 1)) in                   (* :405 *)
  let retry := u16 (S_inflight_retries B) in                                               (* :406 *)
  let B := upd B (A_S_inflight_frame + DIGINET_ETH_HDR_LEN + 12) (put 1 (u8 (Z.shiftr retry 8))) in   (* :407 *)
  let B := upd B (A_S_inflight_frame + DIGINET_ETH_HDR_LEN + 13) (put 1 (u8 retry)) in    (* :408 *)
  let B := set_S_inflight_sent_us B now in                                                 (* :409 *)
  let B := set_S_stats_tx_retransmits B (u64 (S_stats_tx_retransmits B + 1)) in           (* :410 *)
  match inflight_bytes B with
  | None => None
  | Some fr => send_raw_m I F B fr                                                          (* :411 *)
  end.

(* ---- diginet_session_tick (:414-472), now a uint64_t ---- *)
Definition diginet_session_tick_m (I : timg) (F : option tframe) (B : list byte) (now : Z) : option (list byte * Z) :=
  (* :416-417 !s is false *)
  let st := S_state B in
  if (st =? DIGINET_S_CLOSED) || (st =? DIGINET_S_IDLE) then Some (B, DIGINET_OK)         (* :418-419 *)
  else if (st =? DIGINET_S_WAKING) && (ms_m (S_cfg_wake_timeout_ms B) <=? u64 (now - S_wake_sent_us B)) then  (* :421 *)
    match session_lost_m I F B DIGINET_R_WAKE_TIMEOUT with                                 (* :422 *)
    | None => None
    | Some (B, _) => Some (B, DIGINET_OK)                                                  (* :423 *)
    end
  else if (st =? DIGINET_S_ONLINE) && (ms_m (S_cfg_offline_ms B) <=? u64 (now - S_last_rx_us B)) then  (* :425 *)
    match session_lost_m I F B DIGINET_R_SILENCE with                                      (* :426 *)
    | None => None
    | Some (B, _) => Some (B, DIGINET_OK)                                                  (* :427 *)
    end
  else
  (* :430-443; inl = the return of :434, inr = on to :445 *)
  let step :=
    if negb (S_inflight B =? 0) && (ms_m (S_cfg_ack_timeout_ms B) <=? u64 (now - S_inflight_sent_us B)) then  (* :430 *)
      if S_inflight_retries B <? S_cfg_max_retries B then                                  (* :431 *)
        match retransmit_m I F B now with                                                  (* :432 *)
        | None => None
        | Some (B, r) => if r <? 0 then Some (inl (B, r)) else Some (inr B)                (* :433-434 *)
        end
      else
        let B := set_S_inflight B 0 in                                                     (* :436 *)
        let B := set_S_stats_ack_lost B (u64 (S_stats_ack_lost B + 1)) in                  (* :437 *)
        let n := Ntc DIGINET_N_ACK_LOST (S_state B) 0 0 (S_inflight_counter B) (u16 (S_inflight_retries B))
                     0 0 None [] 0 in                                                      (* :438-440 *)
        match call_notify I F B n with                                                     (* :441 *)
        | None => None
        | Some (B, _) => Some (inr B)
        end
    else Some (inr B) in
  match step with
  | None => None
  | Some (inl (B, r)) => Some (B, r)
  | Some (inr B) =>
      if negb (S_state B =? DIGINET_S_ONLINE) || negb (S_inflight B =? 0) || (now <? S_backoff_until_us B) then
        Some (B, DIGINET_OK)                                                               (* :445-446 *)
      else if S_next_keepalive_us B <=? now then                                           (* :449 *)
        let B := set_S_next_keepalive_us B (u64 (S_next_keepalive_us B + ms_m (S_cfg_keepalive_ms B))) in  (* :451 *)
        let B := if S_next_keepalive_us B <=? now
                 then set_S_next_keepalive_us B (u64 (now + ms_m (S_cfg_keepalive_ms B))) else B in   (* :452-453 *)
        let B := set_S_stats_tx_keepalives B (u64 (S_stats_tx_keepalives B + 1)) in       (* :454 *)
        send_data_m I F B [b8 0] 1 now                                                     (* :450 ka = 0x00; :455 *)
      else if S_queued B =? 0 then Some (B, DIGINET_OK)                                    (* :458-459 *)
      else
        let allow := int_of_bool ((S_display_sent B =? 0) ||
                                  (S_cfg_display_gap_us B <=? u64 (now - S_last_display_us B))) in   (* :460 *)
        match take_m B allow with                                                          (* :461-464 *)
        | None => None
        | Some (B, (body, body_len, has_display, n)) =>
            if n =? 0 then Some (B, DIGINET_OK)                                            (* :465-466 *)
            else
              let B := if has_display =? 0 then B
                       else set_S_last_display_us (set_S_display_sent B 1) now in          (* :467-470 *)
              send_data_m I F B (firstn (Z.to_nat body_len) body) n now                    (* :471 *)
        end
  end.

(* ---- diginet_session_rx (:263-318) ----
   buf = the len bytes the caller passes (len = length buf): receive's heap frame (fuzz_transport.c:1021) or
   poll's local buf (:521, :525), never NULL; now_us a uint64_t. f is the local struct diginet_frame (:265). *)
Definition diginet_session_rx_m (I : timg) (F : option tframe) (B : list byte) (buf : list byte) (now : Z)
    : option (list byte * Z) :=
  (* :266-267 !s, !buf are false *)
  let r := fr_code buf in                                                                  (* :268 *)
  if negb (r =? DIGINET_OK) then
    Some (set_S_stats_rx_ignored B (u64 (S_stats_rx_ignored B + 1)), r)                    (* :269-272 *)
  else
  let src := fr_src buf in
  let dst := fr_dst buf in
  let cmd := fr_cmd buf in
  let ignored (B : list byte) := Some (set_S_stats_rx_ignored B (u64 (S_stats_rx_ignored B + 1)), DIGINET_OK) in
  (* :293-317, once the source is the desk's *)
  let accept (B : list byte) :=
    if S_state B =? DIGINET_S_CLOSED then Some (B, DIGINET_OK)                             (* :293-294 *)
    else
    let B := set_S_stats_rx_frames B (u64 (S_stats_rx_frames B + 1)) in                   (* :296 *)
    let B := set_S_last_rx_us B now in                                                     (* :297 *)
    let sw :=                                                                              (* :298-316 *)
      if (cmd =? DIGINET_CMD_ANNOUNCE) || (cmd =? DIGINET_CMD_ANNOUNCE_SESSION)
      then on_announce_m I F B buf now                                                     (* :299-302 *)
      else if cmd =? DIGINET_CMD_ACK then on_ack_m I F B buf                               (* :303-305 *)
      else if cmd =? DIGINET_CMD_DATA then on_data_m I F B buf now                         (* :306-308 *)
      else if cmd =? DIGINET_CMD_DISCONNECT then                                           (* :309-312 *)
        (if (S_state B =? DIGINET_S_ONLINE) || (S_state B =? DIGINET_S_WAKING)
         then session_lost_m I F B DIGINET_R_DESK_DISCONNECT else Some (B, tt))
      else Some (set_S_stats_rx_ignored B (u64 (S_stats_rx_ignored B + 1)), tt) in        (* :313-315 *)
    match sw with
    | None => None
    | Some (B, _) => diginet_session_tick_m I F B now                                      (* :317 *)
    end in
  if memeq 6 src (S_cfg_host_mac B) ||
     (negb (memeq 6 dst (S_cfg_host_mac B)) && negb (memeq 6 dst BROADCAST)) then ignored B   (* :273-277 *)
  else if negb (S_desk_known B =? 0) then                                                  (* :278 *)
    if negb (memeq 6 src (S_desk_mac B)) then ignored B else accept B                      (* :279-282 *)
  else if negb ((cmd =? DIGINET_CMD_ANNOUNCE) || (cmd =? DIGINET_CMD_ANNOUNCE_SESSION)) then
    Some (B, DIGINET_OK)                                                                   (* :284-285 *)
  else if negb (oui_of src) then ignored B                                                 (* :286-289 *)
  else accept (set_S_desk_known (set_S_desk_mac B src) 1).                                 (* :290-291 *)

(* ---- diginet_session_poll (:505-527) ----
   buf is poll's local uint8_t[1514] (:507); what io_recv copies into it is the bytes io_recv_m returns, and rx
   reads only those (its len is recv's result).
   The drain loop (:524-525): while ((r = recv (ctx, buf, 1514, 0)) > 0) rx (s, buf, r, now_us (ctx)); then
   :526 return r < 0 ? r : 0. Its bound is on the recv side: the harness's io_recv (fuzz_transport.c:906-929)
   hands over a frame only while g_rx_times != 0 and decrements g_rx_times each time, and nothing else the loop
   runs (rx, the notices and sends it makes) writes g_rx_times. So with g_rx_times >= 0 when the loop starts, recv
   hands over at most g_rx_times frames and the loop makes at most g_rx_times turns: the fuel is
   Z.to_nat (g_rx_times B) at the loop's start. Out of fuel while recv hands over one more frame means
   g_rx_times < 0 at the start: the C then goes on until g_rx_times-- overflows INT_MIN (a UBSan trap, None in
   io_recv_m) or a check aborts, so None. *)
Fixpoint poll_drain_m (I : timg) (F : option tframe) (B : list byte) (fuel : nat) {struct fuel}
    : option (list byte * Z) :=
  match call_recv I F B DIGINET_MAX_FRAME_LEN with                                         (* :524 *)
  | None => None
  | Some (B, r, bytes) =>
      if 0 <? r then
        match fuel with
        | O => None                                     (* more frames than g_rx_times: see above *)
        | S f =>
            match call_now I B with                                                         (* :525 now_us *)
            | None => None
            | Some now =>
                match diginet_session_rx_m I F B bytes now with                             (* :525 *)
                | None => None
                | Some (B, _) => poll_drain_m I F B f
                end
            end
        end
      else Some (B, if r <? 0 then r else 0)                                                (* :526 *)
  end.

Definition diginet_session_poll_m (I : timg) (F : option tframe) (B : list byte) (max_wait_ms : Z)
    : option (list byte * Z) :=
  (* :508 !s is false *)
  if (S_io_recv B =? 0) || (S_io_now_us B =? 0) then Some (B, DIGINET_E_ARG)               (* :508-509 *)
  else
  match call_now I B with                                                                   (* :510 *)
  | None => None
  | Some now =>
  match diginet_session_deadline_m B now with                                               (* :511 *)
  | None => None
  | Some due =>
  let wait_us := if now <? due then due - now else 0 in                                     (* :512 *)
  let wait := s32 (u32 (u64 (wait_us + 999) / 1000)) in       (* :513, (int) of a uint64_t: its low 32 bits *)
  let wait := if (0 <=? max_wait_ms) && (max_wait_ms <? wait) then max_wait_ms else wait in (* :514-515 *)
  (* :516 recv (ctx, buf, sizeof buf, wait): io_recv does not read the timeout *)
  match call_recv I F B DIGINET_MAX_FRAME_LEN with
  | None => None
  | Some (B, r, bytes) =>
  if r <? 0 then Some (B, r)                                                                (* :517-518 *)
  else
  match call_now I B with                                                                   (* :519 *)
  | None => None
  | Some now =>
  match (if 0 <? r then diginet_session_rx_m I F B bytes now else Some (B, DIGINET_OK)) with  (* :520-521 *)
  | None => None
  | Some (B, _) =>
  match diginet_session_tick_m I F B now with                                               (* :522 *)
  | None => None
  | Some (B, _) => poll_drain_m I F B (Z.to_nat (g_rx_times B))                             (* :523-526 *)
  end end end end end end.
