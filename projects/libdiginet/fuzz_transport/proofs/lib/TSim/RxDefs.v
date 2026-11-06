(* m_rx_m (TCb.v, fuzz_transport.c:280-375) and diginet_session_rx_m (TSess.v, diginet_session.c:263-318) bind
   their switch and their accept path with local `let`s. The rx simulation states one lemma per branch, so it
   needs those pieces as top-level functions: each definition below is the let-bound body, verbatim, and the two
   equations m_rx_m_eq / diginet_session_rx_m_eq hold by conversion. Nothing here is new behaviour. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess.
Import ListNotations.
Open Scope Z_scope.

Local Notation "'let*' p ':=' c1 'in' c2" := (match c1 with Some p => c2 | None => None end)
  (at level 200, p pattern, c1 at level 200, c2 at level 200).

(* ---- the model, m_rx (FT:280-375), over the heap frame fr read as n bytes ---- *)

(* FT:302-372, the switch on f.cmd (m_rx_m's `sw`) *)
Definition m_rx_sw (I : timg) (fr : tframe) (n : Z) (B2 : list byte) : option (list byte * unit) :=
  let bytes := tf_bytes fr in
  let f := spec_read_frame (zs bytes) n in
  let fc := sf_cmd f in
  let bodyp := tf_addr fr + sf_body f in
  let body := skipn (Z.to_nat (sf_body f)) bytes in
  let blen := sf_body_len f in
      if (fc =? SPEC_CMD_E0) || (fc =? SPEC_CMD_E1) then
        if blen <? SPEC_ANN_MIN then Some (B2, tt) else
        let* (_, off) := if fc =? SPEC_CMD_E1 then host_offset_m B2 body else Some (B2, -1) in
        let* d := int_inc (OW_desk B2) in
        let B3 := set_OW_desk_off (set_OW_desk B2 d) off in
        let* (_, dp) := desk_named_m I B3 body in
        let B4 := set_OW_desk_body (set_OW_desk_p B3 dp) bodyp in
        if fc =? SPEC_CMD_E0 then
          let B5 := set_M_foreign B4 0 in
          let* (B6, _) := if M_state B5 =? S_ONLINE then m_lost_m B5 R_DESK_OFFLINE else Some (B5, tt) in
          if (M_state B6 =? S_IDLE) && truth (Cfg_auto_wake B6) then
            let* (B7, _) := m_wake_m B6 in Some (B7, tt)
          else Some (B6, tt)
        else if 0 <=? off then
          m_maybe_online_m (set_M_e1_us (set_M_foreign B4 0) 1)
        else
          let B5 := set_M_foreign B4 1 in
          let* fo := int_inc (OW_foreign B5) in
          let B6 := set_OW_foreign B5 fo in
          if (M_state B6 =? S_ONLINE) || (M_state B6 =? S_WAKING) then m_lost_m B6 R_FOREIGN
          else Some (B6, tt)
      else if fc =? SPEC_CMD_ACK then
        if truth (M_fly_on B2) && (sf_ack f =? M_fly_counter B2) then
          let* a := int_inc (OW_acked B2) in
          let B3 := set_OW_acked B2 a in
          let B4 := set_OW_acked_counter B3 (M_fly_counter B3) in
          let B5 := set_OW_acked_retry B4 (M_fly_retries B4) in
          let B6 := set_M_fly_on B5 0 in
          if M_state B6 =? S_WAKING then m_maybe_online_m (set_M_e2_acked B6 1)
          else Some (B6, tt)
        else Some (B2, tt)
      else if fc =? SPEC_CMD_DATA then
        let* ak := int_inc (OW_acks B2) in
        let B3 := set_M_fail (set_OW_acks B2 ak) 0 in
        let retry := sf_retry f in
        let send := sf_send f in
        let B4 := if truth retry then set_M_backoff_until B3 (u64 (g_now B3 + h_ms_m (Cfg_backoff_ms B3)))
                  else B3 in
        if truth (M_desk_counter_valid B4) && (send =? M_desk_counter B4) && truth retry then Some (B4, tt)
        else
        let B5 := set_M_desk_counter_valid (set_M_desk_counter B4 send) 1 in
        if (blen =? 1) && (at8 body 0 =? 0) then Some (B5, tt)
        else
        let nd := OW_ndata B5 in
        let* B6 :=
          if nd <? 2 then
            if nd <? 0 then None
            else Some (set_OW_dn_retry (set_OW_dn_counter (set_OW_dn_len (set_OW_dn_body B5 nd bodyp)
                          nd blen) nd send) nd retry)
          else Some B5 in
        let* nd1 := int_inc nd in
        Some (set_OW_ndata B6 nd1, tt)
      else if fc =? SPEC_CMD_E3 then
        if (M_state B2 =? S_ONLINE) || (M_state B2 =? S_WAKING) then m_lost_m B2 R_DESK_DISCONNECT
        else Some (B2, tt)
      else Some (B2, tt).

(* FT:299-301 and :373-374, once the desk is known (m_rx_m's `k`) *)
Definition m_rx_k (I : timg) (fr : tframe) (n : Z) (B1 : list byte) : option (list byte * Z) :=
  if M_state B1 =? S_CLOSED then Some (B1, 0)
  else
    let* (B3, _) := m_rx_sw I fr n (set_M_last_rx B1 (g_now B1)) in
    let* (B4, _) := m_tick_m B3 in
    Some (B4, 1).

(* FT:283-297: the parse and the filters, then k *)
Definition m_rx_flt (I : timg) (fr : tframe) (B : list byte) (n : Z) : option (list byte * Z) :=
    let bytes := tf_bytes fr in
    let f := spec_read_frame (zs bytes) n in
    if negb (sf_code f =? SPEC_OK) then Some (B, 0)
    else
    let src := sub bytes (sf_src f) 6 in
    let dst := sub bytes (sf_dst f) 6 in
    let fc := sf_cmd f in
    if beq_bytes src HOST || (negb (beq_bytes dst HOST) && negb (beq_bytes dst SPEC_BCAST)) then Some (B, 0)
    else if truth (M_desk_known B) then
      if beq_bytes src (M_desk B) then m_rx_k I fr n B else Some (B, 0)
    else if negb ((fc =? SPEC_CMD_E0) || (fc =? SPEC_CMD_E1)) then Some (B, 0)
    else if negb (beq_bytes (firstn 3 src) SPEC_OUI) then Some (B, 0)
    else m_rx_k I fr n (set_M_desk_known (set_M_desk B src) 1).

Lemma m_rx_m_eq : forall I fr B n,
  m_rx_m I (Some fr) B n =
  if (n <? 0) || (Z.of_nat (length (tf_bytes fr)) <? n) then None else m_rx_flt I fr B n.
Proof. reflexivity. Qed.

(* ---- the library, diginet_session_rx (DS:263-318), over buf ---- *)

(* DS:298-316, the switch (the `sw` of diginet_session_rx_m's accept) *)
Definition rx_sw (I : timg) (F : option tframe) (B : list byte) (buf : list byte) (now : Z)
    : option (list byte * unit) :=
  let cmd := fr_cmd buf in
      if (cmd =? DIGINET_CMD_ANNOUNCE) || (cmd =? DIGINET_CMD_ANNOUNCE_SESSION)
      then on_announce_m I F B buf now
      else if cmd =? DIGINET_CMD_ACK then on_ack_m I F B buf
      else if cmd =? DIGINET_CMD_DATA then on_data_m I F B buf now
      else if cmd =? DIGINET_CMD_DISCONNECT then
        (if (S_state B =? DIGINET_S_ONLINE) || (S_state B =? DIGINET_S_WAKING)
         then session_lost_m I F B DIGINET_R_DESK_DISCONNECT else Some (B, tt))
      else Some (set_S_stats_rx_ignored B (u64 (S_stats_rx_ignored B + 1)), tt).

(* DS:293-317 (the `accept` of diginet_session_rx_m) *)
Definition rx_accept (I : timg) (F : option tframe) (B : list byte) (buf : list byte) (now : Z)
    : option (list byte * Z) :=
    if S_state B =? DIGINET_S_CLOSED then Some (B, DIGINET_OK)
    else
    let B := set_S_stats_rx_frames B (u64 (S_stats_rx_frames B + 1)) in
    let B := set_S_last_rx_us B now in
    match rx_sw I F B buf now with
    | None => None
    | Some (B, _) => diginet_session_tick_m I F B now
    end.

(* DS:273-282's `ignored` *)
Definition rx_ignored (B : list byte) : option (list byte * Z) :=
  Some (set_S_stats_rx_ignored B (u64 (S_stats_rx_ignored B + 1)), DIGINET_OK).

Lemma diginet_session_rx_m_eq : forall I F B buf now,
  diginet_session_rx_m I F B buf now =
  if negb (fr_code buf =? DIGINET_OK) then
    Some (set_S_stats_rx_ignored B (u64 (S_stats_rx_ignored B + 1)), fr_code buf)
  else
  let src := fr_src buf in
  let dst := fr_dst buf in
  let cmd := fr_cmd buf in
  if memeq 6 src (S_cfg_host_mac B) ||
     (negb (memeq 6 dst (S_cfg_host_mac B)) && negb (memeq 6 dst BROADCAST)) then rx_ignored B
  else if negb (S_desk_known B =? 0) then
    if negb (memeq 6 src (S_desk_mac B)) then rx_ignored B else rx_accept I F B buf now
  else if negb ((cmd =? DIGINET_CMD_ANNOUNCE) || (cmd =? DIGINET_CMD_ANNOUNCE_SESSION)) then
    Some (B, DIGINET_OK)
  else if negb (oui_of src) then rx_ignored B
  else rx_accept I F (set_S_desk_known (set_S_desk_mac B src) 1) buf now.
Proof. reflexivity. Qed.
