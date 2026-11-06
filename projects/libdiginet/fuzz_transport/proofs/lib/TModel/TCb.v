(* libdiginet/fuzz_transport (new file). One Gallina function per C function of fuzz/fuzz_transport.c that
   the session calls back into or that those callbacks use.
   Shape: f_m I F B args : option (list byte * R), B the world before (TWorld.v), the result the world after and the C
   return value. None exactly when the C code reaches abort() or an operation UBSan traps on. Pure total helpers
   (h_ms_m, h_coalescable_m, io_now_m) return their value.
   Array bounds: every index of a C array the code subscripts (OW.t, GOT.t, OW.dn, g_q, g_cmd, g_s.queue) is held
   strictly below the array length, else None. For the one-past-the-end element that clang's bounds check lets a
   member access or an address-of through (`&g_cmd[1024]`, `g_cmd[1024].display`), the model is None as well: it
   then claims no behaviour the binary may not have, and the simulation proof keeps every index below the length.
   Pointers into the current heap frame (OW.desk_body, OW.dn[k].body, g_rx) are addresses (TImg.tframe); a read
   through one is frame_read / frame_strz_len, None when the read leaves the block.
   The frame reading of fuzz/spec.h is the shared model lib/Spec/DgnSpec.v (spec_read_frame, spec_sum_at,
   spec_system_at over list Z; strz_len over list byte). u64 and DIGINET_SUM_BODY come from TSess0.v, whose
   diginet_session_deadline_m check_inflight_settle_m calls. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TSess0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.

Local Notation "'let*' p ':=' c1 'in' c2" := (match c1 with Some p => c2 | None => None end)
  (at level 200, p pattern, c1 at level 200, c2 at level 200).

(* ---- constants (from the C headers; the values DgnSpec.v already has, SPEC_OK, SPEC_E_*, SPEC_MAC,
   SPEC_BODY_AT, SPEC_CMD_MAX, are used from there) ---- *)

Definition INT_MAX : Z := 2 ^ 31 - 1.
Definition INT_MIN : Z := - 2 ^ 31.
Definition OPS_MAX : Z := 1024.            (* fuzz_transport.c:93 *)
Definition TAG : Z := 0xa0.                (* :94 *)
Definition CMDS_MAX : Z := 1024.           (* :95 *)
Definition TRANS_MAX : Z := 16.            (* :96 *)
Definition RETRY_AT : Z := 26.             (* :99, SPEC_ETH_HDR + 12 *)
Definition S_IDLE : Z := 0.                (* :102 *)
Definition S_WAKING : Z := 1.
Definition S_ONLINE : Z := 2.
Definition S_CLOSED : Z := 3.
Definition R_NONE : Z := 0.                (* :103-104 *)
Definition R_WAKE : Z := 1.
Definition R_ONLINE : Z := 2.
Definition R_DESK_OFFLINE : Z := 3.
Definition R_SILENCE : Z := 4.
Definition R_FOREIGN : Z := 5.
Definition R_WAKE_TIMEOUT : Z := 6.
Definition R_DESK_DISCONNECT : Z := 7.
Definition R_CLOSED : Z := 8.
Definition N_DESK : Z := 1.                (* :105 *)
Definition N_STATE : Z := 2.
Definition N_DATA : Z := 3.
Definition N_ACKED : Z := 4.
Definition N_ACK_LOST : Z := 5.
Definition N_FOREIGN : Z := 6.
Definition QUEUE_MAX : Z := 512.           (* :107 *)
Definition PENDING : Z := 1.               (* :152 *)
Definition SENT : Z := 2.
Definition REPLACED : Z := 3.
Definition EIO : Z := 5.                   (* errno.h (Linux asm-generic/errno-base.h), the -EIO of :230, :898, :912 *)
Definition SPEC_MIN_FRAME : Z := 60.       (* spec.h:35 *)
Definition SPEC_MAX_FRAME : Z := 1514.     (* spec.h:38 *)
Definition SPEC_MAX_BODY : Z := 1484.      (* spec.h:39 *)
Definition SPEC_CMD_DATA : Z := 0x00.      (* spec.h:51-56 *)
Definition SPEC_CMD_ACK : Z := 0xa0.
Definition SPEC_CMD_E0 : Z := 0xe0.
Definition SPEC_CMD_E1 : Z := 0xe1.
Definition SPEC_CMD_E2 : Z := 0xe2.
Definition SPEC_CMD_E3 : Z := 0xe3.
Definition SPEC_ANN_UNKNOWN : Z := 15.     (* spec.h:60-64 *)
Definition SPEC_ANN_FIELD : Z := 9.
Definition SPEC_ANN_VERSION : Z := 15.
Definition SPEC_ANN_NAME : Z := 24.
Definition SPEC_ANN_MIN : Z := 33.
Definition SPEC_KEY_INPUT : Z := 8.        (* spec.h:137-140 *)
Definition SPEC_KEY_KEEPALIVE : Z := 9.
Definition DIGINET_SUM_ZERO : Z := 1.      (* include/diginet/diginet.h:79 *)

(* the MAC tables, fuzz_transport.c:109-113 and spec.h:67-69 *)
Definition HOST : list byte := bs [0x02; 0x00; 0x00; 0x00; 0x00; 0x01].
Definition OTHER : list byte := bs [0x02; 0x00; 0x00; 0x00; 0x00; 0x02].
Definition DESK : list byte := bs [0x00; 0xa0; 0x7e; 0x24; 0x00; 0x01].
Definition DESK2 : list byte := bs [0x00; 0xa0; 0x7e; 0x08; 0x00; 0x01].
Definition NOTDD : list byte := bs [0x00; 0x11; 0x22; 0x33; 0x44; 0x55].
Definition SPEC_OUI : list byte := bs [0x00; 0xa0; 0x7e].
Definition SPEC_BCAST : list byte := bs [0xff; 0xff; 0xff; 0xff; 0xff; 0xff].
(* the names of SPEC_C24 and SPEC_PC, spec.h:110-111: "CNTRL|24", "MAINUNIT" *)
Definition C24_NAME : list byte := bs [0x43; 0x4e; 0x54; 0x52; 0x4c; 0x7c; 0x32; 0x34].
Definition PC_NAME : list byte := bs [0x4d; 0x41; 0x49; 0x4e; 0x55; 0x4e; 0x49; 0x54].

(* ---- C arithmetic and reads ---- *)

Definition truth (x : Z) : bool := negb (x =? 0).         (* a C scalar as a condition *)
Definition b2z (b : bool) : Z := if b then 1 else 0.
(* x + 1, x - 1 in int: None on signed overflow (UBSan traps it) *)
Definition int_inc (x : Z) : option Z := if x =? INT_MAX then None else Some (x + 1).
Definition int_dec (x : Z) : option Z := if x =? INT_MIN then None else Some (x - 1).
(* memcmp (a, b, n) == 0 for two n-byte lists *)
Definition beq_bytes (a b : list byte) : bool :=
  if list_eq_dec Z.eq_dec (zs a) (zs b) then true else false.

(* the n bytes at address p of the heap frame F (TImg.tframe); no read for n = 0; None when F is absent or
   [p, p + n) leaves the block *)
Definition frame_read (F : option tframe) (p n : Z) : option (list byte) :=
  if n =? 0 then Some [] else
  match F with
  | None => None
  | Some f =>
      let off := p - tf_addr f in
      if (off <? 0) || (n <? 0) || (Z.of_nat (length (tf_bytes f)) <? off + n) then None
      else Some (sub (tf_bytes f) off (Z.to_nat n))
  end.

(* spec_strz_len (spec.h:251-257) over the bytes rest from its pointer to the end of the block: it reads rest[0],
   ... up to the first NUL or 9 bytes, that is min 9 (n + 1) bytes for the answer n; None when that leaves rest *)
Definition list_strz_len (rest : list byte) : option nat :=
  let n := strz_len rest in
  if (length rest <? Nat.min 9 (S n))%nat then None else Some n.

(* spec_strz_len (p) for p an address in the heap frame F *)
Definition frame_strz_len (F : option tframe) (p : Z) : option nat :=
  match F with
  | None => None
  | Some f =>
      let off := p - tf_addr f in
      if off <? 0 then None else list_strz_len (skipn (Z.to_nat off) (tf_bytes f))
  end.

(* struct spec_frame f after spec_read_frame (frame, len, &f), len = length frame (spec.h:199-223, DgnSpec.v) *)
Definition rf (frame : list byte) : spec_frame := spec_read_frame (zs frame) (Z.of_nat (length frame)).

(* ---- OW.dn[k] (the plain image's layout: dn at OW + 256, 24 bytes each; body 0 (8), len 8 (8),
   counter 16 (4), retry 20 (2)); TWorld.v has no accessor for these ---- *)
Definition A_OW_dn_body (k : Z) : Z := (OFF_OW + 256 + 24 * k) + 0.
Definition OW_dn_body (B : list byte) (k : Z) : Z := u_at B (A_OW_dn_body k) 8.
Definition set_OW_dn_body (B : list byte) (k v : Z) : list byte := upd B (A_OW_dn_body k) (put 8 v).
Definition A_OW_dn_len (k : Z) : Z := (OFF_OW + 256 + 24 * k) + 8.
Definition OW_dn_len (B : list byte) (k : Z) : Z := u_at B (A_OW_dn_len k) 8.
Definition set_OW_dn_len (B : list byte) (k v : Z) : list byte := upd B (A_OW_dn_len k) (put 8 v).
Definition A_OW_dn_counter (k : Z) : Z := (OFF_OW + 256 + 24 * k) + 16.
Definition OW_dn_counter (B : list byte) (k : Z) : Z := u_at B (A_OW_dn_counter k) 4.
Definition set_OW_dn_counter (B : list byte) (k v : Z) : list byte := upd B (A_OW_dn_counter k) (put 4 v).
Definition A_OW_dn_retry (k : Z) : Z := (OFF_OW + 256 + 24 * k) + 20.
Definition OW_dn_retry (B : list byte) (k : Z) : Z := u_at B (A_OW_dn_retry k) 2.
Definition set_OW_dn_retry (B : list byte) (k v : Z) : list byte := upd B (A_OW_dn_retry k) (put 2 v).

(* ---- the read-only records a pointer selects ---- *)

(* the desk a struct spec_desk pointer names: SPEC_C24 or SPEC_PC (spec.h:110-111; DgnSpec.v c24, pc) *)
Definition spec_desk_at (I : timg) (p : Z) : option desk :=
  if p =? ti_spec_c24 I then Some c24 else if p =? ti_spec_pc I then Some pc else None.

(* the entry of src/diginet_codec.c personalities[] (24-byte elements, DgnLib.v personalities) a pointer names *)
Definition personality_ptr (I : timg) (p : Z) : option dgn_personality :=
  let off := p - ti_personalities I in
  if (off <? 0) || negb (off mod 24 =? 0) then None else personality_at (off / 24).

(* ---- the harness's helpers ---- *)

(* fuzz_transport.c:123-126 ms: (uint64_t)v * 1000u, v a uint32_t *)
Definition h_ms_m (v : Z) : Z := u64 (v * 1000).

(* :188-194 coalescable: k = (uint8_t)(key >> 16), key a uint32_t *)
Definition h_coalescable_m (key : Z) : Z :=
  let k := Z.shiftr key 16 mod 2 ^ 8 in
  b2z (negb (k =? 0) && negb (k =? SPEC_KEY_INPUT) && negb (k =? SPEC_KEY_KEEPALIVE)).

(* ---- the model's state functions, :196-394 ---- *)

(* :196-207 m_set. None: OW.t[OW.n] with OW.n < 0 (index out of bounds, :201-203); OW.n++ at INT_MAX (:205). *)
Definition m_set_m (B : list byte) (st why : Z) : option (list byte * unit) :=
  if M_state B =? st then Some (B, tt)                                              (* :198-199 *)
  else
    let n := OW_n B in
    let* B1 :=
      if n <? TRANS_MAX then                                                        (* :200 *)
        if n <? 0 then None
        else Some (set_OW_t_reason (set_OW_t_old (set_OW_t_state B n st) n (M_state B)) n why)   (* :201-203 *)
      else Some B in
    let* n1 := int_inc n in                                                         (* :205 *)
    Some (set_M_state (set_OW_n B1 n1) st, tt).                                     (* :206 *)

(* :210-215 m_lost. None: m_set's. *)
Definition m_lost_m (B : list byte) (why : Z) : option (list byte * unit) :=
  m_set_m (set_M_desk_counter_valid (set_M_fly_on B 0) 0) S_IDLE why.               (* :212-214 *)

(* :218-233 m_wake: the code a wake owes. None: OW.e2++ at INT_MAX (:226); m_set's. *)
Definition m_wake_m (B : list byte) : option (list byte * Z) :=
  if negb (truth (M_desk_known B)) then Some (B, SPEC_E_ARG)                        (* :220-221 *)
  else if truth (M_foreign B) then Some (B, SPEC_E_REFUSED)                         (* :222-223 *)
  else
    let B1 := set_M_e1_us (set_M_e2_acked B 0) 0 in                                 (* :224 *)
    let B2 := set_M_wake_sent B1 (g_now B1) in                                      (* :225 *)
    let* e2 := int_inc (OW_e2 B2) in                                                (* :226 *)
    let B3 := set_OW_e2 B2 e2 in
    let fails := M_fail B3 in                                                       (* :227 *)
    let B4 := set_M_fail B3 0 in                                                    (* :228 *)
    if truth fails then Some (B4, - EIO)                                            (* :229-230 *)
    else let* (B5, _) := m_set_m B4 S_WAKING R_WAKE in Some (B5, SPEC_OK).          (* :231-232 *)

(* :237-243 m_maybe_online. None: m_set's. *)
Definition m_maybe_online_m (B : list byte) : option (list byte * unit) :=
  if (M_state B =? S_WAKING) && truth (M_e2_acked B) && truth (M_e1_us B) then      (* :239 *)
    let B1 := set_M_next_ka B (u64 (M_last_rx B + h_ms_m (Cfg_keepalive_ms B))) in  (* :240 *)
    m_set_m B1 S_ONLINE R_ONLINE                                                    (* :241 *)
  else Some (B, tt).

(* :246-252 m_tick. None: m_lost's. *)
Definition m_tick_m (B : list byte) : option (list byte * unit) :=
  if (M_state B =? S_WAKING) && (h_ms_m (Cfg_wake_timeout_ms B) <=? u64 (g_now B - M_wake_sent B)) then
    m_lost_m B R_WAKE_TIMEOUT                                                       (* :248-249 *)
  else if (M_state B =? S_ONLINE) && (h_ms_m (Cfg_offline_ms B) <=? u64 (g_now B - M_last_rx B)) then
    m_lost_m B R_SILENCE                                                            (* :250-251 *)
  else Some (B, tt).

(* :258-261, the loop for (int i = 0; i + SPEC_MAC <= SPEC_ANN_UNKNOWN; i++): i = 0 .. 9, fuel 10 *)
Fixpoint host_offset_loop (fuel : nat) (body : list byte) (i : Z) : option Z :=
  match fuel with
  | O => Some (-1)                                                                  (* :261 *)
  | S fuel' =>
      if i + SPEC_MAC <=? SPEC_ANN_UNKNOWN then
        if Z.of_nat (length body) <? i + SPEC_MAC then None                         (* memcmp past the block *)
        else if beq_bytes (sub body i 6) HOST then Some i                           (* :259-260 *)
        else host_offset_loop fuel' body (i + 1)
      else Some (-1)
  end.

(* :256-262 host_offset; body = the bytes from the pointer to the end of its block. None: a read past the block. *)
Definition host_offset_m (B : list byte) (body : list byte) : option (list byte * Z) :=
  let* r := host_offset_loop 10 body 0 in Some (B, r).

(* :265-273 desk_named: &SPEC_C24, &SPEC_PC or NULL (0); strlen of either name is 8. None: spec_strz_len reads past
   the block. *)
Definition desk_named_m (I : timg) (B : list byte) (body : list byte) : option (list byte * Z) :=
  let fld := skipn (Z.to_nat SPEC_ANN_NAME) body in
  let* n := list_strz_len fld in                                                    (* :267 *)
  if (n =? 8)%nat && beq_bytes (firstn n fld) C24_NAME then Some (B, ti_spec_c24 I) (* :268-269 *)
  else if (n =? 8)%nat && beq_bytes (firstn n fld) PC_NAME then Some (B, ti_spec_pc I)   (* :270-271 *)
  else Some (B, 0).                                                                 (* :272 *)

(* :280-375 m_rx (frame, n): frame = tf_addr / tf_bytes of F, read as n bytes. Stores f.body = tf_addr + 30 into
   OW.desk_body and OW.dn[k].body. None: F absent or n past the block; OW.desk++ / OW.foreign++ / OW.acked++ /
   OW.acks++ / OW.ndata++ at INT_MAX (:308, :326, :334, :348, :364); OW.dn[OW.ndata] with OW.ndata < 0
   (:359-362); host_offset's, desk_named's, m_lost's, m_wake's, m_maybe_online's, m_tick's. *)
Definition m_rx_m (I : timg) (F : option tframe) (B : list byte) (n : Z) : option (list byte * Z) :=
  match F with
  | None => None
  | Some fr =>
    let bytes := tf_bytes fr in
    if (n <? 0) || (Z.of_nat (length bytes) <? n) then None else
    let f := spec_read_frame (zs bytes) n in                                        (* :283 *)
    if negb (sf_code f =? SPEC_OK) then Some (B, 0)                                 (* :283-284 *)
    else
    let src := sub bytes (sf_src f) 6 in
    let dst := sub bytes (sf_dst f) 6 in
    let fc := sf_cmd f in
    let bodyp := tf_addr fr + sf_body f in                                          (* f.body *)
    let body := skipn (Z.to_nat (sf_body f)) bytes in                               (* the bytes from f.body on *)
    let blen := sf_body_len f in
    (* :302-372, the switch on f.cmd *)
    let sw (B2 : list byte) : option (list byte * unit) :=
      if (fc =? SPEC_CMD_E0) || (fc =? SPEC_CMD_E1) then                            (* :303-304 *)
        if blen <? SPEC_ANN_MIN then Some (B2, tt) else                             (* :305-306 *)
        let* (_, off) := if fc =? SPEC_CMD_E1 then host_offset_m B2 body else Some (B2, -1) in   (* :307 *)
        let* d := int_inc (OW_desk B2) in                                           (* :308 *)
        let B3 := set_OW_desk_off (set_OW_desk B2 d) off in                         (* :308-309 *)
        let* (_, dp) := desk_named_m I B3 body in                                   (* :310 *)
        let B4 := set_OW_desk_body (set_OW_desk_p B3 dp) bodyp in                   (* :310-311 *)
        if fc =? SPEC_CMD_E0 then                                                   (* :312 *)
          let B5 := set_M_foreign B4 0 in                                           (* :314 *)
          let* (B6, _) := if M_state B5 =? S_ONLINE then m_lost_m B5 R_DESK_OFFLINE else Some (B5, tt) in   (* :315-316 *)
          if (M_state B6 =? S_IDLE) && truth (Cfg_auto_wake B6) then                (* :317 *)
            let* (B7, _) := m_wake_m B6 in Some (B7, tt)                            (* :318 *)
          else Some (B6, tt)
        else if 0 <=? off then                                                      (* :319 *)
          m_maybe_online_m (set_M_e1_us (set_M_foreign B4 0) 1)                     (* :320-322 *)
        else
          let B5 := set_M_foreign B4 1 in                                           (* :325 *)
          let* fo := int_inc (OW_foreign B5) in                                     (* :326 *)
          let B6 := set_OW_foreign B5 fo in
          if (M_state B6 =? S_ONLINE) || (M_state B6 =? S_WAKING) then m_lost_m B6 R_FOREIGN   (* :327-328 *)
          else Some (B6, tt)
      else if fc =? SPEC_CMD_ACK then                                               (* :332 *)
        if truth (M_fly_on B2) && (sf_ack f =? M_fly_counter B2) then               (* :333 *)
          let* a := int_inc (OW_acked B2) in                                        (* :334 *)
          let B3 := set_OW_acked B2 a in
          let B4 := set_OW_acked_counter B3 (M_fly_counter B3) in                   (* :335 *)
          let B5 := set_OW_acked_retry B4 (M_fly_retries B4) in                     (* :336 *)
          let B6 := set_M_fly_on B5 0 in                                            (* :337 *)
          if M_state B6 =? S_WAKING then m_maybe_online_m (set_M_e2_acked B6 1)     (* :338-341 *)
          else Some (B6, tt)
        else Some (B2, tt)
      else if fc =? SPEC_CMD_DATA then                                              (* :344 *)
        let* ak := int_inc (OW_acks B2) in                                          (* :348 *)
        let B3 := set_M_fail (set_OW_acks B2 ak) 0 in                               (* :348-349 *)
        let retry := sf_retry f in
        let send := sf_send f in
        let B4 := if truth retry then set_M_backoff_until B3 (u64 (g_now B3 + h_ms_m (Cfg_backoff_ms B3)))
                  else B3 in                                                        (* :350-351 *)
        if truth (M_desk_counter_valid B4) && (send =? M_desk_counter B4) && truth retry then Some (B4, tt)   (* :352-353 *)
        else
        let B5 := set_M_desk_counter_valid (set_M_desk_counter B4 send) 1 in        (* :354-355 *)
        if (blen =? 1) && (at8 body 0 =? 0) then Some (B5, tt)                      (* :356-357 *)
        else
        let nd := OW_ndata B5 in
        let* B6 :=
          if nd <? 2 then                                                           (* :358 *)
            if nd <? 0 then None
            else Some (set_OW_dn_retry (set_OW_dn_counter (set_OW_dn_len (set_OW_dn_body B5 nd bodyp)
                          nd blen) nd send) nd retry)                               (* :359-362 *)
          else Some B5 in
        let* nd1 := int_inc nd in                                                   (* :364 *)
        Some (set_OW_ndata B6 nd1, tt)
      else if fc =? SPEC_CMD_E3 then                                                (* :366 *)
        if (M_state B2 =? S_ONLINE) || (M_state B2 =? S_WAKING) then m_lost_m B2 R_DESK_DISCONNECT   (* :367-368 *)
        else Some (B2, tt)
      else Some (B2, tt) in                                                         (* :370-371 *)
    (* :299-301 and :373-374, after the desk is known *)
    let k (B1 : list byte) : option (list byte * Z) :=
      if M_state B1 =? S_CLOSED then Some (B1, 0)                                   (* :299-300 *)
      else
        let* (B3, _) := sw (set_M_last_rx B1 (g_now B1)) in                         (* :301-372 *)
        let* (B4, _) := m_tick_m B3 in                                              (* :373 *)
        Some (B4, 1) in                                                             (* :374 *)
    if beq_bytes src HOST || (negb (beq_bytes dst HOST) && negb (beq_bytes dst SPEC_BCAST)) then Some (B, 0)   (* :285-287 *)
    else if truth (M_desk_known B) then                                             (* :288 *)
      if beq_bytes src (M_desk B) then k B else Some (B, 0)                         (* :289-290 *)
    else if negb ((fc =? SPEC_CMD_E0) || (fc =? SPEC_CMD_E1)) then Some (B, 0)      (* :292-293 *)
    else if negb (beq_bytes (firstn 3 src) SPEC_OUI) then Some (B, 0)               (* :294-295 *)
    else k (set_M_desk_known (set_M_desk B src) 1)                                  (* :296-297 *)
  end.

(* :378-386 m_close. None: OW.e3++ at INT_MAX (:381); m_set's. *)
Definition m_close_m (B : list byte) : option (list byte * unit) :=
  let* B1 :=
    if truth (M_desk_known B) && negb (truth (M_foreign B)) && negb (M_state B =? S_CLOSED) then   (* :380 *)
      let* e3 := int_inc (OW_e3 B) in Some (set_M_fail (set_OW_e3 B e3) 0)          (* :381-382 *)
    else Some B in
  m_set_m (set_M_fly_on B1 0) S_CLOSED R_CLOSED.                                    (* :384-385 *)

(* :388-394 op_begin. Never None. *)
Definition op_begin_m (B : list byte) : option (list byte * unit) :=
  let B1 := upd B OFF_OW (repeat (b8 0) (Z.to_nat SZ_OW)) in                        (* :390 *)
  let B2 := upd B1 OFF_GOT (repeat (b8 0) (Z.to_nat SZ_GOT)) in                     (* :391 *)
  let B3 := set_OW_desk_off B2 (-1) in                                              (* :392 *)
  Some (set_M_fail B3 (g_fail_next B3), tt).                                        (* :393 *)

(* ---- the properties, :398-819. Each check: None exactly on its abort(). A check of a `const struct spec_frame
   *f` takes the frame f was read from (f = rf frame). ---- *)

(* :398-420 check_sent_frame (frame, len, &f), len = length frame *)
Definition check_sent_frame_m (B : list byte) (frame : list byte) : option (list byte * unit) :=
  let f := rf frame in
  let len := Z.of_nat (length frame) in
  let blen := sf_body_len f in
  if negb (sf_code f =? SPEC_OK) || negb (beq_bytes (sub frame (sf_src f) 6) HOST)
     || negb (truth (M_desk_known B)) || negb (beq_bytes (sub frame (sf_dst f) 6) (M_desk B))
     || (0 <=? spec_system_at (zs (skipn (Z.to_nat (sf_body f)) frame)) blen) then None   (* :405-407 *)
  else
    let n := if SPEC_BODY_AT + blen <? SPEC_MIN_FRAME then SPEC_MIN_FRAME else SPEC_BODY_AT + blen in   (* :408 *)
    let zeros := forallb (fun x => bz x =? 0) (skipn (Z.to_nat (SPEC_BODY_AT + blen)) frame) in   (* :409-411 *)
    let want := if Cfg_sum_mode B =? DIGINET_SUM_ZERO then 0 else spec_sum_at (zs frame) (sf_body f) blen in
    if negb (len =? n) || negb zeros || negb (sf_sum f =? want) then None           (* :417-419 *)
    else Some (B, tt).

(* :422-430 check_ack_frame (&f) *)
Definition check_ack_frame_m (B : list byte) (frame : list byte) : option (list byte * unit) :=
  let f := rf frame in
  if negb (sf_ack f =? g_rx_send B) || negb (sf_body_len f =? 0) || negb (sf_retry f =? 0) then None   (* :428-429 *)
  else Some (B, tt).

(* :432-448 check_inflight_new *)
Definition check_inflight_new_m (B : list byte) : option (list byte * unit) :=
  if negb (M_state B =? S_ONLINE) || truth (M_fly_on B) then None                   (* :440-441 *)
  else if g_now B <? M_backoff_until B then None                                    (* :446-447 *)
  else Some (B, tt).

(* :450-474 check_inflight_retry (frame, len, &f), len = length frame. The memcmp of :459-460 reads M.fly.frame
   for len bytes; past the world (len > W_LEN - offset of M.fly.frame) the model is None (outside the world). *)
Definition check_inflight_retry_m (B : list byte) (frame : list byte) : option (list byte * unit) :=
  let f := rf frame in
  let len := Z.of_nat (length frame) in
  if negb (truth (M_fly_on B)) || negb (len =? M_fly_len B) || (len <? RETRY_AT + 2) then None   (* :459 *)
  else if W_LEN <? A_M_fly_frame + len then None
  else if negb (beq_bytes (firstn (Z.to_nat RETRY_AT) frame) (sub B A_M_fly_frame (Z.to_nat RETRY_AT)))
       || negb (beq_bytes (skipn (Z.to_nat (RETRY_AT + 2)) frame)
                  (sub B (A_M_fly_frame + RETRY_AT + 2) (Z.to_nat (len - RETRY_AT - 2)))) then None   (* :459-461 *)
  else if negb (sf_retry f =? u32 (M_fly_retries B + 1)) || (Cfg_max_retries B <? sf_retry f) then None   (* :466-467 *)
  else if u64 (g_now B - M_fly_sent B) <? h_ms_m (Cfg_ack_timeout_ms B) then None   (* :472-473 *)
  else Some (B, tt).

(* :476-484 check_inflight_acked (n) *)
Definition check_inflight_acked_m (B : list byte) (n : ntc) : option (list byte * unit) :=
  if (OW_acked B <? GOT_acked B) || negb (n_counter n =? OW_acked_counter B)
     || negb (n_retry n =? OW_acked_retry B) then None                              (* :482-483 *)
  else Some (B, tt).

(* :486-495 check_inflight_lost (n) *)
Definition check_inflight_lost_m (B : list byte) (n : ntc) : option (list byte * unit) :=
  if negb (truth (M_fly_on B)) || negb (n_counter n =? M_fly_counter B)
     || negb (M_fly_retries B =? Cfg_max_retries B) || negb (n_retry n =? Cfg_max_retries B) then None   (* :492-494 *)
  else Some (B, tt).

(* :497-505 check_state_online *)
Definition check_state_online_m (B : list byte) : option (list byte * unit) :=
  if negb (truth (M_e2_acked B)) || negb (truth (M_e1_us B)) then None else Some (B, tt).   (* :503-504 *)

(* :507-515 check_state_wake *)
Definition check_state_wake_m (B : list byte) : option (list byte * unit) :=
  if truth (M_foreign B) then None else Some (B, tt).                               (* :513-514 *)

(* :517-525 check_state_wake_code (rc, want) *)
Definition check_state_wake_code_m (B : list byte) (rc want : Z) : option (list byte * unit) :=
  if negb (rc =? want) then None else Some (B, tt).                                 (* :523-524 *)

(* :527-557 check_state_desk (n). n->personality->device / strips are read from personalities[] (DgnLib.v),
   OW.desk_p->device / strips from SPEC_C24 / SPEC_PC (DgnSpec.v c24 / pc); OW.desk_body + 15 and + 24 from the
   heap frame F. None: the aborts of :537, :543, :556; besides, outside the model, a pointer that names none of those
   records or a read past the frame block (never with OW.desk > 0, which :534 requires, since m_rx then stored
   desk_body into the current frame). *)
Definition check_state_desk_m (I : timg) (F : option tframe) (B : list byte) (n : ntc) : option (list byte * unit) :=
  let pn := n_pers n in
  let pd := OW_desk_p B in
  if (OW_desk B <? GOT_desk B) || negb (n_mac_offset n =? OW_desk_off B)
     || negb (Bool.eqb (pn =? 0) (pd =? 0)) then None                               (* :534, :537 *)
  else
    let* bad :=
      if pn =? 0 then Some false else
      let* p := personality_ptr I pn in
      let* d := spec_desk_at I pd in
      Some (negb (dp_device p =? d_dev d) || negb (dp_strips p =? d_strips d)) in   (* :535-536 *)
    if bad then None else                                                           (* :537 *)
    match n_ann n with
    | None => None                                                                  (* :542-543 *)
    | Some a =>
        let db := OW_desk_body B in
        if db =? 0 then None else                                                  (* :544, NULL + 15: the ubsan trap *)
        let* vn := frame_strz_len F (db + SPEC_ANN_VERSION) in                      (* :544 *)
        let* nn := frame_strz_len F (db + SPEC_ANN_NAME) in                         (* :545 *)
        let* vb := frame_read F (db + SPEC_ANN_VERSION) (Z.of_nat vn) in
        let* nb := frame_read F (db + SPEC_ANN_NAME) (Z.of_nat nn) in
        let ver := ta_version a in
        let nam := ta_name a in
        if negb (beq_bytes (firstn vn ver) vb) then None                            (* :553 *)
        else if (length ver <=? vn)%nat then None                                   (* version[vn] not in the record *)
        else if truth (bz (nth vn ver (b8 0))) then None                            (* :554 *)
        else if negb (beq_bytes (firstn nn nam) nb) then None                       (* :554 *)
        else if (length nam <=? nn)%nat then None
        else if truth (bz (nth nn nam (b8 0))) then None                            (* :555-556 *)
        else Some (B, tt)
    end.

(* :559-569 check_state_data (n). None: the abort of :568; OW.dn[GOT.ndata] with GOT.ndata < 0 (:565-567); outside
   the model, a read past the frame block through OW.dn[].body or an ntc whose n_body is shorter than body_len. *)
Definition check_state_data_m (F : option tframe) (B : list byte) (n : ntc) : option (list byte * unit) :=
  let g := GOT_ndata B in
  if (OW_ndata B <=? g) || (2 <=? g) then None                                      (* :565 *)
  else if g <? 0 then None
  else if negb (n_body_len n =? OW_dn_len B g) then None                            (* :565 *)
  else
    let* db := frame_read F (OW_dn_body B g) (n_body_len n) in                      (* :566 *)
    if Z.of_nat (length (n_body n)) <? n_body_len n then None
    else if negb (beq_bytes (firstn (Z.to_nat (n_body_len n)) (n_body n)) db)
            || negb (n_counter n =? OW_dn_counter B g) || negb (n_retry n =? OW_dn_retry B g) then None   (* :566-568 *)
    else Some (B, tt).

(* :571-580 check_keepalive_due *)
Definition check_keepalive_due_m (B : list byte) : option (list byte * unit) :=
  if negb (M_state B =? S_ONLINE) || truth (M_fly_on B) || (g_now B <? M_backoff_until B)
     || (g_now B <? M_next_ka B) then None                                          (* :578-579 *)
  else Some (B, tt).

(* :582-597 check_latest_frame (&f, cmds), cmds an unsigned *)
Definition check_latest_frame_m (B : list byte) (frame : list byte) (cmds : Z) : option (list byte * unit) :=
  let f := rf frame in
  if (Cfg_max_body B <? sf_body_len f) || (Cfg_max_cmds B <? sf_ncmds f)
     || (negb (truth (g_raw B)) && negb (sf_ncmds f =? cmds)) then None             (* :589-590 *)
  else if negb (sf_send f =? u32 (M_host_counter B + sf_ncmds f)) then None         (* :595-596 *)
  else Some (B, tt).

(* :599-607 check_latest_control (&f) *)
Definition check_latest_control_m (B : list byte) (frame : list byte) : option (list byte * unit) :=
  if negb (sf_send (rf frame) =? M_host_counter B) then None else Some (B, tt).     (* :605-606 *)

(* :609-615 tagged_of (b, n); b = the bytes from the pointer to the end of its block. R: Some i for &g_cmd[i],
   None for NULL. None (outer): a read past the block; &g_cmd[serial] with serial >= CMDS_MAX. *)
Definition tagged_of_m (B : list byte) (b : list byte) (n : Z) : option (list byte * option Z) :=
  if n <? 3 then Some (B, None)                                                     (* :611 *)
  else if (length b <? 1)%nat then None
  else if negb (at8 b 0 =? TAG) then Some (B, None)                                 (* :611-612 *)
  else if (length b <? 3)%nat then None
  else
    let serial := Z.lor (at8 b 1) (Z.shiftl (at8 b 2) 7) in                         (* :613 *)
    if serial <? g_ncmd B then                                                      (* :614 *)
      if CMDS_MAX <=? serial then None else Some (B, Some serial)
    else Some (B, None).

(* :619-623, for (unsigned i = 0; i < g_nq; i++) with k the next free place; g_nq does not change in the loop.
   g_q[i] traps once i reaches CMDS_MAX, so fuel CMDS_MAX + 1 covers every run; the O case is unreachable. *)
Fixpoint q_remove_loop (fuel : nat) (B : list byte) (serial nq i k : Z) : option (list byte * Z) :=
  match fuel with
  | O => None
  | S fuel' =>
      if i <? nq then
        if CMDS_MAX <=? i then None                                                 (* g_q[i] out of bounds *)
        else if Q_at B i =? serial then q_remove_loop fuel' B serial nq (i + 1) k   (* :621 *)
        else q_remove_loop fuel' (set_Q_at B k (Q_at B i)) serial nq (i + 1) (k + 1)   (* :622 *)
      else Some (B, k)
  end.

(* :617-624 q_remove (serial). None: g_q[i] with i >= CMDS_MAX (g_nq > CMDS_MAX). *)
Definition q_remove_m (B : list byte) (serial : Z) : option (list byte * unit) :=
  let* (B1, k) := q_remove_loop (S (Z.to_nat CMDS_MAX)) B serial (g_nq B) 0 0 in
  Some (set_g_nq B1 k, tt).                                                         (* :623 *)

(* :630-643, while (at < len): each round either aborts or marks a PENDING command SENT and moves at by its
   length; a round with t->len = 0 leaves at and finds the same command, now SENT, and aborts. So at most len + 1
   rounds and the final test; fuel len + 1, the O case unreachable. pos is at, disp is *display. *)
Fixpoint latest_sent_loop (fuel : nat) (B : list byte) (body : list byte) (len pos disp : Z)
    : option (list byte * Z) :=
  match fuel with
  | O => None
  | S fuel' =>
      if pos <? len then
        let rest := skipn (Z.to_nat pos) body in
        let* (_, t) := tagged_of_m B rest (len - pos) in                            (* :631 *)
        match t with
        | None => None                                                              (* :637-638 *)
        | Some s =>
            let tl := Cmd_len B s in
            if negb (Cmd_st B s =? PENDING) || (len - pos <? tl)
               || negb (beq_bytes (firstn (Z.to_nat tl) rest) (sub B (A_Cmd_bytes s) (Z.to_nat tl))) then None   (* :637-638 *)
            else
              let B1 := set_Cmd_st B s SENT in                                      (* :639 *)
              let* (B2, _) := q_remove_m B1 s in                                    (* :640 *)
              latest_sent_loop fuel' B2 body len (pos + tl) (Z.lor disp (Cmd_display B2 s))   (* :641-642 *)
        end
      else Some (B, disp)
  end.

(* :626-644 check_latest_sent (body, len, &display); body = the len bytes at f.body. R: *display. None: the abort of
   :637-638; tagged_of's; q_remove's. *)
Definition check_latest_sent_m (B : list byte) (body : list byte) (len : Z) : option (list byte * Z) :=
  latest_sent_loop (S (Z.to_nat len)) B body len 0 0.                               (* :628-629 *)

(* :646-654 check_latest_display *)
Definition check_latest_display_m (B : list byte) : option (list byte * unit) :=
  if truth (M_display_sent B) && (u64 (g_now B - M_last_display B) <? Cfg_display_gap_us B) then None   (* :652-653 *)
  else Some (B, tt).

(* :656-665 check_refusal_submit (c, rc, queued_before); c = the 32 bytes of the struct diginet_cmd (bytes[24] at
   0, len at 24). None: the abort of :664; outside the model, c->len > 32 (spec_system_at would read past c). *)
Definition check_refusal_submit_m (B : list byte) (c : list byte) (rc before : Z) : option (list byte * unit) :=
  let clen := at8 c 24 in
  if (length c <? 25)%nat || (Z.of_nat (length c) <? clen) then None
  else
    let sys := 0 <=? spec_system_at (zs c) clen in
    if (if sys then negb (rc =? SPEC_E_REFUSED) || negb (S_queued B =? before) else rc =? SPEC_E_REFUSED)
    then None                                                                       (* :663-664 *)
    else Some (B, tt).

(* :667-676 check_latest_submit (rc, want) *)
Definition check_latest_submit_m (B : list byte) (rc want : Z) : option (list byte * unit) :=
  if negb (rc =? want) then None else Some (B, tt).                                 (* :674-675 *)

(* :680-688 check_ack_settle *)
Definition check_ack_settle_m (B : list byte) : option (list byte * unit) :=
  if negb (GOT_acks B =? OW_acks B) then None else Some (B, tt).                    (* :686-687 *)

(* :718-721, for (int i = 0; i < OW.n && i < TRANS_MAX; i++): fuel TRANS_MAX *)
Fixpoint state_settle_loop (fuel : nat) (B : list byte) (i : Z) (same why : bool) : bool * bool :=
  match fuel with
  | O => (same, why)
  | S fuel' =>
      if (i <? OW_n B) && (i <? TRANS_MAX) then
        state_settle_loop fuel' B (i + 1)
          (same && ((GOT_t_state B i =? OW_t_state B i) && (GOT_t_old B i =? OW_t_old B i)))   (* :719 *)
          (why && (GOT_t_reason B i =? OW_t_reason B i))                            (* :720 *)
      else (same, why)
  end.

(* :690-742 check_state_settle *)
Definition check_state_settle_m (B : list byte) : option (list byte * unit) :=
  if negb (GOT_e2 B =? OW_e2 B) then None                                           (* :696-697 *)
  else if negb (GOT_e3 B =? OW_e3 B) then None                                      (* :702-703 *)
  else if negb (GOT_ndata B =? OW_ndata B) then None                                (* :709-710 *)
  else if negb (GOT_desk B =? OW_desk B) || negb (GOT_foreign B =? OW_foreign B) then None   (* :715-716 *)
  else
    let '(same, why) :=
      state_settle_loop (Z.to_nat TRANS_MAX) B 0 ((GOT_n B =? OW_n B) && (S_state B =? M_state B)) true in   (* :717-721 *)
    if negb same then None                                                          (* :734-735 *)
    else if negb why then None                                                      (* :740-741 *)
    else Some (B, tt).

(* :744-771 check_inflight_settle. None: the aborts of :751, :757, :764, :770; diginet_session_deadline's (TSess0.v,
   the bound trap of diginet_session.c:495-496). *)
Definition check_inflight_settle_m (B : list byte) : option (list byte * unit) :=
  if negb (GOT_acked B =? OW_acked B) then None                                     (* :750-751 *)
  else if truth (M_fly_on B) && (h_ms_m (Cfg_ack_timeout_ms B) <=? u64 (g_now B - M_fly_sent B)) then None   (* :756-757 *)
  else
    let* d := diginet_session_deadline_m B (g_now B) in                             (* :758 *)
    if (d <? g_now B) || (u64 (g_now B + 1000000) <? d) then None                   (* :763-764 *)
    else if truth (M_fly_on B) && (u64 (M_fly_sent B + h_ms_m (Cfg_ack_timeout_ms B)) <? d) then None   (* :769-770 *)
    else Some (B, tt).

(* :773-783 check_keepalive_settle *)
Definition check_keepalive_settle_m (B : list byte) : option (list byte * unit) :=
  if negb (truth (g_raw B)) && (M_state B =? S_ONLINE) && negb (truth (M_fly_on B))
     && (M_backoff_until B <=? g_now B) && (M_next_ka B <=? g_now B) then None      (* :781-782 *)
  else Some (B, tt).

(* :788-789, for (unsigned i = 0; i < g_nq && !ready; i++): g_q[i] traps once i reaches CMDS_MAX, so fuel
   CMDS_MAX + 1 covers every run; the O case is unreachable *)
Fixpoint drain_loop (fuel : nat) (B : list byte) (allow : bool) (i : Z) (ready : bool) : option bool :=
  match fuel with
  | O => None
  | S fuel' =>
      if (i <? g_nq B) && negb ready then
        if CMDS_MAX <=? i then None                                                 (* g_q[i] *)
        else
          let q := Q_at B i in
          if CMDS_MAX <=? q then None                                               (* g_cmd[q] *)
          else drain_loop fuel' B allow (i + 1) (negb (truth (Cmd_display B q)) || allow)   (* :789 *)
      else Some ready
  end.

(* :785-802 check_latest_drain. None: the abort of :801; g_q[i] / g_cmd[g_q[i]] out of bounds. *)
Definition check_latest_drain_m (B : list byte) : option (list byte * unit) :=
  let allow := negb (truth (M_display_sent B))
               || (Cfg_display_gap_us B <=? u64 (g_now B - M_last_display B)) in    (* :787 *)
  let* ready := drain_loop (S (Z.to_nat CMDS_MAX)) B allow 0 false in               (* :788-789 *)
  if (M_state B =? S_ONLINE) && negb (truth (M_fly_on B)) && (M_backoff_until B <=? g_now B) && ready then None   (* :800-801 *)
  else Some (B, tt).

(* :807-810, for (unsigned i = 0; same && i < g_nq; i++): g_s.queue[i] traps once i reaches QUEUE_MAX, so fuel
   QUEUE_MAX + 1 covers every run; the O case is unreachable *)
Fixpoint queue_loop (fuel : nat) (B : list byte) (i : Z) (same : bool) : option bool :=
  match fuel with
  | O => None
  | S fuel' =>
      if same && (i <? g_nq B) then
        if CMDS_MAX <=? i then None                                                 (* g_q[i] *)
        else
          let q := Q_at B i in
          if CMDS_MAX <=? q then None                                               (* &g_cmd[q], :808 *)
          else if QUEUE_MAX <=? i then None                                         (* g_s.queue[i], :809 *)
          else
            let tl := Cmd_len B q in
            queue_loop fuel' B (i + 1)
              ((S_queue_len B i =? tl)
               && beq_bytes (sub B (A_S_queue_bytes i) (Z.to_nat tl)) (sub B (A_Cmd_bytes q) (Z.to_nat tl)))   (* :809 *)
      else Some same
  end.

(* :804-819 check_latest_queue. None: the abort of :818; g_q[i] / g_cmd[g_q[i]] / g_s.queue[i] out of bounds. *)
Definition check_latest_queue_m (B : list byte) : option (list byte * unit) :=
  let* same := queue_loop (S (Z.to_nat QUEUE_MAX)) B 0 (S_queued B =? g_nq B) in    (* :806-810 *)
  if negb same then None else Some (B, tt).                                         (* :817-818 *)

(* :980-991 settle (ticked). None: the checks'. *)
Definition settle_m (B : list byte) (ticked : Z) : option (list byte * unit) :=
  let* (B1, _) := check_ack_settle_m B in                                           (* :982 *)
  let* (B2, _) := check_state_settle_m B1 in                                        (* :983 *)
  let* (B3, _) := check_inflight_settle_m B2 in                                     (* :984 *)
  let* (B4, _) := check_keepalive_settle_m B3 in                                    (* :985 *)
  if negb (truth (g_raw B4)) then                                                   (* :986 *)
    let* (B5, _) := check_latest_queue_m B4 in                                      (* :987 *)
    if truth ticked then check_latest_drain_m B5 else Some (B5, tt)                 (* :988-989 *)
  else Some (B4, tt).

(* ---- the io and the notices, :823-973 ---- *)

(* :859-862, for (size_t at = 0; at < f.body_len; cmds++): each round moves at by t->len (t not NULL) or to the end;
   a round with t->len = 0 never moves at and the loop never ends (C11 6.8.5p6 lets the compiler assume it ends):
   None, outside the model. Every other round moves at by >= 1: fuel body_len + 1, the O case unreachable.
   pos is at. *)
Fixpoint cmds_loop (fuel : nat) (B : list byte) (body : list byte) (blen pos cmds : Z) : option Z :=
  match fuel with
  | O => None
  | S fuel' =>
      if pos <? blen then
        let* (_, t) := tagged_of_m B (skipn (Z.to_nat pos) body) (blen - pos) in    (* :860 *)
        let step := match t with Some s => Cmd_len B s | None => blen - pos end in  (* :861 *)
        if step =? 0 then None
        else cmds_loop fuel' B body blen (pos + step) (u32 (cmds + 1))
      else Some cmds
  end.

(* :823-899 io_send (ctx, frame, len), len = length frame; returns 0 or -EIO. None: check_sent_frame's,
   check_ack_frame's, check_latest_control's, check_inflight_retry's, check_state_wake's, check_inflight_new's,
   check_latest_frame's, check_keepalive_due's, check_latest_sent's, check_latest_display's aborts; GOT.acks++ /
   GOT.e2++ / GOT.e3++ at INT_MAX (:834, :849, :892); the command count loop's (tagged_of's, or a command of
   length 0). *)
Definition io_send_m (I : timg) (B : list byte) (frame : list byte) : option (list byte * Z) :=
  let len := Z.of_nat (length frame) in
  let fail := g_fail_next B in                                                      (* :826 *)
  let B0 := set_g_fail_next B 0 in                                                  (* :829 *)
  let f := rf frame in                                                              (* :830 *)
  let* (B1, _) := check_sent_frame_m B0 frame in                                    (* :831 *)
  let fc := sf_cmd f in
  (* :883-889, the frame in flight *)
  let fly (Bx : list byte) : option (list byte * unit) :=
    let flen := if len <? SPEC_MAX_FRAME then len else SPEC_MAX_FRAME in            (* :888 *)
    let By := set_M_fly_sent (set_M_fly_retries (set_M_fly_counter (set_M_fly_cmd (set_M_fly_on Bx 1) fc)
                (sf_send f)) 0) (g_now Bx) in                                       (* :883-887 *)
    Some (set_M_fly_frame (set_M_fly_len By flen) (firstn (Z.to_nat flen) frame), tt) in   (* :888-889 *)
  let* (B2, _) :=
    if fc =? SPEC_CMD_ACK then                                                      (* :833 *)
      let* a := int_inc (GOT_acks B1) in                                            (* :834 *)
      let* (B3, _) := check_ack_frame_m (set_GOT_acks B1 a) frame in                (* :835 *)
      check_latest_control_m B3 frame                                               (* :836 *)
    else if (fc =? SPEC_CMD_E2) || (fc =? SPEC_CMD_DATA) then                       (* :838-839 *)
      if truth (sf_retry f) then                                                    (* :840 *)
        let* (B3, _) := check_inflight_retry_m B1 frame in                          (* :841 *)
        Some (set_M_fly_sent (set_M_fly_retries B3 (u32 (M_fly_retries B3 + 1))) (g_now B3), tt)   (* :842-843 *)
      else if fc =? SPEC_CMD_E2 then                                                (* :846 *)
        let* (B3, _) := check_state_wake_m B1 in                                    (* :847 *)
        let* (B4, _) := check_latest_control_m B3 frame in                          (* :848 *)
        let* e2 := int_inc (GOT_e2 B4) in                                           (* :849 *)
        let B5 := set_g_last_counter (set_GOT_e2 B4 e2) (sf_send f) in              (* :849-850 *)
        if truth fail then Some (B5, tt) else fly B5                                (* :851-852 *)
      else
        let body := skipn (Z.to_nat (sf_body f)) frame in                           (* f.body *)
        let blen := sf_body_len f in
        let ka := (blen =? 1) && (at8 body 0 =? 0) && (sf_ncmds f =? 1) in          (* :854 *)
        let* (B3, _) := check_inflight_new_m B1 in                                  (* :857 *)
        let* cmds :=
          if negb (truth (g_raw B3)) && negb ka then cmds_loop (S (Z.to_nat blen)) B3 body blen 0 0   (* :858-862 *)
          else Some (sf_ncmds f) in                                                 (* :863-865 *)
        let* (B4, _) := check_latest_frame_m B3 frame cmds in                       (* :866 *)
        let B5 := set_g_last_counter (set_M_host_counter B4 (sf_send f)) (sf_send f) in   (* :867-868 *)
        let* (B6, _) :=
          if negb (truth (g_raw B5)) && ka then                                     (* :869 *)
            let* (Bk, _) := check_keepalive_due_m B5 in                             (* :870 *)
            let nk := u64 (M_next_ka Bk + h_ms_m (Cfg_keepalive_ms Bk)) in          (* :871 *)
            let Bk1 := set_M_next_ka Bk nk in
            if nk <=? g_now Bk1 then
              Some (set_M_next_ka Bk1 (u64 (g_now Bk1 + h_ms_m (Cfg_keepalive_ms Bk1))), tt)   (* :872-873 *)
            else Some (Bk1, tt)
          else if negb (truth (g_raw B5)) then                                      (* :874 *)
            let* (Bs, disp) := check_latest_sent_m B5 (firstn (Z.to_nat blen) body) blen in   (* :875 *)
            if truth disp then                                                      (* :876 *)
              let* (Bd, _) := check_latest_display_m Bs in                          (* :877 *)
              Some (set_M_last_display (set_M_display_sent Bd 1) (g_now Bd), tt)    (* :878-879 *)
            else Some (Bs, tt)
          else Some (B5, tt) in
        fly B6
    else if fc =? SPEC_CMD_E3 then                                                  (* :891 *)
      let* e3 := int_inc (GOT_e3 B1) in                                             (* :892 *)
      check_latest_control_m (set_GOT_e3 B1 e3) frame                               (* :893 *)
    else Some (B1, tt) in                                                           (* :895-896 *)
  Some (B2, if truth fail then - EIO else 0).                                       (* :898 *)

(* The heap frame F seen from the address p on: the block's bytes from p to its end, at address p (TImg.tframe), the
   frame m_rx_m reads when the C passes p as m_rx's frame argument (m_rx_m reads its frame from tf_addr on and stores
   tf_addr-based pointers). None when F is absent or p lies outside [tf_addr, tf_addr + length]. *)
Definition frame_from (F : option tframe) (p : Z) : option tframe :=
  match F with
  | None => None
  | Some f =>
      let off := p - tf_addr f in
      if (off <? 0) || (Z.of_nat (length (tf_bytes f)) <? off) then None
      else Some (TFrame p (skipn (Z.to_nat off) (tf_bytes f)))
  end.

Lemma frame_from_base : forall f, frame_from (Some f) (tf_addr f) = Some f.
Proof.
  intros [a bs]. unfold frame_from. cbn [tf_addr tf_bytes]. rewrite Z.sub_diag.
  rewrite (proj2 (Z.ltb_ge (Z.of_nat (length bs)) 0) (Nat2Z.is_nonneg (length bs))).
  reflexivity.
Qed.

(* :906-929 io_recv (ctx, buf, cap, timeout_ms), as the harness fix on 835f336c (c47f6290) has it: the model takes
   each frame recv hands over, just before the session reads it (:918-926; the pin's :906-920 ran no model step,
   receive ran it ahead of the poll). R: the world after, the return value, the bytes copied into buf (when the
   return value is > 0, else []). g_rx points into the heap frame F: m_rx (g_rx, n) reads the frame from g_rx on
   (frame_from), and memcpy reads g_rx after m_rx (which writes no g_rx). None: g_rx_times-- at INT_MIN (:916);
   m_rx's, m_tick's; outside the model, a read through g_rx past the frame block. *)
Definition io_recv_m (I : timg) (F : option tframe) (B : list byte) (cap : Z) : option (list byte * Z * list byte) :=
  if truth (g_rx_fail B) then Some (set_g_rx_fail B 0, - EIO, [])                   (* :910-913 *)
  else if (g_rx B =? 0) || (g_rx_times B =? 0) then Some (B, 0, [])                 (* :914-915 *)
  else
    let* t := int_dec (g_rx_times B) in                                             (* :916 *)
    let B1 := set_g_rx_times B t in
    let n := if g_rx_len B1 <? cap then g_rx_len B1 else cap in                     (* :917 *)
    let* B2 :=
      if n =? 0 then (let* (Bt, _) := m_tick_m B1 in Some Bt)                       (* :925-926 *)
      else (let* (Br, _) := m_rx_m I (frame_from F (g_rx B1)) B1 n in Some Br) in   (* :923-924, m_rx (g_rx, n) *)
    let* bytes := frame_read F (g_rx B2) n in                                       (* :927 *)
    let r := bv_swrap 32 n in                                                       (* :928, (int)n *)
    Some (B2, r, if 0 <? r then bytes else []).

(* :931-935 io_now *)
Definition io_now_m (B : list byte) : Z := g_now B.

(* :937-973 notice (ctx, n). None: GOT.t[GOT.n] with GOT.n < 0 (:942-946); GOT.n++ / GOT.acked++ / GOT.desk++ /
   GOT.ndata++ / GOT.foreign++ at INT_MAX (:947, :952, :960, :965, :968); check_state_online's,
   check_inflight_acked's, check_inflight_lost's, check_state_desk's, check_state_data's. *)
Definition notice_m (I : timg) (F : option tframe) (B : list byte) (n : ntc) : option (list byte * unit) :=
  let kind := n_kind n in
  if kind =? N_STATE then                                                           (* :941 *)
    let g := GOT_n B in
    let* B1 :=
      if g <? TRANS_MAX then                                                        (* :942 *)
        if g <? 0 then None
        else Some (set_GOT_t_reason (set_GOT_t_old (set_GOT_t_state B g (n_state n)) g (n_old n)) g (n_reason n))   (* :943-945 *)
      else Some B in
    let* g1 := int_inc g in                                                         (* :947 *)
    let B2 := set_GOT_n B1 g1 in
    if n_state n =? S_ONLINE then check_state_online_m B2 else Some (B2, tt)        (* :948-949 *)
  else if kind =? N_ACKED then                                                      (* :951 *)
    let* a := int_inc (GOT_acked B) in                                              (* :952 *)
    check_inflight_acked_m (set_GOT_acked B a) n                                    (* :953 *)
  else if kind =? N_ACK_LOST then                                                   (* :955 *)
    let* (B1, _) := check_inflight_lost_m B n in                                    (* :956 *)
    Some (set_M_fly_on B1 0, tt)                                                    (* :957 *)
  else if kind =? N_DESK then                                                       (* :959 *)
    let* d := int_inc (GOT_desk B) in                                               (* :960 *)
    check_state_desk_m I F (set_GOT_desk B d) n                                     (* :961 *)
  else if kind =? N_DATA then                                                       (* :963 *)
    let* (B1, _) := check_state_data_m F B n in                                     (* :964 *)
    let* d := int_inc (GOT_ndata B1) in                                             (* :965 *)
    Some (set_GOT_ndata B1 d, tt)
  else if kind =? N_FOREIGN then                                                    (* :967 *)
    let* fo := int_inc (GOT_foreign B) in Some (set_GOT_foreign B fo, tt)           (* :968 *)
  else Some (B, tt).                                                                (* :970-971 *)
