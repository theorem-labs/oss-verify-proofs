(* transport/src/diginet_session.c: diginet_session_config_default (:11-27), diginet_session_init (:56-75),
   ms (:77), inflight_start (:111-117), coalescable (:322-326), diginet_session_submit (:328-349),
   take (:353-386), min64 (:474), diginet_session_deadline (:476-503).

   The world B (TWorld.v) holds g_s and g_cfg. The harness passes &g_s, &g_cfg and its own locals to these
   functions (fuzz_transport.c:1134, :1165, :758, :1081, :1103; the session's own callers pass s), so the
   NULL tests (`!s`, `!c`, `!cfg`, `!io`) are never taken; each is named in a comment.
   Shape: a function that writes the world or can reach a UBSan trap returns option (list byte * R); None = a
   UBSan-trapped operation (none of these functions calls abort()). A function that reads no world and
   cannot trap returns its value (ms_m, min64_m, coalescable_m).
   Integers: uint8_t / uint16_t / uint32_t wrap by DgnSpec's u8 / u16 / u32, uint64_t and size_t by u64
   below; every value read from the world is already in its C type's range (u_at, s32_at of TWorld.v).
   s->queue is struct diginet_cmd queue[512] (diginet_session.h:144, S_queue_N): UBSan's array-bounds check
   traps an access s->queue[i] with i >= 512, and the model is None there. For the address `&s->queue[i]`
   (take, :359) the check lets i = 512 through; the model is None at i = 512 too, which is stricter than the binary
   and is never reached while s->queued <= 512.
   Library functions: body_check, lib_build_code, lib_frame (DgnLib.v, the list byte reading of
   diginet_body_check and diginet_frame_build), the fr_ / ann_ / copy_ functions (DgnSpec.v); what the shared
   model lacks is in TNeed.v. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.

(* ---- constants (values: the C headers cited on each line); DIGINET_OK and DIGINET_E_REFUSED are DgnLib's ---- *)
Definition DIGINET_E_ARG : Z := -1.                   (* include/diginet/diginet.h:60 *)
Definition DIGINET_E_SPACE : Z := -5.                 (* diginet.h:64 *)
Definition DIGINET_MAC_LEN : Z := 6.                  (* diginet.h:32 *)
Definition DIGINET_ETH_HDR_LEN : Z := 14.             (* diginet.h:33 *)
Definition DIGINET_MIN_FRAME_LEN : Z := 60.           (* diginet.h:36 *)
Definition DIGINET_MAX_FRAME_LEN : Z := 1514.         (* diginet.h:37 *)
Definition DIGINET_MAX_BODY_LEN : Z := 1484.          (* diginet.h:38 *)
Definition DIGINET_CMD_DATA : Z := 0x00.              (* diginet.h:48 *)
Definition DIGINET_CMD_ACK : Z := 0xa0.               (* diginet.h:49 *)
Definition DIGINET_CMD_ANNOUNCE : Z := 0xe0.          (* diginet.h:50 *)
Definition DIGINET_CMD_ANNOUNCE_SESSION : Z := 0xe1.  (* diginet.h:51 *)
Definition DIGINET_CMD_WAKE : Z := 0xe2.              (* diginet.h:52 *)
Definition DIGINET_CMD_DISCONNECT : Z := 0xe3.        (* diginet.h:53 *)
Definition DIGINET_SUM_BODY : Z := 0.                 (* diginet.h:78 *)
Definition DIGINET_CMD_MAX_LEN : Z := 24.             (* include/diginet/diginet_codec.h:46 *)
Definition DIGINET_KEY_INPUT : Z := 8.                (* diginet_codec.h:57 *)
Definition DIGINET_KEY_KEEPALIVE : Z := 9.            (* diginet_codec.h:58 *)
Definition DIGINET_S_IDLE : Z := 0.                   (* include/diginet/transport/diginet_session.h:40 *)
Definition DIGINET_S_WAKING : Z := 1.                 (* diginet_session.h:41 *)
Definition DIGINET_S_ONLINE : Z := 2.                 (* diginet_session.h:42 *)
Definition DIGINET_S_CLOSED : Z := 3.                 (* diginet_session.h:43 *)
Definition DIGINET_R_NONE : Z := 0.                   (* diginet_session.h:48 *)
Definition DIGINET_R_WAKE : Z := 1.                   (* diginet_session.h:49 *)
Definition DIGINET_R_ONLINE : Z := 2.                 (* diginet_session.h:50 *)
Definition DIGINET_R_DESK_OFFLINE : Z := 3.           (* diginet_session.h:51 *)
Definition DIGINET_R_SILENCE : Z := 4.                (* diginet_session.h:52 *)
Definition DIGINET_R_FOREIGN : Z := 5.                (* diginet_session.h:53 *)
Definition DIGINET_R_WAKE_TIMEOUT : Z := 6.           (* diginet_session.h:54 *)
Definition DIGINET_R_DESK_DISCONNECT : Z := 7.        (* diginet_session.h:55 *)
Definition DIGINET_R_CLOSED : Z := 8.                 (* diginet_session.h:56 *)
Definition DIGINET_N_DESK : Z := 1.                   (* diginet_session.h:79 *)
Definition DIGINET_N_STATE : Z := 2.                  (* diginet_session.h:80 *)
Definition DIGINET_N_DATA : Z := 3.                   (* diginet_session.h:81 *)
Definition DIGINET_N_ACKED : Z := 4.                  (* diginet_session.h:82 *)
Definition DIGINET_N_ACK_LOST : Z := 5.               (* diginet_session.h:83 *)
Definition DIGINET_N_FOREIGN : Z := 6.                (* diginet_session.h:84 *)
Definition DIGINET_QUEUE_MAX : Z := 512.              (* diginet_session.h:109 *)

(* ---- C helpers ---- *)

(* conversion to uint64_t / size_t (64 bits on riscv64 lp64d): reduction modulo 2^64 *)
Definition u64 (x : Z) : Z := x mod 2 ^ 64.

(* memcmp (x, y, n) == 0 over the first n bytes of x and y *)
Definition memeq (n : nat) (x y : list byte) : bool := forallb (fun i => at8 x i =? at8 y i) (seq 0 n).

(* struct diginet_cmd (include/diginet/diginet_codec.h:64-69) as its 32 bytes: bytes[24] at 0, len at 24,
   display at 25, two padding bytes, key (uint32_t, little-endian) at 28 (the plain image's layout) *)
Definition cmd_len_of (c : list byte) : Z := u_at c 24 1.
Definition cmd_display_of (c : list byte) : Z := u_at c 25 1.
Definition cmd_key_of (c : list byte) : Z := u_at c 28 4.

(* ---- diginet_session_config_default (diginet_session.c:11-27) ----
   The harness's one call passes &g_cfg (fuzz_transport.c:1134): c != NULL, :13-14 not taken. *)
Definition diginet_session_config_default_m (B : list byte) : option (list byte * unit) :=
  let B := upd B OFF_g_cfg (put (Z.to_nat SZ_g_cfg) 0) in   (* :15 memset (c, 0, sizeof *c), sizeof = 60 *)
  let B := set_Cfg_auto_wake B 1 in                     (* :16 *)
  let B := set_Cfg_sum_mode B DIGINET_SUM_BODY in       (* :17 *)
  let B := set_Cfg_keepalive_ms B 10000 in              (* :18 *)
  let B := set_Cfg_ack_timeout_ms B 100 in              (* :19 *)
  let B := set_Cfg_max_retries B 5 in                   (* :20 *)
  let B := set_Cfg_backoff_ms B 300 in                  (* :21 *)
  let B := set_Cfg_offline_ms B 25000 in                (* :22 *)
  let B := set_Cfg_wake_timeout_ms B 3000 in            (* :23 *)
  let B := set_Cfg_display_gap_us B 2000 in             (* :24 *)
  let B := set_Cfg_max_cmds B 48 in                     (* :25 *)
  let B := set_Cfg_max_body B 314 in                    (* :26 *)
  Some (B, tt).

(* ---- diginet_session_init (diginet_session.c:56-75) ----
   s = &g_s, cfg = &g_cfg (fuzz_transport.c:1165); io = the harness's local struct diginet_io, given by its
   four fields io_ctx, io_send, io_recv, io_now (fuzz_transport.c:1127: NULL, io_send, io_recv, io_now);
   notify, ctx = the two last arguments (notice and NULL at :1165). Result: 0 (DIGINET_OK) or -1. *)
Definition diginet_session_init_m (B : list byte) (io_ctx io_send io_recv io_now notify ctx : Z)
    : option (list byte * Z) :=
  (* :58 !s, !cfg, !io are false; !io->send, !notify *)
  if (io_send =? 0) || (notify =? 0) then Some (B, DIGINET_E_ARG)                       (* :58-59 *)
  (* :60-61: uint32_t against int constants, compared unsigned *)
  else if (Cfg_max_cmds B =? 0) || (Cfg_max_body B <? DIGINET_CMD_MAX_LEN) ||
          (DIGINET_MAX_BODY_LEN <? Cfg_max_body B) || (255 <? Cfg_max_cmds B)
  then Some (B, DIGINET_E_ARG)                                                          (* :62 *)
  else
    let cfg := sub B OFF_g_cfg (Z.to_nat SZ_g_cfg) in
    let B1 := upd B OFF_g_s (put (Z.to_nat SZ_g_s) 0) in   (* :63 memset (s, 0, sizeof *s), sizeof = 18264 *)
    let B1 := upd B1 A_S_cfg_host_mac cfg in            (* :64 s->cfg = *cfg, 60 bytes at g_s + 0 *)
    let B1 := set_S_io_ctx B1 io_ctx in                 (* :65 s->io = *io, 32 bytes at g_s + 64 *)
    let B1 := set_S_io_send B1 io_send in
    let B1 := set_S_io_recv B1 io_recv in
    let B1 := set_S_io_now_us B1 io_now in
    let B1 := set_S_notify B1 notify in                 (* :66 *)
    let B1 := set_S_notify_ctx B1 ctx in                (* :67 *)
    let B1 := set_S_state B1 DIGINET_S_IDLE in          (* :68 *)
    if negb (Cfg_desk_mac_set B =? 0) then              (* :69 *)
      let B1 := set_S_desk_mac B1 (Cfg_desk_mac B) in   (* :70 *)
      Some (set_S_desk_known B1 1, DIGINET_OK)          (* :71, :74 *)
    else Some (B1, DIGINET_OK).                         (* :74 *)

(* ---- ms (diginet_session.c:77): (uint64_t)v * 1000u; v is a uint32_t ---- *)
Definition ms_m (v : Z) : Z := u64 (v * 1000).

(* ---- inflight_start (diginet_session.c:111-117); counter is a uint32_t, now a uint64_t ---- *)
Definition inflight_start_m (B : list byte) (counter now : Z) : option (list byte * unit) :=
  let B := set_S_inflight B 1 in                        (* :113 *)
  let B := set_S_inflight_counter B counter in          (* :114 *)
  let B := set_S_inflight_retries B 0 in                (* :115 *)
  Some (set_S_inflight_sent_us B now, tt).              (* :116 *)

(* ---- coalescable (diginet_session.c:322-326), the session's; key is a uint32_t ---- *)
Definition coalescable_m (key : Z) : Z :=
  let k := u8 (Z.shiftr key 16) in                      (* :324 DIGINET_KEY_KIND (key) = (uint8_t)((key) >> 16) *)
  int_of_bool (negb (k =? 0) && negb (k =? DIGINET_KEY_INPUT) && negb (k =? DIGINET_KEY_KEEPALIVE)).  (* :325 *)

(* ---- diginet_session_submit (diginet_session.c:328-349) ----
   c = the 32 bytes of the struct diginet_cmd the caller passes (op_submit's local c, fuzz_transport.c:1070,
   which its memset at :1075 zeroes first). Result: 0, -1 (E_ARG), -10 (E_REFUSED) or -5 (E_SPACE). *)

(* :337-343: for (i = 0; i < s->queued; i++) if (s->queue[i].key == c->key) ...; Some (Some i) = the
   entry it replaces, Some None = the loop ran out. Fuel = s->queued - i, the turns left (nothing in the loop
   writes s->queued); None = s->queue[i] with i >= 512 (UBSan array bounds). *)
Fixpoint submit_find_m (B : list byte) (key i : Z) (fuel : nat) : option (option Z) :=
  match fuel with
  | O => Some None                                      (* i = s->queued: the test of :337 fails *)
  | S f =>
      if S_queue_N <=? i then None                      (* :338 s->queue[i], i >= 512 *)
      else if S_queue_key B i =? key then Some (Some i) (* :338 *)
      else submit_find_m B key (i + 1) f
  end.

Definition diginet_session_submit_m (B : list byte) (c : list byte) : option (list byte * Z) :=
  let len := cmd_len_of c in
  (* :330 !s, !c are false *)
  if (len =? 0) || (DIGINET_CMD_MAX_LEN <? len) then Some (B, DIGINET_E_ARG)            (* :330-331 *)
  else if negb (body_check (firstn (Z.to_nat len) c) =? DIGINET_OK) then               (* :332, c->bytes, c->len *)
    Some (set_S_stats_refused B (u64 (S_stats_refused B + 1)), DIGINET_E_REFUSED)       (* :333-334 *)
  else
    let found := if coalescable_m (cmd_key_of c) =? 0 then Some None                   (* :336 *)
                 else submit_find_m B (cmd_key_of c) 0 (Z.to_nat (S_queued B)) in
    match found with
    | None => None
    | Some (Some i) =>
        let B := upd B (A_S_queue_bytes i) c in                                          (* :339 s->queue[i] = *c *)
        Some (set_S_stats_coalesced B (u64 (S_stats_coalesced B + 1)), DIGINET_OK)      (* :340-341 *)
    | Some None =>
        let q := S_queued B in
        if q =? DIGINET_QUEUE_MAX then Some (B, DIGINET_E_SPACE)                         (* :345-346 *)
        else if S_queue_N <=? q then None                (* :347 s->queue[s->queued], index >= 512 *)
        else Some (set_S_queued (upd B (A_S_queue_bytes q) c) (u32 (q + 1)), DIGINET_OK) (* :347-348 *)
    end.

(* ---- take (diginet_session.c:353-386) ----
   allow_display: the int tick passes (:460, :464). body, body_len, has_display: tick's locals (:461-463).
   Result R = (body, body_len, has_display, taken): body = the body_len bytes take leaves at body[0 ..
   body_len), the only ones tick's send_data reads (:471); bytes a refused command's memcpy left past
   body_len are overwritten by the next command taken, or never read.
   None: s->queue[i] with i >= 512 (UBSan array bounds; see the header for &s->queue[512]); and the memcpy
   of :365 writing past tick's body[1484] (len + c->len > 1484 while it fits max_body), which is not a UBSan
   check but writes tick's stack, outside the world: it needs s->cfg.max_body > 1484, which
   diginet_session_init refuses (:60-61), and nothing else writes s->cfg. *)

(* :378-379: for (unsigned j = i + 1; j < s->queued; j++) s->queue[kept++] = s->queue[j]; called with
   j = i + 1 and fuel = s->queued - j, the turns left *)
Fixpoint take_tail_m (B : list byte) (kept j : Z) (fuel : nat) : option (list byte * Z) :=
  match fuel with
  | O => Some (B, kept)                                 (* j = s->queued: the test of :378 fails *)
  | S f =>
      if (S_queue_N <=? j) || (S_queue_N <=? kept) then None       (* :379, an index >= 512 *)
      else take_tail_m (upd B (A_S_queue_bytes kept) (sub B (A_S_queue_bytes j) 32)) (kept + 1) (j + 1) f
  end.

(* :358-382: the loop from i, with taken, kept, len, *has_display and the body so far; fuel =
   s->queued - i, the turns left (the loop writes queue entries, not s->queued). Result: the world and
   (body, len, *has_display, taken, kept) when the loop ends. *)
Fixpoint take_loop_m (B : list byte) (allow_display : Z) (i taken kept len has_display : Z)
    (body : list byte) (fuel : nat) : option (list byte * (list byte * Z * Z * Z * Z)) :=
  match fuel with
  | O => Some (B, (body, len, has_display, taken, kept))       (* i = s->queued: the test of :358 fails *)
  | S f =>
      if S_queue_N <=? i then None                              (* :359 c = &s->queue[i], i >= 512 *)
      else
      let clen := S_queue_len B i in                            (* c->len, uint8_t *)
      (* :360-361: unsigned taken < uint32_t max_cmds; size_t len + c->len <= max_body (no wrap) *)
      let fits0 := (taken <? S_cfg_max_cmds B) && (len + clen <=? S_cfg_max_body B) &&
                   (negb (allow_display =? 0) || (S_queue_display B i =? 0)) in
      if fits0 && (DIGINET_MAX_BODY_LEN <? len + clen) then None    (* :365 past tick's body[1484] *)
      else
      (* :362-367: memcpy (body + len, c->bytes, c->len): c->len bytes from &c->bytes (a len over 24 reads on
         into the entry and the next ones, all inside g_s); fits = diginet_body_check (body, len + c->len) == 0 *)
      let cand := body ++ sub B (A_S_queue_bytes i) (Z.to_nat clen) in
      let fits := fits0 && (body_check cand =? DIGINET_OK) in
      let '(B1, body1, len1, taken1, hd1, kept1) :=
        if fits then
          (B, cand, len + clen, taken + 1, Z.lor has_display (S_queue_display B i), kept)   (* :368-371 *)
        else
          ((if kept =? i then B
            else upd B (A_S_queue_bytes kept) (sub B (A_S_queue_bytes i) 32)),   (* :373-374 s->queue[kept] = *c *)
           body, len, taken, has_display, kept + 1) in                           (* :375 *)
      if (taken1 =? S_cfg_max_cmds B1) || (len1 =? S_cfg_max_body B1) then    (* :377 *)
        match take_tail_m B1 kept1 (i + 1) (Z.to_nat (S_queued B1 - (i + 1))) with
        | None => None
        | Some (B2, kept2) => Some (B2, (body1, len1, hd1, taken1, kept2))     (* :380 break *)
        end
      else take_loop_m B1 allow_display (i + 1) taken1 kept1 len1 hd1 body1 f
  end.

Definition take_m (B : list byte) (allow_display : Z) : option (list byte * (list byte * Z * Z * Z)) :=
  (* :355-356 taken = kept = 0, len = 0; :357 *has_display = 0 *)
  match take_loop_m B allow_display 0 0 0 0 0 [] (Z.to_nat (S_queued B)) with
  | None => None
  | Some (B1, (body, len, hd, taken, kept)) =>
      Some (set_S_queued B1 kept, (body, len, hd, taken))       (* :383-385 *)
  end.

(* ---- min64 (diginet_session.c:474) ---- *)
Definition min64_m (a b : Z) : Z := if a <? b then a else b.

(* ---- diginet_session_deadline (diginet_session.c:476-503), now a uint64_t ----
   option Z, None = the UBSan array-bounds trap of
   s->queue[i].display (:497) with i >= 512, reached only when s->queued > 512 and queue[0..511] are all
   display writes. *)

(* :495-497: for (unsigned i = 0; i < s->queued && display_only; i++) display_only = s->queue[i].display;
   fuel = s->queued - i, the turns left *)
Fixpoint deadline_display_only_m (B : list byte) (i display_only : Z) (fuel : nat) : option Z :=
  match fuel with
  | O => Some display_only                              (* i = s->queued *)
  | S f =>
      if display_only =? 0 then Some display_only       (* :496 && display_only *)
      else if S_queue_N <=? i then None                 (* :497 s->queue[i], i >= 512 *)
      else deadline_display_only_m B (i + 1) (S_queue_display B i) f
  end.

Definition diginet_session_deadline_m (B : list byte) (now : Z) : option Z :=
  let d := u64 (now + 1000000) in                                                       (* :478 *)
  let st := S_state B in
  (* :479 !s is false *)
  if (st =? DIGINET_S_CLOSED) || (st =? DIGINET_S_IDLE) then Some d                      (* :479-480 *)
  else
  let d := if st =? DIGINET_S_WAKING
           then min64_m d (u64 (S_wake_sent_us B + ms_m (S_cfg_wake_timeout_ms B))) else d in  (* :481-482 *)
  let d := if st =? DIGINET_S_ONLINE then
             let d := min64_m d (u64 (S_last_rx_us B + ms_m (S_cfg_offline_ms B))) in      (* :484 *)
             if S_inflight B =? 0 then                                                    (* :487 *)
               min64_m d (if S_backoff_until_us B <? S_next_keepalive_us B
                          then S_next_keepalive_us B else S_backoff_until_us B)           (* :488-489 *)
             else d
           else d in
  if negb (S_inflight B =? 0) then
    Some (min64_m d (u64 (S_inflight_sent_us B + ms_m (S_cfg_ack_timeout_ms B))))       (* :491-492 *)
  else
  let dq := if (st =? DIGINET_S_ONLINE) && negb (S_queued B =? 0) then                   (* :493 *)
      let t := if now <? S_backoff_until_us B then S_backoff_until_us B else now in      (* :494 *)
      match deadline_display_only_m B 0 1 (Z.to_nat (S_queued B)) with                   (* :495-497 display_only = 1, the loop *)
      | None => None
      | Some display_only =>
          let t := if negb (display_only =? 0) && negb (S_display_sent B =? 0) then       (* :498 *)
                     let g := u64 (S_last_display_us B + S_cfg_display_gap_us B) in
                     if g <? t then t else g                                              (* :499 *)
                   else t in
          Some (min64_m d t)                                                              (* :500 *)
      end
    else Some d in
  match dq with
  | None => None
  | Some d => Some (if d <? now then now else d)                                          (* :502 *)
  end.
