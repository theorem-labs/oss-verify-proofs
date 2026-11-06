(* libdiginet/fuzz_transport: the model of fuzz.h's input cursor and of the operations of fuzz/fuzz_transport.c
   (receive, build_and_receive, op_frame, op_announce, op_submit, LLVMFuzzerTestOneInput) (new file).
   Build-independent: the plain and the ubsan build share it.
   Rules: one function per C function, named <c name>_m; a world B : list byte (TWorld.v) in, the
   world after and the C value out; None exactly when the C code calls abort() or performs an operation UBSan
   traps on (or, where a comment says so, leaves the model); C arithmetic exactly.

   The input bytes. LLVMFuzzerTestOneInput(data, size) reads `size` bytes at `data`; the model takes them as the
   list D (size = length D). The cursor struct fuzz_in { p, n } (fuzz.h:29-32) is modelled by the OFFSET of p into
   D and n: p = data + fi_off. The machine contract relates the two and carries data + size <= 2^64 (the driver's
   buffer is one object), so p++ (fuzz.h:45) and p += n (fuzz.h:67) never overflow a pointer and UBSan's
   pointer-overflow check never fires; the cursor functions are therefore total. A pointer the cursor hands out
   (fuzz_take's *out) is an offset into D as well; the bytes there are `sub D off n`.

   The heap. fuzz_dup (fuzz.h:90) is the only allocation of the harness; the allocator is outside the model.
   receive_m takes the address malloc returned as a parameter `a` (0 = malloc returned NULL, the abort() of
   fuzz.h:86: None). LLVMFuzzerTestOneInput_m takes the addresses of all receives of one run as a STREAM
   A : nat -> Z, A k = the address the k-th receive (k = 0, 1, ...) got. A function rather than a list: it is total,
   so the model has no "addresses ran out" case that is neither the C code's nor the allocator's; the simulation
   layer proves Some for every A with A k <> 0 for every k (the allocator never fails under the statements'
   environment), and the machine layer instantiates A with the addresses its run's allocator returned (only the
   first <= OPS_MAX = 1024 indices are ever read: at most one receive per operation). *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess.
Import ListNotations.
Open Scope Z_scope.

(* The option monad of the model: a step that is None (abort / trap) ends the run. *)
Local Notation "'let?' p ':=' e 'in' b" :=
  (match e with Some p => b | None => None end)
  (at level 200, p pattern, e at level 100, b at level 200, right associativity).

(* ---------------------------------------------------------------- constants *)
(* TCb.v defines the harness's constants and MAC tables with their C names (OPS_MAX, TAG, CMDS_MAX, QUEUE_MAX,
   PENDING, REPLACED, SPEC_OK, SPEC_E_SPACE, SPEC_E_REFUSED, SPEC_MAX_FRAME, SPEC_MAX_BODY, SPEC_CMD_MAX,
   SPEC_ANN_VERSION, SPEC_ANN_NAME, SPEC_ANN_MIN, SPEC_CMD_E0, SPEC_CMD_E1, DIGINET_SUM_BODY, DIGINET_SUM_ZERO;
   HOST, OTHER, DESK, DESK2, NOTDD, SPEC_BCAST as list byte); this file uses those. *)
Definition FUZZ_INPUT_MAX : Z := 67108864.  (* fuzz.h:23, (size_t)64 << 20 *)

(* ---------------------------------------------------------------- fuzz.h: the cursor *)

(* fuzz.h:29-32 struct fuzz_in { const uint8_t *p; size_t n; }: p as its offset into D. *)
Record fuzz_in := FuzzIn { fi_off : Z; fi_n : Z }.

(* fuzz.h:34-38 fuzz_in(data, size) = { data, size }. *)
Definition fuzz_in_m (size : Z) : fuzz_in := FuzzIn 0 size.

(* fuzz.h:40-46 fuzz_u8: 0 when n == 0; else n--, the byte *p, p++. *)
Definition fuzz_u8_m (D : list byte) (c : fuzz_in) : fuzz_in * Z :=
  if fi_n c =? 0 then (c, 0)
  else (FuzzIn (fi_off c + 1) (fi_n c - 1), at8 D (Z.to_nat (fi_off c))).

(* fuzz.h:50-54 fuzz_u16: lo = fuzz_u8, then (uint16_t)(lo | (uint16_t)fuzz_u8 << 8), little-endian; the shift
   is of an int <= 255 by 8, no overflow. *)
Definition fuzz_u16_m (D : list byte) (c : fuzz_in) : fuzz_in * Z :=
  let (c1, lo) := fuzz_u8_m D c in
  let (c2, hi) := fuzz_u8_m D c1 in
  (c2, Z.lor lo (Z.shiftl hi 8) mod 2^16).

(* fuzz.h:63-70 fuzz_take(in, want, out): n = min(want, in->n); *out = p; p += n; in->n -= n; returns n.
   Result: the cursor after, *out (an offset into D), n. *)
Definition fuzz_take_m (c : fuzz_in) (want : Z) : fuzz_in * Z * Z :=
  let n := if want <? fi_n c then want else fi_n c in
  (FuzzIn (fi_off c + n) (fi_n c - n), fi_off c, n).

(* fuzz.h:73-76 fuzz_record(in, out) = fuzz_take(in, fuzz_u16(in), out). *)
Definition fuzz_record_m (D : list byte) (c : fuzz_in) : fuzz_in * Z * Z :=
  let (c1, w) := fuzz_u16_m D c in
  fuzz_take_m c1 w.

(* fuzz.h:81-88 fuzz_alloc(n): b = malloc(n ? n : 1); NULL -> abort() (fuzz.h:86, "the harness's own
   allocation failed"; not reachable under the statements' environment, modelled as None). The allocation itself
   is outside the model: `a` is the address malloc returned. *)
Definition fuzz_alloc_m (a : Z) : option Z := if a =? 0 then None else Some a.

(* fuzz.h:90-96 fuzz_dup(p, n): fuzz_alloc(n), then memcpy of the n bytes at p when n != 0. Result: the heap
   block (address and the bytes copied into it), the current frame of TImg.v. *)
Definition fuzz_dup_m (a : Z) (bytes : list byte) : option tframe :=
  let? b := fuzz_alloc_m a in
  Some (TFrame b bytes).

(* ---------------------------------------------------------------- fuzz_transport.c: the operations *)

(* fuzz_transport.c:995-1025 receive(p, n, by_poll, poll_flags), as the harness fix on 835f336c (c47f6290) has it.
   `a`: the address fuzz_dup's malloc returned; `bytes`: the n bytes at p (n = length bytes). spec_read_frame
   (spec.h:199) memsets f, so f.send is 0 unless the code is SPEC_OK (DgnSpec fr_code / fr_send). The frame block is
   the current heap frame F of every callee (m_rx stores pointers into it; io_recv runs m_rx on g_rx = frame and
   copies from it). The by-poll branch runs no model step itself (:1009-1010; the pin's :1001-1007 ran m_rx, m_tick
   and m_rx ahead of the poll): io_recv (TCb.v io_recv_m, :923-926) runs m_rx on each frame it hands over and
   m_tick on an empty one. *)
Definition receive_m (I : timg) (B : list byte) (a : Z) (bytes : list byte) (by_poll poll_flags : Z)
    : option (list byte * unit) :=
  let n := Z.of_nat (length bytes) in
  let? fr := fuzz_dup_m a bytes in                                          (* :997 *)
  let F := Some fr in
  let? (B1, _) := op_begin_m B in                                           (* :1001 *)
  let B2 := set_g_rx_send B1 (if fr_code bytes =? 0 then fr_send bytes else 0) in   (* :1002-1003 *)
  let? (B3, ticked) :=
    if negb (by_poll =? 0) then
      let got := if SPEC_MAX_FRAME <? n then SPEC_MAX_FRAME else n in       (* :1005 *)
      let twice := Z.land poll_flags 1 in                                   (* :1006 *)
      let fails := Z.land (Z.shiftr poll_flags 1) 1 in
      let gbytes := firstn (Z.to_nat got) bytes in
      let B2a := set_g_rx_send B2 (if fr_code gbytes =? 0 then fr_send gbytes else 0) in   (* :1007-1008 *)
      let ticked := if fails =? 0 then 1 else 0 in                          (* :1011 *)
      let B2c := set_g_rx_fail
                   (set_g_rx_times (set_g_rx_len (set_g_rx B2a (tf_addr fr)) got)
                      (if twice =? 0 then 1 else 2))
                   fails in                                                 (* :1012-1015 *)
      let? (B2d, _) := diginet_session_poll_m I F B2c 0 in                  (* :1016 *)
      Some (set_g_rx_fail (set_g_rx B2d 0) 0, ticked)                       (* :1017-1018 *)
    else
      let? (Bx, ticked) := m_rx_m I F B2 n in                               (* :1020 *)
      let? (By, _) := diginet_session_rx_m I F Bx bytes (g_now Bx) in       (* :1021 *)
      Some (By, ticked) in
  let? (B4, _) := settle_m B3 ticked in                                     (* :1023 *)
  Some (B4, tt).                                                            (* :1024 free(frame): outside the world *)

(* fuzz_transport.c:1027-1033 build_and_receive(dst, src, send, ack, retry, cmd, body, len):
   n = spec_build_frame(frame, dst, src, send, ack, retry, cmd, 1, body, len, 0) (TNeed.v) into the local
   uint8_t frame[SPEC_MAX_FRAME], then receive(frame, n, 0, 0) of the n bytes it wrote.
   A body past SPEC_MAX_BODY makes n > SPEC_MAX_FRAME, and spec_build_frame writes past frame[] (undefined
   behaviour UBSan does not trap): outside the model, None. Never reached: op_frame passes len <= 1484,
   op_announce 34. *)
Definition build_and_receive_m (I : timg) (B : list byte) (a : Z) (dst src : list byte) (send ack retry cmd : Z)
    (body : list byte) : option (list byte * unit) :=
  if SPEC_MAX_BODY <? Z.of_nat (length body) then None
  else
    let (frame, n) := spec_build_frame dst src send ack retry cmd 1 body 0 in      (* :1031 *)
    receive_m I B a frame 0 0.                                                     (* :1032, length frame = n *)

(* fuzz_transport.c:1037-1041 the tables of op_frame (rodata; SRC / DST hold pointers to the MAC tables, the model
   holds their bytes). *)
Definition op_frame_CMD : list Z := [0x00; 0xa0; 0xe0; 0xe1; 0xe2; 0xe3; 0x55].
Definition op_frame_SRC : list (list byte) := [DESK; DESK2; HOST; NOTDD].
Definition op_frame_DST : list (list byte) := [HOST; SPEC_BCAST; OTHER; HOST].

(* fuzz_transport.c:1035-1050 op_frame(in). Every table index is in bounds (sel >> 5 & 3, sel >> 3 & 3 < 4,
   (sel & 7) % 7 < 7). Result: the world after and the cursor after. *)
Definition op_frame_m (I : timg) (B : list byte) (D : list byte) (a : Z) (c : fuzz_in)
    : option (list byte * fuzz_in) :=
  let (c1, sel) := fuzz_u8_m D c in                                         (* :1043 *)
  let (c2, send) := fuzz_u16_m D c1 in                                      (* :1044 *)
  let (c3, ack0) := fuzz_u16_m D c2 in
  let ack := if Z.land sel 0x80 =? 0 then ack0 else g_last_counter B in     (* :1045-1046 *)
  let (c4, r) := fuzz_u8_m D c3 in
  let retry := Z.land r 3 in                                                (* :1047 *)
  let (c5, w) := fuzz_u16_m D c4 in
  let '(c6, off, len) := fuzz_take_m c5 (w mod (SPEC_MAX_BODY + 1)) in      (* :1048 *)
  let? (B1, _) :=
    build_and_receive_m I B a
      (nth (Z.to_nat (Z.land (Z.shiftr sel 5) 3)) op_frame_DST [])
      (nth (Z.to_nat (Z.land (Z.shiftr sel 3) 3)) op_frame_SRC [])
      send ack retry (nth (Z.to_nat (Z.land sel 7 mod 7)) op_frame_CMD 0)
      (sub D off (Z.to_nat len)) in                                         (* :1049 *)
  Some (B1, c6).

(* fuzz_transport.c:1054 NAME[3] = { "CNTRL|24", "MAINUNIT", "OTHER" }: the bytes strlen counts. *)
Definition op_announce_NAME : list (list byte) :=
  [bs [0x43; 0x4e; 0x54; 0x52; 0x4c; 0x7c; 0x32; 0x34];
   bs [0x4d; 0x41; 0x49; 0x4e; 0x55; 0x4e; 0x49; 0x54];
   bs [0x4f; 0x54; 0x48; 0x45; 0x52]].
(* :1063 "1.37" *)
Definition ANN_VERSION_137 : list byte := bs [0x31; 0x2e; 0x33; 0x37].

(* fuzz_transport.c:1052-1066 op_announce(in): a 34-byte announce body (uint8_t body[SPEC_ANN_MIN + 1]), zeros,
   then HOST at mac (mac < 10) or OTHER at mac - 10 (10 <= mac < 13), "1.37" at 15, NAME[name] at 24; then the
   e1 (sel & 1) or e0 from DESK to the broadcast address. Every write is inside body[]. *)
Definition op_announce_m (I : timg) (B : list byte) (D : list byte) (a : Z) (c : fuzz_in)
    : option (list byte * fuzz_in) :=
  let (c1, sel) := fuzz_u8_m D c in                                         (* :1055 *)
  let (c2, m) := fuzz_u8_m D c1 in
  let mac := m mod 16 in
  let (c3, nm) := fuzz_u8_m D c2 in
  let name := nm mod 3 in
  let body0 := repeat (b8 0) (Z.to_nat (SPEC_ANN_MIN + 1)) in              (* :1058 *)
  let body1 := if mac <? 10 then upd body0 mac HOST                         (* :1059-1060 *)
               else if mac <? 13 then upd body0 (mac - 10) OTHER            (* :1061-1062 *)
               else body0 in
  let body2 := upd body1 SPEC_ANN_VERSION ANN_VERSION_137 in                (* :1063 *)
  let body3 := upd body2 SPEC_ANN_NAME (nth (Z.to_nat name) op_announce_NAME []) in   (* :1064 *)
  let? (B1, _) :=
    build_and_receive_m I B a SPEC_BCAST DESK 0 0 0
      (if Z.land sel 1 =? 0 then SPEC_CMD_E0 else SPEC_CMD_E1) body3 in     (* :1065 *)
  Some (B1, c3).

(* struct diginet_cmd (include/diginet/diginet_codec.h:64-69) as its 32 bytes: bytes[24] @0, len @24,
   display @25, the 2 padding bytes @26 (0: op_submit memsets c), key (u32 LE) @28. *)
Definition cmd_struct (bytes : list byte) (len display key : Z) : list byte :=
  bytes ++ [b8 len; b8 display; b8 0; b8 0] ++ put 4 key.

(* fuzz_transport.c:1097-1101: at = the first i < g_nq with g_cmd[g_q[i]].key == key, or -1.
   g_q[i] with i >= CMDS_MAX and g_cmd[s] with s >= CMDS_MAX index past the array: UBSan trap, None.
   Fuel: the C bound is g_nq, but i reaches CMDS_MAX = 1024 at the latest (it returns or traps there), so fuel
   CMDS_MAX + 1 from i = 0 is never exhausted. *)
Fixpoint submit_find_at (fuel : nat) (B : list byte) (key i : Z) : option Z :=
  match fuel with
  | O => None
  | S f =>
      if i <? g_nq B then
        if CMDS_MAX <=? i then None
        else let s := Q_at B i in
             if CMDS_MAX <=? s then None
             else if Cmd_key B s =? key then Some i
             else submit_find_at f B key (i + 1)
      else Some (-1)
  end.

(* fuzz_transport.c:1068-1122 op_submit(in). Result: the world after and the cursor after.
   :1076 c.key = SPEC_KEY(fuzz_u8(in) % 9 + 1, fuzz_u8(in)): the order of the two reads is unspecified in C; both
   binaries read the kind's byte first (plain 0x13964 lbu 1(s4) is the one reduced % 9 and shifted << 16; ubsan
   0x13e88 reads the address byte 2(s5) after the kind's). SPEC_KEY = (u32)kind << 16 | (addr & 0xffff) is DgnSpec's
   KEY (kind <= 9: the shift loses no bit).
   :1087 memset(&g_cmd[serial], ...): serial > CMDS_MAX traps (array bounds of &g_cmd[]); serial = CMDS_MAX writes
   past g_cmd (undefined behaviour, untrapped): None for both (never: g_ncmd <= ops < OPS_MAX = CMDS_MAX). *)
Definition op_submit_m (B : list byte) (D : list byte) (c : fuzz_in) : option (list byte * fuzz_in) :=
  let before := S_queued B in                                               (* :1072 *)
  let? (B1, _) := op_begin_m B in                                           (* :1074 *)
  let (c1, kb) := fuzz_u8_m D c in                                          (* :1076 *)
  let (c2, ab) := fuzz_u8_m D c1 in
  let key := KEY (kb mod 9 + 1) ab in                                       (* DgnSpec KEY = SPEC_KEY *)
  let (c3, db) := fuzz_u8_m D c2 in
  let display := Z.land db 1 in                                             (* :1077 *)
  if negb (g_raw B1 =? 0) then                                              (* :1078 *)
    let (c4, w) := fuzz_u16_m D c3 in
    let '(c5, off, t) := fuzz_take_m c4 (w mod (SPEC_CMD_MAX + 1)) in
    let len := t mod 2^8 in                                                 (* :1079 (uint8_t) *)
    let cbytes := sub D off (Z.to_nat len) ++ repeat (b8 0) (Z.to_nat (24 - len)) in   (* :1080 *)
    let cs := cmd_struct cbytes len display key in
    let? (B2, rc) := diginet_session_submit_m B1 cs in                      (* :1081 *)
    let? (B3, _) := check_refusal_submit_m B2 cs rc before in               (* :1082 *)
    let? (B4, _) := settle_m B3 0 in                                        (* :1083 *)
    Some (B4, c5)
  else
    let serial := g_ncmd B1 in                                              (* :1086 *)
    if CMDS_MAX <=? serial then None
    else
    let B2 := upd B1 (A_Cmd_st serial) (repeat (b8 0) (Z.to_nat Cmd_ESZ)) in   (* :1087 *)
    let (c4, lb) := fuzz_u8_m D c3 in
    let len := lb mod 22 + 3 in                                             (* :1088 *)
    let '(c5, off, n) := fuzz_take_m c4 (len - 3) in                        (* :1092 *)
    let cbytes := [b8 TAG; b8 (Z.land serial 0x7f); b8 (Z.land (Z.shiftr serial 7) 0x7f)]
                  ++ sub D off (Z.to_nat n) ++ repeat (b8 0) (Z.to_nat (21 - n)) in   (* :1089-1093 *)
    let sys := system_at (firstn (Z.to_nat len) cbytes) in                  (* :1096 spec_system_at >= 0 *)
    let? at_ :=                                                             (* :1097-1101 *)
      if negb (h_coalescable_m key =? 0)
      then submit_find_at (S (Z.to_nat CMDS_MAX)) B2 key 0
      else Some (-1) in
    let want := if sys then SPEC_E_REFUSED                                  (* :1102 *)
                else if (at_ <? 0) && (g_nq B2 =? QUEUE_MAX) then SPEC_E_SPACE
                else SPEC_OK in
    let cs := cmd_struct cbytes len display key in
    let? (B3, rc) := diginet_session_submit_m B2 cs in                      (* :1103 *)
    let? (B4, _) := check_refusal_submit_m B3 cs rc before in               (* :1104 *)
    let? (B5, _) := if sys then Some (B4, tt) else check_latest_submit_m B4 rc want in   (* :1105-1106 *)
    let? B6 :=
      if want =? SPEC_OK then                                               (* :1107 *)
        let Bw := set_Cmd_bytes
                    (set_Cmd_len (set_Cmd_display (set_Cmd_key (set_Cmd_st B5 serial PENDING) serial key)
                                    serial display) serial len)
                    serial (firstn (Z.to_nat len) cbytes) in                (* :1108-1112 *)
        if 0 <=? at_ then                                                   (* :1113 *)
          let q := Q_at Bw at_ in
          if CMDS_MAX <=? q then None                                       (* :1114 g_cmd[g_q[at]] *)
          else Some (set_Q_at (set_Cmd_st Bw q REPLACED) at_ serial)        (* :1114-1115 *)
        else
          let nq := g_nq Bw in
          if CMDS_MAX <=? nq then None                                      (* :1117 g_q[g_nq] *)
          else Some (set_g_nq (set_Q_at Bw nq serial) ((nq + 1) mod 2^32))  (* :1117 g_q[g_nq++] = serial *)
      else Some B5 in
    let B7 := set_g_ncmd B6 ((g_ncmd B6 + 1) mod 2^32) in                   (* :1120 g_ncmd++ (unsigned) *)
    let? (B8, _) := settle_m B7 0 in                                        (* :1121 *)
    Some (B8, c5).

(* ---------------------------------------------------------------- LLVMFuzzerTestOneInput *)

(* :1126 SCALE[4] = { 1, 1000, 100000, 1000000 } *)
Definition LLVMFuzzerTestOneInput_SCALE : list Z := [1; 1000; 100000; 1000000].

(* One operation of the loop of LLVMFuzzerTestOneInput, fuzz_transport.c:1169-1215: the switch on
   fuzz_u8(&in) % 9. k: the number of receives so far (the index into the address stream A). Result: the world
   after, the cursor after, the receive count after. Every case that receives (0, 1, 2, 8) receives once.
   Cases 3 to 7 run with no heap frame (F = None): the frame of an earlier receive is freed. *)
Definition LLVMFuzzerTestOneInput_op_m (I : timg) (B : list byte) (A : nat -> Z) (D : list byte) (c : fuzz_in)
    (k : nat) : option (list byte * (fuzz_in * nat)) :=
  let (c1, opb) := fuzz_u8_m D c in                                         (* :1170 *)
  let op := opb mod 9 in
  if op =? 0 then                                                           (* :1171-1174 *)
    let '(c2, off, n) := fuzz_record_m D c1 in
    let? (B1, _) := receive_m I B (A k) (sub D off (Z.to_nat n)) 0 0 in
    Some (B1, (c2, S k))
  else if op =? 1 then                                                      (* :1175-1177 *)
    let? (B1, c2) := op_frame_m I B D (A k) c1 in
    Some (B1, (c2, S k))
  else if op =? 2 then                                                      (* :1178-1180 *)
    let? (B1, c2) := op_announce_m I B D (A k) c1 in
    Some (B1, (c2, S k))
  else if op =? 3 then                                                      (* :1181-1189 *)
    let (c2, sb) := fuzz_u8_m D c1 in
    let scale := nth (Z.to_nat (sb mod 4)) LLVMFuzzerTestOneInput_SCALE 0 in   (* :1182 *)
    let? (B1, _) := op_begin_m B in                                         (* :1183 *)
    let (c3, t) := fuzz_u16_m D c2 in
    let B2 := set_g_now B1 ((g_now B1 + scale * t) mod 2^64) in             (* :1184 uint64_t += *)
    let? (B3, _) := m_tick_m B2 in                                          (* :1185 *)
    let? (B4, _) := diginet_session_tick_m I None B3 (g_now B3) in          (* :1186 *)
    let? (B5, _) := settle_m B4 1 in                                        (* :1187 *)
    Some (B5, (c3, k))
  else if op =? 4 then                                                      (* :1190-1192 *)
    let? (B1, c2) := op_submit_m B D c1 in
    Some (B1, (c2, k))
  else if op =? 5 then                                                      (* :1193-1199 *)
    let? (B1, _) := op_begin_m B in                                         (* :1194 *)
    let? (B2, want) := m_wake_m B1 in                                       (* :1195 *)
    let? (B3, rc) := diginet_session_wake_m I None B2 (g_now B2) in         (* :1196 *)
    let? (B4, _) := check_state_wake_code_m B3 rc want in
    let? (B5, _) := settle_m B4 0 in                                        (* :1197 *)
    Some (B5, (c1, k))
  else if op =? 6 then                                                      (* :1200-1205 *)
    let? (B1, _) := op_begin_m B in                                         (* :1201 *)
    let? (B2, _) := m_close_m B1 in                                         (* :1202 *)
    let? (B3, _) := diginet_session_close_m I None B2 (g_now B2) in         (* :1203 *)
    let? (B4, _) := settle_m B3 0 in                                        (* :1204 *)
    Some (B4, (c1, k))
  else if op =? 7 then                                                      (* :1206-1208 *)
    Some (set_g_fail_next B 1, (c1, k))
  else                                                                      (* :1209-1214 default *)
    let (c2, pf) := fuzz_u8_m D c1 in
    let '(c3, off, n) := fuzz_record_m D c2 in
    let? (B1, _) := receive_m I B (A k) (sub D off (Z.to_nat n)) 1 pf in
    Some (B1, (c3, S k)).

(* fuzz_transport.c:1168 for (int ops = 0; ops < OPS_MAX && in.n; ops++): fuel = OPS_MAX - ops (ops <= 1024, the
   int never overflows). *)
Fixpoint LLVMFuzzerTestOneInput_loop_m (fuel : nat) (I : timg) (B : list byte) (A : nat -> Z) (D : list byte)
    (c : fuzz_in) (k : nat) : option (list byte * unit) :=
  match fuel with
  | O => Some (B, tt)                                                       (* ops == OPS_MAX *)
  | S f =>
      if fi_n c =? 0 then Some (B, tt)                                      (* in.n == 0 *)
      else
        let? (B1, (c1, k1)) := LLVMFuzzerTestOneInput_op_m I B A D c k in
        LLVMFuzzerTestOneInput_loop_m f I B1 A D c1 k1
  end.

(* fuzz_transport.c:1124-1218 LLVMFuzzerTestOneInput(data, size), data = the bytes D, size = length D.
   The prologue: the config from the cursor (:1133-1148), the scalars and M (:1150-1158), then
   diginet_session_init(&g_s, &g_cfg, &io, notice, NULL) with io = { NULL, io_send, io_recv, io_now } (:1127);
   != SPEC_OK -> abort() (:1165-1166). Then the loop; returns 0. *)
Definition LLVMFuzzerTestOneInput_m (I : timg) (B : list byte) (A : nat -> Z) (D : list byte)
    : option (list byte * Z) :=
  let size := Z.of_nat (length D) in
  if FUZZ_INPUT_MAX <=? size then Some (B, 0) else                          (* :1130-1131 *)
  let c0 := fuzz_in_m size in                                               (* :1132 *)
  let (c1, flags) := fuzz_u8_m D c0 in                                      (* :1133 *)
  let? (B1, _) := diginet_session_config_default_m B in                     (* :1134 *)
  let B2 := set_Cfg_host_mac B1 HOST in                                     (* :1135 *)
  let B3 := set_Cfg_auto_wake B2 (Z.land flags 1) in                        (* :1136 *)
  let B4 := set_Cfg_sum_mode B3
              (if Z.land flags 2 =? 0 then DIGINET_SUM_BODY else DIGINET_SUM_ZERO) in   (* :1137 *)
  let B5 := set_Cfg_desk_mac_set B4 (Z.land (Z.shiftr flags 2) 1) in        (* :1138 *)
  let B6 := set_Cfg_desk_mac B5 DESK in                                     (* :1139 *)
  let (c2, v1) := fuzz_u8_m D c1 in
  let B7 := set_Cfg_max_retries B6 (v1 mod 8) in                            (* :1140 *)
  let (c3, v2) := fuzz_u8_m D c2 in
  let B8 := set_Cfg_ack_timeout_ms B7 ((1 + v2) mod 2^32) in                (* :1141 *)
  let (c4, v3) := fuzz_u16_m D c3 in
  let B9 := set_Cfg_keepalive_ms B8 ((1 + v3) mod 2^32) in                  (* :1142 *)
  let (c5, v4) := fuzz_u8_m D c4 in
  let B10 := set_Cfg_backoff_ms B9 v4 in                                    (* :1143 *)
  let (c6, v5) := fuzz_u16_m D c5 in
  let B11 := set_Cfg_offline_ms B10 ((1 + v5) mod 2^32) in                  (* :1144 *)
  let (c7, v6) := fuzz_u16_m D c6 in
  let B12 := set_Cfg_wake_timeout_ms B11 ((1 + v6) mod 2^32) in             (* :1145 *)
  let (c8, v7) := fuzz_u16_m D c7 in
  let B13 := set_Cfg_display_gap_us B12 v7 in                               (* :1146 *)
  let (c9, v8) := fuzz_u8_m D c8 in
  let B14 := set_Cfg_max_cmds B13 ((1 + v8 mod 255) mod 2^32) in            (* :1147 *)
  let (c10, v9) := fuzz_u16_m D c9 in
  let B15 := set_Cfg_max_body B14
               ((SPEC_CMD_MAX + v9 mod (SPEC_MAX_BODY - SPEC_CMD_MAX + 1)) mod 2^32) in   (* :1148 *)
  let B16 := set_g_raw B15 (Z.land (Z.shiftr flags 3) 1) in                 (* :1150 *)
  let B17 := set_g_now B16 1000000 in                                       (* :1151 *)
  let B18 := set_g_fail_next B17 0 in                                       (* :1152 *)
  let B19 := set_g_last_counter B18 0 in                                    (* :1153 *)
  let B20 := upd B19 OFF_M (repeat (b8 0) (Z.to_nat SZ_M)) in               (* :1154 memset(&M, 0, sizeof M) *)
  let B21 := set_M_desk_known B20 (Cfg_desk_mac_set B20) in                 (* :1155 *)
  let B22 := set_M_desk B21 DESK in                                         (* :1156 *)
  let B23 := set_g_ncmd (set_g_nq B22 0) 0 in                               (* :1157 g_ncmd = g_nq = 0 *)
  let B24 := set_g_rx B23 0 in                                              (* :1158 *)
  let? (B25, rc) := diginet_session_init_m B24 0 (ti_io_send I) (ti_io_recv I) (ti_io_now I)
                      (ti_notice I) 0 in                                    (* :1165 *)
  if negb (rc =? SPEC_OK) then None                                         (* :1166 abort() *)
  else
    let? (B26, _) := LLVMFuzzerTestOneInput_loop_m (Z.to_nat OPS_MAX) I B25 A D c10 O in   (* :1168-1216 *)
    Some (B26, 0).                                                          (* :1217 *)
