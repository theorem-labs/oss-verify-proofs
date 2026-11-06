(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Spec/DgnSpec.v; 21 of its 714 lines of code are new or changed and 21 lines of the source are left out. *)
(* libdiginet's Gallina model, part one (DgnLib.v is part two). Pure Gallina:
   - fuzz/spec.h, the protocol as the harnesses read it: spec_be16, spec_be32, spec_sum_at,
     spec_read_frame, spec_system_at, spec_msg_step, spec_segments, spec_event_of;
   - folded from fuzz_codec's model with their names kept: spec.h's two desks SPEC_C24 / SPEC_PC
     (desk, c24, pc), SPEC_KEY (KEY), four return codes (E_ARG, E_SPACE, E_REFUSED, E_RANGE),
     struct diginet_cmd (cmd) and spec_segments as that model writes it (spec_segments_spec);
   - the library's result structs (include/diginet/diginet.h, include/diginet/diginet_codec.h):
     dgn_cursor (dc_), dgn_msg (dm_), dgn_event (de_);
   - the frame as functions of the bytes of a frame, folded from fuzz_frame's model with its names
     kept (fuzz/spec.h at 835f336c): spec_be16 and rd16 (be16), spec_be32 and rd32 (be32), spec_sum
     and diginet_sum16 (sum16, spec_sum, lib_sum16), spec_read_frame and diginet_frame_parse
     (the fr_ functions), spec_build_frame (build_frame), what diginet_frame_build answers as
     fuzz_frame holds it (build_code), spec_strz_len (strz_len), spec_system_at (sys_hit,
     system_at), field_len of fuzz/fuzz_frame.c, and src/diginet_frame.c's
     diginet_mac_is_digidesign (oui_of), diginet_frame_is_keepalive (keepalive_of), copy_strz
     (copy_strz) and diginet_announce_parse (the ann_ functions).
   The checks and loops of a harness are in that harness's file (fuzz_decode: DgnDecHarness.v).
   Nothing here walks the binary.

   Conventions. A byte buffer is a list Z, each element in [0, 256) (riscv64 lp64d: char is
   unsigned); byte i is byte_at b i. Lengths, positions and every C integer are Z. A pointer
   into a buffer is modelled as its offset in that buffer. Outside the folded parts, each C
   integer conversion is modelled exactly by u8 / u16 / u32 / s8 / s16 and names its file:line;
   the parts folded from fuzz_frame's and fuzz_codec's models write conversions as those models
   do (b8 / bz, mod 2^16, KEY's Z.lor / Z.land) and name the C they follow. size_t arithmetic
   never wraps on the harnesses' domain: their input is under fuzz.h's FUZZ_INPUT_MAX = 2^26
   bytes (fuzz.h:23; fuzz_decode.c:289, fuzz_frame.c:270), so every length and position is
   under 2^26; no definition here needs that as a hypothesis, since each one is written for the
   values C computes there.
   Loops are structural recursions whose fuel is the exact bound of the C loop.
   The folded frame part reads a frame as a list byte, a position in it as a nat and a byte or a
   field value as a Z (at8); DgnLib.v's linking lemmas join it to the list Z reading
   (spec_read_frame_fr, spec_system_at_system_at). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* ---- C integers and bytes ---- *)

(* conversion to uint8_t, uint16_t, uint32_t: reduction modulo 2^N (C11 6.3.1.3p2) *)
Definition u8 (x : Z) : Z := x mod 256.
Definition u16 (x : Z) : Z := x mod 65536.
Definition u32 (x : Z) : Z := x mod 2 ^ 32.
(* conversion to int8_t, int16_t: two's complement wrap, which is GCC's implementation-defined
   choice for an out-of-range value (C11 6.3.1.3p3) *)
Definition s8 (x : Z) : Z := (x + 128) mod 256 - 128.
Definition s16 (x : Z) : Z := (x + 32768) mod 65536 - 32768.

(* b[i] *)
Definition byte_at (b : list Z) (i : Z) : Z := nth (Z.to_nat i) b 0.

(* 0, 1, ..., n - 1 *)
Definition zseq (n : nat) : list Z := map Z.of_nat (seq 0 n).

(* memcmp (x, y, n) == 0, over unsigned bytes *)
Definition bytes_eq (n : Z) (x y : list Z) : bool :=
  forallb (fun k => byte_at x k =? byte_at y k) (zseq (Z.to_nat n)).

(* ---- constants of fuzz/spec.h ---- *)

Definition SPEC_ETHERTYPE : Z := 34911.           (* spec.h:27, 0x885f *)
Definition SPEC_MAC : Z := 6.                     (* spec.h:29 *)
Definition SPEC_ETH_HDR : Z := 14.                (* spec.h:30 *)
Definition SPEC_HDR : Z := 16.                    (* spec.h:32 *)
Definition SPEC_BODY_AT : Z := 30.                (* spec.h:33, SPEC_ETH_HDR + SPEC_HDR *)
Definition SPEC_AT_NUMBYTES : Z := 14.            (* spec.h:42-48 *)
Definition SPEC_AT_SUM : Z := 16.
Definition SPEC_AT_SEND : Z := 18.
Definition SPEC_AT_ACK : Z := 22.
Definition SPEC_AT_RETRY : Z := 26.
Definition SPEC_AT_CMD : Z := 28.
Definition SPEC_AT_NCMDS : Z := 29.

Definition SPEC_MAKER : Z := 19.                  (* spec.h:74, 0x13 *)
Definition SPEC_FN_RING : Z := 0.                 (* spec.h:75-80 *)
Definition SPEC_FN_METER : Z := 16.               (* 0x10 *)
Definition SPEC_FN_LEDS : Z := 32.                (* 0x20 *)
Definition SPEC_FN_COUNTER : Z := 48.             (* 0x30 *)
Definition SPEC_FN_SCRIBBLE : Z := 64.            (* 0x40 *)
Definition SPEC_FN_SYSTEM : Z := 112.             (* 0x70 *)

Definition SPEC_BTN_TOUCH : Z := 9.               (* spec.h:83 *)
Definition SPEC_ZONE_FIRST : Z := 24.             (* spec.h:85, 0x18 *)
Definition SPEC_ZONE_LAST : Z := 29.              (* spec.h:86, 0x1d *)
Definition SPEC_JOG_CC : Z := 92.                 (* spec.h:88, 0x5c *)
Definition SPEC_VPOTS : Z := 24.                  (* spec.h:90 *)
Definition SPEC_FADER_MAX : Z := 1023.            (* spec.h:92 *)
Definition SPEC_RING_LEDS : Z := 15.              (* spec.h:94 *)
Definition SPEC_METER_BITS : Z := 14.             (* spec.h:96 *)
Definition SPEC_DIGITS : Z := 8.                  (* spec.h:98 *)
Definition SPEC_CHARS_MAX : Z := 8.               (* spec.h:368 *)
Definition SPEC_CMD_MAX : Z := 24.                (* spec.h:144 *)

(* the return codes, spec.h:116-127 *)
Definition SPEC_OK : Z := 0.
Definition SPEC_E_ARG : Z := -1.
Definition SPEC_E_SHORT : Z := -2.
Definition SPEC_E_ETHERTYPE : Z := -3.
Definition SPEC_E_LENGTH : Z := -4.
Definition SPEC_E_SPACE : Z := -5.
Definition SPEC_E_TRUNCATED : Z := -6.
Definition SPEC_E_NO_STATUS : Z := -7.
Definition SPEC_E_STATUS : Z := -8.
Definition SPEC_E_NOT_ANNOUNCE : Z := -9.
Definition SPEC_E_REFUSED : Z := -10.
Definition SPEC_E_RANGE : Z := -11.

(* fuzz_codec's model's names for four of the codes and for SPEC_KEY (spec.h:141), folded with
   their names kept *)
(** Return codes: include/diginet/diginet.h, the same values as fuzz/spec.h SPEC_E_*. *)
Definition E_ARG : Z := -1.
Definition E_SPACE : Z := -5.
Definition E_REFUSED : Z := -10.
Definition E_RANGE : Z := -11.

(** DIGINET_KEY (diginet_codec.h:61) = SPEC_KEY (fuzz/spec.h). *)
Definition KEY (kind addr : Z) : Z := Z.lor (kind * 65536) (Z.land addr 0xffff).

(* the event kinds, spec.h:130-134 *)
Definition SPEC_EV_FADER : Z := 1.
Definition SPEC_EV_TOUCH : Z := 2.
Definition SPEC_EV_STRIP_BUTTON : Z := 3.
Definition SPEC_EV_SECTION_BUTTON : Z := 4.
Definition SPEC_EV_VPOT : Z := 5.
Definition SPEC_EV_JOG : Z := 6.
Definition SPEC_EV_RING : Z := 7.
Definition SPEC_EV_METER : Z := 8.
Definition SPEC_EV_STRIP_LEDS : Z := 9.
Definition SPEC_EV_SCRIBBLE : Z := 10.
Definition SPEC_EV_COUNTER : Z := 11.
Definition SPEC_EV_SYSTEM : Z := 12.
Definition SPEC_EV_OTHER : Z := 13.

(* enum diginet_desk, diginet_codec.h:25-29 *)
Definition DIGINET_DESK_UNKNOWN : Z := 0.
Definition DIGINET_DESK_CONTROL24 : Z := 1.
Definition DIGINET_DESK_PROCONTROL : Z := 2.

(* ---- the two desks, struct spec_desk SPEC_C24 / SPEC_PC (spec.h:100-111), folded from fuzz_codec's
   model with its names kept. spec_desk's announce name is not a field here; DgnLib.v's
   dp_announce_name holds the library's (diginet_codec.c:12-15). ---- *)

(** A desk: device byte, strips, scribble characters, counter address. The library's personalities[]
    (diginet_codec.c:12-15) and the harness's SPEC_C24 / SPEC_PC (fuzz/spec.h) hold the same fields:
    Control|24 = c24, ProControl = pc. A personality pointer is [option desk] (NULL = None). *)
Record desk := { d_dev : Z; d_strips : Z; d_chars : Z; d_counter : Z }.
Definition c24 : desk := {| d_dev := 1; d_strips := 24; d_chars := 4; d_counter := 0x19 |}.
Definition pc : desk := {| d_dev := 0; d_strips := 8; d_chars := 8; d_counter := 0x09 |}.

(* ---- the library's result structs ---- *)

(* struct diginet_cursor, diginet.h:149-154. The body pointer is not modelled: the body is an
   argument of every function that reads it. dc_len, dc_pos: size_t; dc_status: uint8_t. *)
Record dgn_cursor := DgnCursor { dc_len : Z; dc_pos : Z; dc_status : Z }.

(* struct diginet_msg, diginet.h:139-147. dm_status, dm_running, dm_d1, dm_d2: uint8_t;
   dm_sysex_len, dm_offset, dm_len: size_t. dm_sysex is the OFFSET of the payload in the body:
   the C pointer `sysex` equals body + dm_sysex, and fuzz_decode's checks compare it only with
   b + sm_sysex_at, and only for a message whose status is 0xF0. *)
Record dgn_msg := DgnMsg {
  dm_status : Z; dm_running : Z; dm_d1 : Z; dm_d2 : Z;
  dm_sysex : Z; dm_sysex_len : Z; dm_offset : Z; dm_len : Z }.

(* struct diginet_event, diginet_codec.h:193-206. de_kind: the enum's value; de_strip ..
   de_lsb_missing, de_len, de_dots, de_device: uint8_t; de_value, de_mask: uint16_t; de_delta:
   int16_t; de_segments: int8_t; de_text: char[9] (9 elements, unsigned char values);
   de_seg: uint8_t[8] (8 elements); de_msg: the message the event came from. *)
Record dgn_event := DgnEvent {
  de_kind : Z; de_strip : Z; de_button : Z; de_zone : Z; de_on : Z; de_right : Z; de_addr : Z;
  de_lsb_missing : Z; de_value : Z; de_delta : Z; de_mask : Z; de_segments : Z; de_len : Z;
  de_text : list Z; de_seg : list Z; de_dots : Z; de_device : Z; de_msg : dgn_msg }.

(* fuzz_decode's memset (&msg, 0, sizeof msg) and memset (&ev, 0, sizeof ev),
   fuzz_decode.c:312, :330; DgnLib.v's diginet_body_check also starts its message from it *)
Definition dgn_msg_zero : dgn_msg := DgnMsg 0 0 0 0 0 0 0 0.

Definition dgn_event_zero : dgn_event :=
  {| de_kind := 0; de_strip := 0; de_button := 0; de_zone := 0; de_on := 0; de_right := 0;
     de_addr := 0; de_lsb_missing := 0; de_value := 0; de_delta := 0; de_mask := 0;
     de_segments := 0; de_len := 0; de_text := repeat 0 9; de_seg := repeat 0 8; de_dots := 0;
     de_device := 0; de_msg := dgn_msg_zero |}.

(* struct diginet_cmd (diginet_codec.h), as fuzz_codec's model holds a command: (bytes[0..len), key,
   display), folded with its name kept *)
Definition cmd : Type := (list Z * Z * Z)%type.

(* ---- reading bytes, spec.h:148-180 ---- *)

(* spec.h:148-151: (uint16_t)(p[0] << 8 | p[1]), computed in int then converted (spec.h:150) *)
Definition spec_be16 (b : list Z) (p : Z) : Z :=
  u16 (Z.lor (Z.shiftl (byte_at b p) 8) (byte_at b (p + 1))).

(* spec.h:153-156: each (uint32_t)p[k] << s is computed in uint32_t (spec.h:155); p[3] is an int
   converted to uint32_t for the | *)
Definition spec_be32 (b : list Z) (p : Z) : Z :=
  Z.lor (u32 (Z.shiftl (byte_at b p) 24))
    (Z.lor (u32 (Z.shiftl (byte_at b (p + 1)) 16))
       (Z.lor (u32 (Z.shiftl (byte_at b (p + 2)) 8)) (byte_at b (p + 3)))).

(* spec.h:174-180: s = (s + p[i]) & 0xffff for i < n (spec.h:178), then (uint16_t)s (spec.h:179);
   the bytes are b[p], ..., b[p + n - 1]; the fuel is the loop's n iterations *)
Fixpoint spec_sum_loop (b : list Z) (p s i : Z) (fuel : nat) : Z :=
  match fuel with
  | O => s
  | S fuel' => spec_sum_loop b p (Z.land (s + byte_at b (p + i)) 65535) (i + 1) fuel'
  end.

Definition spec_sum_at (b : list Z) (p n : Z) : Z := u16 (spec_sum_loop b p 0 0 (Z.to_nat n)).

(* ---- a frame, spec.h:188-223 ---- *)

(* struct spec_frame, spec.h:188-197. sf_dst, sf_src, sf_body are the offsets in the frame
   buffer of the C pointers dst, src, body; when sf_code <> SPEC_OK the C pointers are NULL
   (the memset of spec.h:201) and the model holds 0 for them. *)
Record spec_frame := SpecFrame {
  sf_code : Z; sf_dst : Z; sf_src : Z;
  sf_ethertype : Z; sf_numbytes : Z; sf_sum : Z; sf_retry : Z;
  sf_send : Z; sf_ack : Z; sf_cmd : Z; sf_ncmds : Z;
  sf_body : Z; sf_body_len : Z; sf_pad_len : Z; sf_body_sum : Z }.

(* spec.h:199-223; the result's sf_code is also the function's return value *)
Definition spec_read_frame (b : list Z) (len : Z) : spec_frame :=
  let zero code et nb :=
    {| sf_code := code; sf_dst := 0; sf_src := 0; sf_ethertype := et; sf_numbytes := nb;
       sf_sum := 0; sf_retry := 0; sf_send := 0; sf_ack := 0; sf_cmd := 0; sf_ncmds := 0;
       sf_body := 0; sf_body_len := 0; sf_pad_len := 0; sf_body_sum := 0 |} in
  if len <? SPEC_BODY_AT then zero SPEC_E_SHORT 0 0
  else
    let et := spec_be16 b 12 in
    if negb (et =? SPEC_ETHERTYPE) then zero SPEC_E_ETHERTYPE et 0
    else
      let nb := spec_be16 b SPEC_AT_NUMBYTES in
      (* spec.h:208, len - SPEC_ETH_HDR in size_t: len >= 30 here, so no wrap *)
      if (nb <? SPEC_HDR) || (len - SPEC_ETH_HDR <? nb) then zero SPEC_E_LENGTH et nb
      else
        (* spec.h:219, int numbytes - 16 >= 0 converted to size_t *)
        let body_len := nb - SPEC_HDR in
        {| sf_code := SPEC_OK; sf_dst := 0; sf_src := SPEC_MAC; sf_ethertype := et;
           sf_numbytes := nb; sf_sum := spec_be16 b SPEC_AT_SUM;
           sf_retry := spec_be16 b SPEC_AT_RETRY; sf_send := spec_be32 b SPEC_AT_SEND;
           sf_ack := spec_be32 b SPEC_AT_ACK; sf_cmd := byte_at b SPEC_AT_CMD;
           sf_ncmds := byte_at b SPEC_AT_NCMDS; sf_body := SPEC_BODY_AT; sf_body_len := body_len;
           (* spec.h:220, size_t: len >= 14 + numbytes = 30 + body_len, so no wrap *)
           sf_pad_len := len - SPEC_BODY_AT - body_len;
           sf_body_sum := spec_sum_at b SPEC_BODY_AT body_len |}.

(* ---- the system family, spec.h:264-270 ---- *)

(* for (i = 0; i + 3 < len; i++) ...: the fuel len covers every iteration, and when it runs out
   i = len, where the loop condition fails too *)
Fixpoint system_at_loop (b : list Z) (len i : Z) (fuel : nat) : Z :=
  match fuel with
  | O => -1
  | S fuel' =>
      if i + 3 <? len then
        if (byte_at b i =? 240) && (byte_at b (i + 1) =? SPEC_MAKER)
           && (byte_at b (i + 3) =? SPEC_FN_SYSTEM)
        then i
        else system_at_loop b len (i + 1) fuel'
      else -1
  end.

(* the offset of the first F0 13 xx 70, whole or cut short, or -1 (a long) *)
Definition spec_system_at (b : list Z) (len : Z) : Z := system_at_loop b len 0 (Z.to_nat len).

(* ---- the command stream, spec.h:291-363 ---- *)

(* struct spec_msg, spec.h:291-296. sm_code: int; sm_at, sm_len, sm_next, sm_sysex_at,
   sm_sysex_len: size_t; sm_status, sm_running, sm_d1, sm_d2, sm_status_out: uint8_t. *)
Record spec_msg := SpecMsg {
  sm_code : Z; sm_at : Z; sm_len : Z; sm_next : Z;
  sm_status : Z; sm_running : Z; sm_d1 : Z; sm_d2 : Z; sm_status_out : Z;
  sm_sysex_at : Z; sm_sysex_len : Z }.

(* spec.h:311-313: while (i < len && b[i] != 0xf7) i++; the fuel len - i is the most
   iterations the loop can make, and when it runs out i = len, where the loop stops too *)
Fixpoint scan_f7 (b : list Z) (len i : Z) (fuel : nat) : Z :=
  match fuel with
  | O => i
  | S fuel' => if (i <? len) && negb (byte_at b i =? 247) then scan_f7 b len (i + 1) fuel' else i
  end.

(* spec.h:298-363. pos is the parameter `at`; status_in is a uint8_t. Every field the C code does
   not set keeps the 0 of the memset at spec.h:301. *)
Definition spec_msg_step (b : list Z) (len pos status_in : Z) : spec_msg :=
  let stop code next status_out :=
    {| sm_code := code; sm_at := pos; sm_len := 0; sm_next := next; sm_status := 0;
       sm_running := 0; sm_d1 := 0; sm_d2 := 0; sm_status_out := status_out; sm_sysex_at := 0;
       sm_sysex_len := 0 |} in
  if len <=? pos then stop 0 pos status_in
  else
    let lead := byte_at b pos in
    if lead =? 240 then
      let i := scan_f7 b len (pos + 1) (Z.to_nat (len - (pos + 1))) in
      if i =? len then stop SPEC_E_TRUNCATED len 0
      else
        {| sm_code := 1; sm_at := pos; sm_len := i + 1 - pos; sm_next := i + 1; sm_status := 240;
           sm_running := 0; sm_d1 := 0; sm_d2 := 0; sm_status_out := 0; sm_sysex_at := pos + 1;
           sm_sysex_len := i - pos - 1 |}
    else if 240 <? lead then stop SPEC_E_STATUS (pos + 1) 0
    else if (lead <? 128) && (status_in =? 0) then stop SPEC_E_NO_STATUS (pos + 1) status_in
    else
      (* spec.h:339, uint8_t from uint8_t *)
      let status := if 128 <=? lead then lead else status_in in
      let data := if 128 <=? lead then pos + 1 else pos in
      (* spec.h:341 *)
      let n := if (Z.land status 240 =? 192) || (Z.land status 240 =? 208) then 1 else 2 in
      if len <? data + n then stop SPEC_E_TRUNCATED len status_in
      (* spec.h:347-354: for (k = 0; k < n; k++) if (b[data + k] >= 0x80) ..., n is 1 or 2 *)
      else if 128 <=? byte_at b data then stop SPEC_E_TRUNCATED data 0
      else if (n =? 2) && (128 <=? byte_at b (data + 1)) then stop SPEC_E_TRUNCATED (data + 1) 0
      else
        {| sm_code := 1; sm_at := pos; sm_len := data + n - pos; sm_next := data + n;
           sm_status := status;
           sm_running := if lead <? 128 then 1 else 0;             (* spec.h:357 *)
           sm_d1 := byte_at b data;
           sm_d2 := if n =? 2 then byte_at b (data + 1) else 0;   (* spec.h:359 *)
           sm_status_out := status; sm_sysex_at := 0; sm_sysex_len := 0 |}.

(* ---- the controls, spec.h:372-499 ---- *)

(* spec.h:372-378: for (n = 0; n <= 14; n++) if (mask == (1u << n) - 1) return n; return -1.
   (1u << n) - 1 is unsigned and never wraps for n <= 14 (spec.h:375). *)
Fixpoint segments_loop (mask n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => -1
  | S fuel' => if mask =? 2 ^ n - 1 then n else segments_loop mask (n + 1) fuel'
  end.

Definition spec_segments (mask : Z) : Z := segments_loop mask 0 15.

(* spec_segments as fuzz_codec's model writes it (folded, names kept), and spec_segments_spec_eq *)
(** spec_segments (fuzz/spec.h:372-378): the first n of 0..14 with mask = 2^n - 1, else -1; k is the
    iterations left. *)
Fixpoint spec_seg_go (mask : Z) (n k : nat) : Z :=
  match k with
  | O => -1
  | S k' => if mask =? 2 ^ Z.of_nat n - 1 then Z.of_nat n else spec_seg_go mask (S n) k'
  end.
Definition spec_segments_spec (mask : Z) : Z := spec_seg_go mask 0 15.

Lemma spec_segments_spec_eq : forall mask, spec_segments_spec mask = spec_segments mask.
Proof.
  assert (G : forall mask k n, spec_seg_go mask n k = segments_loop mask (Z.of_nat n) k).
  { intros mask k. induction k as [|k IH]; intros n; cbn [spec_seg_go segments_loop]; [reflexivity|].
    rewrite IH. replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia. reflexivity. }
  intros mask. unfold spec_segments_spec, spec_segments. apply G.
Qed.

(* struct spec_event, spec.h:382-390. se_kind: int; se_strip .. se_dots: uint8_t; se_value,
   se_mask: uint16_t; se_delta: int16_t; se_segments: int8_t; se_text: uint8_t[8] and se_seg:
   uint8_t[8], 8 elements each. *)
Record spec_event := SpecEvent {
  se_kind : Z; se_strip : Z; se_button : Z; se_zone : Z; se_on : Z; se_right : Z; se_addr : Z;
  se_device : Z; se_len : Z; se_dots : Z; se_value : Z; se_mask : Z; se_delta : Z;
  se_segments : Z; se_text : list Z; se_seg : list Z }.

(* memset (e, 0, sizeof *e) *)
Definition se_zero : spec_event :=
  {| se_kind := 0; se_strip := 0; se_button := 0; se_zone := 0; se_on := 0; se_right := 0;
     se_addr := 0; se_device := 0; se_len := 0; se_dots := 0; se_value := 0; se_mask := 0;
     se_delta := 0; se_segments := 0; se_text := repeat 0 8; se_seg := repeat 0 8 |}.

(* DIGINET_EV_OTHER after the memset, with the device byte when spec.h:434 has set it *)
Definition se_other (device : Z) : spec_event :=
  {| se_kind := SPEC_EV_OTHER; se_strip := 0; se_button := 0; se_zone := 0; se_on := 0;
     se_right := 0; se_addr := 0; se_device := device; se_len := 0; se_dots := 0; se_value := 0;
     se_mask := 0; se_delta := 0; se_segments := 0; se_text := repeat 0 8;
     se_seg := repeat 0 8 |}.

(* spec.h:446-451, one LED: if (byte >> bit & 1) mask |= (uint16_t)(1u << (led - 1)) (spec.h:450,
   the |= converts the int result back to uint16_t) *)
Definition ring_step (p1 p2 mask led : Z) : Z :=
  let byte := if led <=? 8 then p1 else p2 in
  let bit := if led <=? 8 then 8 - led else 15 - led in
  if Z.land (Z.shiftr byte bit) 1 =? 1 then u16 (Z.lor mask (u16 (Z.shiftl 1 (led - 1))))
  else mask.

(* spec.h:445-451: mask = pl[0] >> 6 & 1, then LEDs 2..15 in order *)
Definition ring_mask (p0 p1 p2 : Z) : Z :=
  fold_left (ring_step p1 p2) (map (fun k => k + 2) (zseq 14)) (Z.land (Z.shiftr p0 6) 1).

(* spec.h:392-499 *)
Definition spec_event_of (b : list Z) (m : spec_msg) : spec_event :=
  let family := Z.land (sm_status m) 240 in                  (* spec.h:396, uint8_t *)
  if family =? 144 then
    (* spec.h:397-411 *)
    let tid := Z.land (sm_d2 m) 63 in                         (* spec.h:400, uint8_t *)
    let onb := Z.land (Z.shiftr (sm_d2 m) 6) 1 in             (* spec.h:402, 0 or 1 *)
    if (SPEC_ZONE_FIRST <=? tid) && (tid <=? SPEC_ZONE_LAST) then
      {| se_kind := SPEC_EV_SECTION_BUTTON; se_strip := 0; se_button := sm_d1 m; se_zone := tid;
         se_on := onb; se_right := 0; se_addr := 0; se_device := 0; se_len := 0; se_dots := 0;
         se_value := 0; se_mask := 0; se_delta := 0; se_segments := 0; se_text := repeat 0 8;
         se_seg := repeat 0 8 |}
    else
      {| se_kind := if sm_d1 m =? SPEC_BTN_TOUCH then SPEC_EV_TOUCH else SPEC_EV_STRIP_BUTTON;
         se_strip := tid; se_button := sm_d1 m; se_zone := 0; se_on := onb; se_right := 0;
         se_addr := 0; se_device := 0; se_len := 0; se_dots := 0; se_value := 0; se_mask := 0;
         se_delta := 0; se_segments := 0; se_text := repeat 0 8; se_seg := repeat 0 8 |}
  else if family =? 176 then
    (* spec.h:412-427 *)
    if sm_d1 m <? 32 then
      {| se_kind := SPEC_EV_FADER; se_strip := sm_d1 m; se_button := 0; se_zone := 0; se_on := 0;
         se_right := 0; se_addr := 0; se_device := 0; se_len := 0; se_dots := 0;
         se_value := u16 (Z.shiftl (sm_d2 m) 3);            (* spec.h:417 *)
         se_mask := 0; se_delta := 0; se_segments := 0; se_text := repeat 0 8;
         se_seg := repeat 0 8 |}
    else if sm_d1 m =? SPEC_JOG_CC then
      {| se_kind := SPEC_EV_JOG; se_strip := 0; se_button := 0; se_zone := 0; se_on := 0;
         se_right := 0; se_addr := 0; se_device := 0; se_len := 0; se_dots := 0; se_value := 0;
         se_mask := 0;
         se_delta := s16 (sm_d2 m - 64);                     (* spec.h:420 *)
         se_segments := 0; se_text := repeat 0 8; se_seg := repeat 0 8 |}
    else if (64 <=? sm_d1 m) && (sm_d1 m <? 64 + SPEC_VPOTS) then
      {| se_kind := SPEC_EV_VPOT;
         se_strip := u8 (sm_d1 m - 64);                      (* spec.h:423 *)
         se_button := 0; se_zone := 0; se_on := 0; se_right := 0; se_addr := 0; se_device := 0;
         se_len := 0; se_dots := 0; se_value := 0; se_mask := 0;
         se_delta := s16 (sm_d2 m - 64);                     (* spec.h:424 *)
         se_segments := 0; se_text := repeat 0 8; se_seg := repeat 0 8 |}
    else se_other 0
  else if negb (sm_status m =? 240) then se_other 0
  else
    (* spec.h:428-499; s = b + sysex_at, pl = s + 3 *)
    let s := sm_sysex_at m in
    let n := sm_sysex_len m in
    if (n <? 3) || negb (byte_at b s =? SPEC_MAKER) then se_other 0
    else
      let device := byte_at b (s + 1) in                     (* spec.h:434 *)
      let pl := s + 3 in
      let pn := n - 3 in                                     (* spec.h:436, size_t, n >= 3 *)
      let p0 := byte_at b pl in
      let p1 := byte_at b (pl + 1) in
      let p2 := byte_at b (pl + 2) in
      let fn := byte_at b (s + 2) in
      if fn =? SPEC_FN_RING then
        (* spec.h:438-452 *)
        if negb (pn =? 3) then se_other device
        else
          {| se_kind := SPEC_EV_RING;
             se_strip := Z.land p0 63;                       (* spec.h:444 *)
             se_button := 0; se_zone := 0; se_on := 0; se_right := 0; se_addr := 0;
             se_device := device; se_len := 0; se_dots := 0; se_value := 0;
             se_mask := ring_mask p0 p1 p2;                  (* spec.h:445-451 *)
             se_delta := 0; se_segments := 0; se_text := repeat 0 8; se_seg := repeat 0 8 |}
      else if fn =? SPEC_FN_METER then
        (* spec.h:453-464 *)
        if negb (pn =? 3) then se_other device
        else
          let mask := u16 (Z.lor (Z.shiftl (Z.land p1 127) 7) (Z.land p2 127)) in (* spec.h:462 *)
          {| se_kind := SPEC_EV_METER;
             se_strip := Z.land p0 31;                       (* spec.h:460 *)
             se_button := 0; se_zone := 0; se_on := 0;
             se_right := Z.land (Z.shiftr p0 5) 1;           (* spec.h:461, 0 or 1 *)
             se_addr := p0; se_device := device; se_len := 0; se_dots := 0; se_value := 0;
             se_mask := mask; se_delta := 0;
             se_segments := s8 (spec_segments mask);         (* spec.h:463 *)
             se_text := repeat 0 8; se_seg := repeat 0 8 |}
      else if fn =? SPEC_FN_LEDS then
        (* spec.h:465-473 *)
        if negb (pn =? 2) then se_other device
        else
          {| se_kind := SPEC_EV_STRIP_LEDS; se_strip := p0; se_button := 0; se_zone := 0;
             se_on := 0; se_right := 0; se_addr := p0; se_device := device; se_len := 0;
             se_dots := 0; se_value := 0;
             se_mask := p1;                                  (* spec.h:472, uint8_t to uint16_t *)
             se_delta := 0; se_segments := 0; se_text := repeat 0 8; se_seg := repeat 0 8 |}
      else if fn =? SPEC_FN_SCRIBBLE then
        (* spec.h:474-482; pn - 2 in size_t, pn >= 3 here *)
        if (pn <? 3) || (SPEC_CHARS_MAX <? pn - 2) then se_other device
        else
          let l := u8 (pn - 2) in                            (* spec.h:480 *)
          {| se_kind := SPEC_EV_SCRIBBLE; se_strip := 0; se_button := 0; se_zone := 0; se_on := 0;
             se_right := 0; se_addr := p0; se_device := device; se_len := l; se_dots := 0;
             se_value := 0; se_mask := 0; se_delta := 0; se_segments := 0;
             (* spec.h:481: memcpy (e->text, pl + 2, e->len), the rest stays 0 *)
             se_text := map (fun k => if k <? l then byte_at b (pl + 2 + k) else 0) (zseq 8);
             se_seg := repeat 0 8 |}
      else if fn =? SPEC_FN_COUNTER then
        (* spec.h:483-492 *)
        if negb (pn =? 2 + SPEC_DIGITS) then se_other device
        else
          {| se_kind := SPEC_EV_COUNTER; se_strip := 0; se_button := 0; se_zone := 0; se_on := 0;
             se_right := 0; se_addr := p0; se_device := device; se_len := 0; se_dots := p1;
             se_value := 0; se_mask := 0; se_delta := 0; se_segments := 0;
             se_text := repeat 0 8;
             (* spec.h:491: seg[k] = pl[2 + 8 - 1 - k] *)
             se_seg := map (fun k => byte_at b (pl + 2 + SPEC_DIGITS - 1 - k)) (zseq 8) |}
      else if fn =? SPEC_FN_SYSTEM then
        (* spec.h:493-495 *)
        {| se_kind := SPEC_EV_SYSTEM; se_strip := 0; se_button := 0; se_zone := 0; se_on := 0;
           se_right := 0; se_addr := 0; se_device := device; se_len := 0; se_dots := 0;
           se_value := 0; se_mask := 0; se_delta := 0; se_segments := 0; se_text := repeat 0 8;
           se_seg := repeat 0 8 |}
      else se_other device.

(* ---- the frame as a list byte, folded from fuzz_frame's model (names kept) ---- *)

(** * Bytes *)

Definition bz (x : byte) : Z := bv_unsigned x.
Definition b8 (z : Z) : byte := Z_to_bv 8 z.

(* The byte at index i of l, as a number; 0 past the end. *)
Definition at8 (l : list byte) (i : nat) : Z := bz (nth i l (b8 0)).

(* spec_be16 and rd16, spec_be32 and rd32: the big-endian value at index i. *)
Definition be16 (l : list byte) (i : nat) : Z := at8 l i * 2^8 + at8 l (S i).
Definition be32 (l : list byte) (i : nat) : Z :=
  at8 l i * 2^24 + at8 l (S i) * 2^16 + at8 l (S (S i)) * 2^8 + at8 l (S (S (S i))).

(* spec_put16 and wr16, spec_put32 and wr32: the big-endian bytes of v. Each byte is
   (uint8_t)(v >> k): b8 keeps the low 8 bits. *)
Definition put16 (v : Z) : list byte := [b8 (v / 2^8); b8 v].
Definition put32 (v : Z) : list byte := [b8 (v / 2^24); b8 (v / 2^16); b8 (v / 2^8); b8 v].

Lemma bz_range : forall x, 0 <= bz x < 2^8.
Proof.
  intros x. unfold bz. pose proof (bv_unsigned_in_range 8 x) as H.
  unfold bv_modulus in H. exact H.
Qed.

Lemma at8_range : forall l i, 0 <= at8 l i < 2^8.
Proof. intros l i. apply bz_range. Qed.

Lemma bz_b8 : forall z, 0 <= z < 2^8 -> bz (b8 z) = z.
Proof. intros z Hz. unfold bz, b8. apply Z_to_bv_small. unfold bv_modulus. exact Hz. Qed.

Lemma b8_bz : forall x, b8 (bz x) = x.
Proof. intros x. unfold b8, bz. apply Z_to_bv_bv_unsigned. Qed.

Lemma bz_inj : forall x y, bz x = bz y -> x = y.
Proof. intros x y H. apply bv_eq. exact H. Qed.

Lemma b8_mod : forall z, b8 (z mod 2^8) = b8 z.
Proof.
  intros z. unfold b8. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  apply Zmod_mod.
Qed.

Lemma at8_firstn : forall l n i, (i < n)%nat -> at8 (firstn n l) i = at8 l i.
Proof. intros l n i H. unfold at8. rewrite nth_firstn. destruct (Nat.ltb_spec i n); [reflexivity|lia]. Qed.

Lemma at8_skipn : forall l n i, at8 (skipn n l) i = at8 l (n + i).
Proof. intros l n i. unfold at8. rewrite nth_skipn. reflexivity. Qed.

Lemma at8_app_l : forall l1 l2 i, (i < length l1)%nat -> at8 (l1 ++ l2) i = at8 l1 i.
Proof. intros l1 l2 i H. unfold at8. rewrite app_nth1 by exact H. reflexivity. Qed.

Lemma be16_range : forall l i, 0 <= be16 l i < 2^16.
Proof.
  intros l i. unfold be16. pose proof (at8_range l i). pose proof (at8_range l (S i)). lia.
Qed.

Lemma be32_range : forall l i, 0 <= be32 l i < 2^32.
Proof.
  intros l i. unfold be32.
  pose proof (at8_range l i). pose proof (at8_range l (S i)).
  pose proof (at8_range l (S (S i))). pose proof (at8_range l (S (S (S i)))). lia.
Qed.

(* (x mod 2^b) mod 2^a = x mod 2^a for a <= b. *)
Lemma mod_mod_pow2 : forall x a b, 0 <= a <= b -> (x mod 2^b) mod 2^a = x mod 2^a.
Proof.
  intros x a b Hab.
  rewrite (Z.mod_eq x (2^b)) by (apply Z.pow_nonzero; lia).
  replace (x - 2^b * (x / 2^b)) with (x + (- (x / 2^b) * 2^(b - a)) * 2^a).
  - apply Z_mod_plus_full.
  - replace (2^b) with (2^(b - a) * 2^a) by (rewrite <- Z.pow_add_r by lia; f_equal; lia). ring.
Qed.

(* The byte (uint8_t)(v >> k) does not change when v is cut to w >= k + 8 bits first. *)
Lemma b8_div_mod : forall v k w, 0 <= k -> k + 8 <= w -> b8 (v mod 2^w / 2^k) = b8 (v / 2^k).
Proof.
  intros v k w Hk Hw.
  rewrite <- (b8_mod (v mod 2^w / 2^k)), <- (b8_mod (v / 2^k)). f_equal.
  rewrite (Z.mod_eq v (2^w)) by (apply Z.pow_nonzero; lia).
  replace (v - 2^w * (v / 2^w)) with (v + (- (v / 2^w) * 2^(w - k - 8) * 2^8) * 2^k).
  - rewrite Z.div_add by (apply Z.pow_nonzero; lia). apply Z_mod_plus_full.
  - replace (2^w) with (2^(w - k - 8) * 2^8 * 2^k)
      by (rewrite <- !Z.pow_add_r by lia; f_equal; lia). ring.
Qed.

Lemma b8_mod_w : forall v w, 8 <= w -> b8 (v mod 2^w) = b8 v.
Proof.
  intros v w Hw. rewrite <- (b8_mod (v mod 2^w)), <- (b8_mod v). f_equal.
  apply mod_mod_pow2. lia.
Qed.

(* wr16 of a uint16_t and wr32 of a uint32_t write the bytes of the untruncated value. *)
Lemma put16_mod : forall v, put16 (v mod 2^16) = put16 v.
Proof.
  intros v. unfold put16. rewrite (b8_div_mod v 8 16) by lia. rewrite (b8_mod_w v 16) by lia.
  reflexivity.
Qed.

Lemma put32_mod : forall v, put32 (v mod 2^32) = put32 v.
Proof.
  intros v. unfold put32.
  rewrite (b8_div_mod v 24 32), (b8_div_mod v 16 32), (b8_div_mod v 8 32) by lia.
  rewrite (b8_mod_w v 32) by lia. reflexivity.
Qed.

Lemma length_put16 : forall v, length (put16 v) = 2%nat.
Proof. reflexivity. Qed.

Lemma length_put32 : forall v, length (put32 v) = 4%nat.
Proof. reflexivity. Qed.

(* For a decision over the 256 byte values by computation. *)
Lemma byte_forall : forall (f : Z -> bool),
  forallb (fun n => f (Z.of_nat n)) (seq 0 256) = true -> forall z, 0 <= z < 2^8 -> f z = true.
Proof.
  intros f H z Hz. rewrite forallb_forall in H.
  replace z with (Z.of_nat (Z.to_nat z)) by lia.
  apply H. apply in_seq. lia.
Qed.

(** * The 16-bit sum of the body *)

Fixpoint sum_bytes (l : list byte) : Z :=
  match l with [] => 0 | x :: r => bz x + sum_bytes r end.

(* The header sum: the additive sum of the body bytes, mod 2^16 (docs/protocol.md:38). *)
Definition sum16 (l : list byte) : Z := sum_bytes l mod 2^16.

(* spec_sum (spec.h:174): s = (s + p[i]) & 0xffff at each byte. *)
Fixpoint spec_sum_from (s : Z) (l : list byte) : Z :=
  match l with [] => s | x :: r => spec_sum_from (Z.land (s + bz x) 0xffff) r end.
Definition spec_sum (l : list byte) : Z := spec_sum_from 0 l.

(* diginet_sum16 (src/diginet_frame.c:42): a uint32_t sum, cut to uint16_t. *)
Definition lib_sum16 (l : list byte) : Z := (sum_bytes l mod 2^32) mod 2^16.

Lemma sum_bytes_app : forall l1 l2, sum_bytes (l1 ++ l2) = sum_bytes l1 + sum_bytes l2.
Proof. induction l1 as [|x l1 IH]; intros l2; cbn; [lia|]. rewrite IH. lia. Qed.

Lemma sum_bytes_range : forall l, 0 <= sum_bytes l <= 255 * Z.of_nat (length l).
Proof.
  induction l as [|x l IH]; cbn [sum_bytes length]; [lia|].
  pose proof (bz_range x). lia.
Qed.

Lemma sum_bytes_firstn_S : forall l i, (i < length l)%nat ->
  sum_bytes (firstn (S i) l) = sum_bytes (firstn i l) + at8 l i.
Proof.
  intros l i H.
  assert (E : firstn (S i) l = firstn i l ++ [nth i l (b8 0)]).
  { revert i H. induction l as [|x l IH]; intros [|i] H; cbn in *; try lia; [reflexivity|].
    rewrite (IH i) by lia. reflexivity. }
  rewrite E, sum_bytes_app. cbn. unfold at8. lia.
Qed.

Lemma sum16_range : forall l, 0 <= sum16 l < 2^16.
Proof. intros l. unfold sum16. apply Z.mod_pos_bound. lia. Qed.

Lemma spec_sum_eq : forall l, spec_sum l = sum16 l.
Proof.
  assert (G : forall l s, 0 <= s < 2^16 -> spec_sum_from s l = (s + sum_bytes l) mod 2^16).
  { induction l as [|x l IH]; intros s Hs; cbn [spec_sum_from sum_bytes].
    - rewrite Z.add_0_r. symmetry. apply Z.mod_small. exact Hs.
    - change 0xffff with (Z.ones 16). rewrite Z.land_ones by lia.
      rewrite IH by (apply Z.mod_pos_bound; lia).
      rewrite Zplus_mod_idemp_l. f_equal. lia. }
  intros l. unfold spec_sum, sum16. rewrite G by lia. reflexivity.
Qed.

Lemma lib_sum16_eq : forall l, lib_sum16 l = sum16 l.
Proof. intros l. unfold lib_sum16, sum16. apply mod_mod_pow2. lia. Qed.

(** * The frame as spec_read_frame (spec.h:199) reads it *)

(* The body starts at byte 30: the 14-byte Ethernet header, then the 16-byte header. *)
Definition fr_dst (b : list byte) : list byte := firstn 6 b.
Definition fr_src (b : list byte) : list byte := firstn 6 (skipn 6 b).
Definition fr_ethertype (b : list byte) : Z := be16 b 12.
Definition fr_numbytes (b : list byte) : Z := be16 b 14.
Definition fr_sum (b : list byte) : Z := be16 b 16.
Definition fr_send (b : list byte) : Z := be32 b 18.
Definition fr_ack (b : list byte) : Z := be32 b 22.
Definition fr_retry (b : list byte) : Z := be16 b 26.
Definition fr_cmd (b : list byte) : Z := at8 b 28.
Definition fr_ncmds (b : list byte) : Z := at8 b 29.
Definition fr_body_len (b : list byte) : Z := fr_numbytes b - 16.
Definition fr_pad_len (b : list byte) : Z := Z.of_nat (length b) - 30 - fr_body_len b.
Definition fr_body (b : list byte) : list byte := firstn (Z.to_nat (fr_body_len b)) (skipn 30 b).
Definition fr_body_sum (b : list byte) : Z := sum16 (fr_body b).

(* The code: -2 (SHORT) for fewer than 30 bytes, -3 (ETHERTYPE) for an EtherType other than
   0x885F, -4 (LENGTH) for a numbytes under 16 or past the buffer, else 0 (OK).
   diginet_frame_parse (src/diginet_frame.c:60) answers the same code and, on 0, the same
   fields; the frame_parse contract states its result with these functions. *)
Definition fr_code (b : list byte) : Z :=
  if (length b <? 30)%nat then -2
  else if negb (fr_ethertype b =? 0x885f) then -3
  else if (fr_numbytes b <? 16) || (Z.of_nat (length b) - 14 <? fr_numbytes b) then -4
  else 0.

Lemma fr_code_cases : forall b, fr_code b = 0 \/ fr_code b = -2 \/ fr_code b = -3 \/ fr_code b = -4.
Proof.
  intros b. unfold fr_code.
  destruct (length b <? 30)%nat; [tauto|]. destruct (negb _); [tauto|].
  destruct (_ || _); tauto.
Qed.

Lemma fr_code_ok : forall b, fr_code b = 0 ->
  (30 <= length b)%nat /\ fr_ethertype b = 0x885f /\
  16 <= fr_numbytes b /\ fr_numbytes b <= Z.of_nat (length b) - 14.
Proof.
  intros b H. unfold fr_code in H.
  destruct (Nat.ltb_spec (length b) 30); [discriminate|].
  destruct (Z.eqb_spec (fr_ethertype b) 0x885f); cbn in H; [|discriminate].
  destruct (Z.ltb_spec (fr_numbytes b) 16); cbn in H; [discriminate|].
  destruct (Z.ltb_spec (Z.of_nat (length b) - 14) (fr_numbytes b)); cbn in H; [discriminate|].
  repeat split; lia.
Qed.

Lemma fr_body_len_ok : forall b, fr_code b = 0 ->
  0 <= fr_body_len b /\ 0 <= fr_pad_len b /\ 30 + fr_body_len b + fr_pad_len b = Z.of_nat (length b).
Proof.
  intros b H. destruct (fr_code_ok b H) as (H1 & _ & H3 & H4).
  unfold fr_pad_len, fr_body_len. lia.
Qed.

Lemma length_fr_body : forall b, fr_code b = 0 -> length (fr_body b) = Z.to_nat (fr_body_len b).
Proof.
  intros b H. destruct (fr_code_ok b H) as (H1 & _ & H3 & H4).
  unfold fr_body, fr_body_len in *. rewrite length_firstn, length_skipn. lia.
Qed.

(* diginet_frame_is_keepalive (src/diginet_frame.c:55) of a frame with these fields, and the
   harness's own test (fuzz_frame.c:105). *)
Definition keepalive_of (cmd blen : Z) (body : list byte) : bool :=
  (cmd =? 0) && (blen =? 1) && (at8 body 0 =? 0).
Definition fr_keepalive (b : list byte) : bool := keepalive_of (fr_cmd b) (fr_body_len b) (fr_body b).

(* diginet_mac_is_digidesign (src/diginet_frame.c:50): the OUI 00:a0:7e. *)
Definition oui_of (mac : list byte) : bool :=
  (at8 mac 0 =? 0x00) && (at8 mac 1 =? 0xa0) && (at8 mac 2 =? 0x7e).

(* The harness compares the source MAC with SPEC_OUI by memcmp of 3 bytes. *)
Lemma oui_of_firstn : forall mac, (3 <= length mac)%nat ->
  oui_of mac = true <-> firstn 3 mac = [b8 0x00; b8 0xa0; b8 0x7e].
Proof.
  intros [|x0 [|x1 [|x2 r]]] H; cbn in H; try lia.
  unfold oui_of, at8. cbn [nth firstn].
  rewrite !andb_true_iff, !Z.eqb_eq.
  split.
  - intros [[E0 E1] E2]. rewrite <- (b8_bz x0), <- (b8_bz x1), <- (b8_bz x2), E0, E1, E2.
    reflexivity.
  - intros E. injection E as E0 E1 E2. subst.
    rewrite !bz_b8 by lia. tauto.
Qed.

(** * The system family F0 13 xx 70 *)

(* F0 13 xx 70 starts at index i. *)
Definition sys_hit (b : list byte) (i : nat) : bool :=
  (at8 b i =? 0xf0) && (at8 b (S i) =? 0x13) && (at8 b (S (S (S i))) =? 0x70).

(* spec_system_at (spec.h:264) >= 0: some i with i + 3 < length b starts F0 13 xx 70. *)
Definition system_at (b : list byte) : bool := existsb (sys_hit b) (seq 0 (length b - 3)).

Lemma system_at_true : forall b,
  system_at b = true <-> exists i, (i + 3 < length b)%nat /\ sys_hit b i = true.
Proof.
  intros b. unfold system_at. rewrite existsb_exists.
  split; intros [i [Hi Hh]]; exists i; (split; [|exact Hh]); [apply in_seq in Hi | apply in_seq]; lia.
Qed.

Lemma system_at_false : forall b,
  system_at b = false <-> forall i, (i + 3 < length b)%nat -> sys_hit b i = false.
Proof.
  intros b. split.
  - intros H i Hi. destruct (sys_hit b i) eqn:E; [|reflexivity].
    assert (system_at b = true) by (apply system_at_true; eauto). congruence.
  - intros H. destruct (system_at b) eqn:E; [|reflexivity].
    apply system_at_true in E. destruct E as [i [Hi Hh]]. rewrite H in Hh by exact Hi. discriminate.
Qed.

(** * The frame spec_build_frame (spec.h:228) makes *)

(* Its length: 30 bytes and the body, at least 60. *)
Definition frame_len (n : nat) : Z := Z.max 60 (30 + Z.of_nat n).

(* The two MACs, 0x885F, numbytes 16 + body length, the body's sum or zero, the counters,
   retry, command and count, the body, then zeros up to 60 bytes. dst and src are the 6 bytes
   of each MAC. *)
Definition build_frame (dst src : list byte) (send ack retry cmd ncmds : Z) (body : list byte)
    (zero_sum : bool) : list byte :=
  dst ++ src ++ put16 0x885f ++ put16 (16 + Z.of_nat (length body)) ++
  put16 (if zero_sum then 0 else spec_sum body) ++ put32 send ++ put32 ack ++ put16 retry ++
  [b8 cmd; b8 ncmds] ++ body ++ repeat (b8 0) (30 - length body).

Lemma length_build_frame : forall dst src send ack retry cmd ncmds body z,
  length dst = 6%nat -> length src = 6%nat ->
  Z.of_nat (length (build_frame dst src send ack retry cmd ncmds body z)) = frame_len (length body).
Proof.
  intros. unfold build_frame, frame_len, put16, put32.
  rewrite !length_app, repeat_length. cbn [length]. rewrite H, H0. lia.
Qed.

(* What diginet_frame_build answers, as the harness holds it (fuzz_frame.c:134-153): -4
   (LENGTH) for a body past 1484 bytes, -10 (REFUSED) for a body holding F0 13 xx 70, -5
   (SPACE) for a buffer shorter than the frame, else the frame length. *)
Definition build_code (body : list byte) (cap : Z) : Z :=
  if 1484 <? Z.of_nat (length body) then -4
  else if system_at body then -10
  else if cap <? frame_len (length body) then -5
  else frame_len (length body).

(** * Strings of the announce *)

(* the number of bytes before the first NUL of l, or length l *)
Fixpoint nz_run (l : list byte) : nat :=
  match l with [] => O | x :: r => if bz x =? 0 then O else S (nz_run r) end.

(* spec_strz_len (spec.h:251): up to the first NUL, at most 9 bytes. *)
Definition strz_len (p : list byte) : nat := nz_run (firstn 9 p).

(* field_len (fuzz_frame.c:204): the string in a field of cap bytes. *)
Definition field_len (cap : nat) (s : list byte) : nat := nz_run (firstn cap s).

(* copy_strz (src/diginet_frame.c:130): it copies the bytes of src up to its first NUL, at most
   n and at most dst_size - 1, then writes a NUL. *)
Definition copy_len (dst_size n : nat) (src : list byte) : nat :=
  nz_run (firstn (Nat.min n (dst_size - 1)) src).

(* The field old after copy_strz: bytes 0 .. k-1 are src's, byte k is NUL, k = copy_len; it
   does not write bytes k+1 .. dst_size-1. *)
Definition copy_strz (dst_size n : nat) (src old : list byte) : list byte :=
  firstn (copy_len dst_size n src) src ++ b8 0 :: skipn (S (copy_len dst_size n src)) old.

Lemma nz_run_le : forall l, (nz_run l <= length l)%nat.
Proof. induction l as [|x l IH]; cbn; [lia|]. destruct (bz x =? 0); cbn; lia. Qed.

Lemma nz_run_nonzero : forall l i, (i < nz_run l)%nat -> at8 l i <> 0.
Proof.
  induction l as [|x l IH]; intros i H; cbn in H; [lia|].
  destruct (Z.eqb_spec (bz x) 0) as [E|E]; [lia|].
  destruct i as [|i]; [exact E|]. unfold at8. cbn [nth]. apply IH. lia.
Qed.

Lemma nz_run_zero : forall l, (nz_run l < length l)%nat -> at8 l (nz_run l) = 0.
Proof.
  induction l as [|x l IH]; intros H; cbn in H; [lia|].
  cbn [nz_run]. destruct (Z.eqb_spec (bz x) 0) as [E|E]; [exact E|].
  cbn in H. unfold at8. cbn [nth]. apply IH. lia.
Qed.

(* nz_run is the first index of a NUL, or the length. *)
Lemma nz_run_char : forall l k, (k <= length l)%nat ->
  (forall i, (i < k)%nat -> at8 l i <> 0) -> ((k < length l)%nat -> at8 l k = 0) -> nz_run l = k.
Proof.
  induction l as [|x l IH]; intros k Hk Hnz Hz; cbn in Hk.
  - cbn. lia.
  - cbn [nz_run]. destruct k as [|k].
    + pose proof (Hz ltac:(cbn; lia)) as Z0. unfold at8 in Z0. cbn [nth] in Z0. rewrite Z0. reflexivity.
    + assert (E : bz x <> 0) by exact (Hnz O ltac:(lia)).
      destruct (Z.eqb_spec (bz x) 0); [contradiction|]. f_equal. apply IH; [lia| |].
      * intros i Hi. exact (Hnz (S i) ltac:(lia)).
      * intros Hi. exact (Hz ltac:(cbn; lia)).
Qed.

Lemma strz_len_le : forall p, (strz_len p <= 9)%nat.
Proof.
  intros p. unfold strz_len. pose proof (nz_run_le (firstn 9 p)). rewrite length_firstn in H. lia.
Qed.

(* spec_strz_len's loop: k bytes that are not NUL, then a NUL or the ninth byte. *)
Lemma strz_len_char : forall p k, (9 <= length p)%nat -> (k <= 9)%nat ->
  (forall i, (i < k)%nat -> at8 p i <> 0) -> ((k < 9)%nat -> at8 p k = 0) -> strz_len p = k.
Proof.
  intros p k Hp Hk Hnz Hz. unfold strz_len. apply nz_run_char.
  - rewrite length_firstn. lia.
  - intros i Hi. rewrite at8_firstn by lia. exact (Hnz i Hi).
  - intros Hi. rewrite length_firstn in Hi. rewrite at8_firstn by lia. apply Hz. lia.
Qed.

Lemma copy_len_strz : forall src, copy_len 10 9 src = strz_len src.
Proof. reflexivity. Qed.

Lemma length_copy_strz : forall src old, length old = 10%nat ->
  length (copy_strz 10 9 src old) = 10%nat.
Proof.
  intros src old H. unfold copy_strz. rewrite copy_len_strz.
  pose proof (strz_len_le src) as L.
  assert (L2 : (strz_len src <= length src)%nat).
  { unfold strz_len. pose proof (nz_run_le (firstn 9 src)). rewrite length_firstn in H0. lia. }
  rewrite length_app, length_firstn. cbn [length]. rewrite length_skipn. lia.
Qed.

(* The string the library leaves in the field is the string spec_strz_len reads. *)
Lemma field_len_copy_strz : forall src old, field_len 10 (copy_strz 10 9 src old) = strz_len src.
Proof.
  intros src old. unfold field_len, copy_strz. change (copy_len 10 9 src) with (strz_len src).
  pose proof (strz_len_le src) as L.
  assert (L2 : (strz_len src <= length src)%nat).
  { unfold strz_len. pose proof (nz_run_le (firstn 9 src)). rewrite length_firstn in H. lia. }
  apply nz_run_char.
  - rewrite length_firstn, length_app, length_firstn. cbn [length]. lia.
  - intros i Hi. rewrite at8_firstn by lia. rewrite at8_app_l by (rewrite length_firstn; lia).
    rewrite at8_firstn by lia.
    assert (Hi9 : (i < nz_run (firstn 9 src))%nat) by exact Hi.
    pose proof (nz_run_nonzero (firstn 9 src) i Hi9) as N. rewrite at8_firstn in N by lia. exact N.
  - intros _. rewrite at8_firstn by lia.
    unfold at8. rewrite app_nth2 by (rewrite length_firstn; lia).
    rewrite length_firstn. replace (strz_len src - Nat.min (strz_len src) (length src))%nat with O by lia.
    cbn [nth]. apply bz_b8. lia.
Qed.

Lemma copy_strz_prefix : forall src old,
  firstn (strz_len src) (copy_strz 10 9 src old) = firstn (strz_len src) src.
Proof.
  intros src old. unfold copy_strz. change (copy_len 10 9 src) with (strz_len src).
  assert (L2 : (strz_len src <= length src)%nat).
  { unfold strz_len. pose proof (nz_run_le (firstn 9 src)). rewrite length_firstn in H. lia. }
  rewrite firstn_app. rewrite firstn_firstn, Nat.min_id. rewrite length_firstn.
  replace (strz_len src - Nat.min (strz_len src) (length src))%nat with O by lia.
  rewrite app_nil_r. reflexivity.
Qed.

(** * The announce: diginet_announce_parse (src/diginet_frame.c:138) *)

(* The code: -9 (NOT_ANNOUNCE) for a command other than e0 and e1, -4 (LENGTH) for a body
   under 33 bytes, else 0. *)
Definition ann_cmd (cmd : Z) : bool := (cmd =? 0xe0) || (cmd =? 0xe1).
Definition ann_code (cmd blen : Z) : Z :=
  if negb (ann_cmd cmd) then -9 else if blen <? 33 then -4 else 0.

(* On 0: unknown points at the body, 15 bytes; version and name are copy_strz of 9 bytes at
   15 and at 24 of the body, into fields of 10 bytes. *)
Definition ann_unknown (body : list byte) : list byte := firstn 15 body.
Definition ann_version (body old : list byte) : list byte := copy_strz 10 9 (skipn 15 body) old.
Definition ann_name (body old : list byte) : list byte := copy_strz 10 9 (skipn 24 body) old.

(* The binary and the harness test (cmd & 0xfe) == 0xe0. *)
Lemma ann_cmd_land : forall cmd, 0 <= cmd < 2^8 -> (Z.land cmd 0xfe =? 0xe0) = ann_cmd cmd.
Proof.
  assert (G : forall cmd, 0 <= cmd < 2^8 -> Bool.eqb (Z.land cmd 0xfe =? 0xe0) (ann_cmd cmd) = true).
  { apply (byte_forall (fun cmd => Bool.eqb (Z.land cmd 0xfe =? 0xe0) (ann_cmd cmd))).
    vm_compute. reflexivity. }
  intros cmd Hc. apply Bool.eqb_prop. exact (G cmd Hc).
Qed.

(* ---- worked examples: corpus seeds of fuzz/corpus/decode (fuzz/gen-corpus.c:190-272),
   values worked by hand from the C source ---- *)

Definition ex_button_mute : list Z := [144; 8; 64].                          (* 90 08 40 *)
Definition ex_scribble_write : list Z := [240; 19; 1; 64; 0; 0; 79; 77; 88; 49; 247].
Definition ex_meter : list Z := [240; 19; 1; 16; 0; 7; 127; 247].            (* f0 13 01 10 00 07 7f f7 *)
Definition ex_meter_right : list Z := [240; 19; 0; 16; 35; 127; 127; 247].   (* f0 13 00 10 23 7f 7f f7 *)
Definition ex_counter_write : list Z :=
  [240; 19; 1; 48; 25; 64; 91; 109; 48; 0; 0; 0; 0; 0; 247].                (* f0 13 01 30 19 40 5b 6d 30 00 .. f7 *)
Definition ex_ring : list Z := [240; 19; 1; 0; 69; 127; 64; 247].            (* f0 13 01 00 45 7f 40 f7 *)
Definition ex_strip_leds : list Z := [240; 19; 1; 32; 2; 68; 247].           (* f0 13 01 20 02 44 f7 *)
Definition ex_sysex_no_f7 : list Z := [240; 19; 1; 64; 0].                   (* f0 13 01 40 00 *)
Definition ex_one_data_byte : list Z := [192; 5; 208; 127; 16].              (* c0 05 d0 7f 10 *)
Definition ex_touch : list Z := [144; 9; 69].                                (* 90 09 45 *)
(* the frame of fader_move-frame after its sel byte 0x80: dst, src, 88 5f, numbytes 0x15, sum
   0x110, send 0x105, ack 0, retry 0, cmd 0, ncmds 1, body b0 00 40 20 00, 25 bytes of padding *)
Definition ex_fader_move_frame : list Z :=
  [2; 0; 0; 0; 0; 1; 0; 160; 126; 36; 0; 1; 136; 95; 0; 21; 1; 16; 0; 0; 1; 5; 0; 0; 0; 0;
   0; 0; 0; 1; 176; 0; 64; 32; 0] ++ repeat 0 25.
(* frame-refused: the first 20 bytes of the keepalive frame *)
Definition ex_frame_refused : list Z :=
  [0; 160; 126; 36; 0; 1; 2; 0; 0; 0; 0; 1; 136; 95; 0; 17; 0; 0; 0; 0].

(* button_mute: 90 08 40 is one whole message, a strip button, button 08 (mute), down, strip 0 *)
Example worked_step_button_mute :
  spec_msg_step ex_button_mute 3 0 0 =
  {| sm_code := 1; sm_at := 0; sm_len := 3; sm_next := 3; sm_status := 144; sm_running := 0;
     sm_d1 := 8; sm_d2 := 64; sm_status_out := 144; sm_sysex_at := 0; sm_sysex_len := 0 |} := eq_refl.

Example worked_event_button_mute :
  let e := spec_event_of ex_button_mute (spec_msg_step ex_button_mute 3 0 0) in
  (se_kind e, se_button e, se_on e, se_strip e, se_zone e) = (SPEC_EV_STRIP_BUTTON, 8, 1, 0, 0) := eq_refl.

(* scribble_write: F7 at 10, payload 13 01 40 00 00 4f 4d 58 31 (9 bytes at 1); scribble,
   device 01, address 00, 4 characters "OMX1" *)
Example worked_scribble_write :
  let m := spec_msg_step ex_scribble_write 11 0 0 in
  let e := spec_event_of ex_scribble_write m in
  (sm_code m, sm_len m, sm_sysex_at m, sm_sysex_len m, sm_status_out m,
   se_kind e, se_device e, se_addr e, se_len e, se_text e) =
  (1, 11, 1, 9, 0, SPEC_EV_SCRIBBLE, 1, 0, 4, [79; 77; 88; 49; 0; 0; 0; 0]) := eq_refl.

(* meter: channel 00, left, mask 07 << 7 | 7f = 1023, ten segments *)
Example worked_meter :
  let e := spec_event_of ex_meter (spec_msg_step ex_meter 8 0 0) in
  (se_kind e, se_addr e, se_strip e, se_right e, se_mask e, se_segments e, se_device e) =
  (SPEC_EV_METER, 0, 0, 0, 1023, 10, 1) := eq_refl.

(* meter-right: ch 0x23 = channel 3 | 0x20 (right), mask 7f << 7 | 7f = 16383, 14 segments,
   ProControl device 00 *)
Example worked_meter_right :
  let e := spec_event_of ex_meter_right (spec_msg_step ex_meter_right 8 0 0) in
  (se_kind e, se_addr e, se_strip e, se_right e, se_mask e, se_segments e, se_device e) =
  (SPEC_EV_METER, 35, 3, 1, 16383, 14, 0) := eq_refl.

(* counter_write: address 0x19, dots 0x40, wire digits 5b 6d 30 00 00 00 00 00 reversed *)
Example worked_counter_write :
  let e := spec_event_of ex_counter_write (spec_msg_step ex_counter_write 15 0 0) in
  (se_kind e, se_addr e, se_dots e, se_seg e) =
  (SPEC_EV_COUNTER, 25, 64, [0; 0; 0; 0; 0; 48; 109; 91]) := eq_refl.

(* ring: 45 = strip 5 | LED 1, 7f = LEDs 2..8, 40 = LED 9: mask 0x1ff *)
Example worked_ring :
  let e := spec_event_of ex_ring (spec_msg_step ex_ring 8 0 0) in
  (se_kind e, se_strip e, se_mask e) = (SPEC_EV_RING, 5, 511) := eq_refl.

(* strip-leds: strip 2, bits 0x44 (write | read) *)
Example worked_strip_leds :
  let e := spec_event_of ex_strip_leds (spec_msg_step ex_strip_leds 7 0 0) in
  (se_kind e, se_addr e, se_strip e, se_mask e) = (SPEC_EV_STRIP_LEDS, 2, 2, 68) := eq_refl.

(* touch: 90 09 45 is strip button 09 on strip 5, down: the fader touch *)
Example worked_touch :
  let e := spec_event_of ex_touch (spec_msg_step ex_touch 3 0 0) in
  (se_kind e, se_button e, se_on e, se_strip e) = (SPEC_EV_TOUCH, 9, 1, 5) := eq_refl.

(* sysex-no-f7: cut short at the end of the body, running status cancelled *)
Example worked_sysex_no_f7 :
  let m := spec_msg_step ex_sysex_no_f7 5 0 0 in
  (sm_code m, sm_next m, sm_status_out m) = (SPEC_E_TRUNCATED, 5, 0) := eq_refl.

(* one-data-byte: C0 05, D0 7F, then 10 under running status D0: one data byte each *)
Example worked_one_data_byte :
  let m := spec_msg_step ex_one_data_byte 5 4 208 in
  (sm_code m, sm_status m, sm_running m, sm_d1 m, sm_d2 m, sm_len m, sm_next m) = (1, 208, 1, 16, 0, 1, 5) := eq_refl.

(* the system family: after a message, of another maker, cut short, inside another sysex *)
Example worked_system_at :
  (spec_system_at [144; 8; 64; 240; 19; 0; 112; 1; 2] 9, spec_system_at [240; 18; 1; 112; 247] 5,
   spec_system_at [240; 19; 1; 112] 4, spec_system_at [240; 1; 240; 19; 1; 112; 247] 7) =
  (3, -1, 0, 2) := eq_refl.

Example worked_segments :
  (spec_segments 0, spec_segments 5, spec_segments 16383, spec_segments 32767) = (0, -1, 14, -1) := eq_refl.

(* fader_move-frame: a data frame whose body is the 5 bytes of fader_move; sum 0xb0 + 0x40 +
   0x20 = 0x110 *)
Example worked_read_frame :
  let w := spec_read_frame ex_fader_move_frame 60 in
  (sf_code w, sf_ethertype w, sf_numbytes w, sf_sum w, sf_send w, sf_ack w, sf_retry w, sf_cmd w,
   sf_ncmds w, sf_body w, sf_body_len w, sf_pad_len w, sf_body_sum w) =
  (SPEC_OK, 34911, 21, 272, 261, 0, 0, 0, 1, 30, 5, 25, 272) := eq_refl.

Example worked_read_frame_refused : sf_code (spec_read_frame ex_frame_refused 20) = SPEC_E_SHORT := eq_refl.
