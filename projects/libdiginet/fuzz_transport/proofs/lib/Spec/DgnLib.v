(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* libdiginet's Gallina model, part two (DgnSpec.v is part one). Pure Gallina models of
   - src/diginet_msg.c: diginet_cursor_init, channel_data_len, diginet_msg_next;
   - src/diginet_decode.c: diginet_decoder_init, decode_note, decode_sysex, diginet_decoder_next;
   - src/diginet_codec.c: the personalities table, diginet_personality_of, diginet_meter_segments,
     diginet_body_check;
   and, folded from fuzz_frame's model with its names kept, the same library code read over a list byte with
   nat positions: diginet_msg_next as msg_step (msg_res), diginet_body_check as body_check (bc_loop, refused),
   and src/diginet_frame.c's diginet_frame_build (lib_build_code, lib_frame). The linking lemmas after it join
   the two readings: diginet_msg_next_msg_step, diginet_body_check_body_check, spec_system_at_system_at
   (spec_system_at_first), spec_read_frame_fr (holds_body_fr_body).
   Then, folded from fuzz_codec's model with its names kept but for bit and upd (bit_or_0, upd_at),
   src/diginet_codec.c's encoders and helpers (sysex_spec, the fader .. counter encoders, ring_dot / ring_fill,
   meter_mask, meter_segments, seg7, scribble_text, counter_text) and enc_of_call, fuzz_codec's run() dispatch
   over them (fuzz_codec.c:531-548); and the lemmas that join it to this file: personalities_desks,
   personality_desk, meter_segments_spec_eq.
   A body is a list Z of bytes in [0, 256), read with byte_at (DgnSpec.v). The body pointer is not modelled: the
   body list is an argument, and a pointer into the body is its offset. The build is riscv64 lp64d: char is
   unsigned, int is 32 bits, size_t is 64 bits. Sizes and positions are Z; the size_t sums below never wrap, since
   every body is shorter than 2^26 bytes (the harnesses refuse an input of 64 MiB or more, fuzz.h:23;
   fuzz_decode.c:289-290, fuzz_frame.c:270-271).
   NULL object pointers are not modelled: every call fuzz_decode makes passes the address of one of its own
   objects (fuzz_decode.c:283-287), and diginet_body_check passes its own (diginet_codec.c:49-53), so the
   early returns on `!c`, `!m`, `!d`, `!ev` (diginet_msg.c:12-13, :29-30;
   diginet_decode.c:14-15, :110-111) are never taken.
   u8, u16, s8, s16 (DgnSpec.v) are the C conversions to uint8_t, uint16_t, int8_t, int16_t; outside the folded
   fuzz_codec part, each narrowing conversion the C code makes is written with one of them and the file:line
   where C makes it. A copy between
   objects of the same type (uint8_t to uint8_t), or a widening one (uint8_t to uint16_t), changes no value and is
   a plain read. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* ---- constants (include/diginet/diginet.h, include/diginet/diginet_codec.h) ---- *)

Definition DIGINET_OK : Z := 0.                 (* diginet.h:59 *)
Definition DIGINET_E_TRUNCATED : Z := -6.       (* diginet.h:65 *)
Definition DIGINET_E_NO_STATUS : Z := -7.       (* diginet.h:66 *)
Definition DIGINET_E_STATUS : Z := -8.          (* diginet.h:67 *)
Definition DIGINET_E_REFUSED : Z := -10.        (* diginet.h:69 *)

Definition DIGINET_BTN_TOUCH : Z := 0x09.       (* diginet_codec.h:87 *)
Definition DIGINET_ZONE_FIRST : Z := 0x18.      (* diginet_codec.h:90 *)
Definition DIGINET_ZONE_LAST : Z := 0x1d.       (* diginet_codec.h:91 *)
Definition DIGINET_JOG_CC : Z := 0x5c.          (* diginet_codec.h:98 *)
Definition DIGINET_METER_SEGMENTS : Z := 14.    (* diginet_codec.h:114 *)
Definition DIGINET_SCRIBBLE_MAX : Z := 8.       (* diginet_codec.h:134 *)
Definition DIGINET_COUNTER_DIGITS : Z := 8.     (* diginet_codec.h:144 *)
Definition DIGINET_SYSEX_MAKER : Z := 0x13.     (* diginet_codec.h:162 *)
Definition DIGINET_FN_RING : Z := 0x00.         (* diginet_codec.h:163 *)
Definition DIGINET_FN_METER : Z := 0x10.        (* diginet_codec.h:164 *)
Definition DIGINET_FN_LEDS : Z := 0x20.         (* diginet_codec.h:165 *)
Definition DIGINET_FN_COUNTER : Z := 0x30.      (* diginet_codec.h:166 *)
Definition DIGINET_FN_SCRIBBLE : Z := 0x40.     (* diginet_codec.h:167 *)
Definition DIGINET_FN_SYSTEM : Z := 0x70.       (* diginet_codec.h:168 *)

(* enum diginet_event_kind, diginet_codec.h:177-191 *)
Definition DIGINET_EV_FADER : Z := 1.
Definition DIGINET_EV_TOUCH : Z := 2.
Definition DIGINET_EV_STRIP_BUTTON : Z := 3.
Definition DIGINET_EV_SECTION_BUTTON : Z := 4.
Definition DIGINET_EV_VPOT : Z := 5.
Definition DIGINET_EV_JOG : Z := 6.
Definition DIGINET_EV_RING : Z := 7.
Definition DIGINET_EV_METER : Z := 8.
Definition DIGINET_EV_STRIP_LEDS : Z := 9.
Definition DIGINET_EV_SCRIBBLE : Z := 10.
Definition DIGINET_EV_COUNTER : Z := 11.
Definition DIGINET_EV_SYSTEM : Z := 12.
Definition DIGINET_EV_OTHER : Z := 13.

(* the int value of a C comparison or logical expression *)
Definition int_of_bool (b : bool) : Z := if b then 1 else 0.

(* ---- src/diginet_msg.c ---- *)

(* diginet_msg.c:10-18. `c->len = body ? len : 0` (:15) is len: the body is a list, so its pointer is not NULL
   (fuzz.h:81-88 aborts when the allocation fails, fuzz.h:90-96; fuzz_decode.c:292-298 passes that block or a pointer
   into it). *)
Definition diginet_cursor_init (len : Z) : dgn_cursor :=
  {| dc_len := len; dc_pos := 0; dc_status := 0 |}.

(* diginet_msg.c:21-25; kind = (uint8_t)(status & 0xf0) at :23 *)
Definition channel_data_len (status : Z) : Z :=
  let kind := u8 (Z.land status 0xf0) in
  if (kind =? 0xc0) || (kind =? 0xd0) then 1 else 2.

(* diginet_msg.c:44-46, `while (i < c->len && b[i] != 0xf7) i++;`. Called with fuel len - i, which is exact: each
   turn adds one to i, and the loop stops at i = len at the latest. *)
Fixpoint msg_scan_f7 (b : list Z) (len i : Z) (fuel : nat) : Z :=
  match fuel with
  | O => i
  | S f => if (i <? len) && negb (byte_at b i =? 0xf7) then msg_scan_f7 b len (i + 1) f else i
  end.

(* diginet_msg.c:88-95, `for (i = 0; i < n; i++) if (b[data_at + i] & 0x80) ...`: called with i = 0 and fuel n,
   the first i < n whose byte has bit 7 set *)
Fixpoint first_high (b : list Z) (data_at i : Z) (fuel : nat) : option Z :=
  match fuel with
  | O => None
  | S f => if negb (Z.land (byte_at b (data_at + i)) 0x80 =? 0) then Some i else first_high b data_at (i + 1) f
  end.

(* The tail of diginet_msg_next for a channel message (diginet_msg.c:83-102), from the message m0 written at
   :38-41, the effective status, the place of the first data byte and the running flag (:70-72 or :78-80). *)
Definition msg_channel (b : list Z) (c : dgn_cursor) (m0 : dgn_msg) (status data_at running : Z)
  : Z * dgn_msg * dgn_cursor :=
  let len := dc_len c in
  let m1 := {| dm_status := dm_status m0; dm_running := running; dm_d1 := dm_d1 m0; dm_d2 := dm_d2 m0;
               dm_sysex := dm_sysex m0; dm_sysex_len := dm_sysex_len m0; dm_offset := dm_offset m0;
               dm_len := dm_len m0 |} in
  let n := channel_data_len status in                                                      (* :83 *)
  if len <? data_at + n then                                                               (* :84-87 *)
    (DIGINET_E_TRUNCATED, m1, {| dc_len := len; dc_pos := len; dc_status := dc_status c |})
  else
    match first_high b data_at 0 (Z.to_nat n) with                                         (* :88-95 *)
    | Some i => (DIGINET_E_TRUNCATED, m1, {| dc_len := len; dc_pos := data_at + i; dc_status := 0 |})
    | None =>                                                                              (* :96-102 *)
        (1, {| dm_status := status; dm_running := running; dm_d1 := byte_at b data_at;
               (* :98, (uint8_t) of the int `n > 1 ? b[data_at + 1] : 0` *)
               dm_d2 := u8 (if 1 <? n then byte_at b (data_at + 1) else 0);
               dm_sysex := dm_sysex m0; dm_sysex_len := dm_sysex_len m0; dm_offset := dm_offset m0;
               dm_len := data_at + n - dc_pos c |},
         {| dc_len := len; dc_pos := data_at + n; dc_status := status |})
    end.

(* diginet_msg.c:27-103: (r, *m, *c) after the call. *m is an argument because the C function writes only some of
   its fields on each path. The fields each path leaves as they were:
   - r = 0 (:31-32): every field of *m, and *c;
   - r = DIGINET_E_TRUNCATED after F0 (:48-51), r = DIGINET_E_STATUS (:64-69), r = DIGINET_E_NO_STATUS (:74-77):
     status, running and len (offset, sysex, sysex_len, d1 and d2 are written at :38-41 on every path past :32);
   - r = DIGINET_E_TRUNCATED in a channel message (:84-87, :88-94): status and len (running is written at :72 or
     :80);
   - r = 1: none.
   dm_sysex is the offset of the payload in the body: the C pointer is body + dm_sysex. NULL (:39) is 0, which no
   payload offset is, since a payload starts after its F0 (:54, offset start + 1 >= 1). *)
Definition diginet_msg_next (b : list Z) (c : dgn_cursor) (m : dgn_msg) : Z * dgn_msg * dgn_cursor :=
  let len := dc_len c in
  let start := dc_pos c in
  if len <=? start then (0, m, c)                                                          (* :31-32 *)
  else
    let lead := byte_at b start in                                                         (* :36 *)
    let m0 := {| dm_status := dm_status m; dm_running := dm_running m; dm_d1 := 0; dm_d2 := 0; dm_sysex := 0;
                 dm_sysex_len := 0; dm_offset := start; dm_len := dm_len m |} in           (* :38-41 *)
    if lead =? 0xf0 then                                                                   (* :43-59 *)
      let i := msg_scan_f7 b len (start + 1) (Z.to_nat (len - (start + 1))) in
      if len <=? i then
        (DIGINET_E_TRUNCATED, m0, {| dc_len := len; dc_pos := len; dc_status := 0 |})
      else
        (1, {| dm_status := 0xf0; dm_running := 0; dm_d1 := 0; dm_d2 := 0; dm_sysex := start + 1;
               dm_sysex_len := i - start - 1; dm_offset := start; dm_len := i + 1 - start |},
         {| dc_len := len; dc_pos := i + 1; dc_status := 0 |})
    else if negb (Z.land lead 0x80 =? 0) then                                              (* :63 *)
      if 0xf0 <=? lead then                                                                (* :64-69 *)
        (DIGINET_E_STATUS, m0, {| dc_len := len; dc_pos := start + 1; dc_status := 0 |})
      else msg_channel b c m0 lead (start + 1) 0                                           (* :70-72 *)
    else if dc_status c =? 0 then                                                          (* :74-77 *)
      (DIGINET_E_NO_STATUS, m0, {| dc_len := len; dc_pos := start + 1; dc_status := dc_status c |})
    else msg_channel b c m0 (dc_status c) start 1.                                         (* :78-80 *)

(* ---- the personalities (src/diginet_codec.c) ---- *)

(* struct diginet_personality, diginet_codec.h:31-38; announce_name is the bytes of the C string before its NUL *)
Record dgn_personality := DgnPersonality {
  dp_desk : Z;
  dp_announce_name : list Z;
  dp_device : Z;
  dp_strips : Z;
  dp_scribble_chars : Z;
  dp_counter_addr : Z
}.

(* diginet_codec.c:12-15: "CNTRL|24" and "MAINUNIT" *)
Definition personalities : list dgn_personality :=
  [ {| dp_desk := DIGINET_DESK_CONTROL24; dp_announce_name := [0x43; 0x4e; 0x54; 0x52; 0x4c; 0x7c; 0x32; 0x34];
       dp_device := 0x01; dp_strips := 24; dp_scribble_chars := 4; dp_counter_addr := 0x19 |};
    {| dp_desk := DIGINET_DESK_PROCONTROL; dp_announce_name := [0x4d; 0x41; 0x49; 0x4e; 0x55; 0x4e; 0x49; 0x54];
       dp_device := 0x00; dp_strips := 8; dp_scribble_chars := 8; dp_counter_addr := 0x09 |} ].

(* diginet_codec.c:29-31: the index of the first entry of t, counted from i, whose desk is desk *)
Fixpoint personality_find (t : list dgn_personality) (i desk : Z) : option Z :=
  match t with
  | [] => None
  | p :: t' => if dp_desk p =? desk then Some i else personality_find t' (i + 1) desk
  end.

(* diginet_codec.c:27-33: a pointer to personalities[i] is Some i; NULL (:32) is None *)
Definition diginet_personality_of (desk : Z) : option Z := personality_find personalities 0 desk.

(* the entry a personality index points to *)
Definition personality_at (i : Z) : option dgn_personality := nth_error personalities (Z.to_nat i).

(* ---- src/diginet_codec.c: meters and the refusal ---- *)

(* diginet_codec.c:211-213: n counts up while n < 14 and bit n of mask is set; fuel 14 is exact, since the
   loop stops at n = 14 at the latest *)
Fixpoint meter_count (mask n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S f =>
      if (n <? DIGINET_METER_SEGMENTS) && negb (Z.land mask (Z.shiftl 1 n) =? 0)
      then meter_count mask (n + 1) f else n
  end.

(* diginet_codec.c:209-215; mask is a uint16_t, so it is in [0, 2^16) *)
Definition diginet_meter_segments (mask : Z) : Z :=
  let n := meter_count mask 0 14 in
  if negb (Z.shiftr mask n =? 0) then -1 else n.

(* diginet_codec.c:52-56, the loop over the cursor: Some true when it returns DIGINET_E_REFUSED (:56), Some false
   when diginet_msg_next returns 0 and the loop ends; None when the fuel runs out, which body_check_loop_fuel shows
   does not happen with fuel len - pos + 1. The condition reads m only when r = 1 (:54). *)
Fixpoint body_check_loop (b : list Z) (c : dgn_cursor) (m : dgn_msg) (fuel : nat) : option bool :=
  match fuel with
  | O => None
  | S f =>
      let '(r, m', c') := diginet_msg_next b c m in
      if r =? 0 then Some false
      else if (r =? 1) && (dm_status m' =? 0xf0) && (3 <=? dm_sysex_len m') &&
              (byte_at b (dm_sysex m') =? DIGINET_SYSEX_MAKER) &&
              (byte_at b (dm_sysex m' + 2) =? DIGINET_FN_SYSTEM)
      then Some true
      else body_check_loop b c' m' f
  end.

(* diginet_codec.c:59-62, `for (i = 0; i + 3 < len; i++)`: true when it finds F0 13 xx 70 at i. Called with i = 0
   and fuel len, which is exact: the loop makes at most len - 2 tests of i + 3 < len. *)
Fixpoint system_prefix_scan (b : list Z) (len i : Z) (fuel : nat) : bool :=
  match fuel with
  | O => false
  | S f =>
      if i + 3 <? len then
        if (byte_at b i =? 0xf0) && (byte_at b (i + 1) =? DIGINET_SYSEX_MAKER) &&
           (byte_at b (i + 3) =? DIGINET_FN_SYSTEM)
        then true else system_prefix_scan b len (i + 1) f
      else false
  end.

(* diginet_codec.c:47-64. m is uninitialised (:50); the model starts it at dgn_msg_zero, which gives the same
   result as any other start value: the condition reads m only after diginet_msg_next returned 1, and then every
   field of m is written (diginet_msg_next_fills). *)
Definition diginet_body_check (b : list Z) (len : Z) : Z :=
  match body_check_loop b (diginet_cursor_init len) dgn_msg_zero (S (Z.to_nat len)) with
  | Some true => DIGINET_E_REFUSED
  | _ => if system_prefix_scan b len 0 (Z.to_nat len) then DIGINET_E_REFUSED else DIGINET_OK
  end.

(* ---- src/diginet_decode.c ---- *)

(* struct diginet_decoder, diginet_codec.h:208-211: the cursor, and p as the index of the personalities entry it
   points to (None for NULL) *)
Record dgn_decoder := DgnDecoder {
  dd_c : dgn_cursor;
  dd_p : option Z
}.

(* diginet_decode.c:11-18: `d->p = p ? p : diginet_personality_of(DIGINET_DESK_CONTROL24)` (:17) *)
Definition diginet_decoder_init (p : option Z) (len : Z) : dgn_decoder :=
  {| dd_c := diginet_cursor_init len;
     dd_p := match p with Some _ => p | None => diginet_personality_of DIGINET_DESK_CONTROL24 end |}.

(* One store to a field of struct diginet_event (diginet_codec.h:193-206). *)
Definition de_set_kind (v : Z) (e : dgn_event) : dgn_event :=
  DgnEvent v (de_strip e) (de_button e) (de_zone e) (de_on e) (de_right e) (de_addr e) (de_lsb_missing e)
    (de_value e) (de_delta e) (de_mask e) (de_segments e) (de_len e) (de_text e) (de_seg e) (de_dots e)
    (de_device e) (de_msg e).
Definition de_set_strip (v : Z) (e : dgn_event) : dgn_event :=
  DgnEvent (de_kind e) v (de_button e) (de_zone e) (de_on e) (de_right e) (de_addr e) (de_lsb_missing e)
    (de_value e) (de_delta e) (de_mask e) (de_segments e) (de_len e) (de_text e) (de_seg e) (de_dots e)
    (de_device e) (de_msg e).
Definition de_set_button (v : Z) (e : dgn_event) : dgn_event :=
  DgnEvent (de_kind e) (de_strip e) v (de_zone e) (de_on e) (de_right e) (de_addr e) (de_lsb_missing e)
    (de_value e) (de_delta e) (de_mask e) (de_segments e) (de_len e) (de_text e) (de_seg e) (de_dots e)
    (de_device e) (de_msg e).
Definition de_set_zone (v : Z) (e : dgn_event) : dgn_event :=
  DgnEvent (de_kind e) (de_strip e) (de_button e) v (de_on e) (de_right e) (de_addr e) (de_lsb_missing e)
    (de_value e) (de_delta e) (de_mask e) (de_segments e) (de_len e) (de_text e) (de_seg e) (de_dots e)
    (de_device e) (de_msg e).
Definition de_set_on (v : Z) (e : dgn_event) : dgn_event :=
  DgnEvent (de_kind e) (de_strip e) (de_button e) (de_zone e) v (de_right e) (de_addr e) (de_lsb_missing e)
    (de_value e) (de_delta e) (de_mask e) (de_segments e) (de_len e) (de_text e) (de_seg e) (de_dots e)
    (de_device e) (de_msg e).
Definition de_set_right (v : Z) (e : dgn_event) : dgn_event :=
  DgnEvent (de_kind e) (de_strip e) (de_button e) (de_zone e) (de_on e) v (de_addr e) (de_lsb_missing e)
    (de_value e) (de_delta e) (de_mask e) (de_segments e) (de_len e) (de_text e) (de_seg e) (de_dots e)
    (de_device e) (de_msg e).
Definition de_set_addr (v : Z) (e : dgn_event) : dgn_event :=
  DgnEvent (de_kind e) (de_strip e) (de_button e) (de_zone e) (de_on e) (de_right e) v (de_lsb_missing e)
    (de_value e) (de_delta e) (de_mask e) (de_segments e) (de_len e) (de_text e) (de_seg e) (de_dots e)
    (de_device e) (de_msg e).
Definition de_set_lsb_missing (v : Z) (e : dgn_event) : dgn_event :=
  DgnEvent (de_kind e) (de_strip e) (de_button e) (de_zone e) (de_on e) (de_right e) (de_addr e) v
    (de_value e) (de_delta e) (de_mask e) (de_segments e) (de_len e) (de_text e) (de_seg e) (de_dots e)
    (de_device e) (de_msg e).
Definition de_set_value (v : Z) (e : dgn_event) : dgn_event :=
  DgnEvent (de_kind e) (de_strip e) (de_button e) (de_zone e) (de_on e) (de_right e) (de_addr e)
    (de_lsb_missing e) v (de_delta e) (de_mask e) (de_segments e) (de_len e) (de_text e) (de_seg e) (de_dots e)
    (de_device e) (de_msg e).
Definition de_set_delta (v : Z) (e : dgn_event) : dgn_event :=
  DgnEvent (de_kind e) (de_strip e) (de_button e) (de_zone e) (de_on e) (de_right e) (de_addr e)
    (de_lsb_missing e) (de_value e) v (de_mask e) (de_segments e) (de_len e) (de_text e) (de_seg e) (de_dots e)
    (de_device e) (de_msg e).
Definition de_set_mask (v : Z) (e : dgn_event) : dgn_event :=
  DgnEvent (de_kind e) (de_strip e) (de_button e) (de_zone e) (de_on e) (de_right e) (de_addr e)
    (de_lsb_missing e) (de_value e) (de_delta e) v (de_segments e) (de_len e) (de_text e) (de_seg e) (de_dots e)
    (de_device e) (de_msg e).
Definition de_set_segments (v : Z) (e : dgn_event) : dgn_event :=
  DgnEvent (de_kind e) (de_strip e) (de_button e) (de_zone e) (de_on e) (de_right e) (de_addr e)
    (de_lsb_missing e) (de_value e) (de_delta e) (de_mask e) v (de_len e) (de_text e) (de_seg e) (de_dots e)
    (de_device e) (de_msg e).
Definition de_set_len (v : Z) (e : dgn_event) : dgn_event :=
  DgnEvent (de_kind e) (de_strip e) (de_button e) (de_zone e) (de_on e) (de_right e) (de_addr e)
    (de_lsb_missing e) (de_value e) (de_delta e) (de_mask e) (de_segments e) v (de_text e) (de_seg e) (de_dots e)
    (de_device e) (de_msg e).
Definition de_set_text (v : list Z) (e : dgn_event) : dgn_event :=
  DgnEvent (de_kind e) (de_strip e) (de_button e) (de_zone e) (de_on e) (de_right e) (de_addr e)
    (de_lsb_missing e) (de_value e) (de_delta e) (de_mask e) (de_segments e) (de_len e) v (de_seg e) (de_dots e)
    (de_device e) (de_msg e).
Definition de_set_seg (v : list Z) (e : dgn_event) : dgn_event :=
  DgnEvent (de_kind e) (de_strip e) (de_button e) (de_zone e) (de_on e) (de_right e) (de_addr e)
    (de_lsb_missing e) (de_value e) (de_delta e) (de_mask e) (de_segments e) (de_len e) (de_text e) v (de_dots e)
    (de_device e) (de_msg e).
Definition de_set_dots (v : Z) (e : dgn_event) : dgn_event :=
  DgnEvent (de_kind e) (de_strip e) (de_button e) (de_zone e) (de_on e) (de_right e) (de_addr e)
    (de_lsb_missing e) (de_value e) (de_delta e) (de_mask e) (de_segments e) (de_len e) (de_text e) (de_seg e) v
    (de_device e) (de_msg e).
Definition de_set_device (v : Z) (e : dgn_event) : dgn_event :=
  DgnEvent (de_kind e) (de_strip e) (de_button e) (de_zone e) (de_on e) (de_right e) (de_addr e)
    (de_lsb_missing e) (de_value e) (de_delta e) (de_mask e) (de_segments e) (de_len e) (de_text e) (de_seg e)
    (de_dots e) v (de_msg e).
Definition de_set_msg (v : dgn_msg) (e : dgn_event) : dgn_event :=
  DgnEvent (de_kind e) (de_strip e) (de_button e) (de_zone e) (de_on e) (de_right e) (de_addr e)
    (de_lsb_missing e) (de_value e) (de_delta e) (de_mask e) (de_segments e) (de_len e) (de_text e) (de_seg e)
    (de_dots e) (de_device e) v.

(* a store to element i of a C array held as its full-length list; every index the decoder stores to is in
   range (text[0..8], seg[0..7]) *)
Fixpoint list_set (l : list Z) (i : nat) (v : Z) : list Z :=
  match l, i with
  | [], _ => []
  | _ :: t, O => v :: t
  | x :: t, S j => x :: list_set t j v
  end.

(* diginet_decode.c:20-35 *)
Definition decode_note (m : dgn_msg) (ev : dgn_event) : dgn_event :=
  let id := u8 (Z.land (dm_d2 m) 0x3f) in                                   (* :22, (uint8_t) of an int *)
  let ev := de_set_on (u8 (int_of_bool (negb (Z.land (dm_d2 m) 0x40 =? 0)))) ev in   (* :23, int to uint8_t *)
  let ev := de_set_button (dm_d1 m) ev in                                    (* :24 *)
  if (DIGINET_ZONE_FIRST <=? id) && (id <=? DIGINET_ZONE_LAST) then          (* :25-27 *)
    de_set_zone id (de_set_kind DIGINET_EV_SECTION_BUTTON ev)
  else if dm_d1 m =? DIGINET_BTN_TOUCH then                                  (* :28-30 *)
    de_set_strip id (de_set_kind DIGINET_EV_TOUCH ev)
  else                                                                       (* :31-33 *)
    de_set_strip id (de_set_kind DIGINET_EV_STRIP_BUTTON ev).

(* diginet_decode.c:56-61, the ring's LED loop over k = 0..6 (fuel 7) from bits b1 = pl[1] and b2 = pl[2]; each
   `ev->mask |= (uint16_t)(1u << j)` converts 1u << j to uint16_t, then the int ev->mask | that to uint16_t *)
Fixpoint ring_loop (mask b1 b2 k : Z) (fuel : nat) : Z :=
  match fuel with
  | O => mask
  | S f =>
      let mask := if negb (Z.land b1 (Z.shiftl 1 (6 - k)) =? 0)                       (* :57-58 *)
                  then u16 (Z.lor mask (u16 (Z.shiftl 1 (1 + k)))) else mask in
      let mask := if negb (Z.land b2 (Z.shiftl 1 (6 - k)) =? 0)                       (* :59-60 *)
                  then u16 (Z.lor mask (u16 (Z.shiftl 1 (8 + k)))) else mask in
      ring_loop mask b1 b2 (k + 1) f
  end.

(* diginet_decode.c:87, memcpy(ev->text, pl + 2, ev->len): text[j] = b[src + j] for j = i.. (i = 0, fuel len) *)
Fixpoint copy_text (text : list Z) (b : list Z) (src i : Z) (fuel : nat) : list Z :=
  match fuel with
  | O => text
  | S f => copy_text (list_set text (Z.to_nat i) (byte_at b (src + i))) b src (i + 1) f
  end.

(* diginet_decode.c:96-97, seg[DIGINET_COUNTER_DIGITS - 1 - k] = pl[2 + k] for k = 0..7 (k from 0, fuel 8) *)
Fixpoint counter_loop (seg : list Z) (b : list Z) (pl k : Z) (fuel : nat) : list Z :=
  match fuel with
  | O => seg
  | S f =>
      counter_loop (list_set seg (Z.to_nat (DIGINET_COUNTER_DIGITS - 1 - k)) (byte_at b (pl + 2 + k))) b pl (k + 1) f
  end.

(* diginet_decode.c:37-105, every case of the switch at :49. The decoder argument d is not read ((void)d, :42), so
   the model does not take it. s = m->sysex is the payload offset dm_sysex m; s[k] is byte_at b (s + k). *)
Definition decode_sysex (b : list Z) (m : dgn_msg) (ev : dgn_event) : dgn_event :=
  let s := dm_sysex m in                                                     (* :40 *)
  let n := dm_sysex_len m in                                                 (* :41 *)
  let ev := de_set_kind DIGINET_EV_OTHER ev in                               (* :43 *)
  if (n <? 3) || negb (byte_at b s =? DIGINET_SYSEX_MAKER) then ev           (* :44-45 *)
  else
    let ev := de_set_device (byte_at b (s + 1)) ev in                        (* :46 *)
    let pl := s + 3 in                                                       (* :47 *)
    let pn := n - 3 in                                                       (* :48, n >= 3: no wrap *)
    let fn := byte_at b (s + 2) in                                           (* :49 *)
    if fn =? DIGINET_FN_RING then                                            (* :50-62 *)
      if negb (pn =? 3) then ev
      else
        let p0 := byte_at b pl in
        let ev := de_set_kind DIGINET_EV_RING ev in
        let ev := de_set_strip (u8 (Z.land p0 0x3f)) ev in                   (* :54, int to uint8_t *)
        let mask := u16 (if negb (Z.land p0 0x40 =? 0) then 1 else 0) in     (* :55, int to uint16_t *)
        de_set_mask (ring_loop mask (byte_at b (pl + 1)) (byte_at b (pl + 2)) 0 7) ev
    else if fn =? DIGINET_FN_METER then                                      (* :63-72 *)
      if negb (pn =? 3) then ev
      else
        let p0 := byte_at b pl in
        let ev := de_set_kind DIGINET_EV_METER ev in
        let ev := de_set_addr p0 ev in                                       (* :67 *)
        let ev := de_set_strip (u8 (Z.land p0 0x1f)) ev in                   (* :68, int to uint8_t *)
        let ev := de_set_right (u8 (int_of_bool (negb (Z.land p0 0x20 =? 0)))) ev in   (* :69, int to uint8_t *)
        let mask := u16 (Z.lor (Z.shiftl (Z.land (byte_at b (pl + 1)) 0x7f) 7)
                               (Z.land (byte_at b (pl + 2)) 0x7f)) in        (* :70, int to uint16_t *)
        let ev := de_set_mask mask ev in
        de_set_segments (s8 (diginet_meter_segments mask)) ev                (* :71, int to int8_t *)
    else if fn =? DIGINET_FN_LEDS then                                       (* :73-80 *)
      if negb (pn =? 2) then ev
      else
        let ev := de_set_kind DIGINET_EV_STRIP_LEDS ev in
        let ev := de_set_addr (byte_at b pl) ev in                           (* :77 *)
        let ev := de_set_strip (byte_at b pl) ev in                          (* :78 *)
        de_set_mask (byte_at b (pl + 1)) ev                                  (* :79, uint8_t to uint16_t *)
    else if fn =? DIGINET_FN_SCRIBBLE then                                   (* :81-89 *)
      if (pn <? 3) || (DIGINET_SCRIBBLE_MAX <? pn - 2) then ev               (* :82, pn >= 3: no wrap *)
      else
        let ev := de_set_kind DIGINET_EV_SCRIBBLE ev in
        let ev := de_set_addr (byte_at b pl) ev in                           (* :85 *)
        let len := u8 (pn - 2) in                                            (* :86, size_t to uint8_t *)
        let ev := de_set_len len ev in
        let text := copy_text (de_text ev) b (pl + 2) 0 (Z.to_nat len) in    (* :87 *)
        de_set_text (list_set text (Z.to_nat len) 0) ev                      (* :88 *)
    else if fn =? DIGINET_FN_COUNTER then                                    (* :90-98 *)
      if negb (pn =? 2 + DIGINET_COUNTER_DIGITS) then ev
      else
        let ev := de_set_kind DIGINET_EV_COUNTER ev in
        let ev := de_set_addr (byte_at b pl) ev in                           (* :94 *)
        let ev := de_set_dots (byte_at b (pl + 1)) ev in                     (* :95 *)
        de_set_seg (counter_loop (de_seg ev) b pl 0 8) ev                    (* :96-97 *)
    else if fn =? DIGINET_FN_SYSTEM then                                     (* :99-101 *)
      de_set_kind DIGINET_EV_SYSTEM ev
    else ev.                                                                 (* :102-103 *)

(* diginet_decode.c:107-158: (r, *ev, *d) after the call. *ev is an argument because the function leaves it as it
   was when diginet_msg_next does not return 1 (:113-114); otherwise it zeroes it first (:115), so the result does
   not depend on it. The messages m (:109) and lsb (:136) are uninitialised; the model starts them at
   dgn_msg_zero, which gives the same result as any other start value: each is read only after diginet_msg_next
   returned 1, and then every field is written (diginet_msg_next_fills). The cursor d->c moves on every path,
   including the refusals (:112); a fader takes its LSB only through the peek cursor (:135-140). *)
Definition diginet_decoder_next (b : list Z) (d : dgn_decoder) (ev : dgn_event) : Z * dgn_event * dgn_decoder :=
  let '(r, m, c1) := diginet_msg_next b (dd_c d) dgn_msg_zero in             (* :112 *)
  let d1 := {| dd_c := c1; dd_p := dd_p d |} in
  if negb (r =? 1) then (r, ev, d1)                                          (* :113-114 *)
  else
    let e := de_set_kind DIGINET_EV_OTHER (de_set_msg m dgn_event_zero) in   (* :115-117 *)
    if Z.land (dm_status m) 0xf0 =? 0x90 then (1, decode_note m e, d1)      (* :119-122 *)
    else if dm_status m =? 0xf0 then (1, decode_sysex b m e, d1)            (* :123-126 *)
    else if negb (Z.land (dm_status m) 0xf0 =? 0xb0) then (1, e, d1)        (* :127-128 *)
    else if dm_d1 m <? 0x20 then                                             (* :130-145 *)
      let e := de_set_kind DIGINET_EV_FADER e in
      let e := de_set_strip (dm_d1 m) e in                                   (* :133 *)
      let e := de_set_value (u16 (Z.shiftl (dm_d2 m) 3)) e in                (* :134, int to uint16_t *)
      let '(rl, lsb, peek) := diginet_msg_next b c1 dgn_msg_zero in          (* :135-137 *)
      if (rl =? 1) && (Z.land (dm_status lsb) 0xf0 =? 0xb0) && (dm_d1 lsb =? 0x20 + dm_d1 m) then
        (* :139, (uint16_t) of the int (lsb.d2 >> 4) & 7, then of the int ev->value | that; :140 *)
        (1, de_set_value (u16 (Z.lor (de_value e) (u16 (Z.land (Z.shiftr (dm_d2 lsb) 4) 7)))) e,
         {| dd_c := peek; dd_p := dd_p d |})
      else (1, de_set_lsb_missing 1 e, d1)                                   (* :142 *)
    else if dm_d1 m =? DIGINET_JOG_CC then                                   (* :146-150 *)
      (1, de_set_delta (s16 (dm_d2 m - 64)) (de_set_kind DIGINET_EV_JOG e), d1)   (* :148, int to int16_t *)
    else if (0x40 <=? dm_d1 m) && (dm_d1 m <? 0x40 + DIGINET_ZONE_FIRST) then    (* :151-156 *)
      (1, de_set_delta (s16 (dm_d2 m - 64))                                  (* :154, int to int16_t *)
            (de_set_strip (u8 (dm_d1 m - 0x40)) (de_set_kind DIGINET_EV_VPOT e)), d1)   (* :153, int to uint8_t *)
    else (1, e, d1).                                                         (* :157 *)

(* ---- facts the models rest on ---- *)

Lemma msg_scan_f7_ge : forall b len fuel i, i <= msg_scan_f7 b len i fuel.
Proof.
  intros b len fuel; induction fuel as [|f IH]; intros i; cbn [msg_scan_f7]; [lia|].
  destruct ((i <? len) && negb (byte_at b i =? 0xf7)); [specialize (IH (i + 1)); lia | lia].
Qed.

Lemma msg_scan_f7_le : forall b len fuel i, i <= len -> msg_scan_f7 b len i fuel <= len.
Proof.
  intros b len fuel; induction fuel as [|f IH]; intros i Hi; cbn [msg_scan_f7]; [lia|].
  destruct ((i <? len) && negb (byte_at b i =? 0xf7)) eqn:E; [|lia].
  apply andb_true_iff in E as [E _]. apply Z.ltb_lt in E. apply IH. lia.
Qed.

Lemma first_high_some : forall b a fuel i j, first_high b a i fuel = Some j ->
  i <= j < i + Z.of_nat fuel /\ Z.land (byte_at b (a + j)) 0x80 <> 0.
Proof.
  intros b a fuel; induction fuel as [|f IH]; intros i j H; cbn [first_high] in H; [discriminate|].
  destruct (negb (Z.land (byte_at b (a + i)) 0x80 =? 0)) eqn:E.
  - injection H as <-. apply negb_true_iff, Z.eqb_neq in E. split; [lia | exact E].
  - apply IH in H as [H1 H2]. split; [lia | exact H2].
Qed.

Lemma channel_data_len_range : forall s, 1 <= channel_data_len s <= 2.
Proof.
  intros s. unfold channel_data_len; cbv zeta.
  destruct ((u8 (Z.land s 0xf0) =? 0xc0) || (u8 (Z.land s 0xf0) =? 0xd0)); lia.
Qed.

(* the shape of diginet_msg_next_progress *)
Definition moves (c : dgn_cursor) (res : Z * dgn_msg * dgn_cursor) : Prop :=
  match res with
  | (r, _, c') => (r = 0 /\ c' = c) \/ (r <> 0 /\ dc_len c' = dc_len c /\ dc_pos c < dc_pos c' <= dc_len c)
  end.

Ltac moves_leaf :=
  unfold moves; cbn [dc_len dc_pos]; right;
  unfold DIGINET_E_TRUNCATED, DIGINET_E_STATUS, DIGINET_E_NO_STATUS; lia.

Lemma msg_channel_progress : forall b c m0 status data_at running,
  dc_pos c < dc_len c -> dc_pos c <= data_at ->
  (data_at = dc_pos c -> Z.land (byte_at b data_at) 0x80 = 0) ->
  moves c (msg_channel b c m0 status data_at running).
Proof.
  intros b c m0 status data_at running H1 H2 H3. unfold msg_channel; cbv zeta.
  pose proof (channel_data_len_range status) as Hn.
  destruct (dc_len c <? data_at + channel_data_len status) eqn:E; [moves_leaf|].
  apply Z.ltb_ge in E.
  destruct (first_high b data_at 0 (Z.to_nat (channel_data_len status))) as [i|] eqn:F; [|moves_leaf].
  apply first_high_some in F as [F1 F2]. rewrite Z2Nat.id in F1 by lia.
  assert (Hi : i <> 0 \/ data_at <> dc_pos c).
  { destruct (Z.eq_dec data_at (dc_pos c)) as [Ed|Ed]; [|right; exact Ed].
    left. intros Ei. apply F2. rewrite Ei, Z.add_0_r. apply H3, Ed. }
  destruct Hi; moves_leaf.
Qed.

(* Each call either returns 0 and leaves the cursor, or moves it forward within the body. *)
Lemma diginet_msg_next_progress : forall b c m,
  0 <= dc_pos c -> moves c (diginet_msg_next b c m).
Proof.
  intros b c m Hpos. unfold diginet_msg_next; cbv zeta.
  destruct (dc_len c <=? dc_pos c) eqn:E0; [unfold moves; cbv beta iota; left; split; reflexivity|].
  apply Z.leb_gt in E0.
  destruct (byte_at b (dc_pos c) =? 0xf0) eqn:E1.
  - pose proof (msg_scan_f7_ge b (dc_len c) (Z.to_nat (dc_len c - (dc_pos c + 1))) (dc_pos c + 1)) as G.
    pose proof (msg_scan_f7_le b (dc_len c) (Z.to_nat (dc_len c - (dc_pos c + 1))) (dc_pos c + 1) ltac:(lia)) as L.
    destruct (dc_len c <=? msg_scan_f7 b (dc_len c) (dc_pos c + 1) (Z.to_nat (dc_len c - (dc_pos c + 1)))) eqn:E2.
    + moves_leaf.
    + apply Z.leb_gt in E2. moves_leaf.
  - destruct (negb (Z.land (byte_at b (dc_pos c)) 0x80 =? 0)) eqn:E2.
    + destruct (0xf0 <=? byte_at b (dc_pos c)) eqn:E3; [moves_leaf|].
      cbv beta iota. apply msg_channel_progress; [lia | lia | intros Heq; lia].
    + destruct (dc_status c =? 0) eqn:E3; [moves_leaf|].
      apply negb_false_iff, Z.eqb_eq in E2.
      cbv beta iota. apply msg_channel_progress; [lia | lia | intros _; exact E2].
Qed.

Ltac split_msg_next :=
  repeat match goal with
  | |- context [if ?x then _ else _] => destruct x
  | |- context [match ?x with Some _ => _ | None => _ end] => destruct x
  end.

(* The return value and the cursor never depend on the incoming message. *)
Lemma diginet_msg_next_indep : forall b c m m',
  fst (fst (diginet_msg_next b c m)) = fst (fst (diginet_msg_next b c m')) /\
  snd (diginet_msg_next b c m) = snd (diginet_msg_next b c m').
Proof.
  intros b c m m'. unfold diginet_msg_next, msg_channel; cbv zeta.
  split_msg_next; split; reflexivity.
Qed.

(* When diginet_msg_next returns 1 it has written every field of the message: the result does not depend on the
   incoming one, so an uninitialised message (diginet_decode.c:109, :136; diginet_codec.c:50) is any message. *)
Lemma diginet_msg_next_fills : forall b c m m',
  fst (fst (diginet_msg_next b c m)) = 1 -> diginet_msg_next b c m = diginet_msg_next b c m'.
Proof.
  intros b c m m'. unfold diginet_msg_next, msg_channel; cbv zeta.
  split_msg_next; cbn [fst]; intro H;
    try (unfold DIGINET_E_TRUNCATED, DIGINET_E_STATUS, DIGINET_E_NO_STATUS in H; discriminate H);
    reflexivity.
Qed.

(* The cursor loop of diginet_body_check ends before its fuel runs out. *)
Lemma body_check_loop_fuel : forall fuel b c m,
  0 <= dc_pos c -> (Z.to_nat (dc_len c - dc_pos c) < fuel)%nat -> body_check_loop b c m fuel <> None.
Proof.
  induction fuel as [|f IH]; intros b c m Hpos Hf; [lia|].
  cbn [body_check_loop].
  pose proof (diginet_msg_next_progress b c m Hpos) as P.
  destruct (diginet_msg_next b c m) as [[r m'] c'].
  unfold moves in P. cbv beta iota zeta in P |- *.
  destruct (r =? 0) eqn:R; [discriminate|].
  match goal with |- (if ?x then _ else _) <> None => destruct x end; [discriminate|].
  destruct P as [[P _]|[_ [P1 P2]]]; [apply Z.eqb_neq in R; contradiction|].
  apply IH; lia.
Qed.

Corollary diginet_body_check_loop_ends : forall b len,
  0 <= len -> body_check_loop b (diginet_cursor_init len) dgn_msg_zero (S (Z.to_nat len)) <> None.
Proof. intros b len Hl. apply body_check_loop_fuel; cbn [dc_pos dc_len diginet_cursor_init]; lia. Qed.

(* ---- the library over a list byte, folded from fuzz_frame's model (names kept) ---- *)

(** * The command stream: diginet_msg_next (src/diginet_msg.c:27) *)

(* How a step ends. *)
Inductive msg_kind : Type :=
| MkEnd        (* pos >= len: 0, nothing written *)
| MkSysex      (* F0 up to its first F7: 1 *)
| MkSysexCut   (* F0 and no F7 before the end: -6 (TRUNCATED) *)
| MkBadStatus  (* a status byte F1..FF: -8 (STATUS) *)
| MkNoStatus   (* a data byte with no running status: -7 (NO_STATUS) *)
| MkChanShort  (* the data bytes run past the end: -6 *)
| MkChanCut    (* a status byte where a data byte is due: -6 *)
| MkChan.      (* a channel message: 1 *)

(* One step from the cursor (pos, st). The cursor fields are the new c->pos and c->status. The
   message fields are the values of struct diginet_msg that the step writes; writes_* below say
   which ones it writes. *)
Record msg_res : Type := MsgRes {
  mr_kind : msg_kind;
  mr_start : nat;       (* m->offset: where the message starts, the old pos *)
  mr_pos : nat;         (* c->pos after the step *)
  mr_st : Z;            (* c->status after the step *)
  mr_status : Z;        (* m->status *)
  mr_running : Z;       (* m->running *)
  mr_d1 : Z;            (* m->d1 *)
  mr_d2 : Z;            (* m->d2 *)
  mr_sysex : nat;       (* m->sysex as an index into the body (MkSysex only) *)
  mr_sysex_len : nat;   (* m->sysex_len *)
  mr_len : nat }.       (* m->len *)

Definition mr_code (r : msg_res) : Z :=
  match mr_kind r with
  | MkEnd => 0
  | MkSysex | MkChan => 1
  | MkSysexCut | MkChanShort | MkChanCut => -6
  | MkBadStatus => -8
  | MkNoStatus => -7
  end.

(* Every step but MkEnd writes m->offset, m->d1, m->d2, m->sysex (NULL unless MkSysex) and
   m->sysex_len (src/diginet_msg.c:38-41). These write the other fields. *)
Definition writes_status (k : msg_kind) : bool :=
  match k with MkSysex | MkChan => true | _ => false end.
Definition writes_running (k : msg_kind) : bool :=
  match k with MkSysex | MkChanShort | MkChanCut | MkChan => true | _ => false end.
Definition writes_len (k : msg_kind) : bool :=
  match k with MkSysex | MkChan => true | _ => false end.
Definition writes_sysex (k : msg_kind) : bool :=
  match k with MkSysex => true | _ => false end.
Definition is_end (r : msg_res) : bool :=
  match mr_kind r with MkEnd => true | _ => false end.

(* the index of the first F7 of l *)
Fixpoint find_f7 (l : list byte) : option nat :=
  match l with
  | [] => None
  | x :: r => if bz x =? 0xf7 then Some O else option_map S (find_f7 r)
  end.

(* channel_data_len (src/diginet_msg.c:21): one data byte for C0 and D0, else two *)
Definition chan_n (status : Z) : nat :=
  if (Z.land status 0xf0 =? 0xc0) || (Z.land status 0xf0 =? 0xd0) then 1 else 2.

Definition mr_plain (k : msg_kind) (start pos : nat) (st run : Z) : msg_res :=
  MsgRes k start pos st 0 run 0 0 0 0 0.

(* A channel message with status `status` whose data starts at d (src/diginet_msg.c:83-102);
   st is the running status before the step and run the value of m->running. *)
Definition chan_step (b : list byte) (start : nat) (st status run : Z) (d : nat) : msg_res :=
  if (length b <? d + chan_n status)%nat then mr_plain MkChanShort start (length b) st run
  else if 0x80 <=? at8 b d then mr_plain MkChanCut start d 0 run
  else if (chan_n status =? 2)%nat && (0x80 <=? at8 b (S d)) then mr_plain MkChanCut start (S d) 0 run
  else MsgRes MkChan start (d + chan_n status) status status run (at8 b d)
         (if (chan_n status =? 2)%nat then at8 b (S d) else 0) 0 0 (d + chan_n status - start).

Definition msg_step (b : list byte) (pos : nat) (st : Z) : msg_res :=
  if (length b <=? pos)%nat then mr_plain MkEnd pos pos st 0
  else if at8 b pos =? 0xf0 then
    match find_f7 (skipn (S pos) b) with
    | Some j => MsgRes MkSysex pos (pos + j + 2) 0 0xf0 0 0 0 (S pos) j (j + 2)
    | None => mr_plain MkSysexCut pos (length b) 0 0
    end
  else if 0xf0 <=? at8 b pos then mr_plain MkBadStatus pos (S pos) 0 0
  else if 0x80 <=? at8 b pos then chan_step b pos st (at8 b pos) 0 (S pos)
  else if st =? 0 then mr_plain MkNoStatus pos (S pos) st 0
  else chan_step b pos st st 1 pos.

(* The running status a cursor can hold: none, or a channel status 80..EF. *)
Definition st_ok (st : Z) : Prop := st = 0 \/ 0x80 <= st < 0xf0.

Lemma find_f7_some : forall l j, find_f7 l = Some j ->
  (j < length l)%nat /\ at8 l j = 0xf7 /\ forall k, (k < j)%nat -> at8 l k <> 0xf7.
Proof.
  induction l as [|x l IH]; intros j H; cbn in H; [discriminate|].
  destruct (Z.eqb_spec (bz x) 0xf7) as [E|NE].
  - injection H as <-. cbn. split; [lia|]. split; [exact E|]. intros; lia.
  - destruct (find_f7 l) as [j'|] eqn:F; cbn in H; [|discriminate]. injection H as <-.
    destruct (IH j' eq_refl) as (H1 & H2 & H3). cbn [length].
    split; [lia|]. split; [exact H2|].
    intros [|k] Hk; [exact NE|]. apply H3. lia.
Qed.

Lemma find_f7_none : forall l, find_f7 l = None -> forall k, (k < length l)%nat -> at8 l k <> 0xf7.
Proof.
  induction l as [|x l IH]; intros H k Hk; cbn in Hk; [lia|].
  cbn in H. destruct (Z.eqb_spec (bz x) 0xf7) as [E|NE]; [discriminate|].
  destruct (find_f7 l) eqn:F; cbn in H; [discriminate|].
  destruct k as [|k]; [exact NE|]. apply (IH eq_refl). lia.
Qed.

Lemma find_f7_intro : forall l j, (j < length l)%nat -> at8 l j = 0xf7 ->
  (forall k, (k < j)%nat -> at8 l k <> 0xf7) -> find_f7 l = Some j.
Proof.
  intros l j Hj Hv Hmin. destruct (find_f7 l) as [j'|] eqn:F.
  - destruct (find_f7_some l j' F) as (H1 & H2 & H3). f_equal.
    destruct (Nat.lt_trichotomy j j') as [Hlt|[Heq|Hgt]]; [|exact (eq_sym Heq)|].
    + exfalso. exact (H3 j Hlt Hv).
    + exfalso. exact (Hmin j' Hgt H2).
  - exfalso. exact (find_f7_none l F j Hj Hv).
Qed.

Lemma find_f7_none_intro : forall l, (forall k, (k < length l)%nat -> at8 l k <> 0xf7) -> find_f7 l = None.
Proof.
  intros l H. destruct (find_f7 l) as [j|] eqn:F; [|reflexivity].
  destruct (find_f7_some l j F) as (H1 & H2 & _). exfalso. exact (H j H1 H2).
Qed.

Lemma chan_n_cases : forall s, chan_n s = 1%nat \/ chan_n s = 2%nat.
Proof. intros s. unfold chan_n. destruct (_ || _); auto. Qed.

(* The binary tests (status & 0xe0) == 0xc0. *)
Lemma chan_n_land : forall s, 0 <= s < 2^8 ->
  chan_n s = if Z.land s 0xe0 =? 0xc0 then 1%nat else 2%nat.
Proof.
  intros s Hs. apply Nat.eqb_eq. revert s Hs.
  apply (byte_forall (fun s => Nat.eqb (chan_n s) (if Z.land s 0xe0 =? 0xc0 then 1%nat else 2%nat))).
  vm_compute. reflexivity.
Qed.

Lemma is_end_chan_step : forall b start st status run d, is_end (chan_step b start st status run d) = false.
Proof.
  intros. unfold chan_step.
  destruct (_ <? _)%nat; [reflexivity|]. destruct (0x80 <=? _); [reflexivity|].
  destruct (_ && _); reflexivity.
Qed.

Lemma is_end_msg_step : forall b pos st, is_end (msg_step b pos st) = (length b <=? pos)%nat.
Proof.
  intros b pos st. unfold msg_step.
  destruct (length b <=? pos)%nat; [reflexivity|].
  destruct (at8 b pos =? 0xf0); [destruct (find_f7 _); reflexivity|].
  destruct (0xf0 <=? at8 b pos); [reflexivity|].
  destruct (0x80 <=? at8 b pos); [apply is_end_chan_step|].
  destruct (st =? 0); [reflexivity|apply is_end_chan_step].
Qed.

Lemma mr_start_chan_step : forall b start st status run d, mr_start (chan_step b start st status run d) = start.
Proof.
  intros. unfold chan_step.
  destruct (_ <? _)%nat; [reflexivity|]. destruct (0x80 <=? _); [reflexivity|].
  destruct (_ && _); reflexivity.
Qed.

Lemma msg_step_start : forall b pos st, mr_start (msg_step b pos st) = pos.
Proof.
  intros b pos st. unfold msg_step.
  destruct (length b <=? pos)%nat; [reflexivity|].
  destruct (at8 b pos =? 0xf0); [destruct (find_f7 _); reflexivity|].
  destruct (0xf0 <=? at8 b pos); [reflexivity|].
  destruct (0x80 <=? at8 b pos); [apply mr_start_chan_step|].
  destruct (st =? 0); [reflexivity|apply mr_start_chan_step].
Qed.

Lemma chan_step_progress : forall b start st status run d,
  (start < length b)%nat -> (start <= d)%nat -> (d = start -> at8 b d < 0x80) ->
  (start < mr_pos (chan_step b start st status run d) <= length b)%nat.
Proof.
  intros b start st status run d H1 H2 H3. unfold chan_step.
  pose proof (chan_n_cases status) as Hn.
  destruct (Nat.ltb_spec (length b) (d + chan_n status)) as [L|L]; cbn; [lia|].
  destruct (Z.leb_spec 0x80 (at8 b d)) as [A|A]; cbn.
  - assert (d <> start) by (intros E; specialize (H3 E); lia). lia.
  - destruct (Nat.eqb_spec (chan_n status) 2); destruct (Z.leb_spec 0x80 (at8 b (S d))); cbn; lia.
Qed.

(* A step that is not the end moves the cursor forward, and never past the end. *)
Lemma msg_step_progress : forall b pos st, (pos < length b)%nat ->
  (pos < mr_pos (msg_step b pos st) <= length b)%nat.
Proof.
  intros b pos st H. unfold msg_step.
  destruct (Nat.leb_spec (length b) pos) as [L|_]; [lia|].
  destruct (at8 b pos =? 0xf0).
  - destruct (find_f7 (skipn (S pos) b)) as [j|] eqn:F; cbn; [|lia].
    apply find_f7_some in F. rewrite length_skipn in F. lia.
  - destruct (0xf0 <=? at8 b pos); [cbn; lia|].
    destruct (Z.leb_spec 0x80 (at8 b pos)) as [A|A]; [apply chan_step_progress; lia|].
    destruct (st =? 0); [cbn; lia|].
    apply chan_step_progress; [lia|lia|intros _; lia].
Qed.

Lemma msg_step_pos_le : forall b pos st, (pos <= length b)%nat -> (mr_pos (msg_step b pos st) <= length b)%nat.
Proof.
  intros b pos st H. destruct (Nat.lt_ge_cases pos (length b)) as [L|L].
  - pose proof (msg_step_progress b pos st L). lia.
  - unfold msg_step. destruct (Nat.leb_spec (length b) pos); [cbn; lia|lia].
Qed.

Lemma chan_step_st_ok : forall b start st status run d, st_ok st -> st_ok status ->
  st_ok (mr_st (chan_step b start st status run d)).
Proof.
  intros b start st status run d Hs Hst. unfold chan_step.
  destruct (_ <? _)%nat; [exact Hs|]. destruct (0x80 <=? _); [left; reflexivity|].
  destruct (_ && _); [left; reflexivity|exact Hst].
Qed.

(* The running status stays none or a channel status. *)
Lemma msg_step_st_ok : forall b pos st, st_ok st -> st_ok (mr_st (msg_step b pos st)).
Proof.
  intros b pos st Hs. unfold msg_step.
  destruct (length b <=? pos)%nat; [exact Hs|].
  destruct (at8 b pos =? 0xf0); [destruct (find_f7 _); left; reflexivity|].
  destruct (Z.leb_spec 0xf0 (at8 b pos)) as [A|A]; [left; reflexivity|].
  destruct (Z.leb_spec 0x80 (at8 b pos)) as [B|B]; [apply chan_step_st_ok; [exact Hs|right; lia]|].
  destruct (Z.eqb_spec st 0); [exact Hs|].
  apply chan_step_st_ok; exact Hs.
Qed.

Lemma chan_step_status : forall b start st status run d,
  mr_kind (chan_step b start st status run d) = MkChan -> mr_status (chan_step b start st status run d) = status.
Proof.
  intros. unfold chan_step in *.
  destruct (_ <? _)%nat; [discriminate|]. destruct (0x80 <=? _); [discriminate|].
  destruct (_ && _); [discriminate|reflexivity].
Qed.

(* A step that answers 1 has the status F0 exactly when it read a sysex. *)
Lemma msg_step_code1_f0 : forall b pos st, st_ok st -> mr_code (msg_step b pos st) = 1 ->
  (mr_status (msg_step b pos st) = 0xf0 <-> mr_kind (msg_step b pos st) = MkSysex).
Proof.
  intros b pos st Hs. unfold msg_step.
  destruct (length b <=? pos)%nat; [cbn; discriminate|].
  destruct (at8 b pos =? 0xf0).
  { destruct (find_f7 _); cbn; [tauto|discriminate]. }
  destruct (Z.leb_spec 0xf0 (at8 b pos)) as [A|A]; [cbn; discriminate|].
  assert (G : forall start status run d, 0x80 <= status < 0xf0 ->
            mr_code (chan_step b start st status run d) = 1 ->
            (mr_status (chan_step b start st status run d) = 0xf0 <->
             mr_kind (chan_step b start st status run d) = MkSysex)).
  { intros start status run d Hr. unfold chan_step.
    destruct (_ <? _)%nat; [cbn; discriminate|]. destruct (0x80 <=? _); [cbn; discriminate|].
    destruct (_ && _); cbn; [discriminate|]. intros _. split; [lia|discriminate]. }
  destruct (Z.leb_spec 0x80 (at8 b pos)) as [B|B]; [apply G; lia|].
  destruct (Z.eqb_spec st 0) as [E|E]; [cbn; discriminate|].
  apply G. destruct Hs; lia.
Qed.

Lemma msg_step_sysex : forall b pos st, mr_kind (msg_step b pos st) = MkSysex ->
  at8 b pos = 0xf0 /\ mr_sysex (msg_step b pos st) = S pos /\
  (S pos + mr_sysex_len (msg_step b pos st) < length b)%nat /\
  mr_pos (msg_step b pos st) = (pos + mr_sysex_len (msg_step b pos st) + 2)%nat.
Proof.
  intros b pos st. unfold msg_step.
  destruct (Nat.leb_spec (length b) pos); [cbn; discriminate|].
  destruct (Z.eqb_spec (at8 b pos) 0xf0) as [E|E].
  - destruct (find_f7 (skipn (S pos) b)) as [j|] eqn:F; cbn; [|discriminate]. intros _.
    apply find_f7_some in F. rewrite length_skipn in F. repeat split; lia.
  - destruct (0xf0 <=? at8 b pos); [cbn; discriminate|].
    assert (G : forall start status run d, mr_kind (chan_step b start st status run d) <> MkSysex).
    { intros. unfold chan_step. destruct (_ <? _)%nat; [discriminate|].
      destruct (0x80 <=? _); [discriminate|]. destruct (_ && _); discriminate. }
    destruct (0x80 <=? at8 b pos); [intros Hk; exfalso; exact (G _ _ _ _ Hk)|].
    destruct (st =? 0); [cbn; discriminate|]. intros Hk; exfalso; exact (G _ _ _ _ Hk).
Qed.

(** * diginet_body_check (src/diginet_codec.c:47) *)

(* The test of src/diginet_codec.c:54-55: a whole sysex F0 13 xx 70 .. F7. *)
Definition refused (b : list byte) (r : msg_res) : bool :=
  match mr_kind r with
  | MkSysex => (3 <=? mr_sysex_len r)%nat && (at8 b (mr_sysex r) =? 0x13) &&
               (at8 b (mr_sysex r + 2) =? 0x70)
  | _ => false
  end.

(* The loop of src/diginet_codec.c:53-57 from the cursor (pos, st), with `fuel` steps at most:
   true when it finds a refused message. fuel = length b - pos is enough (bc_loop_fuel). *)
Fixpoint bc_loop (fuel : nat) (b : list byte) (pos : nat) (st : Z) : bool :=
  match fuel with
  | O => false
  | S f =>
      let r := msg_step b pos st in
      if is_end r then false
      else if refused b r then true
      else bc_loop f b (mr_pos r) (mr_st r)
  end.

(* diginet_body_check: -10 (REFUSED) when the cursor finds F0 13 xx 70 .. F7 or the prefix
   scan of src/diginet_codec.c:59-62 finds F0 13 xx 70, else 0. The prefix scan is
   system_at. *)
Definition body_check (b : list byte) : Z :=
  if bc_loop (length b) b 0 0 then -10
  else if system_at b then -10
  else 0.

Lemma bc_loop_end : forall f b pos st, (length b <= pos)%nat -> bc_loop f b pos st = false.
Proof.
  intros [|f] b pos st H; [reflexivity|]. cbn [bc_loop].
  rewrite is_end_msg_step. destruct (Nat.leb_spec (length b) pos); [reflexivity|lia].
Qed.

Lemma bc_loop_fuel : forall f g b pos st, (length b - pos <= f)%nat -> (length b - pos <= g)%nat ->
  bc_loop f b pos st = bc_loop g b pos st.
Proof.
  induction f as [|f IH]; intros g b pos st Hf Hg.
  - rewrite (bc_loop_end g) by lia. reflexivity.
  - destruct g as [|g].
    + rewrite (bc_loop_end (S f)) by lia. reflexivity.
    + cbn [bc_loop]. rewrite is_end_msg_step.
      destruct (Nat.leb_spec (length b) pos) as [L|L]; [reflexivity|].
      destruct (refused b (msg_step b pos st)); [reflexivity|].
      pose proof (msg_step_progress b pos st L). apply IH; lia.
Qed.

(* One turn of the loop, as the binary takes it. *)
Lemma bc_loop_step : forall f b pos st, (pos < length b)%nat -> (length b - pos <= f)%nat ->
  bc_loop f b pos st =
  if refused b (msg_step b pos st) then true
  else bc_loop (length b - mr_pos (msg_step b pos st)) b (mr_pos (msg_step b pos st))
         (mr_st (msg_step b pos st)).
Proof.
  intros f b pos st L Hf. destruct f as [|f]; [lia|]. cbn [bc_loop].
  rewrite is_end_msg_step. destruct (Nat.leb_spec (length b) pos); [lia|].
  destruct (refused b (msg_step b pos st)); [reflexivity|].
  pose proof (msg_step_progress b pos st L). apply bc_loop_fuel; lia.
Qed.

Lemma refused_hit : forall b pos st, refused b (msg_step b pos st) = true ->
  (pos + 3 < length b)%nat /\ sys_hit b pos = true.
Proof.
  intros b pos st H. unfold refused in H.
  destruct (mr_kind (msg_step b pos st)) eqn:K; try discriminate.
  destruct (msg_step_sysex b pos st K) as (E0 & Es & Hl & _).
  rewrite Es in H. rewrite !andb_true_iff, Nat.leb_le, !Z.eqb_eq in H.
  destruct H as [[H3 H13] H70]. split; [lia|].
  unfold sys_hit. rewrite E0, H13. replace (S (S (S pos))) with (S pos + 2)%nat by lia.
  rewrite H70. reflexivity.
Qed.

Lemma bc_loop_system_at : forall f b pos st, bc_loop f b pos st = true -> system_at b = true.
Proof.
  induction f as [|f IH]; intros b pos st H; cbn [bc_loop] in H; [discriminate|].
  destruct (is_end (msg_step b pos st)); [discriminate|].
  destruct (refused b (msg_step b pos st)) eqn:R.
  - apply refused_hit in R. apply system_at_true. exists pos. exact R.
  - eapply IH. exact H.
Qed.

(* A sysex the cursor finds starts with the prefix, so body_check is system_at. *)
Lemma body_check_spec : forall b, body_check b = if system_at b then -10 else 0.
Proof.
  intros b. unfold body_check.
  destruct (bc_loop (length b) b 0 0) eqn:E; [|reflexivity].
  rewrite (bc_loop_system_at _ _ _ _ E). reflexivity.
Qed.

Lemma body_check_refused : forall b, body_check b = -10 <-> system_at b = true.
Proof.
  intros b. rewrite body_check_spec. destruct (system_at b); split; intros; congruence.
Qed.

(** * diginet_frame_build (src/diginet_frame.c:93) as the library computes it *)

(* The code: E_LENGTH, then diginet_body_check, then E_SPACE (src/diginet_frame.c:102-109). *)
Definition lib_build_code (body : list byte) (cap : Z) : Z :=
  if 1484 <? Z.of_nat (length body) then -4
  else if negb (body_check body =? 0) then -10
  else if cap <? frame_len (length body) then -5
  else frame_len (length body).

(* The bytes it writes (src/diginet_frame.c:111-125): wr16 and wr32 of the uint16_t and
   uint32_t values, diginet_sum16 in the DIGINET_SUM_BODY mode (0) and 0 in the
   DIGINET_SUM_ZERO mode (1), the body, then out - len zero bytes. *)
Definition lib_frame (dst src : list byte) (send ack retry cmd ncmds : Z) (body : list byte)
    (mode : Z) : list byte :=
  dst ++ src ++ put16 0x885f ++ put16 ((16 + Z.of_nat (length body)) mod 2^16) ++
  put16 (if mode =? 0 then lib_sum16 body else 0) ++
  put32 (send mod 2^32) ++ put32 (ack mod 2^32) ++ put16 (retry mod 2^16) ++
  [b8 cmd; b8 ncmds] ++ body ++
  repeat (b8 0) (Z.to_nat (frame_len (length body) - (30 + Z.of_nat (length body)))).

Lemma lib_build_code_eq : forall body cap, lib_build_code body cap = build_code body cap.
Proof.
  intros body cap. unfold lib_build_code, build_code. rewrite body_check_spec.
  destruct (1484 <? _); [reflexivity|]. destruct (system_at body); reflexivity.
Qed.

(* The library's bytes are the frame spec_build_frame makes. *)
Lemma frame_build_bytes : forall dst src send ack retry cmd ncmds body mode,
  mode = 0 \/ mode = 1 ->
  lib_frame dst src send ack retry cmd ncmds body mode =
  build_frame dst src send ack retry cmd ncmds body (mode =? 1).
Proof.
  intros dst src send ack retry cmd ncmds body mode Hm. unfold lib_frame, build_frame.
  rewrite put16_mod, !put32_mod, put16_mod, lib_sum16_eq, spec_sum_eq.
  assert (Ez : Z.to_nat (frame_len (length body) - (30 + Z.of_nat (length body))) = (30 - length body)%nat)
    by (unfold frame_len; lia).
  rewrite Ez. destruct Hm as [-> | ->]; reflexivity.
Qed.

(* For a body of at most 1484 bytes that does not hold F0 13 xx 70, in a buffer of the frame's
   length or more, diginet_frame_build answers the frame length and writes build_frame. *)
Lemma frame_build_ok : forall dst src send ack retry cmd ncmds body mode cap,
  mode = 0 \/ mode = 1 -> (length body <= 1484)%nat -> system_at body = false ->
  frame_len (length body) <= cap ->
  lib_build_code body cap = frame_len (length body) /\
  lib_frame dst src send ack retry cmd ncmds body mode =
  build_frame dst src send ack retry cmd ncmds body (mode =? 1).
Proof.
  intros dst src send ack retry cmd ncmds body mode cap Hm Hl Hs Hc. split.
  - rewrite lib_build_code_eq. unfold build_code.
    destruct (Z.ltb_spec 1484 (Z.of_nat (length body))); [lia|]. rewrite Hs.
    destruct (Z.ltb_spec cap (frame_len (length body))); [lia|reflexivity].
  - apply frame_build_bytes. exact Hm.
Qed.

(* ---- the linking lemmas: the list byte reading (fuzz_frame's, above and in DgnSpec.v) against the
   list Z reading (diginet_msg_next, diginet_body_check, spec_system_at, spec_read_frame) ---- *)

(* b holds the bytes bb in its first length bb places; past them b may hold anything (in frame mode
   the body list runs on into the frame's padding). map bz bb is such a b (holds_body_map). *)
Definition holds_body (b : list Z) (bb : list byte) : Prop :=
  forall i, (i < length bb)%nat -> byte_at b (Z.of_nat i) = at8 bb i.

Lemma holds_body_map : forall bb, holds_body (map bz bb) bb.
Proof.
  intros bb i _. unfold byte_at, at8. rewrite Nat2Z.id.
  assert (E : bz (b8 0) = 0) by (apply bz_b8; lia).
  transitivity (nth i (map bz bb) (bz (b8 0))); [rewrite E; reflexivity | apply map_nth].
Qed.

(* The cursor c->len = length bb, c->pos = pos, c->status = st over the body bb: cursor_cells of
   fuzz_frame's contract lib/Prog/diginet_cursor_init_c.v without c->body (dgn_cursor has no field
   for the body pointer, and diginet_msg_next does not write it, nor c->len). *)
Definition cursor_of (bb : list byte) (pos : nat) (st : Z) : dgn_cursor :=
  {| dc_len := Z.of_nat (length bb); dc_pos := Z.of_nat pos; dc_status := st |}.

(* *m after the step r when it was m before: msg_cells of fuzz_frame's contract
   lib/Prog/diginet_msg_next_c.v, field by field. The end writes nothing. Every other step writes
   d1, d2, sysex (the payload offset mr_sysex for a sysex, 0 for NULL otherwise), sysex_len and
   offset (the old pos), and status, running and len when writes_status, writes_running and
   writes_len say so; a field it does not write keeps m's value. The 4 padding bytes after d2
   (msg_cells keeps them) have no dgn_msg field. *)
Definition msg_after (r : msg_res) (m : dgn_msg) : dgn_msg :=
  if is_end r then m
  else {| dm_status := if writes_status (mr_kind r) then mr_status r else dm_status m;
          dm_running := if writes_running (mr_kind r) then mr_running r else dm_running m;
          dm_d1 := mr_d1 r;
          dm_d2 := mr_d2 r;
          dm_sysex := if writes_sysex (mr_kind r) then Z.of_nat (mr_sysex r) else 0;
          dm_sysex_len := Z.of_nat (mr_sysex_len r);
          dm_offset := Z.of_nat (mr_start r);
          dm_len := if writes_len (mr_kind r) then Z.of_nat (mr_len r) else dm_len m |}.

Lemma lk_triple : forall (r r' : Z) (m m' : dgn_msg) (c c' : dgn_cursor),
  r = r' -> m = m' -> c = c' -> (r, m, c) = (r', m', c').
Proof. intros; subst; reflexivity. Qed.

Lemma lk_msg_ext : forall a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8,
  a1 = b1 -> a2 = b2 -> a3 = b3 -> a4 = b4 -> a5 = b5 -> a6 = b6 -> a7 = b7 -> a8 = b8 ->
  DgnMsg a1 a2 a3 a4 a5 a6 a7 a8 = DgnMsg b1 b2 b3 b4 b5 b6 b7 b8.
Proof. intros; subst; reflexivity. Qed.

Lemma lk_cursor_ext : forall a1 a2 a3 b1 b2 b3,
  a1 = b1 -> a2 = b2 -> a3 = b3 -> DgnCursor a1 a2 a3 = DgnCursor b1 b2 b3.
Proof. intros; subst; reflexivity. Qed.

(* a leaf of the case analyses below: the code, then each field of the message and the cursor *)
Local Ltac lk_fin :=
  unfold msg_after, cursor_of, mr_code, mr_plain;
  cbn [is_end mr_kind mr_start mr_pos mr_st mr_status mr_running mr_d1 mr_d2 mr_sysex mr_sysex_len
       mr_len writes_status writes_running writes_sysex writes_len negb andb orb Nat.eqb];
  apply lk_triple; [ | apply lk_msg_ext | apply lk_cursor_ext ]; try reflexivity; try lia.

(* b & 0x80 (diginet_msg.c:63, :89) on a byte is b < 0x80 *)
Lemma lk_high_bit : forall z, 0 <= z < 2^8 -> (Z.land z 0x80 =? 0) = (z <? 0x80).
Proof.
  intros z Hz. apply Bool.eqb_prop. revert z Hz.
  apply (byte_forall (fun z => Bool.eqb (Z.land z 0x80 =? 0) (z <? 0x80))). vm_compute. reflexivity.
Qed.

Lemma lk_channel_data_len : forall s, channel_data_len s = Z.of_nat (chan_n s).
Proof.
  intros s. unfold channel_data_len, chan_n; cbv beta zeta.
  replace (u8 (Z.land s 0xf0)) with (Z.land s 0xf0).
  - destruct ((Z.land s 0xf0 =? 0xc0) || (Z.land s 0xf0 =? 0xd0)); reflexivity.
  - unfold u8. change 256 with (2 ^ 8). rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc.
    reflexivity.
Qed.

Lemma lk_skipn_nth : forall (l : list byte) k, (k < length l)%nat ->
  skipn k l = nth k l (b8 0) :: skipn (S k) l.
Proof.
  induction l as [|x l IH]; intros [|k] H; cbn [length] in H; try lia; [reflexivity|].
  cbn [skipn nth]. apply IH. lia.
Qed.

(* the F7 scan of diginet_msg.c:44-46 from k is find_f7 on the bytes from k *)
Lemma lk_msg_scan_f7 : forall b bb, holds_body b bb ->
  forall fuel k, (k + fuel = length bb)%nat ->
  msg_scan_f7 b (Z.of_nat (length bb)) (Z.of_nat k) fuel =
  match find_f7 (skipn k bb) with Some j => Z.of_nat (k + j) | None => Z.of_nat (length bb) end.
Proof.
  intros b bb Hb fuel. induction fuel as [|f IH]; intros k Hk; cbn [msg_scan_f7].
  - rewrite skipn_all2 by lia. cbn [find_f7]. f_equal. lia.
  - rewrite (lk_skipn_nth bb k) by lia. cbn [find_f7].
    rewrite (Hb k) by lia. unfold at8.
    assert (C : (Z.of_nat k <? Z.of_nat (length bb)) = true) by (apply Z.ltb_lt; lia).
    rewrite C. cbn [andb].
    destruct (bz (nth k bb (b8 0)) =? 0xf7); cbn [negb].
    + f_equal. lia.
    + replace (Z.of_nat k + 1) with (Z.of_nat (S k)) by lia.
      rewrite IH by lia.
      destruct (find_f7 (skipn (S k) bb)); cbn [option_map]; [f_equal; lia | reflexivity].
Qed.

(* the channel-message tail, diginet_msg.c:83-102 against chan_step *)
Lemma lk_msg_channel : forall b bb m pos st status run d,
  holds_body b bb -> (pos < length bb)%nat -> (pos <= d)%nat ->
  msg_channel b (cursor_of bb pos st)
    {| dm_status := dm_status m; dm_running := dm_running m; dm_d1 := 0; dm_d2 := 0; dm_sysex := 0;
       dm_sysex_len := 0; dm_offset := Z.of_nat pos; dm_len := dm_len m |} status (Z.of_nat d) run =
  (mr_code (chan_step bb pos st status run d), msg_after (chan_step bb pos st status run d) m,
   cursor_of bb (mr_pos (chan_step bb pos st status run d)) (mr_st (chan_step bb pos st status run d))).
Proof.
  intros b bb m pos st status run d Hb Hp Hd.
  unfold msg_channel, chan_step; cbv beta zeta. rewrite lk_channel_data_len.
  change (dc_len (cursor_of bb pos st)) with (Z.of_nat (length bb)).
  change (dc_pos (cursor_of bb pos st)) with (Z.of_nat pos).
  change (dc_status (cursor_of bb pos st)) with st.
  cbn [dm_status dm_running dm_d1 dm_d2 dm_sysex dm_sysex_len dm_offset dm_len].
  destruct (Nat.ltb_spec (length bb) (d + chan_n status)) as [L|L].
  { assert (C : (Z.of_nat (length bb) <? Z.of_nat d + Z.of_nat (chan_n status)) = true)
      by (apply Z.ltb_lt; lia).
    rewrite C. lk_fin. }
  assert (C : (Z.of_nat (length bb) <? Z.of_nat d + Z.of_nat (chan_n status)) = false)
    by (apply Z.ltb_ge; lia).
  rewrite C, Nat2Z.id.
  destruct (chan_n_cases status) as [Hn|Hn]; rewrite Hn in *.
  - cbn [first_high]. rewrite Z.add_0_r, (Hb d) by lia.
    pose proof (at8_range bb d) as R.
    rewrite lk_high_bit by lia.
    destruct (Z.ltb_spec (at8 bb d) 0x80) as [A|A]; destruct (Z.leb_spec 0x80 (at8 bb d)) as [B|B];
      try lia; lk_fin.
  - cbn [first_high]. rewrite Z.add_0_r.
    replace (Z.of_nat d + (0 + 1)) with (Z.of_nat (S d)) by lia.
    replace (Z.of_nat d + 1) with (Z.of_nat (S d)) by lia.
    rewrite (Hb d), (Hb (S d)) by lia.
    change (1 <? Z.of_nat 2) with true.
    pose proof (at8_range bb d) as R. pose proof (at8_range bb (S d)) as R1.
    rewrite !lk_high_bit by lia.
    destruct (Z.ltb_spec (at8 bb d) 0x80) as [A|A]; destruct (Z.leb_spec 0x80 (at8 bb d)) as [B|B];
      try lia;
    destruct (Z.ltb_spec (at8 bb (S d)) 0x80) as [A1|A1];
      destruct (Z.leb_spec 0x80 (at8 bb (S d))) as [B1|B1]; try lia; lk_fin.
    unfold u8. apply Z.mod_small. lia.
Qed.

(* diginet_msg_next on the cursor (length bb, pos, st) over a list b that holds bb is the step
   msg_step bb pos st of fuzz_frame's model: the code is mr_code, the cursor after it is
   (length bb, mr_pos, mr_st), and the message after it is msg_after, which names each field of
   the message the step writes and keeps every other field of m. No hypothesis on pos or st. *)
Theorem diginet_msg_next_msg_step : forall b bb pos st m,
  holds_body b bb ->
  diginet_msg_next b (cursor_of bb pos st) m =
  (mr_code (msg_step bb pos st), msg_after (msg_step bb pos st) m,
   cursor_of bb (mr_pos (msg_step bb pos st)) (mr_st (msg_step bb pos st))).
Proof.
  intros b bb pos st m Hb.
  unfold diginet_msg_next, msg_step; cbv beta zeta.
  change (dc_len (cursor_of bb pos st)) with (Z.of_nat (length bb)).
  change (dc_pos (cursor_of bb pos st)) with (Z.of_nat pos).
  change (dc_status (cursor_of bb pos st)) with st.
  destruct (Nat.leb_spec (length bb) pos) as [E|E].
  { assert (C : (Z.of_nat (length bb) <=? Z.of_nat pos) = true) by (apply Z.leb_le; lia).
    rewrite C. reflexivity. }
  assert (C : (Z.of_nat (length bb) <=? Z.of_nat pos) = false) by (apply Z.leb_gt; lia).
  rewrite C, (Hb pos E).
  pose proof (at8_range bb pos) as R.
  replace (Z.of_nat pos + 1) with (Z.of_nat (S pos)) by lia.
  destruct (Z.eqb_spec (at8 bb pos) 0xf0) as [F0|F0].
  - replace (Z.to_nat (Z.of_nat (length bb) - Z.of_nat (S pos))) with (length bb - S pos)%nat by lia.
    rewrite (lk_msg_scan_f7 b bb Hb (length bb - S pos) (S pos)) by lia.
    destruct (find_f7 (skipn (S pos) bb)) as [j|] eqn:Fj.
    + apply find_f7_some in Fj. rewrite length_skipn in Fj.
      assert (C1 : (Z.of_nat (length bb) <=? Z.of_nat (S pos + j)) = false) by (apply Z.leb_gt; lia).
      rewrite C1. lk_fin.
    + assert (C1 : (Z.of_nat (length bb) <=? Z.of_nat (length bb)) = true) by (apply Z.leb_le; lia).
      rewrite C1. reflexivity.
  - rewrite lk_high_bit by lia.
    destruct (Z.leb_spec 0xf0 (at8 bb pos)) as [G|G];
      destruct (Z.ltb_spec (at8 bb pos) 0x80) as [H|H];
      destruct (Z.leb_spec 0x80 (at8 bb pos)) as [K|K]; try lia; cbn [negb].
    + lk_fin.
    + destruct (Z.eqb_spec st 0) as [S0|S0].
      * lk_fin.
      * exact (lk_msg_channel b bb m pos st st 1 pos Hb E (le_n pos)).
    + exact (lk_msg_channel b bb m pos st (at8 bb pos) 0 (S pos) Hb E ltac:(lia)).
Qed.

Lemma lk_code_end : forall r, (mr_code r =? 0) = is_end r.
Proof. intros [k ? ? ? ? ? ? ? ? ? ?]; destruct k; reflexivity. Qed.

(* the refusal test of diginet_codec.c:54-55 on the step's message is refused *)
Lemma lk_refused : forall b bb pos st m, holds_body b bb -> st_ok st ->
  (mr_code (msg_step bb pos st) =? 1) && (dm_status (msg_after (msg_step bb pos st) m) =? 0xf0) &&
  (3 <=? dm_sysex_len (msg_after (msg_step bb pos st) m)) &&
  (byte_at b (dm_sysex (msg_after (msg_step bb pos st) m)) =? DIGINET_SYSEX_MAKER) &&
  (byte_at b (dm_sysex (msg_after (msg_step bb pos st) m) + 2) =? DIGINET_FN_SYSTEM) =
  refused bb (msg_step bb pos st).
Proof.
  intros b bb pos st m Hb Hs.
  pose proof (msg_step_code1_f0 bb pos st Hs) as Hf0.
  pose proof (msg_step_sysex bb pos st) as Hsx.
  revert Hf0 Hsx. unfold refused, msg_after.
  destruct (msg_step bb pos st) as [k start p st' status run d1 d2 sx sxl len].
  cbn [mr_kind mr_code mr_status mr_sysex mr_sysex_len is_end].
  intros Hf0 Hsx.
  destruct k; cbn [mr_kind mr_code mr_status mr_sysex mr_sysex_len is_end writes_status writes_sysex
                   dm_status dm_sysex dm_sysex_len] in *; try reflexivity.
  - destruct (Hsx eq_refl) as (_ & Esx & Hl & _). subst sx.
    assert (Est : status = 0xf0) by (apply (proj2 (Hf0 eq_refl)); reflexivity). subst status.
    rewrite !Z.eqb_refl. cbn [andb].
    destruct (Nat.leb_spec 3 sxl) as [L3|L3].
    + assert (C : (3 <=? Z.of_nat sxl) = true) by (apply Z.leb_le; lia). rewrite C.
      rewrite (Hb (S pos)) by lia.
      replace (Z.of_nat (S pos) + 2) with (Z.of_nat (S pos + 2)) by lia.
      rewrite (Hb (S pos + 2)%nat) by lia. reflexivity.
    + assert (C : (3 <=? Z.of_nat sxl) = false) by (apply Z.leb_gt; lia). rewrite C. reflexivity.
  - assert (C : (status =? 0xf0) = false).
    { apply Z.eqb_neq. intros E. apply (proj1 (Hf0 eq_refl)) in E. discriminate E. }
    rewrite C. reflexivity.
Qed.

Lemma lk_body_check_loop : forall f g b bb pos st m, holds_body b bb -> st_ok st ->
  (pos <= length bb)%nat -> (length bb - pos < f)%nat -> (length bb - pos <= g)%nat ->
  body_check_loop b (cursor_of bb pos st) m f = Some (bc_loop g bb pos st).
Proof.
  induction f as [|f IH]; intros g b bb pos st m Hb Hs Hp Hf Hg; [lia|].
  cbn [body_check_loop]. rewrite (diginet_msg_next_msg_step b bb pos st m Hb). cbv beta iota.
  rewrite lk_code_end, is_end_msg_step.
  destruct (Nat.leb_spec (length bb) pos) as [E|E].
  - rewrite bc_loop_end by lia. reflexivity.
  - rewrite (lk_refused b bb pos st m Hb Hs).
    destruct g as [|g]; [lia|]. cbn [bc_loop]. rewrite is_end_msg_step.
    destruct (Nat.leb_spec (length bb) pos) as [E'|_]; [lia|].
    destruct (refused bb (msg_step bb pos st)); [reflexivity|].
    pose proof (msg_step_progress bb pos st E) as P.
    apply IH; [exact Hb | apply msg_step_st_ok, Hs | lia | lia | lia].
Qed.

(* the prefix scan of diginet_codec.c:59-62 from k *)
Lemma lk_prefix_scan : forall b bb, holds_body b bb ->
  forall fuel k, (length bb - 3 - k <= fuel)%nat ->
  system_prefix_scan b (Z.of_nat (length bb)) (Z.of_nat k) fuel =
  existsb (sys_hit bb) (seq k (length bb - 3 - k)).
Proof.
  intros b bb Hb fuel. induction fuel as [|f IH]; intros k Hk; cbn [system_prefix_scan].
  - replace (length bb - 3 - k)%nat with 0%nat by lia. reflexivity.
  - destruct (Z.ltb_spec (Z.of_nat k + 3) (Z.of_nat (length bb))) as [L|L].
    + replace (length bb - 3 - k)%nat with (S (length bb - 3 - S k)) by lia.
      cbn [seq existsb].
      replace (Z.of_nat k + 1) with (Z.of_nat (S k)) by lia.
      replace (Z.of_nat k + 3) with (Z.of_nat (S (S (S k)))) by lia.
      rewrite (Hb k), (Hb (S k)), (Hb (S (S (S k)))) by lia.
      change (sys_hit bb k) with
        ((at8 bb k =? 0xf0) && (at8 bb (S k) =? 0x13) && (at8 bb (S (S (S k))) =? 0x70)).
      unfold DIGINET_SYSEX_MAKER, DIGINET_FN_SYSTEM.
      destruct ((at8 bb k =? 0xf0) && (at8 bb (S k) =? 0x13) && (at8 bb (S (S (S k))) =? 0x70));
        [reflexivity|].
      cbn [orb]. apply IH. lia.
    + replace (length bb - 3 - k)%nat with 0%nat by lia. reflexivity.
Qed.

Lemma lk_prefix_scan_system_at : forall b bb, holds_body b bb ->
  system_prefix_scan b (Z.of_nat (length bb)) 0 (length bb) = system_at bb.
Proof.
  intros b bb Hb. unfold system_at. replace (length bb - 3)%nat with (length bb - 3 - 0)%nat by lia.
  exact (lk_prefix_scan b bb Hb (length bb) 0 ltac:(lia)).
Qed.

(* diginet_body_check (b, length bb) over a list b that holds bb is fuzz_frame's body_check bb:
   the same cursor loop, step for step, then the same prefix scan *)
Theorem diginet_body_check_body_check : forall b bb, holds_body b bb ->
  diginet_body_check b (Z.of_nat (length bb)) = body_check bb.
Proof.
  intros b bb Hb. unfold diginet_body_check, body_check.
  change (diginet_cursor_init (Z.of_nat (length bb))) with (cursor_of bb 0 0).
  rewrite (lk_body_check_loop (S (Z.to_nat (Z.of_nat (length bb)))) (length bb) b bb 0 0 dgn_msg_zero Hb
             (or_introl eq_refl)) by lia.
  rewrite Nat2Z.id, (lk_prefix_scan_system_at b bb Hb).
  destruct (bc_loop (length bb) bb 0 0); reflexivity.
Qed.

(* spec_system_at's loop (spec.h:264-270) from k *)
Lemma lk_system_at_loop : forall b bb, holds_body b bb ->
  forall fuel k, (length bb - 3 - k <= fuel)%nat ->
  (system_at_loop b (Z.of_nat (length bb)) (Z.of_nat k) fuel = -1 /\
   forall i, (k <= i)%nat -> (i + 3 < length bb)%nat -> sys_hit bb i = false) \/
  (exists i, system_at_loop b (Z.of_nat (length bb)) (Z.of_nat k) fuel = Z.of_nat i /\ (k <= i)%nat /\
     (i + 3 < length bb)%nat /\ sys_hit bb i = true /\ forall j, (k <= j < i)%nat -> sys_hit bb j = false).
Proof.
  intros b bb Hb fuel. induction fuel as [|f IH]; intros k Hk; cbn [system_at_loop].
  - left. split; [reflexivity|]. intros i Hi1 Hi2. lia.
  - destruct (Z.ltb_spec (Z.of_nat k + 3) (Z.of_nat (length bb))) as [L|L].
    + replace (Z.of_nat k + 1) with (Z.of_nat (S k)) by lia.
      replace (Z.of_nat k + 3) with (Z.of_nat (S (S (S k)))) by lia.
      rewrite (Hb k), (Hb (S k)), (Hb (S (S (S k)))) by lia.
      unfold SPEC_MAKER, SPEC_FN_SYSTEM.
      destruct ((at8 bb k =? 240) && (at8 bb (S k) =? 19) && (at8 bb (S (S (S k))) =? 112)) eqn:Hk3.
      * right. exists k. split; [reflexivity|]. split; [lia|]. split; [lia|].
        split; [exact Hk3|]. intros j Hj. lia.
      * assert (Nk : sys_hit bb k = false) by exact Hk3.
        destruct (IH (S k) ltac:(lia)) as [[E1 E2] | (i & E1 & E2 & E3 & E4 & E5)].
        -- left. split; [exact E1|]. intros i Hi1 Hi2.
           destruct (Nat.eq_dec i k) as [->|Ne]; [exact Nk|]. apply E2; lia.
        -- right. exists i. split; [exact E1|]. split; [lia|]. split; [exact E3|]. split; [exact E4|].
           intros j Hj. destruct (Nat.eq_dec j k) as [->|Ne]; [exact Nk|]. apply E5; lia.
    + left. split; [reflexivity|]. intros i Hi1 Hi2. lia.
Qed.

(* spec_system_at (b, length bb) over a list b that holds bb: -1 when system_at bb is false, else
   the first i of system_at bb, the least i with i + 3 < length bb and F0 13 xx 70 at i *)
Theorem spec_system_at_first : forall b bb, holds_body b bb ->
  (spec_system_at b (Z.of_nat (length bb)) = -1 /\ system_at bb = false) \/
  (exists i, spec_system_at b (Z.of_nat (length bb)) = Z.of_nat i /\ system_at bb = true /\
     (i + 3 < length bb)%nat /\ sys_hit bb i = true /\ forall k, (k < i)%nat -> sys_hit bb k = false).
Proof.
  intros b bb Hb. unfold spec_system_at. rewrite Nat2Z.id.
  destruct (lk_system_at_loop b bb Hb (length bb) 0 ltac:(lia)) as [[E1 E2] | (i & E1 & E2 & E3 & E4 & E5)].
  - left. split; [exact E1|]. apply system_at_false. intros i Hi. apply E2; lia.
  - right. exists i. split; [exact E1|]. split; [apply system_at_true; exists i; split; assumption|].
    split; [exact E3|]. split; [exact E4|]. intros k Hk. apply E5. lia.
Qed.

(* the refusal test of the harnesses, 0 <= spec_system_at, is system_at *)
Corollary spec_system_at_system_at : forall b bb, holds_body b bb ->
  (0 <=? spec_system_at b (Z.of_nat (length bb))) = system_at bb.
Proof.
  intros b bb Hb.
  destruct (spec_system_at_first b bb Hb) as [[E1 E2] | (i & E1 & E2 & _)]; rewrite E1, E2.
  - reflexivity.
  - apply Z.leb_le. lia.
Qed.

Lemma lk_lor_mul_pow2 : forall x y k, 0 <= k -> 0 <= y < 2 ^ k -> Z.lor (x * 2 ^ k) y = x * 2 ^ k + y.
Proof.
  intros x y k Hk Hy.
  assert (D : Z.land (x * 2 ^ k) y = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases n k) as [L|L].
    - rewrite <- Z.shiftl_mul_pow2 by lia. rewrite Z.shiftl_spec_low by lia. reflexivity.
    - rewrite <- (Z.mod_small y (2 ^ k)) by lia. rewrite Z.mod_pow2_bits_high by lia.
      apply andb_false_r. }
  rewrite <- Z.lxor_lor by exact D. rewrite Z.add_nocarry_lxor by exact D. reflexivity.
Qed.

Lemma lk_be16 : forall b bb i, holds_body b bb -> (S i < length bb)%nat ->
  spec_be16 b (Z.of_nat i) = be16 bb i.
Proof.
  intros b bb i Hb Hi. unfold spec_be16, be16.
  replace (Z.of_nat i + 1) with (Z.of_nat (S i)) by lia.
  rewrite (Hb i), (Hb (S i)) by lia.
  pose proof (at8_range bb i). pose proof (at8_range bb (S i)).
  rewrite Z.shiftl_mul_pow2 by lia. rewrite lk_lor_mul_pow2 by lia.
  unfold u16. apply Z.mod_small. lia.
Qed.

Lemma lk_be32 : forall b bb i, holds_body b bb -> (S (S (S i)) < length bb)%nat ->
  spec_be32 b (Z.of_nat i) = be32 bb i.
Proof.
  intros b bb i Hb Hi. unfold spec_be32, be32.
  replace (Z.of_nat i + 1) with (Z.of_nat (S i)) by lia.
  replace (Z.of_nat i + 2) with (Z.of_nat (S (S i))) by lia.
  replace (Z.of_nat i + 3) with (Z.of_nat (S (S (S i)))) by lia.
  rewrite (Hb i), (Hb (S i)), (Hb (S (S i))), (Hb (S (S (S i)))) by lia.
  pose proof (at8_range bb i). pose proof (at8_range bb (S i)).
  pose proof (at8_range bb (S (S i))). pose proof (at8_range bb (S (S (S i)))).
  rewrite !Z.shiftl_mul_pow2 by lia. unfold u32. rewrite !Z.mod_small by lia.
  rewrite (lk_lor_mul_pow2 (at8 bb (S (S i))) (at8 bb (S (S (S i)))) 8) by lia.
  rewrite (lk_lor_mul_pow2 (at8 bb (S i)) (at8 bb (S (S i)) * 2 ^ 8 + at8 bb (S (S (S i)))) 16) by lia.
  rewrite (lk_lor_mul_pow2 (at8 bb i)
             (at8 bb (S i) * 2 ^ 16 + (at8 bb (S (S i)) * 2 ^ 8 + at8 bb (S (S (S i))))) 24) by lia.
  lia.
Qed.

(* spec_sum's loop (spec.h:174-180) over the bytes from p + k *)
Lemma lk_sum_loop : forall b bb, holds_body b bb ->
  forall fuel s p k, 0 <= s < 2 ^ 16 -> (p + k + fuel <= length bb)%nat ->
  spec_sum_loop b (Z.of_nat p) s (Z.of_nat k) fuel =
  (s + sum_bytes (firstn fuel (skipn (p + k) bb))) mod 2 ^ 16.
Proof.
  intros b bb Hb fuel. induction fuel as [|f IH]; intros s p k Hs Hk; cbn [spec_sum_loop].
  - cbn [firstn sum_bytes]. rewrite Z.add_0_r. symmetry. apply Z.mod_small. exact Hs.
  - rewrite (lk_skipn_nth bb (p + k)) by lia. cbn [firstn sum_bytes].
    rewrite <- Nat2Z.inj_add, (Hb (p + k)%nat) by lia.
    replace (Z.of_nat k + 1) with (Z.of_nat (S k)) by lia.
    change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
    rewrite IH.
    + replace (p + S k)%nat with (S (p + k)) by lia.
      unfold at8. rewrite Zplus_mod_idemp_l. f_equal. lia.
    + apply Z.mod_pos_bound. lia.
    + lia.
Qed.

(* spec_read_frame (b, length bb) over a list b that holds bb is fuzz_frame's frame parse: the same
   code, and on code 0 the same fields, the body at offset 30 with fr_body_len bytes *)
Theorem spec_read_frame_fr : forall b bb, holds_body b bb ->
  sf_code (spec_read_frame b (Z.of_nat (length bb))) = fr_code bb /\
  (fr_code bb = 0 ->
   let w := spec_read_frame b (Z.of_nat (length bb)) in
   sf_dst w = 0 /\ sf_src w = 6 /\ sf_ethertype w = fr_ethertype bb /\ sf_numbytes w = fr_numbytes bb /\
   sf_sum w = fr_sum bb /\ sf_send w = fr_send bb /\ sf_ack w = fr_ack bb /\ sf_retry w = fr_retry bb /\
   sf_cmd w = fr_cmd bb /\ sf_ncmds w = fr_ncmds bb /\ sf_body w = 30 /\ sf_body_len w = fr_body_len bb /\
   sf_pad_len w = fr_pad_len bb /\ sf_body_sum w = fr_body_sum bb).
Proof.
  intros b bb Hb.
  destruct (Nat.ltb_spec (length bb) 30) as [S30|S30].
  { assert (C : fr_code bb = -2) by (unfold fr_code; destruct (Nat.ltb_spec (length bb) 30); [reflexivity | lia]).
    rewrite C. split; [|intros E; discriminate E].
    unfold spec_read_frame, SPEC_BODY_AT; cbv beta zeta.
    assert (C1 : (Z.of_nat (length bb) <? 30) = true) by (apply Z.ltb_lt; lia).
    rewrite C1. reflexivity. }
  assert (E12 : spec_be16 b 12 = fr_ethertype bb) by exact (lk_be16 b bb 12 Hb ltac:(lia)).
  assert (E14 : spec_be16 b SPEC_AT_NUMBYTES = fr_numbytes bb) by exact (lk_be16 b bb 14 Hb ltac:(lia)).
  unfold spec_read_frame, fr_code; cbv beta zeta.
  rewrite E12, E14.
  unfold SPEC_BODY_AT, SPEC_ETHERTYPE, SPEC_HDR, SPEC_ETH_HDR, SPEC_OK, SPEC_E_SHORT, SPEC_E_ETHERTYPE,
    SPEC_E_LENGTH.
  assert (C1 : (Z.of_nat (length bb) <? 30) = false) by (apply Z.ltb_ge; lia).
  assert (C2 : (length bb <? 30)%nat = false) by (apply Nat.ltb_ge; lia).
  rewrite C1, C2.
  destruct (Z.eqb_spec (fr_ethertype bb) 34911) as [Et|Et]; cbn [negb];
    [| split; [reflexivity | intros E; discriminate E]].
  destruct ((fr_numbytes bb <? 16) || (Z.of_nat (length bb) - 14 <? fr_numbytes bb)) eqn:Nb;
    cbn [negb orb]; [split; [reflexivity | intros E; discriminate E]|].
  split; [reflexivity|]. intros _.
  apply orb_false_iff in Nb. destruct Nb as [N1 N2]. apply Z.ltb_ge in N1, N2.
  cbn [negb orb sf_dst sf_src sf_ethertype sf_numbytes sf_sum sf_retry sf_send sf_ack sf_cmd sf_ncmds
       sf_body sf_body_len sf_pad_len sf_body_sum].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact (lk_be16 b bb 16 Hb ltac:(lia))|].
  split; [exact (lk_be32 b bb 18 Hb ltac:(lia))|].
  split; [exact (lk_be32 b bb 22 Hb ltac:(lia))|].
  split; [exact (lk_be16 b bb 26 Hb ltac:(lia))|].
  split; [exact (Hb 28%nat ltac:(lia))|].
  split; [exact (Hb 29%nat ltac:(lia))|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  unfold spec_sum_at, fr_body_sum, sum16, fr_body, fr_body_len, u16.
  change (spec_sum_loop b 30 0 0) with (spec_sum_loop b (Z.of_nat 30) 0 (Z.of_nat 0)).
  rewrite (lk_sum_loop b bb Hb (Z.to_nat (fr_numbytes bb - 16)) 0 30 0) by lia.
  rewrite Z.add_0_l. change 65536 with (2 ^ 16). apply Zmod_mod.
Qed.

(* the body of an accepted frame, from offset 30 of b with fr_body_len bytes, holds fr_body *)
Lemma holds_body_fr_body : forall b bb, holds_body b bb -> fr_code bb = 0 ->
  holds_body (skipn 30 b) (fr_body bb) /\ Z.of_nat (length (fr_body bb)) = fr_body_len bb.
Proof.
  intros b bb Hb Hc. destruct (fr_code_ok bb Hc) as (H1 & _ & H3 & H4). split.
  - intros i Hi. rewrite length_fr_body in Hi by exact Hc.
    transitivity (byte_at b (Z.of_nat (30 + i))).
    + unfold byte_at. rewrite !Nat2Z.id, nth_skipn. reflexivity.
    + unfold fr_body_len in Hi. rewrite (Hb (30 + i)%nat) by lia.
      unfold fr_body. rewrite at8_firstn by (unfold fr_body_len; lia). rewrite at8_skipn. reflexivity.
  - rewrite length_fr_body by exact Hc. unfold fr_body_len. lia.
Qed.

(* ---- src/diginet_codec.c's encoders and text helpers, folded from fuzz_codec's model (names kept;
   desk, c24, pc, cmd, KEY and E_ARG .. E_RANGE are in DgnSpec.v, u8 is DgnSpec.v's, and bit and upd
   are bit_or_0 and upd_at here, since the kit's Reusable/YO0i.v and Lib/Arr.v name a bit and an upd
   of their own). This part writes each C conversion as fuzz_codec's model does (u8, s32, mod 256,
   mod 2 ^ 16, mod 2 ^ 32), and each function names the C it follows. ---- *)

(** The library's view of fuzz_codec: the encoders and helpers of src/diginet_codec.c as functions over
    the integers, with C's unsigned conversions written out (char is unsigned on this target). Each
    function names the C it follows. A command is (bytes, key, display): bytes[0..len) of struct
    diginet_cmd, its key and its display flag. An encoder's result is (rc, Some cmd) on success and
    (rc, None) on failure, when the C leaves the command as it was. *)

(** b ? v : 0 *)
Definition bit_or_0 (b : bool) (v : Z) : Z := if b then v else 0.
(** (int) of an unsigned in [0, 2^32) *)
Definition s32 (c : Z) : Z := if c <? 2 ^ 31 then c else c - 2 ^ 32.

(** diginet_sysex_encode (diginet_codec.c:66-91); device and fn are uint8_t, pl the len payload bytes. *)
Definition sysex_spec (device fn : Z) (pl : list Z) : Z * option cmd :=
  if 0x7f <? device then (E_ARG, None)
  else if fn =? 0x70 then (E_REFUSED, None)
  else if 0x7f <? fn then (E_RANGE, None)
  else if 24 <? Z.of_nat (length pl) + 5 then (E_SPACE, None)
  else if existsb (fun x => Z.testbit x 7) pl then (E_RANGE, None)
  else (0, Some ([0xf0; 0x13; device; fn] ++ pl ++ [0xf7], 0, bit_or_0 ((fn =? 0x40) || (fn =? 0x30)) 1)).

(** The key an encoder writes after a successful sysex_encode. *)
Definition with_key (r : Z * option cmd) (k : Z) : Z * option cmd :=
  match r with
  | (0, Some (bs, _, dp)) => (0, Some (bs, k, dp))
  | x => x
  end.

(** diginet_fader_encode (diginet_codec.c:95-111) *)
Definition fader_spec (p : option desk) (strip value : Z) : Z * option cmd :=
  match p with
  | None => (E_ARG, None)
  | Some d =>
    if (d_strips d <=? strip) || (1023 <? value) then (E_RANGE, None)
    else (0, Some ([0xb0; u8 strip; u8 (value / 8); u8 (0x20 + strip); u8 ((value mod 8) * 16)],
                   KEY 1 strip, 0))
  end.

(** diginet_button_encode (diginet_codec.c:113-122); on is the int argument. *)
Definition button_spec (button id on : Z) : Z * option cmd :=
  if (0x7f <? button) || (0x3f <? id) then (E_RANGE, None)
  else (0, Some ([0x90; u8 button; u8 (Z.lor (bit_or_0 (negb (on =? 0)) 0x40) id)],
                 KEY 2 (Z.lor ((button * 256) mod 2 ^ 32) id), 0)).

(** diginet_touch_encode (diginet_codec.c:124-134) *)
Definition touch_spec (p : option desk) (strip on : Z) : Z * option cmd :=
  match p with
  | None => (E_ARG, None)
  | Some d =>
    if d_strips d <=? strip then (E_RANGE, None) else with_key (button_spec 9 strip on) (KEY 8 0)
  end.

(** diginet_vpot_encode with delta_byte (diginet_codec.c:136-154) *)
Definition vpot_spec (p : option desk) (strip delta : Z) : Z * option cmd :=
  match p with
  | None => (E_ARG, None)
  | Some d =>
    if (d_strips d <=? strip) || (delta <? -64) || (63 <? delta) then (E_RANGE, None)
    else (0, Some ([0xb0; u8 (Z.lor 0x40 strip); u8 (delta + 64)], KEY 8 0, 0))
  end.

(** diginet_jog_encode (diginet_codec.c:156-165) *)
Definition jog_spec (delta : Z) : Z * option cmd :=
  if (delta <? -64) || (63 <? delta) then (E_RANGE, None)
  else (0, Some ([0xb0; 0x5c; u8 (delta + 64)], KEY 8 0, 0)).

(** The loop of diginet_ring_encode (diginet_codec.c:186-191): bit 1 + k of the mask sets bit 6 - k of
    b1, bit 8 + k sets bit 6 - k of b2, k = 0..6. *)
Definition ring_bits (mask : Z) : Z * Z :=
  fold_left (fun '(b1, b2) k =>
               (Z.lor b1 (bit_or_0 (Z.testbit mask (1 + k)) (2 ^ (6 - k))),
                Z.lor b2 (bit_or_0 (Z.testbit mask (8 + k)) (2 ^ (6 - k)))))
            (map Z.of_nat (seq 0 7)) (0, 0).

(** diginet_ring_encode (diginet_codec.c:179-198); mask is the uint16_t argument. *)
Definition ring_spec (p : option desk) (strip mask : Z) : Z * option cmd :=
  match p with
  | None => (E_ARG, None)
  | Some d =>
    if (d_strips d <=? strip) || negb (Z.shiftr mask 15 =? 0) then (E_RANGE, None)
    else
      let '(b1, b2) := ring_bits mask in
      with_key (sysex_spec (d_dev d) 0x00 [u8 (Z.lor strip (bit_or_0 (Z.testbit mask 0) 0x40)); b1; b2])
               (KEY 3 strip)
  end.

(** diginet_ring_dot and diginet_ring_fill (diginet_codec.c:169-177); n is the unsigned argument. *)
Definition ring_dot_spec (n : Z) : Z := if n <? 15 then (2 ^ n) mod 2 ^ 16 else 0.
Definition ring_fill_spec (n : Z) : Z := if n <=? 15 then (2 ^ n - 1) mod 2 ^ 16 else 0.

(** diginet_meter_mask (diginet_codec.c:202-207); s is the unsigned argument. *)
Definition meter_mask_spec (s : Z) : Z := (2 ^ (Z.min s 14) - 1) mod 2 ^ 16.

(** The loop of diginet_meter_segments (diginet_codec.c:211-213): n counts up from n while n < 14 and
    bit n of the mask is set; k is the iterations left. *)
Fixpoint meter_run (mask : Z) (n k : nat) : nat :=
  match k with
  | O => n
  | S k' => if Z.testbit mask (Z.of_nat n) then meter_run mask (S n) k' else n
  end.

(** diginet_meter_segments (diginet_codec.c:209-215); mask is the uint16_t argument. *)
Definition meter_segments_spec (mask : Z) : Z :=
  let n := Z.of_nat (meter_run mask 0 14) in if Z.shiftr mask n =? 0 then n else -1.

(** diginet_meter_encode (diginet_codec.c:217-231); right is the int argument. *)
Definition meter_spec (p : option desk) (channel right segments : Z) : Z * option cmd :=
  match p with
  | None => (E_ARG, None)
  | Some d =>
    if (0x20 <=? channel) || (14 <? segments) then (E_RANGE, None)
    else
      let m := meter_mask_spec segments in
      let ch := u8 (Z.lor channel (bit_or_0 (negb (right =? 0)) 0x20)) in
      with_key (sysex_spec (d_dev d) 0x10 [ch; u8 (Z.shiftr m 7); u8 (Z.land m 0x7f)]) (KEY 4 ch)
  end.

(** leds_encode (diginet_codec.c:235-245) *)
Definition leds_spec (d : desk) (addr bits : Z) : Z * option cmd :=
  if 0x7f <? bits then (E_RANGE, None)
  else with_key (sysex_spec (d_dev d) 0x20 [u8 addr; u8 bits]) (KEY 5 addr).

(** diginet_strip_leds_encode, diginet_counter_leds_encode (diginet_codec.c:247-263) *)
Definition strip_leds_spec (p : option desk) (strip bits : Z) : Z * option cmd :=
  match p with
  | None => (E_ARG, None)
  | Some d => if d_strips d <=? strip then (E_RANGE, None) else leds_spec d strip bits
  end.
Definition counter_leds_spec (p : option desk) (bits : Z) : Z * option cmd :=
  match p with
  | None => (E_ARG, None)
  | Some d => leds_spec d (d_counter d) bits
  end.

(** diginet_scribble_encode (diginet_codec.c:287-303); chars is the memory chars points at. *)
Definition scribble_spec (p : option desk) (addr : Z) (chars : list Z) : Z * option cmd :=
  match p with
  | None => (E_ARG, None)
  | Some d =>
    if 0x7f <? addr then (E_RANGE, None)
    else with_key (sysex_spec (d_dev d) 0x40 ([u8 addr; 0] ++ firstn (Z.to_nat (d_chars d)) chars))
                  (KEY 7 addr)
  end.

(** diginet_counter_encode (diginet_codec.c:371-386); seg is the memory seg points at, dots the
    uint8_t argument. *)
Definition counter_spec (p : option desk) (seg : list Z) (dots : Z) : Z * option cmd :=
  match p with
  | None => (E_ARG, None)
  | Some d =>
    with_key (sysex_spec (d_dev d) 0x30 ([d_counter d; dots] ++ rev (firstn 8 seg))) (KEY 6 (d_counter d))
  end.

(** The library call of run() (fuzz_codec.c:531-548) for a call record: kind, the personality, the
    fields a, b, c (unsigned), delta (int), bytes (the 24 bytes of the record) and n. *)
Definition enc_of_call (kind : Z) (p : option desk) (a b c delta : Z) (bytes : list Z) (n : Z)
  : Z * option cmd :=
  if kind =? 0 then fader_spec p a b
  else if kind =? 1 then button_spec a b (s32 c)
  else if kind =? 2 then touch_spec p a (s32 c)
  else if kind =? 3 then vpot_spec p a delta
  else if kind =? 4 then jog_spec delta
  else if kind =? 5 then ring_spec p a (b mod 2 ^ 16)
  else if kind =? 6 then meter_spec p a (s32 c) b
  else if kind =? 7 then strip_leds_spec p a b
  else if kind =? 8 then counter_leds_spec p b
  else if kind =? 9 then scribble_spec p a bytes
  else if kind =? 10 then counter_spec p bytes (b mod 256)
  else sysex_spec (a mod 256) (b mod 256) (firstn (Z.to_nat n) bytes).

(** ---- the text helpers ---- *)

(** A C string held in memory is a list of byte values read from its start; the string ends at its
    first 0 or at the end of the list, so the bytes after the terminator are never read. *)

(** diginet_scribble_text (diginet_codec.c:267-285): t the text from its current byte, k the output
    slots left. The result is the output bytes (k of them) and the text bytes used. *)
Fixpoint scr_lib (t : list Z) (k : nat) : list Z * Z :=
  match k with
  | O => ([], 0)
  | S k' =>
    match t with
    | [] => (repeat 0x20 k, 0)
    | x :: t' =>
      if x =? 0 then (repeat 0x20 k, 0)
      else
        match t' with
        | y :: t'' =>
          if (x =? 0x2e) && (0x31 <=? y) && (y <=? 0x39)
          then let '(o, u) := scr_lib t'' k' in ((y - 26) :: o, u + 2)
          else let '(o, u) := scr_lib t' k' in ((if x <? 0x80 then x else 0x3f) :: o, u + 1)
        | [] => let '(o, u) := scr_lib t' k' in ((if x <? 0x80 then x else 0x3f) :: o, u + 1)
        end
    end
  end.
Definition scribble_text_spec (t : list Z) (n : Z) : list Z * Z := scr_lib t (Z.to_nat n).

(** diginet_seg7 (diginet_codec.c:308-335) as the compiled switch reads it: a table of 91 words for the
    characters 0x20..0x7a, -1 outside it. c is the unsigned char. *)
Definition seg7_table : list Z :=
  [0; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; 1; -1; -1;
   126; 48; 109; 121; 51; 91; 95; 112; 127; 123; -1; -1; -1; -1; -1; -1;
   -1; 119; 31; 78; 61; 79; 71; -1; 55; -1; 60; -1; 14; -1; -1; 29; 103; -1; 5; 91; -1; 62; -1; -1; -1; 59;
   109; -1; -1; -1; -1; -1; -1;
   119; 31; 78; 61; 79; 71; -1; 23; -1; 60; -1; 14; -1; -1; 29; 103; -1; 5; 91; -1; 62; -1; -1; -1; 59;
   109].
Definition seg7_spec (c : Z) : Z :=
  let i := (c - 0x20) mod 256 in if i <=? 90 then nth (Z.to_nat i) seg7_table (-1) else -1.

(** l with l[i] := v *)
Definition upd_at (l : list Z) (i v : Z) : list Z :=
  firstn (Z.to_nat i) l ++ v :: skipn (S (Z.to_nat i)) l.

(** The first loop of diginet_counter_text (diginet_codec.c:344-356): n digits placed, s their patterns
    (length n), dot the 8 flags. None is the E_RANGE return of the loop. *)
Fixpoint ct1_lib (t : list Z) (n : Z) (s dot : list Z) : option (Z * list Z * list Z) :=
  match t with
  | [] => Some (n, s, dot)
  | ch :: t' =>
    if ch =? 0 then Some (n, s, dot)
    else if (ch =? 0x2e) && (0 <? n) && (nth (Z.to_nat (n - 1)) dot 0 =? 0)
    then ct1_lib t' n s (upd_at dot (n - 1) 1)
    else
      let v := seg7_spec (if ch =? 0x2e then 0x20 else ch) in
      if (v <? 0) || (n =? 8) then None
      else ct1_lib t' (n + 1) (s ++ [v]) (if ch =? 0x2e then upd_at dot n 1 else dot)
  end.

(** The second loop of diginet_counter_text (diginet_codec.c:357-366), which the harness's
    owed_counter_text (fuzz_codec.c:418-428) also runs: digit i (from 0, k digits left) takes
    s[i - (8 - n)] or 0; a dot on digit 7 is E_RANGE, a dot on digit i < 7 sets bit i. seg is the
    digits so far, d the dots so far. The result is (rc, the 8 digits, the dots); on E_RANGE all 8
    digits have been computed and d holds the dots of digits 0..6. *)
Fixpoint ct2_go (n : Z) (s dot : list Z) (i : Z) (k : nat) (seg : list Z) (d : Z) : Z * list Z * Z :=
  match k with
  | O => (0, seg, d)
  | S k' =>
    let from := i - (8 - n) in
    let v := if from <? 0 then 0 else nth (Z.to_nat from) s 0 in
    if (0 <=? from) && negb (nth (Z.to_nat from) dot 0 =? 0) then
      if i =? 7 then (E_RANGE, seg ++ [v], d)
      else ct2_go n s dot (i + 1) k' (seg ++ [v]) (Z.lor d (2 ^ i))
    else ct2_go n s dot (i + 1) k' (seg ++ [v]) d
  end.
Definition ct2 (n : Z) (s dot : list Z) : Z * list Z * Z := ct2_go n s dot 0 8 [] 0.

(** diginet_counter_text (diginet_codec.c:337-369): (rc, seg, dots). *)
Definition counter_text_spec (t : list Z) : Z * list Z * Z :=
  match ct1_lib t 0 [] (repeat 0 8) with
  | None => (E_RANGE, [], 0)
  | Some (n, s, dot) => ct2 n s dot
  end.

(* ---- fuzz_codec's model against this file's: the desks and the meter count ---- *)

(* the desk of a personalities entry (struct diginet_personality, diginet_codec.h:31-38) *)
Definition desk_of_personality (p : dgn_personality) : desk :=
  {| d_dev := dp_device p; d_strips := dp_strips p; d_chars := dp_scribble_chars p;
     d_counter := dp_counter_addr p |}.

(* personalities[] (diginet_codec.c:12-15) are spec.h's SPEC_C24 and SPEC_PC *)
Lemma personalities_desks : map desk_of_personality personalities = [c24; pc].
Proof. reflexivity. Qed.

(* the personality pointer diginet_personality_of (desk) gives (diginet_codec.c:27-33), as fuzz_codec's
   model's [option desk] *)
Lemma personality_desk : forall dsk,
  option_map desk_of_personality
    (match diginet_personality_of dsk with Some i => personality_at i | None => None end) =
  if dsk =? DIGINET_DESK_CONTROL24 then Some c24
  else if dsk =? DIGINET_DESK_PROCONTROL then Some pc else None.
Proof.
  intros dsk. unfold diginet_personality_of, personalities. cbn [personality_find dp_desk].
  rewrite (Z.eqb_sym DIGINET_DESK_CONTROL24 dsk), (Z.eqb_sym DIGINET_DESK_PROCONTROL dsk).
  destruct (dsk =? DIGINET_DESK_CONTROL24); [reflexivity|].
  destruct (dsk =? DIGINET_DESK_PROCONTROL); reflexivity.
Qed.

(* mask & (1u << n) (diginet_codec.c:212) is bit n of mask *)
Lemma lk_land_pow2 : forall a n, 0 <= n -> (Z.land a (Z.shiftl 1 n) =? 0) = negb (Z.testbit a n).
Proof.
  intros a n Hn. rewrite Z.shiftl_1_l.
  destruct (Z.testbit a n) eqn:T; cbn [negb].
  - apply Z.eqb_neq. intros E.
    assert (B : Z.testbit (Z.land a (2 ^ n)) n = false) by (rewrite E; apply Z.bits_0).
    rewrite Z.land_spec, T, Z.pow2_bits_true in B by lia. discriminate B.
  - apply Z.eqb_eq. apply Z.bits_inj'. intros m Hm.
    rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
    destruct (Z.eqb_spec n m) as [<-|_]; [rewrite T; reflexivity | apply andb_false_r].
Qed.

Lemma lk_meter_run : forall mask k n, (n + k = 14)%nat ->
  meter_count mask (Z.of_nat n) k = Z.of_nat (meter_run mask n k).
Proof.
  intros mask k. induction k as [|k IH]; intros n Hn; cbn [meter_count meter_run]; [reflexivity|].
  assert (C : (Z.of_nat n <? DIGINET_METER_SEGMENTS) = true)
    by (unfold DIGINET_METER_SEGMENTS; apply Z.ltb_lt; lia).
  rewrite C, lk_land_pow2 by lia. cbn [andb]. rewrite Bool.negb_involutive.
  destruct (Z.testbit mask (Z.of_nat n)); [|reflexivity].
  replace (Z.of_nat n + 1) with (Z.of_nat (S n)) by lia. apply IH. lia.
Qed.

(* fuzz_codec's meter_segments_spec is diginet_meter_segments, for every mask *)
Theorem meter_segments_spec_eq : forall mask, meter_segments_spec mask = diginet_meter_segments mask.
Proof.
  intros mask. unfold meter_segments_spec, diginet_meter_segments; cbv zeta.
  change (meter_count mask 0 14) with (meter_count mask (Z.of_nat 0) 14).
  rewrite (lk_meter_run mask 14 0) by lia.
  destruct (Z.shiftr mask (Z.of_nat (meter_run mask 0 14)) =? 0); reflexivity.
Qed.

(* ---- examples: the corpus seeds (fuzz/gen-corpus.c, tests/golden/frames.txt), worked by hand from the C ---- *)

Definition body_keepalive : list Z := [0x00].
Definition body_button_mute : list Z := [0x90; 0x08; 0x40].
Definition body_running_status : list Z :=
  [0x90; 0x08; 0x40; 0x07; 0x41; 0xb0; 0x01; 0x7f; 0x21; 0x70; 0x40; 0x41; 0x5c; 0x3f].
Definition body_sysex_no_f7 : list Z := [0xf0; 0x13; 0x01; 0x40; 0x00].
Definition body_status_f1 : list Z := [0xf1; 0x90; 0x08; 0x40; 0xff].
Definition body_status_for_data : list Z := [0x90; 0x90; 0x40].
Definition body_status_for_second_data : list Z := [0x90; 0x08; 0xc0; 0x05].
Definition body_no_status : list Z := [0x07; 0x41; 0x90; 0x08; 0x40].
Definition body_one_data_byte : list Z := [0xc0; 0x05; 0xd0; 0x7f; 0x10].
Definition body_status_cancelled : list Z :=
  [0x90; 0x08; 0x40; 0xf0; 0x13; 0x01; 0x20; 0x01; 0x40; 0xf7; 0x08; 0x40].
Definition body_scribble_write : list Z := [0xf0; 0x13; 0x01; 0x40; 0x00; 0x00; 0x4f; 0x4d; 0x58; 0x31; 0xf7].
Definition body_fader_move : list Z := [0xb0; 0x00; 0x40; 0x20; 0x00].
Definition body_fader_msb_only : list Z := [0xb0; 0x03; 0x40; 0x90; 0x08; 0x40].
Definition body_meter_right : list Z := [0xf0; 0x13; 0x00; 0x10; 0x23; 0x7f; 0x7f; 0xf7].
Definition body_meter_not_thermometer : list Z := [0xf0; 0x13; 0x01; 0x10; 0x00; 0x00; 0x05; 0xf7].
Definition body_counter_write : list Z :=
  [0xf0; 0x13; 0x01; 0x30; 0x19; 0x40; 0x5b; 0x6d; 0x30; 0x00; 0x00; 0x00; 0x00; 0x00; 0xf7].
Definition body_ring : list Z := [0xf0; 0x13; 0x01; 0x00; 0x45; 0x7f; 0x40; 0xf7].
Definition body_strip_leds : list Z := [0xf0; 0x13; 0x01; 0x20; 0x02; 0x44; 0xf7].
Definition body_jog_vpot : list Z := [0xb0; 0x5c; 0x41; 0xb0; 0x45; 0x3f; 0x58; 0x10].
Definition body_touch : list Z := [0x90; 0x09; 0x45].
Definition body_zone_key : list Z := [0x90; 0x05; 0x58; 0x90; 0x05; 0x1d].
Definition body_system_whole : list Z := [0xf0; 0x13; 0x01; 0x70; 0x00; 0xf7].
Definition body_system_cut_short : list Z := [0xf0; 0x13; 0x01; 0x70].
Definition body_system_in_sysex : list Z := [0xf0; 0x01; 0xf0; 0x13; 0x01; 0x70; 0xf7].
Definition body_system_after_message : list Z := [0x90; 0x08; 0x40; 0xf0; 0x13; 0x00; 0x70; 0x01; 0x02].
Definition body_system_other_maker : list Z := [0xf0; 0x12; 0x01; 0x70; 0xf7].

Definition cur (len pos status : Z) : dgn_cursor := {| dc_len := len; dc_pos := pos; dc_status := status |}.
Definition z9 : list Z := repeat 0 9.
Definition z8 : list Z := repeat 0 8.
(* a message whose every field is 0x55, to show the fields a refusal leaves *)
Definition msg55 : dgn_msg := DgnMsg 0x55 0x55 0x55 0x55 0x55 0x55 0x55 0x55.

(* keepalive: the data byte 00 with no running status is refused, the cursor steps past it; then the end *)
Example dl_keepalive_no_status :
  diginet_msg_next body_keepalive (diginet_cursor_init 1) dgn_msg_zero =
  (DIGINET_E_NO_STATUS, DgnMsg 0 0 0 0 0 0 0 0, cur 1 1 0) := eq_refl.
Example dl_keepalive_end :
  diginet_msg_next body_keepalive (cur 1 1 0) msg55 = (0, msg55, cur 1 1 0) := eq_refl.

(* button_mute: 90 08 40, two data bytes, running status 90 afterwards *)
Example dl_button_mute_msg :
  diginet_msg_next body_button_mute (diginet_cursor_init 3) dgn_msg_zero =
  (1, DgnMsg 0x90 0 0x08 0x40 0 0 0 3, cur 3 3 0x90) := eq_refl.

(* running_status: the second message 07 41 takes the status 90 in force, running = 1 *)
Example dl_running_status_msg :
  diginet_msg_next body_running_status (cur 14 3 0x90) dgn_msg_zero =
  (1, DgnMsg 0x90 1 0x07 0x41 0 0 3 2, cur 14 5 0x90) := eq_refl.

(* sysex-no-f7: no F7, truncated, cursor at the end, running status cancelled; status, running, len untouched *)
Example dl_sysex_no_f7 :
  diginet_msg_next body_sysex_no_f7 (diginet_cursor_init 5) msg55 =
  (DIGINET_E_TRUNCATED, DgnMsg 0x55 0x55 0 0 0 0 0 0x55, cur 5 5 0) := eq_refl.

(* status-f1: F1 refused, the cursor steps past it; the last byte FF too *)
Example dl_status_f1_first :
  diginet_msg_next body_status_f1 (diginet_cursor_init 5) dgn_msg_zero =
  (DIGINET_E_STATUS, DgnMsg 0 0 0 0 0 0 0 0, cur 5 1 0) := eq_refl.
Example dl_status_f1_last :
  diginet_msg_next body_status_f1 (cur 5 4 0x90) msg55 =
  (DIGINET_E_STATUS, DgnMsg 0x55 0x55 0 0 0 0 4 0x55, cur 5 5 0) := eq_refl.

(* status-for-data: the status byte 90 where the first data byte is due; the cursor stops at it *)
Example dl_status_for_data :
  diginet_msg_next body_status_for_data (diginet_cursor_init 3) dgn_msg_zero =
  (DIGINET_E_TRUNCATED, DgnMsg 0 0 0 0 0 0 0 0, cur 3 1 0) := eq_refl.

(* status-for-second-data: C0 where the second data byte is due; running is written (0), status and len are not *)
Example dl_status_for_second_data :
  diginet_msg_next body_status_for_second_data (diginet_cursor_init 4) msg55 =
  (DIGINET_E_TRUNCATED, DgnMsg 0x55 0 0 0 0 0 0 0x55, cur 4 2 0) := eq_refl.

(* a running-status message cut short by the end keeps the running status in force (diginet_msg.c:84-87) *)
Example dl_running_cut_by_end :
  diginet_msg_next [0x90; 0x08; 0x40; 0x08] (cur 4 3 0x90) msg55 =
  (DIGINET_E_TRUNCATED, DgnMsg 0x55 1 0 0 0 0 3 0x55, cur 4 4 0x90) := eq_refl.

(* no-status *)
Example dl_no_status :
  diginet_msg_next body_no_status (diginet_cursor_init 5) dgn_msg_zero =
  (DIGINET_E_NO_STATUS, DgnMsg 0 0 0 0 0 0 0 0, cur 5 1 0) := eq_refl.

(* one-data-byte: C0 and D0 take one data byte, d2 = 0; the last 10 runs on status D0 *)
Example dl_one_data_byte_c0 :
  diginet_msg_next body_one_data_byte (diginet_cursor_init 5) dgn_msg_zero =
  (1, DgnMsg 0xc0 0 0x05 0 0 0 0 2, cur 5 2 0xc0) := eq_refl.
Example dl_one_data_byte_running :
  diginet_msg_next body_one_data_byte (cur 5 4 0xd0) dgn_msg_zero =
  (1, DgnMsg 0xd0 1 0x10 0 0 0 4 1, cur 5 5 0xd0) := eq_refl.

(* status-cancelled: the sysex F0 .. F7 at 3 (payload 4..8) cancels the running status, then 08 is refused *)
Example dl_status_cancelled_sysex :
  diginet_msg_next body_status_cancelled (cur 12 3 0x90) dgn_msg_zero =
  (1, DgnMsg 0xf0 0 0 0 4 5 3 7, cur 12 10 0) := eq_refl.
Example dl_status_cancelled_refusal :
  diginet_msg_next body_status_cancelled (cur 12 10 0) dgn_msg_zero =
  (DIGINET_E_NO_STATUS, DgnMsg 0 0 0 0 0 0 10 0, cur 12 11 0) := eq_refl.

(* scribble_write: the payload 13 01 40 00 00 "OMX1" at 1, 9 bytes *)
Example dl_scribble_write_msg :
  diginet_msg_next body_scribble_write (diginet_cursor_init 11) dgn_msg_zero =
  (1, DgnMsg 0xf0 0 0 0 1 9 0 11, cur 11 11 0) := eq_refl.

Example dl_scribble_write_event :
  diginet_decoder_next body_scribble_write (diginet_decoder_init None 11) dgn_event_zero =
  (1, DgnEvent DIGINET_EV_SCRIBBLE 0 0 0 0 0 0 0 0 0 0 0 4 [0x4f; 0x4d; 0x58; 0x31; 0; 0; 0; 0; 0] z8 0 1
        (DgnMsg 0xf0 0 0 0 1 9 0 11),
   {| dd_c := cur 11 11 0; dd_p := Some 0 |}) := eq_refl.

(* fader_move: B0 00 40, then 20 00 on running status B0 is its LSB: position 0x40 << 3 = 512, the cursor
   moves past the LSB *)
Example dl_fader_move :
  diginet_decoder_next body_fader_move (diginet_decoder_init (Some 0) 5) dgn_event_zero =
  (1, DgnEvent DIGINET_EV_FADER 0 0 0 0 0 0 0 512 0 0 0 0 z9 z8 0 0 (DgnMsg 0xb0 0 0 0x40 0 0 0 3),
   {| dd_c := cur 5 5 0xb0; dd_p := Some 0 |}) := eq_refl.

(* fader-msb-only: the next message is 90 08 40, not B0 23: lsb_missing, the cursor stays after the MSB *)
Example dl_fader_msb_only :
  diginet_decoder_next body_fader_msb_only (diginet_decoder_init None 6) dgn_event_zero =
  (1, DgnEvent DIGINET_EV_FADER 3 0 0 0 0 0 1 512 0 0 0 0 z9 z8 0 0 (DgnMsg 0xb0 0 3 0x40 0 0 0 3),
   {| dd_c := cur 6 3 0xb0; dd_p := Some 0 |}) := eq_refl.

(* running_status: B0 01 7F then 21 70: position 0x7f << 3 | (0x70 >> 4 & 7) = 1016 | 7 = 1023 *)
Example dl_running_status_fader :
  diginet_decoder_next body_running_status {| dd_c := cur 14 5 0x90; dd_p := Some 0 |} dgn_event_zero =
  (1, DgnEvent DIGINET_EV_FADER 1 0 0 0 0 0 0 1023 0 0 0 0 z9 z8 0 0 (DgnMsg 0xb0 0 1 0x7f 0 0 5 3),
   {| dd_c := cur 14 10 0xb0; dd_p := Some 0 |}) := eq_refl.

(* running_status: 40 41 on B0 is V-Pot 0, delta +1; 5C 3F is the jog, delta -1 *)
Example dl_running_status_vpot :
  diginet_decoder_next body_running_status {| dd_c := cur 14 10 0xb0; dd_p := Some 0 |} dgn_event_zero =
  (1, DgnEvent DIGINET_EV_VPOT 0 0 0 0 0 0 0 0 1 0 0 0 z9 z8 0 0 (DgnMsg 0xb0 1 0x40 0x41 0 0 10 2),
   {| dd_c := cur 14 12 0xb0; dd_p := Some 0 |}) := eq_refl.
Example dl_running_status_jog :
  diginet_decoder_next body_running_status {| dd_c := cur 14 12 0xb0; dd_p := Some 0 |} dgn_event_zero =
  (1, DgnEvent DIGINET_EV_JOG 0 0 0 0 0 0 0 0 (-1) 0 0 0 z9 z8 0 0 (DgnMsg 0xb0 1 0x5c 0x3f 0 0 12 2),
   {| dd_c := cur 14 14 0xb0; dd_p := Some 0 |}) := eq_refl.

(* jog-vpot: B0 5C 41 jog +1; B0 45 3F V-Pot 5, -1; 58 10 on B0 is no control: OTHER *)
Example dl_jog_vpot_jog :
  diginet_decoder_next body_jog_vpot (diginet_decoder_init (Some 1) 8) dgn_event_zero =
  (1, DgnEvent DIGINET_EV_JOG 0 0 0 0 0 0 0 0 1 0 0 0 z9 z8 0 0 (DgnMsg 0xb0 0 0x5c 0x41 0 0 0 3),
   {| dd_c := cur 8 3 0xb0; dd_p := Some 1 |}) := eq_refl.
Example dl_jog_vpot_vpot :
  diginet_decoder_next body_jog_vpot {| dd_c := cur 8 3 0xb0; dd_p := Some 1 |} dgn_event_zero =
  (1, DgnEvent DIGINET_EV_VPOT 5 0 0 0 0 0 0 0 (-1) 0 0 0 z9 z8 0 0 (DgnMsg 0xb0 0 0x45 0x3f 0 0 3 3),
   {| dd_c := cur 8 6 0xb0; dd_p := Some 1 |}) := eq_refl.
Example dl_jog_vpot_other :
  diginet_decoder_next body_jog_vpot {| dd_c := cur 8 6 0xb0; dd_p := Some 1 |} dgn_event_zero =
  (1, DgnEvent DIGINET_EV_OTHER 0 0 0 0 0 0 0 0 0 0 0 0 z9 z8 0 0 (DgnMsg 0xb0 1 0x58 0x10 0 0 6 2),
   {| dd_c := cur 8 8 0xb0; dd_p := Some 1 |}) := eq_refl.

(* button_mute: strip 0, button MUTE (08), on *)
Example dl_button_mute_event :
  diginet_decoder_next body_button_mute (diginet_decoder_init (Some 0) 3) dgn_event_zero =
  (1, DgnEvent DIGINET_EV_STRIP_BUTTON 0 0x08 0 1 0 0 0 0 0 0 0 0 z9 z8 0 0 (DgnMsg 0x90 0 0x08 0x40 0 0 0 3),
   {| dd_c := cur 3 3 0x90; dd_p := Some 0 |}) := eq_refl.

(* touch: 90 09 45, strip 5 touched *)
Example dl_touch :
  diginet_decoder_next body_touch (diginet_decoder_init None 3) dgn_event_zero =
  (1, DgnEvent DIGINET_EV_TOUCH 5 0x09 0 1 0 0 0 0 0 0 0 0 z9 z8 0 0 (DgnMsg 0x90 0 0x09 0x45 0 0 0 3),
   {| dd_c := cur 3 3 0x90; dd_p := Some 0 |}) := eq_refl.

(* zone-key: 90 05 58, zone 18 on, button 05 *)
Example dl_zone_key :
  diginet_decoder_next body_zone_key (diginet_decoder_init None 6) dgn_event_zero =
  (1, DgnEvent DIGINET_EV_SECTION_BUTTON 0 0x05 0x18 1 0 0 0 0 0 0 0 0 z9 z8 0 0 (DgnMsg 0x90 0 0x05 0x58 0 0 0 3),
   {| dd_c := cur 6 3 0x90; dd_p := Some 0 |}) := eq_refl.

(* meter-right: F0 13 00 10 23 7F 7F F7, channel 3 right, mask 0x3fff, 14 segments, device 00 *)
Example dl_meter_right :
  diginet_decoder_next body_meter_right (diginet_decoder_init (Some 1) 8) dgn_event_zero =
  (1, DgnEvent DIGINET_EV_METER 3 0 0 0 1 0x23 0 0 0 0x3fff 14 0 z9 z8 0 0 (DgnMsg 0xf0 0 0 0 1 6 0 8),
   {| dd_c := cur 8 8 0; dd_p := Some 1 |}) := eq_refl.

(* meter-not-thermometer: mask 5 is no thermometer, segments -1 *)
Example dl_meter_not_thermometer :
  diginet_decoder_next body_meter_not_thermometer (diginet_decoder_init None 8) dgn_event_zero =
  (1, DgnEvent DIGINET_EV_METER 0 0 0 0 0 0 0 0 0 5 (-1) 0 z9 z8 0 1 (DgnMsg 0xf0 0 0 0 1 6 0 8),
   {| dd_c := cur 8 8 0; dd_p := Some 0 |}) := eq_refl.

(* counter_write: address 19, dots 40, the wire's 5B 6D 30 00.. reversed into display order *)
Example dl_counter_write :
  diginet_decoder_next body_counter_write (diginet_decoder_init None 15) dgn_event_zero =
  (1, DgnEvent DIGINET_EV_COUNTER 0 0 0 0 0 0x19 0 0 0 0 0 0 z9 [0; 0; 0; 0; 0; 0x30; 0x6d; 0x5b] 0x40 1
        (DgnMsg 0xf0 0 0 0 1 13 0 15),
   {| dd_c := cur 15 15 0; dd_p := Some 0 |}) := eq_refl.

(* ring: F0 13 01 00 45 7F 40 F7, strip 5, LEDs 1..9 (mask 0x1ff) *)
Example dl_ring :
  diginet_decoder_next body_ring (diginet_decoder_init (Some 0) 8) dgn_event_zero =
  (1, DgnEvent DIGINET_EV_RING 5 0 0 0 0 0 0 0 0 0x1ff 0 0 z9 z8 0 1 (DgnMsg 0xf0 0 0 0 1 6 0 8),
   {| dd_c := cur 8 8 0; dd_p := Some 0 |}) := eq_refl.

(* strip-leds: F0 13 01 20 02 44 F7, strip 2, bits WRITE | READ *)
Example dl_strip_leds :
  diginet_decoder_next body_strip_leds (diginet_decoder_init (Some 0) 7) dgn_event_zero =
  (1, DgnEvent DIGINET_EV_STRIP_LEDS 2 0 0 0 0 2 0 0 0 0x44 0 0 z9 z8 0 1 (DgnMsg 0xf0 0 0 0 1 5 0 7),
   {| dd_c := cur 7 7 0; dd_p := Some 0 |}) := eq_refl.

(* system-whole: SYSTEM, device 01 *)
Example dl_system_whole_event :
  diginet_decoder_next body_system_whole (diginet_decoder_init None 6) dgn_event_zero =
  (1, DgnEvent DIGINET_EV_SYSTEM 0 0 0 0 0 0 0 0 0 0 0 0 z9 z8 0 1 (DgnMsg 0xf0 0 0 0 1 4 0 6),
   {| dd_c := cur 6 6 0; dd_p := Some 0 |}) := eq_refl.

(* a refusal leaves the event as it was, and still moves the cursor *)
Example dl_decoder_refusal_keeps_event :
  diginet_decoder_next body_keepalive (diginet_decoder_init None 1)
    (de_set_kind 99 dgn_event_zero) =
  (DIGINET_E_NO_STATUS, de_set_kind 99 dgn_event_zero, {| dd_c := cur 1 1 0; dd_p := Some 0 |}) := eq_refl.

(* the refusal: F0 13 xx 70 whole, cut short, inside another sysex, after a message; not of another maker *)
Example dl_body_check_system_whole : diginet_body_check body_system_whole 6 = DIGINET_E_REFUSED := eq_refl.
Example dl_body_check_system_cut_short : diginet_body_check body_system_cut_short 4 = DIGINET_E_REFUSED := eq_refl.
Example dl_body_check_system_in_sysex : diginet_body_check body_system_in_sysex 7 = DIGINET_E_REFUSED := eq_refl.
Example dl_body_check_system_after_message :
  diginet_body_check body_system_after_message 9 = DIGINET_E_REFUSED := eq_refl.
Example dl_body_check_other_maker : diginet_body_check body_system_other_maker 5 = DIGINET_OK := eq_refl.
Example dl_body_check_running_status : diginet_body_check body_running_status 14 = DIGINET_OK := eq_refl.
Example dl_body_check_empty : diginet_body_check [] 0 = DIGINET_OK := eq_refl.

(* diginet_meter_segments: 0 -> 0; 0x3ff -> 10; 0x3fff -> 14; 0x7fff -> -1 (bit 14 above the count); 4 -> -1 *)
Example dl_meter_segments :
  map diginet_meter_segments [0; 0x3ff; 0x3fff; 0x7fff; 4] = [0; 10; 14; -1; -1] := eq_refl.

(* the personalities: UNKNOWN and 3 are NULL; the decoder's default is Control|24 *)
Example dl_personality_of :
  map diginet_personality_of [DIGINET_DESK_UNKNOWN; DIGINET_DESK_CONTROL24; DIGINET_DESK_PROCONTROL; 3] =
  [None; Some 0; Some 1; None] := eq_refl.
Example dl_personality_procontrol :
  option_map dp_device (personality_at 1) = Some 0x00 /\ option_map dp_strips (personality_at 1) = Some 8 :=
  conj eq_refl eq_refl.
Example dl_decoder_init_default :
  diginet_decoder_init (diginet_personality_of DIGINET_DESK_UNKNOWN) 3 =
  {| dd_c := cur 3 0 0; dd_p := Some 0 |} := eq_refl.

(* channel_data_len: C0..DF one, the rest two *)
Example dl_channel_data_len :
  map channel_data_len [0x80; 0x9f; 0xb0; 0xc0; 0xcf; 0xd5; 0xe0] = [2; 2; 2; 1; 1; 1; 2] := eq_refl.

(* ---- facts about msg_step that the walk of diginet_body_check (src/diginet_codec.c:47-64) uses: the code of a step
   from its kind, the fields of a whole sysex, and the status of a channel message (from fuzz_frame's
   lib/Spec/DgnLibBodyCheck.v, names kept) ---- *)

(* At the end of the body a step answers 0. *)
Lemma bcs_code_end : forall b pos st, (length b <= pos)%nat -> mr_code (msg_step b pos st) = 0.
Proof.
  intros b pos st H. unfold msg_step.
  destruct (Nat.leb_spec (length b) pos); [reflexivity | lia].
Qed.

(* Before the end of the body a step is not the end. *)
Lemma bcs_code_nz : forall b pos st, (pos < length b)%nat -> mr_kind (msg_step b pos st) <> MkEnd.
Proof.
  intros b pos st H E. pose proof (is_end_msg_step b pos st) as I. unfold is_end in I.
  rewrite E in I. revert I.
  destruct (Nat.leb_spec (length b) pos) as [L|L]; [intros _; lia | cbn; discriminate].
Qed.

Lemma bcs_code_cases : forall r, mr_kind r <> MkEnd ->
  mr_code r = 1 \/ mr_code r = -6 \/ mr_code r = -7 \/ mr_code r = -8.
Proof.
  intros r H. unfold mr_code. destruct (mr_kind r); cbn; try congruence; lia.
Qed.

(* The code of a step is the code of its kind. *)
Lemma bcs_code_lit : forall r k, mr_kind r = k -> mr_code r = mr_code (mr_plain k O O 0 0).
Proof. intros r k E. unfold mr_code. rewrite E. reflexivity. Qed.

(* A whole sysex F0 .. F7 from pos: its fields. *)
Lemma bcs_sysex : forall b pos st, mr_kind (msg_step b pos st) = MkSysex ->
  exists j, msg_step b pos st = MsgRes MkSysex pos (pos + j + 2) 0 0xf0 0 0 0 (S pos) j (j + 2) /\
            (S pos + j < length b)%nat /\ at8 b pos = 0xf0.
Proof.
  intros b pos st. unfold msg_step.
  destruct (Nat.leb_spec (length b) pos); [cbn; discriminate|].
  destruct (Z.eqb_spec (at8 b pos) 0xf0) as [E|E].
  - destruct (find_f7 (skipn (S pos) b)) as [j|] eqn:F; cbn; [|discriminate]. intros _.
    apply find_f7_some in F. rewrite length_skipn in F.
    exists j. split; [reflexivity|]. split; [lia | exact E].
  - destruct (0xf0 <=? at8 b pos); [cbn; discriminate|].
    assert (G : forall start status run d, mr_kind (chan_step b start st status run d) <> MkSysex).
    { intros. unfold chan_step. destruct (_ <? _)%nat; [discriminate|].
      destruct (0x80 <=? _); [discriminate|]. destruct (_ && _); discriminate. }
    destruct (0x80 <=? at8 b pos); [intros Hk; exfalso; exact (G _ _ _ _ Hk)|].
    destruct (st =? 0); [cbn; discriminate|]. intros Hk; exfalso; exact (G _ _ _ _ Hk).
Qed.

(* A channel message has a status 80..EF. *)
Lemma bcs_chan_status : forall b pos st, st_ok st -> mr_kind (msg_step b pos st) = MkChan ->
  0x80 <= mr_status (msg_step b pos st) < 0xf0.
Proof.
  intros b pos st Hs. unfold msg_step.
  destruct (length b <=? pos)%nat; [cbn; discriminate|].
  destruct (at8 b pos =? 0xf0).
  { destruct (find_f7 _); cbn; discriminate. }
  destruct (Z.leb_spec 0xf0 (at8 b pos)) as [A|A]; [cbn; discriminate|].
  assert (G : forall start status run d, 0x80 <= status < 0xf0 ->
            mr_kind (chan_step b start st status run d) = MkChan ->
            0x80 <= mr_status (chan_step b start st status run d) < 0xf0).
  { intros start status run d Hr Hk. rewrite (chan_step_status b start st status run d Hk). exact Hr. }
  destruct (Z.leb_spec 0x80 (at8 b pos)) as [B|B]; [apply G; lia|].
  destruct (Z.eqb_spec st 0) as [E|E]; [cbn; discriminate|].
  apply G. destruct Hs; lia.
Qed.
