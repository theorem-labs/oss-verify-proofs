(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode. The harness side of the unit, over the shared model (DgnSpec.v):
   fuzz/fuzz_decode.c's owed_at, its five check_ functions (as booleans that are true exactly when
   the C function returns without abort()), the input set-up and the two loops of
   LLVMFuzzerTestOneInput, over the library's step functions as arguments (DgnLib.v models them).
   Conventions as in DgnSpec.v. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec.
Import ListNotations.
Open Scope Z_scope.

Definition FUZZ_INPUT_MAX : Z := 2 ^ 26.          (* fuzz.h:23, (size_t)64 << 20 *)

(* ---- what the decoder owes, fuzz_decode.c:117-150 ---- *)

(* struct owed, fuzz_decode.c:119-125. ow_lsb_missing: int; ow_next: size_t; ow_status_out:
   uint8_t. *)
Record owed := Owed {
  ow_m : spec_msg; ow_e : spec_event; ow_lsb_missing : Z; ow_next : Z; ow_status_out : Z }.

Definition se_with_value (e : spec_event) (v : Z) : spec_event :=
  {| se_kind := se_kind e; se_strip := se_strip e; se_button := se_button e; se_zone := se_zone e;
     se_on := se_on e; se_right := se_right e; se_addr := se_addr e; se_device := se_device e;
     se_len := se_len e; se_dots := se_dots e; se_value := v; se_mask := se_mask e;
     se_delta := se_delta e; se_segments := se_segments e; se_text := se_text e;
     se_seg := se_seg e |}.

(* fuzz_decode.c:127-150. The event is all zero (kind 0, the memset of :133) unless the step is
   a message. A fader takes the next step as its LSB when that step is a message whose status
   is B0..BF and whose d1 is 0x20 + the fader's strip (:143); then the position's low three bits
   are the LSB's bits 6..4 (:144, value |= (uint16_t)(lsb.d2 >> 4 & 7), the |= converting back
   to uint16_t) and the next step starts after the LSB (:145-146); else lsb_missing is 1 (:148). *)
Definition owed_at (b : list Z) (len pos status : Z) : owed :=
  let m := spec_msg_step b len pos status in
  if negb (sm_code m =? 1) then Owed m se_zero 0 (sm_next m) (sm_status_out m)
  else
    let e := spec_event_of b m in
    if negb (se_kind e =? SPEC_EV_FADER) then Owed m e 0 (sm_next m) (sm_status_out m)
    else
      let lsb := spec_msg_step b len (sm_next m) (sm_status_out m) in
      if (sm_code lsb =? 1) && (Z.land (sm_status lsb) 240 =? 176) && (sm_d1 lsb =? 32 + sm_d1 m)
      then
        Owed m (se_with_value e (u16 (Z.lor (se_value e) (u16 (Z.land (Z.shiftr (sm_d2 lsb) 4) 7)))))
          0 (sm_next lsb) (sm_status_out lsb)
      else Owed m e 1 (sm_next m) (sm_status_out m).

(* ---- the checks: true exactly when the C function returns without abort() ---- *)

(* fuzz_decode.c:41-91; r is diginet_msg_next's result and c the cursor after it *)
Definition check_cursor_step_ok (m : spec_msg) (r : Z) (c : dgn_cursor) : bool :=
  Bool.eqb (sm_code m =? 0) (r =? 0) &&                                   (* :47 *)
  implb (sm_code m =? SPEC_E_NO_STATUS) (r =? SPEC_E_NO_STATUS) &&        (* :53 *)
  implb (sm_code m =? SPEC_E_STATUS) (r =? SPEC_E_STATUS) &&              (* :59 *)
  implb (sm_code m =? SPEC_E_TRUNCATED) (r =? SPEC_E_TRUNCATED) &&        (* :67 *)
  implb (sm_code m =? 1) (r =? 1) &&                                      (* :73 *)
  (dc_pos c =? sm_next m) &&                                              (* :80 *)
  (dc_status c =? sm_status_out m).                                       (* :89 *)

(* the message comparison shared by fuzz_decode.c:99-114 and :171-173: place, length, status,
   running flag, data bytes, and for F0 the payload. The C test msg->sysex != b + m->sysex_at
   compares two pointers into the body, so it is the offset test dm_sysex <> sm_sysex_at; the
   body itself is therefore not an argument. *)
Definition msg_agrees (m : spec_msg) (msg : dgn_msg) : bool :=
  (dm_offset msg =? sm_at m) && (dm_len msg =? sm_len m) &&
  (dm_status msg =? sm_status m) && (dm_running msg =? sm_running m) &&
  (dm_d1 msg =? sm_d1 m) && (dm_d2 msg =? sm_d2 m) &&
  implb (sm_status m =? 240) ((dm_sysex msg =? sm_sysex_at m) && (dm_sysex_len msg =? sm_sysex_len m)).

(* fuzz_decode.c:93-115 (b is read only as the base of b + m->sysex_at, see msg_agrees) *)
Definition check_cursor_message_ok (m : spec_msg) (msg : dgn_msg) : bool := msg_agrees m msg.

(* fuzz_decode.c:152-185; rd is diginet_decoder_next's result. (int)ev->kind (:183) is the
   enum's value, de_kind. b is read only as a pointer base, as in check_cursor_message_ok. *)
Definition check_events_step_ok (o : owed) (rd : Z) (ev : dgn_event) : bool :=
  (rd =? sm_code (ow_m o)) &&                                             (* :161 *)
  implb (rd =? 1)                                                         (* :163 *)
    (msg_agrees (ow_m o) (de_msg ev) &&                                   (* :171-173 *)
     (de_kind ev =? se_kind (ow_e o))).                                   (* :183 *)

(* fuzz_decode.c:187-263 *)
Definition check_events_fields_ok (b : list Z) (o : owed) (ev : dgn_event) : bool :=
  let e := ow_e o in
  let m := ow_m o in
  let k := se_kind e in
  (* :190 *)
  let maker := (sm_status m =? 240) && (3 <=? sm_sysex_len m) && (byte_at b (sm_sysex_at m) =? SPEC_MAKER) in
  (* :191 *)
  let key := (k =? SPEC_EV_TOUCH) || (k =? SPEC_EV_STRIP_BUTTON) || (k =? SPEC_EV_SECTION_BUTTON) in
  (* :196-198 *)
  implb key ((de_button ev =? se_button e) && (de_on ev =? se_on e) &&
             (if k =? SPEC_EV_SECTION_BUTTON then de_zone ev =? se_zone e
              else de_strip ev =? se_strip e)) &&
  (* :207-209 *)
  implb (k =? SPEC_EV_FADER)
    ((de_strip ev =? se_strip e) && (de_value ev =? se_value e) &&
     (de_lsb_missing ev =? ow_lsb_missing o)) &&
  (* :214-216 *)
  implb ((k =? SPEC_EV_JOG) || (k =? SPEC_EV_VPOT))
    ((de_delta ev =? se_delta e) && implb (k =? SPEC_EV_VPOT) (de_strip ev =? se_strip e)) &&
  (* :221-222 *)
  implb (k =? SPEC_EV_RING) ((de_strip ev =? se_strip e) && (de_mask ev =? se_mask e)) &&
  (* :231-234 *)
  implb (k =? SPEC_EV_METER)
    ((de_addr ev =? se_addr e) && (de_strip ev =? se_strip e) && (de_right ev =? se_right e) &&
     (de_mask ev =? se_mask e) && (de_segments ev =? se_segments e)) &&
  (* :239-241 *)
  implb (k =? SPEC_EV_STRIP_LEDS)
    ((de_addr ev =? se_addr e) && (de_strip ev =? se_strip e) && (de_mask ev =? se_mask e)) &&
  (* :246-249: memcmp (ev->text, e->text, e->len) and ev->text[e->len] == '\0' *)
  implb (k =? SPEC_EV_SCRIBBLE)
    ((de_addr ev =? se_addr e) && (de_len ev =? se_len e) &&
     bytes_eq (se_len e) (de_text ev) (se_text e) && (byte_at (de_text ev) (se_len e) =? 0)) &&
  (* :254-256: memcmp (ev->seg, e->seg, 8) *)
  implb (k =? SPEC_EV_COUNTER)
    ((de_addr ev =? se_addr e) && (de_dots ev =? se_dots e) &&
     bytes_eq SPEC_DIGITS (de_seg ev) (se_seg e)) &&
  (* :261 *)
  implb maker (de_device ev =? se_device e).

(* fuzz_decode.c:265-276; rc is diginet_body_check (b, len) *)
Definition check_refusal_ok (b : list Z) (len rc : Z) : bool :=
  rc =? (if 0 <=? spec_system_at b len then SPEC_E_REFUSED else SPEC_OK).

(* ---- LLVMFuzzerTestOneInput, fuzz_decode.c:278-344 ---- *)

(* fuzz_decode.c:280-282 and :324: DESK[sel % 3], sel a uint8_t promoted to int *)
Definition DESK : list Z := [DIGINET_DESK_UNKNOWN; DIGINET_DESK_CONTROL24; DIGINET_DESK_PROCONTROL].

Definition desk_of_sel (sel : Z) : Z := nth (Z.to_nat (sel mod 3)) DESK 0.

(* fuzz_decode.c:289-302: None when the harness returns at once (:289-290); else sel, the body
   and its length. buf is the copy of data + 1 (:292); in frame mode a frame spec_read_frame
   accepts gives body = buf + 30 (the list skipn 30 buf) and len = body_len, and a refused
   frame gives len 0 over buf (:295-302). *)
Definition harness_input (data : list Z) : option (Z * list Z * Z) :=
  let size := Z.of_nat (length data) in
  if (FUZZ_INPUT_MAX <=? size) || (size =? 0) then None
  else
    match data with
    | [] => None
    | sel :: buf =>
        let len := size - 1 in
        if Z.land sel 128 =? 0 then Some (sel, buf, len)
        else
          let w := spec_read_frame buf len in
          if sf_code w =? SPEC_OK then Some (sel, skipn (Z.to_nat (sf_body w)) buf, sf_body_len w)
          else Some (sel, buf, 0)
    end.

(* One pass of the cursor loop (fuzz_decode.c:309-321): the grammar's step, the library's
   result r, the msg it filled and the cursor after the call. *)
Record cursor_step := CursorStep { cs_m : spec_msg; cs_r : Z; cs_msg : dgn_msg; cs_c : dgn_cursor }.

(* fuzz_decode.c:306-321. next c msg is diginet_msg_next (&c, &msg) on the body: its result, the
   msg after the call and the cursor after the call; the harness hands it a zeroed msg (:312).
   The trace lists every pass the C loop makes, whether or not its checks pass; the loop runs
   at most len + 1 passes (steps = 0 .. len) and leaves early after a step whose code is 0
   (:317-318). The next pass starts at m.next under m.status_out (:319-320). *)
Fixpoint cursor_trace (next : dgn_cursor -> dgn_msg -> Z * dgn_msg * dgn_cursor)
    (b : list Z) (len : Z) (fuel : nat) (c : dgn_cursor) (pos status : Z) : list cursor_step :=
  match fuel with
  | O => []
  | S fuel' =>
      let m := spec_msg_step b len pos status in
      let '(r, msg, c') := next c dgn_msg_zero in
      CursorStep m r msg c' ::
        (if sm_code m =? 0 then []
         else cursor_trace next b len fuel' c' (sm_next m) (sm_status_out m))
  end.

(* the checks of one pass, fuzz_decode.c:314-316 *)
Definition cursor_step_ok (s : cursor_step) : bool :=
  check_cursor_step_ok (cs_m s) (cs_r s) (cs_c s) &&
  implb (sm_code (cs_m s) =? 1) (check_cursor_message_ok (cs_m s) (cs_msg s)).

(* no check of the cursor loop aborts; c0 is the cursor diginet_cursor_init (&c, body, len)
   makes (:306), and the loop starts at 0 with no running status (:307-308) *)
Definition cursor_loop_ok (next : dgn_cursor -> dgn_msg -> Z * dgn_msg * dgn_cursor)
    (b : list Z) (len : Z) (c0 : dgn_cursor) : bool :=
  forallb cursor_step_ok (cursor_trace next b len (S (Z.to_nat len)) c0 0 0).

(* One pass of the decoder loop (fuzz_decode.c:327-339): what is owed, the library's result rd
   and the event it filled. *)
Record events_step := EventsStep { es_o : owed; es_rd : Z; es_ev : dgn_event }.

(* fuzz_decode.c:324-339. next d ev is diginet_decoder_next (&d, &ev) on the body: its result,
   the event after the call and the decoder after the call; the harness hands it a zeroed event
   (:330). Same bound and exit as cursor_trace; the next pass starts at o.next under
   o.status_out (:337-338). *)
Fixpoint events_trace {D : Type} (next : D -> dgn_event -> Z * dgn_event * D)
    (b : list Z) (len : Z) (fuel : nat) (d : D) (pos status : Z) : list events_step :=
  match fuel with
  | O => []
  | S fuel' =>
      let o := owed_at b len pos status in
      let '(rd, ev, d') := next d dgn_event_zero in
      EventsStep o rd ev ::
        (if sm_code (ow_m o) =? 0 then []
         else events_trace next b len fuel' d' (ow_next o) (ow_status_out o))
  end.

(* the checks of one pass, fuzz_decode.c:332-334 *)
Definition events_step_ok (b : list Z) (s : events_step) : bool :=
  check_events_step_ok (es_o s) (es_rd s) (es_ev s) &&
  implb (sm_code (ow_m (es_o s)) =? 1) (check_events_fields_ok b (es_o s) (es_ev s)).

(* no check of the decoder loop aborts; d0 is the decoder diginet_decoder_init (&d,
   diginet_personality_of (DESK[sel % 3]), body, len) makes (:324) *)
Definition events_loop_ok {D : Type} (next : D -> dgn_event -> Z * dgn_event * D)
    (b : list Z) (len : Z) (d0 : D) : bool :=
  forallb (events_step_ok b) (events_trace next b len (S (Z.to_nat len)) d0 0 0).

(* The whole harness on input data: true exactly when no check_ function aborts. The library
   enters as its functions: cursor_init len = diginet_cursor_init's cursor; msg_next b =
   diginet_msg_next on body b; decoder_init desk len = the decoder diginet_decoder_init (&d,
   diginet_personality_of (desk), body, len) makes; decoder_next b = diginet_decoder_next on
   body b; body_check b len = diginet_body_check (b, len). *)
Definition fuzz_decode_ok {D : Type}
    (cursor_init : Z -> dgn_cursor)
    (msg_next : list Z -> dgn_cursor -> dgn_msg -> Z * dgn_msg * dgn_cursor)
    (decoder_init : Z -> Z -> D)
    (decoder_next : list Z -> D -> dgn_event -> Z * dgn_event * D)
    (body_check : list Z -> Z -> Z)
    (data : list Z) : bool :=
  match harness_input data with
  | None => true
  | Some (sel, body, len) =>
      cursor_loop_ok (msg_next body) body len (cursor_init len) &&
      events_loop_ok (decoder_next body) body len (decoder_init (desk_of_sel sel) len) &&
      check_refusal_ok body len (body_check body len)
  end.

(* ---- worked examples: corpus seeds of fuzz/corpus/decode (fuzz/gen-corpus.c:190-272),
   values worked by hand from the C source ---- *)

Definition ex_running_status : list Z :=
  [144; 8; 64; 7; 65; 176; 1; 127; 33; 112; 64; 65; 92; 63].                 (* 90 08 40 07 41 b0 01 7f 21 70 40 41 5c 3f *)
Definition ex_fader_move : list Z := [176; 0; 64; 32; 0].                    (* b0 00 40 20 00 *)
Definition ex_fader_msb_only : list Z := [176; 3; 64; 144; 8; 64].           (* b0 03 40 90 08 40 *)
Definition ex_status_f1 : list Z := [241; 144; 8; 64; 255].                  (* f1 90 08 40 ff *)
Definition ex_status_for_data : list Z := [144; 144; 64].                    (* 90 90 40 *)
Definition ex_no_status : list Z := [7; 65; 144; 8; 64].                     (* 07 41 90 08 40 *)
Definition ex_jog_vpot : list Z := [176; 92; 65; 176; 69; 63; 88; 16].       (* b0 5c 41 b0 45 3f 58 10 *)
Definition ex_status_cancelled : list Z := [144; 8; 64; 240; 19; 1; 32; 1; 64; 247; 8; 64].

(* running_status, cursor: 90 08 40 | 07 41 (running 90) | b0 01 7f | 21 70 (running b0) |
   40 41 | 5c 3f | end: seven passes, (code, at, next, running flag, status_out) *)
Example worked_cursor_steps_running_status :
  map (fun s => (sm_code (cs_m s), sm_at (cs_m s), sm_next (cs_m s), sm_running (cs_m s), sm_status_out (cs_m s)))
    (cursor_trace (fun c msg => (0, msg, c)) ex_running_status 14 15 (DgnCursor 14 0 0) 0 0) =
  [(1, 0, 3, 0, 144); (1, 3, 5, 1, 144); (1, 5, 8, 0, 176); (1, 8, 10, 1, 176);
   (1, 10, 12, 1, 176); (1, 12, 14, 1, 176); (0, 14, 14, 0, 176)] := eq_refl.

(* running_status, decoder: the fader b0 01 7f takes 21 70 as its LSB (0x21 = 0x20 + strip 1):
   value 0x7f << 3 | (0x70 >> 4 & 7) = 1016 | 7 = 1023, and the next step is at 10 *)
Example worked_owed_running_status_fader :
  let o := owed_at ex_running_status 14 5 144 in
  (ow_next o, ow_status_out o, ow_lsb_missing o, se_kind (ow_e o), se_strip (ow_e o), se_value (ow_e o)) =
  (10, 176, 0, SPEC_EV_FADER, 1, 1023) := eq_refl.

(* running_status, decoder passes: (code, at, kind, delta): strip button, strip button (solo,
   strip 1), fader, V-Pot 0 delta +1, jog delta -1, end (kind 0, the memset event) *)
Example worked_events_steps_running_status :
  map (fun s => (sm_code (ow_m (es_o s)), sm_at (ow_m (es_o s)), se_kind (ow_e (es_o s)), se_delta (ow_e (es_o s))))
    (events_trace (fun d ev => (0, ev, d)) ex_running_status 14 15 tt 0 0) =
  [(1, 0, 3, 0); (1, 3, 3, 0); (1, 5, 1, 0); (1, 10, 5, 1); (1, 12, 6, -1); (0, 14, 0, 0)] := eq_refl.

(* fader_move: b0 00 40 then the LSB 20 00 under running status: value 0x40 << 3 = 512 *)
Example worked_owed_fader_move :
  let o := owed_at ex_fader_move 5 0 0 in
  (ow_next o, ow_lsb_missing o, se_strip (ow_e o), se_value (ow_e o)) = (5, 0, 0, 512) := eq_refl.

(* fader-msb-only: b0 03 40 then 90 08 40, which is no LSB: lsb_missing, next at 3 *)
Example worked_owed_fader_msb_only :
  let o := owed_at ex_fader_msb_only 6 0 0 in
  (ow_next o, ow_status_out o, ow_lsb_missing o, se_strip (ow_e o), se_value (ow_e o)) = (3, 176, 1, 3, 512) := eq_refl.

(* status-f1: F1 refused and stepped over, 90 08 40, FF refused, end: (code, next, status_out) *)
Example worked_status_f1 :
  map (fun s => (sm_code (cs_m s), sm_next (cs_m s), sm_status_out (cs_m s)))
    (cursor_trace (fun c msg => (0, msg, c)) ex_status_f1 5 6 (DgnCursor 5 0 0) 0 0) =
  [(SPEC_E_STATUS, 1, 0); (1, 4, 144); (SPEC_E_STATUS, 5, 0); (0, 5, 0)] := eq_refl.

(* status-for-data: 90 then a status byte where d1 is due (cut short at 1, status cleared);
   then 90 40 runs past the body (cut short at the end, status unchanged) *)
Example worked_status_for_data :
  map (fun s => (sm_code (cs_m s), sm_next (cs_m s), sm_status_out (cs_m s)))
    (cursor_trace (fun c msg => (0, msg, c)) ex_status_for_data 3 4 (DgnCursor 3 0 0) 0 0) =
  [(SPEC_E_TRUNCATED, 1, 0); (SPEC_E_TRUNCATED, 3, 0); (0, 3, 0)] := eq_refl.

(* no-status: two data bytes with no running status, then 90 08 40 *)
Example worked_no_status :
  map (fun s => (sm_code (cs_m s), sm_next (cs_m s), sm_status_out (cs_m s)))
    (cursor_trace (fun c msg => (0, msg, c)) ex_no_status 5 6 (DgnCursor 5 0 0) 0 0) =
  [(SPEC_E_NO_STATUS, 1, 0); (SPEC_E_NO_STATUS, 2, 0); (1, 5, 144); (0, 5, 144)] := eq_refl.

(* jog-vpot: jog +1, V-Pot 5 delta -1, then 58 10 (CC 0x58, past the last V-Pot): OTHER *)
Example worked_jog_vpot :
  map (fun s => (se_kind (ow_e (es_o s)), se_strip (ow_e (es_o s)), se_delta (ow_e (es_o s))))
    (events_trace (fun d ev => (0, ev, d)) ex_jog_vpot 8 9 tt 0 0) =
  [(SPEC_EV_JOG, 0, 1); (SPEC_EV_VPOT, 5, -1); (SPEC_EV_OTHER, 0, 0); (0, 0, 0)] := eq_refl.

(* status-cancelled: the F0 between 90 08 40 and 08 40 cancels running status, so 08 and 40
   are refused; the sysex is LEDs 01 bits 40 *)
Example worked_status_cancelled :
  map (fun s => (sm_code (ow_m (es_o s)), se_kind (ow_e (es_o s)), se_mask (ow_e (es_o s))))
    (events_trace (fun d ev => (0, ev, d)) ex_status_cancelled 12 13 tt 0 0) =
  [(1, SPEC_EV_STRIP_BUTTON, 0); (1, SPEC_EV_STRIP_LEDS, 64); (SPEC_E_NO_STATUS, 0, 0);
   (SPEC_E_NO_STATUS, 0, 0); (0, 0, 0)] := eq_refl.

Example worked_check_refusal :
  (check_refusal_ok [240; 19; 1; 112; 0; 247] 6 SPEC_E_REFUSED,
   check_refusal_ok [240; 19; 1; 112; 0; 247] 6 SPEC_OK,
   check_refusal_ok ex_meter 8 SPEC_OK) = (true, false, true) := eq_refl.

Example worked_harness_input :
  (harness_input (128 :: ex_fader_move_frame), harness_input (128 :: ex_frame_refused),
   harness_input (1 :: ex_button_mute), harness_input [], harness_input [2]) =
  (Some (128, ex_fader_move ++ repeat 0 25, 5), Some (128, ex_frame_refused, 0),
   Some (1, ex_button_mute, 3), None, Some (2, [], 0)) := eq_refl.

(* sel % 3: 0 none, 1 Control|24, 2 ProControl; a frame seed's sel 0x80 = 128 = 3 * 42 + 2 *)
Example worked_desk_of_sel :
  map desk_of_sel [0; 1; 2; 128; 255] =
  [DIGINET_DESK_UNKNOWN; DIGINET_DESK_CONTROL24; DIGINET_DESK_PROCONTROL; DIGINET_DESK_PROCONTROL;
   DIGINET_DESK_UNKNOWN] := eq_refl.

(* check_cursor_step: the cursor after 07 41 of running_status must stand at 5 with status 90 *)
Example worked_check_cursor_step :
  let m := spec_msg_step ex_running_status 14 3 144 in
  (check_cursor_step_ok m 1 (DgnCursor 14 5 144), check_cursor_step_ok m 1 (DgnCursor 14 5 0),
   check_cursor_step_ok m 1 (DgnCursor 14 6 144), check_cursor_step_ok m SPEC_E_NO_STATUS (DgnCursor 14 5 144)) =
  (true, false, false, false) := eq_refl.

(* check_cursor_message: running_status's second message is 90 07 41, running, at 3, 2 bytes *)
Example worked_check_cursor_message :
  let m := spec_msg_step ex_running_status 14 3 144 in
  (check_cursor_message_ok m (DgnMsg 144 1 7 65 0 0 3 2), check_cursor_message_ok m (DgnMsg 144 0 7 65 0 0 3 2)) =
  (true, false) := eq_refl.

(* check_events_fields on touch: strip 5, button 09, down *)
Definition ex_touch_event (strip zone : Z) : dgn_event :=
  {| de_kind := SPEC_EV_TOUCH; de_strip := strip; de_button := 9; de_zone := zone; de_on := 1;
     de_right := 0; de_addr := 0; de_lsb_missing := 0; de_value := 0; de_delta := 0; de_mask := 0;
     de_segments := 0; de_len := 0; de_text := repeat 0 9; de_seg := repeat 0 8; de_dots := 0;
     de_device := 0; de_msg := DgnMsg 144 0 9 69 0 0 0 3 |}.

Example worked_check_events_touch :
  let o := owed_at ex_touch 3 0 0 in
  (check_events_step_ok o 1 (ex_touch_event 5 0), check_events_fields_ok ex_touch o (ex_touch_event 5 0),
   check_events_fields_ok ex_touch o (ex_touch_event 0 5), check_events_step_ok o 0 (ex_touch_event 5 0)) =
  (true, true, false, false) := eq_refl.

(* The loops over a library that answers exactly what the harness owes. These two step
   functions are fixtures of the examples below only: they model no code of the library. *)
Definition ex_owed_msg (m : spec_msg) : dgn_msg :=
  {| dm_status := sm_status m; dm_running := sm_running m; dm_d1 := sm_d1 m; dm_d2 := sm_d2 m;
     dm_sysex := sm_sysex_at m; dm_sysex_len := sm_sysex_len m; dm_offset := sm_at m;
     dm_len := sm_len m |}.

Definition ex_msg_next (b : list Z) (c : dgn_cursor) (msg : dgn_msg) : Z * dgn_msg * dgn_cursor :=
  let m := spec_msg_step b (dc_len c) (dc_pos c) (dc_status c) in
  (sm_code m, (if sm_code m =? 1 then ex_owed_msg m else msg),
   DgnCursor (dc_len c) (sm_next m) (sm_status_out m)).

Definition ex_decoder_next (b : list Z) (d : dgn_cursor) (ev : dgn_event) : Z * dgn_event * dgn_cursor :=
  let o := owed_at b (dc_len d) (dc_pos d) (dc_status d) in
  let e := ow_e o in
  (sm_code (ow_m o),
   (if sm_code (ow_m o) =? 1 then
      {| de_kind := se_kind e; de_strip := se_strip e; de_button := se_button e;
         de_zone := se_zone e; de_on := se_on e; de_right := se_right e; de_addr := se_addr e;
         de_lsb_missing := ow_lsb_missing o; de_value := se_value e; de_delta := se_delta e;
         de_mask := se_mask e; de_segments := se_segments e; de_len := se_len e;
         de_text := se_text e ++ [0]; de_seg := se_seg e; de_dots := se_dots e;
         de_device := se_device e; de_msg := ex_owed_msg (ow_m o) |}
    else ev),
   DgnCursor (dc_len d) (ow_next o) (ow_status_out o)).

Definition ex_body_check (b : list Z) (len : Z) : Z :=
  if 0 <=? spec_system_at b len then SPEC_E_REFUSED else SPEC_OK.

Example worked_loops_ok :
  (cursor_loop_ok (ex_msg_next ex_running_status) ex_running_status 14 (DgnCursor 14 0 0),
   events_loop_ok (ex_decoder_next ex_running_status) ex_running_status 14 (DgnCursor 14 0 0),
   events_loop_ok (ex_decoder_next ex_scribble_write) ex_scribble_write 11 (DgnCursor 11 0 0),
   (* a cursor that never moves fails at the first pass of a non-empty body *)
   cursor_loop_ok (fun c msg => (1, msg, c)) ex_button_mute 3 (DgnCursor 3 0 0)) =
  (true, true, true, false) := eq_refl.

Example worked_fuzz_decode_ok :
  map (fuzz_decode_ok (fun len => DgnCursor len 0 0) ex_msg_next (fun _ len => DgnCursor len 0 0)
         ex_decoder_next ex_body_check)
    [1 :: ex_running_status; 2 :: ex_counter_write; 128 :: ex_fader_move_frame;
     1 :: [240; 19; 1; 112; 0; 247]; []] =
  [true; true; true; true; true] := eq_refl.
