(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* libdiginet's Gallina model, part three (DgnSpec.v is part one, DgnLib.v part two): the frame and
   the announce over a list Z buffer with C pointers as offsets, the reading a harness that holds
   its frames as list Z (spec_read_frame's reading) needs, and the lemmas that join them. Pure
   Gallina models of
   - src/diginet_frame.c: rd16, rd32, wr16, wr32, diginet_sum16, diginet_mac_is_digidesign,
     diginet_frame_is_keepalive, diginet_frame_parse, diginet_frame_build, copy_strz (as
     copy_strz_z: DgnSpec.v's copy_strz is the list byte reading) and diginet_announce_parse, with
     include/diginet/diginet.h's structs diginet_header (dgn_header), diginet_frame (dgn_frame) and
     diginet_announce (dgn_announce);
   - src/diginet_codec.c: diginet_personality_from_name;
   - fuzz/spec.h: spec_put16, spec_put32, spec_build_frame, spec_strz_len, the names of SPEC_C24 and
     SPEC_PC (spec_c24_name, spec_pc_name; the desks themselves are DgnSpec.v's c24 and pc), SPEC_OUI;
   - fuzz/fuzz_transport.c: desk_named, the desk an announce name selects.
   DgnSpec.v's fr_ functions, build_frame, strz_len, copy_strz, oui_of, keepalive_of and ann_
   functions, and DgnLib.v's lib_build_code and lib_frame, read the same C over a list byte that
   holds one whole frame (or one string); the last section joins the two readings
   (frame_parse_fr, frame_build_lib, spec_build_frame_build_frame, spec_strz_len_strz_len,
   copy_strz_z_copy_strz, announce_parse_ann, mac_is_digidesign_oui_of, frame_is_keepalive_of,
   announce_code_ann_code).
   Conventions are DgnSpec.v's: a buffer is a list Z, byte i is byte_at b i, a pointer into a
   buffer is its offset there, and NULL object pointers are not modelled: a buffer is a list, so
   the early returns on a NULL argument (diginet_frame.c:52, :57, :62-63, :98-99, :140-141;
   diginet_codec.c:19-20) are not modelled either. A function that writes only some fields of a
   struct it is given, or nothing on an error, takes that struct before the call as an argument. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* ---- constants of include/diginet/diginet.h ---- *)

Definition DIGINET_ETHERTYPE : Z := 0x885f.             (* diginet.h:31 *)
Definition DIGINET_MAC_LEN : Z := 6.                    (* diginet.h:32 *)
Definition DIGINET_ETH_HDR_LEN : Z := 14.               (* diginet.h:33 *)
Definition DIGINET_HDR_LEN : Z := 16.                   (* diginet.h:34 *)
Definition DIGINET_BODY_OFFSET : Z := 30.               (* diginet.h:35, 14 + 16 *)
Definition DIGINET_MIN_FRAME_LEN : Z := 60.             (* diginet.h:36 *)
Definition DIGINET_MAX_FRAME_LEN : Z := 1514.           (* diginet.h:37 *)
Definition DIGINET_MAX_BODY_LEN : Z := 1484.            (* diginet.h:38, 1514 - 30 *)
Definition DIGINET_OUI_0 : Z := 0x00.                   (* diginet.h:42-44 *)
Definition DIGINET_OUI_1 : Z := 0xa0.
Definition DIGINET_OUI_2 : Z := 0x7e.
Definition DIGINET_CMD_DATA : Z := 0x00.                (* diginet.h:47-54 *)
Definition DIGINET_CMD_ACK : Z := 0xa0.
Definition DIGINET_CMD_ANNOUNCE : Z := 0xe0.
Definition DIGINET_CMD_ANNOUNCE_SESSION : Z := 0xe1.
Definition DIGINET_E_ARG : Z := -1.                     (* diginet.h:60-68 *)
Definition DIGINET_E_SHORT : Z := -2.
Definition DIGINET_E_ETHERTYPE : Z := -3.
Definition DIGINET_E_LENGTH : Z := -4.
Definition DIGINET_E_SPACE : Z := -5.
Definition DIGINET_E_NOT_ANNOUNCE : Z := -9.
Definition DIGINET_SUM_BODY : Z := 0.                   (* diginet.h:77-80 *)
Definition DIGINET_SUM_ZERO : Z := 1.

(* ---- constants of fuzz/spec.h ---- *)

Definition SPEC_MIN_FRAME : Z := 60.                    (* spec.h:35, SPEC_ETH_HDR + 46 *)
Definition SPEC_MAX_FRAME : Z := 1514.                  (* spec.h:38, SPEC_ETH_HDR + 1500 *)
Definition SPEC_MAX_BODY : Z := 1484.                   (* spec.h:39 *)
Definition SPEC_CMD_DATA : Z := 0x00.                   (* spec.h:51-54 *)
Definition SPEC_CMD_ACK : Z := 0xa0.
Definition SPEC_CMD_E0 : Z := 0xe0.
Definition SPEC_CMD_E1 : Z := 0xe1.
Definition SPEC_ANN_UNKNOWN : Z := 15.                  (* spec.h:60-64 *)
Definition SPEC_ANN_FIELD : Z := 9.
Definition SPEC_ANN_VERSION : Z := 15.
Definition SPEC_ANN_NAME : Z := 24.
Definition SPEC_ANN_MIN : Z := 33.
Definition SPEC_OUI : list Z := [0x00; 0xa0; 0x7e].     (* spec.h:67 *)

(* ---- the library's structs (include/diginet/diginet.h) ---- *)

(* struct diginet_header, diginet.h:82-90: numbytes, sum, retry uint16_t; send_counter, ack_counter
   uint32_t; cmd, num_commands uint8_t *)
Record dgn_header := DgnHeader {
  dh_numbytes : Z; dh_sum : Z; dh_send_counter : Z; dh_ack_counter : Z; dh_retry : Z;
  dh_cmd : Z; dh_num_commands : Z }.

(* struct diginet_frame, diginet.h:92-102. df_dst and df_src are the arrays uint8_t[6], held as their
   6 elements; df_body is the offset, in the buffer the frame was parsed from, of the pointer body
   (diginet.h:97); ethertype, body_sum uint16_t; body_len, pad_len size_t; sum_matches uint8_t. *)
Record dgn_frame := DgnFrame {
  df_dst : list Z; df_src : list Z; df_ethertype : Z; df_h : dgn_header; df_body : Z;
  df_body_len : Z; df_pad_len : Z; df_body_sum : Z; df_sum_matches : Z }.

(* struct diginet_announce, diginet.h:127-132. version and name are char[10], held as their 10
   elements (char is unsigned); da_unknown is the offset of the pointer unknown in the buffer the
   frame's body points into; unknown_len size_t. *)
Record dgn_announce := DgnAnnounce {
  da_version : list Z; da_name : list Z; da_unknown : Z; da_unknown_len : Z }.

(* ---- src/diginet_frame.c ---- *)

(* diginet_frame.c:11: (uint16_t)((p[0] << 8) | p[1]), computed in int; p = b + i *)
Definition rd16 (b : list Z) (i : Z) : Z :=
  u16 (Z.lor (Z.shiftl (byte_at b i) 8) (byte_at b (i + 1))).

(* diginet_frame.c:12-15: each (uint32_t)p[k] << s is computed in uint32_t; p[3] is an int converted
   to uint32_t for the | *)
Definition rd32 (b : list Z) (i : Z) : Z :=
  Z.lor (u32 (Z.shiftl (byte_at b i) 24))
    (Z.lor (u32 (Z.shiftl (byte_at b (i + 1)) 16))
       (Z.lor (u32 (Z.shiftl (byte_at b (i + 2)) 8)) (byte_at b (i + 3)))).

(* diginet_frame.c:16: p[0] = (uint8_t)(v >> 8), p[1] = (uint8_t)v, of the uint16_t v *)
Definition wr16 (v : Z) : list Z := [u8 (Z.shiftr v 8); u8 v].

(* diginet_frame.c:17-20: p[0] = (uint8_t)(v >> 24) .. p[3] = (uint8_t)v, of the uint32_t v *)
Definition wr32 (v : Z) : list Z :=
  [u8 (Z.shiftr v 24); u8 (Z.shiftr v 16); u8 (Z.shiftr v 8); u8 v].

(* diginet_frame.c:45-46: s += p[i] in uint32_t (unsigned int plus int is unsigned int) for i < n;
   the fuel is the loop's n iterations *)
Fixpoint sum16_loop (b : list Z) (p s i : Z) (fuel : nat) : Z :=
  match fuel with
  | O => s
  | S f => sum16_loop b p (u32 (s + byte_at b (p + i))) (i + 1) f
  end.

(* diginet_frame.c:42-48, (uint16_t)s at :47; the bytes are b[p], ..., b[p + n - 1] *)
Definition diginet_sum16 (b : list Z) (p n : Z) : Z := u16 (sum16_loop b p 0 0 (Z.to_nat n)).

(* diginet_frame.c:50-53: the int 0 or 1 of the && *)
Definition diginet_mac_is_digidesign (mac : list Z) : Z :=
  int_of_bool ((byte_at mac 0 =? DIGINET_OUI_0) && (byte_at mac 1 =? DIGINET_OUI_1) &&
               (byte_at mac 2 =? DIGINET_OUI_2)).

(* diginet_frame.c:55-58; f->body[0] is b[df_body f], b the buffer f was parsed from *)
Definition diginet_frame_is_keepalive (b : list Z) (f : dgn_frame) : Z :=
  int_of_bool ((dh_cmd (df_h f) =? DIGINET_CMD_DATA) && (df_body_len f =? 1) &&
               (byte_at b (df_body f) =? 0)).

(* diginet_frame.c:60-91: (r, *f after the call). It writes *f only when it returns DIGINET_OK
   (:75-89), so f is an argument: every other return leaves it as it was. *)
Definition diginet_frame_parse (b : list Z) (len : Z) (f : dgn_frame) : Z * dgn_frame :=
  if len <? DIGINET_BODY_OFFSET then (DIGINET_E_SHORT, f)                              (* :64-65 *)
  else
    let et := rd16 b 12 in                                                              (* :66 *)
    if negb (et =? DIGINET_ETHERTYPE) then (DIGINET_E_ETHERTYPE, f)                     (* :67-68 *)
    else
      let numbytes := rd16 b DIGINET_ETH_HDR_LEN in                         (* :70-71, h = buf + 14 *)
      (* :72-73; len - 14 in size_t: len >= 30 here, so no wrap *)
      if (numbytes <? DIGINET_HDR_LEN) || (len - DIGINET_ETH_HDR_LEN <? numbytes)
      then (DIGINET_E_LENGTH, f)
      else
        let sum := rd16 b 16 in                                                         (* :79 *)
        let body_len := numbytes - DIGINET_HDR_LEN in                (* :86, numbytes >= 16 *)
        let body_sum := diginet_sum16 b DIGINET_BODY_OFFSET body_len in                 (* :88 *)
        (DIGINET_OK,                                                                    (* :90 *)
         {| df_dst := map (byte_at b) (zseq 6);                                         (* :75 *)
            df_src := map (fun k => byte_at b (6 + k)) (zseq 6);                        (* :76 *)
            df_ethertype := et;                                                         (* :77 *)
            df_h := {| dh_numbytes := numbytes; dh_sum := sum;                          (* :78-79 *)
                       dh_send_counter := rd32 b 18; dh_ack_counter := rd32 b 22;       (* :80-81 *)
                       dh_retry := rd16 b 26;                                           (* :82 *)
                       dh_cmd := byte_at b 28; dh_num_commands := byte_at b 29 |};      (* :83-84 *)
            df_body := DIGINET_BODY_OFFSET;                                             (* :85 *)
            df_body_len := body_len;
            (* :87, size_t: numbytes <= len - 14, so len - 30 - body_len >= 0 *)
            df_pad_len := len - DIGINET_BODY_OFFSET - body_len;
            df_body_sum := body_sum;
            df_sum_matches := int_of_bool (body_sum =? sum) |}).                        (* :89 *)

(* diginet_frame.c:93-127: (r, the bytes buf[0 .. r) it writes); for a negative r it writes nothing
   (the empty list). dst and src are the bytes from those pointers, body the bytes from body (the
   list [] for a NULL body with body_len 0, which diginet_session.c:101 passes), h is *h. *)
Definition diginet_frame_build (cap : Z) (dst src : list Z) (h : dgn_header) (body : list Z)
    (body_len mode : Z) : Z * list Z :=
  if negb ((mode =? DIGINET_SUM_BODY) || (mode =? DIGINET_SUM_ZERO))
  then (DIGINET_E_ARG, [])                                                              (* :100-101 *)
  else if DIGINET_MAX_BODY_LEN <? body_len then (DIGINET_E_LENGTH, [])                 (* :102-103 *)
  else if negb (diginet_body_check body body_len =? DIGINET_OK)
  then (DIGINET_E_REFUSED, [])                                                          (* :104-105 *)
  else
    let len := DIGINET_BODY_OFFSET + body_len in                                        (* :106 *)
    let out := if len <? DIGINET_MIN_FRAME_LEN then DIGINET_MIN_FRAME_LEN else len in   (* :107 *)
    if cap <? out then (DIGINET_E_SPACE, [])                                            (* :108-109 *)
    else
      (out,                                                          (* :126, (int)out <= 1514 *)
       map (byte_at dst) (zseq 6) ++ map (byte_at src) (zseq 6) ++                      (* :111-112 *)
       wr16 DIGINET_ETHERTYPE ++                                                        (* :113 *)
       wr16 (u16 (DIGINET_HDR_LEN + body_len)) ++                              (* :114-115, p = buf + 14 *)
       (* :116, the uint16_t diginet_sum16 or 0, through an int, to the uint16_t parameter *)
       wr16 (if mode =? DIGINET_SUM_BODY then diginet_sum16 body 0 body_len else 0) ++
       wr32 (dh_send_counter h) ++ wr32 (dh_ack_counter h) ++ wr16 (dh_retry h) ++     (* :117-119 *)
       [dh_cmd h; dh_num_commands h] ++                                                 (* :120-121 *)
       map (byte_at body) (zseq (Z.to_nat body_len)) ++                                 (* :122-123 *)
       repeat 0 (Z.to_nat (out - len))).                                                (* :124-125 *)

(* diginet_frame.c:133-135: for (; i < n && i + 1 < dst_size && src[i]; i++) dst[i] = (char)src[i]
   (char is unsigned: the value is kept), then dst[i] = '\0'. dst is the field before the call, held
   as its full-length list; src = b + p. The fuel n - i is exact: each turn adds one to i, and the
   loop stops at i = n at the latest. *)
Fixpoint copy_strz_loop (dst b : list Z) (p n dst_size i : Z) (fuel : nat) : list Z :=
  match fuel with
  | O => list_set dst (Z.to_nat i) 0
  | S f =>
      if (i <? n) && (i + 1 <? dst_size) && negb (byte_at b (p + i) =? 0)
      then copy_strz_loop (list_set dst (Z.to_nat i) (byte_at b (p + i))) b p n dst_size (i + 1) f
      else list_set dst (Z.to_nat i) 0
  end.

(* diginet_frame.c:130-136: the field dst after copy_strz (dst, dst_size, b + p, n) *)
Definition copy_strz_z (dst : list Z) (dst_size : Z) (b : list Z) (p n : Z) : list Z :=
  copy_strz_loop dst b p n dst_size 0 (Z.to_nat n).

(* diginet_frame.c:138-151: (r, *a after the call); f's body points into b at df_body f. It writes *a
   only when it returns DIGINET_OK, and the bytes of version and name after the NUL copy_strz writes
   keep a's values. *)
Definition diginet_announce_parse (b : list Z) (f : dgn_frame) (a : dgn_announce) : Z * dgn_announce :=
  if negb ((dh_cmd (df_h f) =? DIGINET_CMD_ANNOUNCE) ||
           (dh_cmd (df_h f) =? DIGINET_CMD_ANNOUNCE_SESSION))
  then (DIGINET_E_NOT_ANNOUNCE, a)                                                      (* :142-143 *)
  else if df_body_len f <? 33 then (DIGINET_E_LENGTH, a)                                (* :144-145 *)
  else
    (DIGINET_OK,                                                                        (* :150 *)
     {| da_unknown := df_body f; da_unknown_len := 15;                                  (* :146-147 *)
        (* :148-149, sizeof a->version = sizeof a->name = 10 *)
        da_version := copy_strz_z (da_version a) 10 b (df_body f + 15) 9;
        da_name := copy_strz_z (da_name a) 10 b (df_body f + 24) 9 |}).

(* ---- src/diginet_codec.c: diginet_personality_from_name ---- *)

(* strcmp (x + i, y + i) == 0 (C11 7.24.4.2; unsigned char values): the bytes agree up to and with
   the first NUL of x. Called with i = 0 and fuel the length of y as a C string, its NUL included;
   for a y whose only NUL is its last byte that fuel is exact, since by y's last index the loop has
   returned, so the O case is never reached. *)
Fixpoint strcmp_eq (x y : list Z) (i : Z) (fuel : nat) : bool :=
  match fuel with
  | O => true
  | S f =>
      if negb (byte_at x i =? byte_at y i) then false
      else if byte_at x i =? 0 then true
      else strcmp_eq x y (i + 1) f
  end.

(* diginet_codec.c:21-23: the index, counted from i, of the first entry of t whose announce_name (its
   bytes dp_announce_name, then the NUL) strcmp finds equal to name *)
Fixpoint personality_named (t : list dgn_personality) (i : Z) (name : list Z) : option Z :=
  match t with
  | [] => None
  | p :: t' =>
      if strcmp_eq name (dp_announce_name p ++ [0]) 0 (S (length (dp_announce_name p)))
      then Some i else personality_named t' (i + 1) name
  end.

(* diginet_codec.c:17-25: a pointer to personalities[i] is Some i and NULL (:24) None, as for
   diginet_personality_of (DgnLib.v); name is the char array it points to, held as a list *)
Definition diginet_personality_from_name (name : list Z) : option Z :=
  personality_named personalities 0 name.

(* ---- fuzz/spec.h ---- *)

(* spec.h:158-162: p[0] = (uint8_t)(v >> 8), p[1] = (uint8_t)v, of the unsigned v *)
Definition spec_put16 (v : Z) : list Z := [u8 (Z.shiftr v 8); u8 v].

(* spec.h:164-170 *)
Definition spec_put32 (v : Z) : list Z :=
  [u8 (Z.shiftr v 24); u8 (Z.shiftr v 16); u8 (Z.shiftr v 8); u8 v].

(* spec.h:228-247: (n, out[0 .. n)). send, ack: uint32_t; retry: uint16_t; cmd, ncmds: uint8_t;
   dst, src, body: the bytes from those pointers. memset (out, 0, n) at :233, then the writes of
   :234-245 over [0, 30 + len): the bytes [30 + len, n) keep their 0. *)
Definition spec_build_frame (dst src : list Z) (send ack retry cmd ncmds : Z) (body : list Z)
    (len zero_sum : Z) : Z * list Z :=
  let n := if SPEC_BODY_AT + len <? SPEC_MIN_FRAME then SPEC_MIN_FRAME else SPEC_BODY_AT + len in (* :232 *)
  (n,                                                                                   (* :246 *)
   map (byte_at dst) (zseq 6) ++ map (byte_at src) (zseq 6) ++                          (* :234-235 *)
   spec_put16 SPEC_ETHERTYPE ++                                                         (* :236 *)
   spec_put16 (u32 (SPEC_HDR + len)) ++                           (* :237, (unsigned) of a size_t *)
   spec_put16 (if zero_sum =? 0 then spec_sum_at body 0 len else 0) ++                  (* :238 *)
   spec_put32 send ++ spec_put32 ack ++ spec_put16 retry ++                             (* :239-241 *)
   [cmd; ncmds] ++                                                                      (* :242-243 *)
   map (byte_at body) (zseq (Z.to_nat len)) ++                                          (* :244-245 *)
   repeat 0 (Z.to_nat (n - SPEC_BODY_AT - len))).                                       (* :233 *)

(* spec.h:254-255: while (n < SPEC_ANN_FIELD && p[n]) n++, p = b + p0. The fuel 9 - n is exact: the
   loop stops at n = 9 at the latest. *)
Fixpoint strz_len_loop (b : list Z) (p n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S f => if (n <? SPEC_ANN_FIELD) && negb (byte_at b (p + n) =? 0) then strz_len_loop b p (n + 1) f else n
  end.

(* spec.h:251-257 *)
Definition spec_strz_len (b : list Z) (p : Z) : Z := strz_len_loop b p 0 9.

(* the names of SPEC_C24 and SPEC_PC, spec.h:110-111: "CNTRL|24" and "MAINUNIT", the bytes before
   their NUL *)
Definition spec_c24_name : list Z := [0x43; 0x4e; 0x54; 0x52; 0x4c; 0x7c; 0x32; 0x34].
Definition spec_pc_name : list Z := [0x4d; 0x41; 0x49; 0x4e; 0x55; 0x4e; 0x49; 0x54].

(* memcmp (b + p, y, n) == 0, over unsigned bytes *)
Definition bytes_eq_at (b : list Z) (p : Z) (y : list Z) (n : Z) : bool :=
  forallb (fun k => byte_at b (p + k) =? byte_at y k) (zseq (Z.to_nat n)).

(* ---- fuzz/fuzz_transport.c: desk_named ---- *)

(* fuzz_transport.c:267-268 (:270 for SPEC_PC): n = spec_strz_len (body + SPEC_ANN_NAME), then
   n == strlen (s) && !memcmp (body + SPEC_ANN_NAME, s, n), for the name s of a desk *)
Definition desk_name_is (b : list Z) (body : Z) (s : list Z) : bool :=
  let n := spec_strz_len b (body + SPEC_ANN_NAME) in
  (n =? Z.of_nat (length s)) && bytes_eq_at b (body + SPEC_ANN_NAME) s n.

(* fuzz_transport.c:265-273: the desk an announce body (at offset body of b) names: &SPEC_C24 is
   Some c24, &SPEC_PC is Some pc, NULL is None *)
Definition desk_named (b : list Z) (body : Z) : option desk :=
  if desk_name_is b body spec_c24_name then Some c24
  else if desk_name_is b body spec_pc_name then Some pc
  else None.

(* ---- worked examples, values worked by hand from the C source ---- *)

Example ln_wr : (wr16 0x885f, wr32 0x01020304) = ([0x88; 0x5f], [1; 2; 3; 4]) := eq_refl.

(* ex_fader_move_frame (DgnSpec.v): numbytes 0x15, sum 0x110, send 0x105 *)
Example ln_rd :
  (rd16 ex_fader_move_frame 14, rd16 ex_fader_move_frame 16, rd32 ex_fader_move_frame 18) =
  (21, 272, 261) := eq_refl.

(* b0 + 00 + 40 + 20 + 00 = 0x110; 300 bytes ff: 76500 mod 65536 = 10964 *)
Example ln_sum16 :
  (diginet_sum16 [176; 0; 64; 32; 0] 0 5, diginet_sum16 ex_fader_move_frame 30 5,
   diginet_sum16 (repeat 255 300) 0 300) = (272, 272, 10964) := eq_refl.

Definition ln_frame0 : dgn_frame :=
  {| df_dst := []; df_src := []; df_ethertype := 0; df_h := DgnHeader 0 0 0 0 0 0 0; df_body := 0;
     df_body_len := 0; df_pad_len := 0; df_body_sum := 0; df_sum_matches := 0 |}.

(* fader_move-frame: dst 02:00:00:00:00:01, src 00:a0:7e:24:00:01, body of 5 bytes at 30, 25 bytes of
   padding, sum 0x110 matches *)
Example ln_parse_fader :
  diginet_frame_parse ex_fader_move_frame 60 ln_frame0 =
  (DIGINET_OK,
   {| df_dst := [2; 0; 0; 0; 0; 1]; df_src := [0; 160; 126; 36; 0; 1]; df_ethertype := 0x885f;
      df_h := DgnHeader 21 272 261 0 0 0 1; df_body := 30; df_body_len := 5; df_pad_len := 25;
      df_body_sum := 272; df_sum_matches := 1 |}) := eq_refl.

(* 20 bytes: short; 30 zeros: EtherType 0; numbytes 21 past 34 - 14: length; 35 bytes: no padding *)
Example ln_parse_codes :
  (fst (diginet_frame_parse ex_frame_refused 20 ln_frame0),
   fst (diginet_frame_parse (repeat 0 30) 30 ln_frame0),
   fst (diginet_frame_parse ex_fader_move_frame 34 ln_frame0),
   df_pad_len (snd (diginet_frame_parse ex_fader_move_frame 35 ln_frame0))) =
  (DIGINET_E_SHORT, DIGINET_E_ETHERTYPE, DIGINET_E_LENGTH, 0) := eq_refl.

Example ln_parse_keeps : snd (diginet_frame_parse ex_frame_refused 20 ln_frame0) = ln_frame0 := eq_refl.

Definition ln_desk : list Z := [0; 160; 126; 36; 0; 1].       (* 00:a0:7e:24:00:01 *)
Definition ln_host : list Z := [2; 0; 0; 0; 0; 1].            (* 02:00:00:00:00:01 *)

(* the library builds fader_move-frame back; numbytes and sum of h are not read *)
Example ln_build_fader :
  diginet_frame_build 60 ln_host ln_desk (DgnHeader 0 0 261 0 0 0 1) [176; 0; 64; 32; 0] 5
    DIGINET_SUM_BODY = (60, ex_fader_move_frame) := eq_refl.

(* an ACK as send_control builds it (diginet_session.c:97-101): no body, numbytes 16, zero sum,
   send 3, ack 5, cmd a0, then 30 zero bytes *)
Example ln_build_ack :
  diginet_frame_build 60 ln_desk ln_host (DgnHeader 0 0 3 5 0 0xa0 0) [] 0 DIGINET_SUM_ZERO =
  (60, [0; 160; 126; 36; 0; 1; 2; 0; 0; 0; 0; 1; 136; 95; 0; 16; 0; 0; 0; 0; 0; 3; 0; 0; 0; 5;
        0; 0; 160; 0] ++ repeat 0 30) := eq_refl.

(* cap 59 < 60; mode 2; the body F0 13 00 70 F7; 1485 bytes *)
Example ln_build_codes :
  (fst (diginet_frame_build 59 ln_host ln_desk (DgnHeader 0 0 261 0 0 0 1) [176; 0; 64; 32; 0] 5
          DIGINET_SUM_BODY),
   fst (diginet_frame_build 60 ln_host ln_desk (DgnHeader 0 0 0 0 0 0 1) [176; 0; 64; 32; 0] 5 2),
   fst (diginet_frame_build 60 ln_host ln_desk (DgnHeader 0 0 0 0 0 0 1) [240; 19; 0; 112; 247] 5
          DIGINET_SUM_BODY),
   fst (diginet_frame_build 1514 ln_host ln_desk (DgnHeader 0 0 0 0 0 0 1) [] 1485 DIGINET_SUM_BODY)) =
  (DIGINET_E_SPACE, DIGINET_E_ARG, DIGINET_E_REFUSED, DIGINET_E_LENGTH) := eq_refl.

(* spec_build_frame makes the same frame; with zero_sum the sum bytes are 00 00 *)
Example ln_spec_build_fader :
  spec_build_frame ln_host ln_desk 261 0 0 0 1 [176; 0; 64; 32; 0] 5 0 = (60, ex_fader_move_frame) := eq_refl.
Example ln_spec_build_zero_sum :
  firstn 18 (snd (spec_build_frame ln_host ln_desk 261 0 0 0 1 [176; 0; 64; 32; 0] 5 1)) =
  [2; 0; 0; 0; 0; 1; 0; 160; 126; 36; 0; 1; 136; 95; 0; 21; 0; 0] := eq_refl.

(* op_announce's body (fuzz_transport.c:1052-1066) with no MAC in it: version "1.37" at 15, name
   "CNTRL|24" at 24, 34 bytes *)
Definition ln_ann_body : list Z :=
  repeat 0 15 ++ [0x31; 0x2e; 0x33; 0x37] ++ repeat 0 5 ++ spec_c24_name ++ [0; 0].
(* its frame as build_and_receive builds it (fuzz_transport.c:1031): broadcast, from ln_desk, e0;
   64 bytes, body at 30 *)
Definition ln_ann_frame : list Z :=
  snd (spec_build_frame [255; 255; 255; 255; 255; 255] ln_desk 0 0 0 0xe0 1 ln_ann_body 34 0).
Definition ln_ann_f : dgn_frame := snd (diginet_frame_parse ln_ann_frame 64 ln_frame0).
Definition ln_ann0 : dgn_announce :=
  {| da_version := repeat 0x55 10; da_name := repeat 0x55 10; da_unknown := 0; da_unknown_len := 0 |}.

Example ln_ann_parse_frame :
  (fst (diginet_frame_parse ln_ann_frame 64 ln_frame0), dh_cmd (df_h ln_ann_f), df_body ln_ann_f,
   df_body_len ln_ann_f, df_pad_len ln_ann_f) = (DIGINET_OK, 0xe0, 30, 34, 0) := eq_refl.

(* "1.37" at 30 + 15, "CNTRL|24" at 30 + 24, nine non-NUL bytes, nothing *)
Example ln_strz :
  (spec_strz_len ln_ann_frame 45, spec_strz_len ln_ann_frame 54, spec_strz_len (repeat 65 12) 0,
   spec_strz_len [] 0) = (4, 8, 9, 0) := eq_refl.

(* the NUL after "1.37" ends the copy; twelve 'A' are cut at 9 *)
Example ln_copy_strz :
  (copy_strz_z (repeat 0x55 10) 10 ln_ann_frame 45 9, copy_strz_z (repeat 0x55 10) 10 (repeat 65 12) 0 9) =
  ([0x31; 0x2e; 0x33; 0x37; 0; 0x55; 0x55; 0x55; 0x55; 0x55], repeat 65 9 ++ [0]) := eq_refl.

Example ln_announce :
  diginet_announce_parse ln_ann_frame ln_ann_f ln_ann0 =
  (DIGINET_OK,
   {| da_version := [0x31; 0x2e; 0x33; 0x37; 0; 0x55; 0x55; 0x55; 0x55; 0x55];
      da_name := [0x43; 0x4e; 0x54; 0x52; 0x4c; 0x7c; 0x32; 0x34; 0; 0x55];
      da_unknown := 30; da_unknown_len := 15 |}) := eq_refl.

(* a data frame is no announce; an e1 body of 32 bytes is too short *)
Example ln_announce_codes :
  (fst (diginet_announce_parse ex_fader_move_frame (snd (diginet_frame_parse ex_fader_move_frame 60 ln_frame0))
          ln_ann0),
   fst (diginet_announce_parse ln_ann_frame
          {| df_dst := []; df_src := []; df_ethertype := 0; df_h := DgnHeader 0 0 0 0 0 0xe1 0;
             df_body := 30; df_body_len := 32; df_pad_len := 0; df_body_sum := 0; df_sum_matches := 0 |}
          ln_ann0)) = (DIGINET_E_NOT_ANNOUNCE, DIGINET_E_LENGTH) := eq_refl.

(* "CNTRL|24", "MAINUNIT", "CNTRL|2", "CNTRL|245", "OTHER" *)
Example ln_personality_from_name :
  map diginet_personality_from_name
    [[0x43; 0x4e; 0x54; 0x52; 0x4c; 0x7c; 0x32; 0x34; 0; 0x55];
     spec_pc_name ++ [0; 0];
     [0x43; 0x4e; 0x54; 0x52; 0x4c; 0x7c; 0x32; 0; 0; 0];
     [0x43; 0x4e; 0x54; 0x52; 0x4c; 0x7c; 0x32; 0x34; 0x35; 0];
     [0x4f; 0x54; 0x48; 0x45; 0x52; 0; 0; 0; 0; 0]] =
  [Some 0; Some 1; None; None; None] := eq_refl.

(* the announce names the Control|24; the padding of fader_move-frame names nothing *)
Example ln_desk_named :
  (desk_named ln_ann_frame 30, desk_named ex_fader_move_frame 30) = (Some c24, None) := eq_refl.

Definition ln_keep_frame : list Z :=
  snd (diginet_frame_build 60 ln_host ln_desk (DgnHeader 0 0 7 0 0 0 1) [0] 1 DIGINET_SUM_BODY).

Example ln_keepalive :
  (diginet_frame_is_keepalive ln_keep_frame (snd (diginet_frame_parse ln_keep_frame 60 ln_frame0)),
   diginet_frame_is_keepalive ex_fader_move_frame (snd (diginet_frame_parse ex_fader_move_frame 60 ln_frame0))) =
  (1, 0) := eq_refl.

Example ln_mac : (diginet_mac_is_digidesign ln_desk, diginet_mac_is_digidesign ln_host) = (1, 0) := eq_refl.

(* ---- facts about lists and bytes ---- *)

Lemma lnk_byte_at_app_l : forall l1 l2 i, 0 <= i < Z.of_nat (length l1) ->
  byte_at (l1 ++ l2) i = byte_at l1 i.
Proof. intros l1 l2 i Hi. unfold byte_at. apply app_nth1. lia. Qed.

Lemma lnk_byte_at_app_r : forall l1 l2 i, Z.of_nat (length l1) <= i ->
  byte_at (l1 ++ l2) i = byte_at l2 (i - Z.of_nat (length l1)).
Proof. intros l1 l2 i Hi. unfold byte_at. rewrite app_nth2 by lia. f_equal. lia. Qed.

Lemma lnk_length_zseq : forall n, length (zseq n) = n.
Proof. intros n. unfold zseq. rewrite length_map, length_seq. reflexivity. Qed.

Lemma lnk_nth_map_seq : forall (g : Z -> Z) n start k, (k < n)%nat ->
  nth k (map g (map Z.of_nat (seq start n))) 0 = g (Z.of_nat (start + k)).
Proof.
  intros g n. induction n as [|n IH]; intros start k Hk; [lia|].
  destruct k as [|k]; cbn [seq map nth].
  - f_equal. lia.
  - rewrite IH by lia. f_equal. lia.
Qed.

Lemma lnk_byte_at_map_zseq : forall (g : Z -> Z) n i, 0 <= i -> (Z.to_nat i < n)%nat ->
  byte_at (map g (zseq n)) i = g i.
Proof. intros g n i Hi Hn. unfold byte_at, zseq. rewrite lnk_nth_map_seq by lia. f_equal. lia. Qed.

Lemma lnk_map_byte_at_zseq : forall l, map (byte_at l) (zseq (length l)) = l.
Proof.
  intros l. apply nth_ext with (d := 0) (d' := 0).
  - rewrite length_map, lnk_length_zseq. reflexivity.
  - intros k Hk. rewrite length_map, lnk_length_zseq in Hk.
    transitivity (byte_at (map (byte_at l) (zseq (length l))) (Z.of_nat k));
      [unfold byte_at; rewrite Nat2Z.id; reflexivity|].
    rewrite lnk_byte_at_map_zseq by lia. unfold byte_at. rewrite Nat2Z.id. reflexivity.
Qed.

Lemma lnk_byte_at_repeat0 : forall k i, byte_at (repeat 0 k) i = 0.
Proof. intros k i. unfold byte_at. apply nth_repeat. Qed.

Lemma lnk_length_list_set : forall l i v, length (list_set l i v) = length l.
Proof.
  induction l as [|x t IH]; intros i v; [reflexivity|].
  destruct i; cbn [list_set length]; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma lnk_nth_list_set : forall l x k v, (x < length l)%nat ->
  nth k (list_set l x v) 0 = if Nat.eqb k x then v else nth k l 0.
Proof.
  induction l as [|a l IH]; intros x k v H; cbn [length] in H; [lia|].
  destruct x as [|x], k as [|k]; cbn [list_set nth Nat.eqb]; try reflexivity.
  apply IH. lia.
Qed.

Lemma lnk_byte_at_list_set : forall l i v j, 0 <= i -> 0 <= j -> (Z.to_nat i < length l)%nat ->
  byte_at (list_set l (Z.to_nat i) v) j = if j =? i then v else byte_at l j.
Proof.
  intros l i v j Hi Hj Hl. unfold byte_at. rewrite lnk_nth_list_set by exact Hl.
  destruct (Z.eqb_spec j i) as [->|Hne].
  - rewrite Nat.eqb_refl. reflexivity.
  - destruct (Nat.eqb_spec (Z.to_nat j) (Z.to_nat i)); [lia|reflexivity].
Qed.

Lemma lnk_bytes_eq_at_true : forall b p y n, 0 <= n ->
  bytes_eq_at b p y n = true <-> forall k, 0 <= k < n -> byte_at b (p + k) = byte_at y k.
Proof.
  intros b p y n Hn. unfold bytes_eq_at. rewrite forallb_forall. split.
  - intros H k Hk. apply Z.eqb_eq. apply H. unfold zseq. apply in_map_iff.
    exists (Z.to_nat k). split; [lia | apply in_seq; lia].
  - intros H x Hx. unfold zseq in Hx. apply in_map_iff in Hx. destruct Hx as (m & <- & Hm).
    apply in_seq in Hm. apply Z.eqb_eq. apply H. lia.
Qed.

Lemma lnk_no_nul : forall s, forallb (fun j => negb (byte_at s j =? 0)) (zseq (length s)) = true ->
  forall j, 0 <= j < Z.of_nat (length s) -> byte_at s j <> 0.
Proof.
  intros s H j Hj. rewrite forallb_forall in H.
  assert (Hin : In j (zseq (length s))).
  { unfold zseq. apply in_map_iff. exists (Z.to_nat j). split; [lia | apply in_seq; lia]. }
  specialize (H j Hin). apply negb_true_iff, Z.eqb_neq in H. exact H.
Qed.

Lemma lnk_int_of_bool_1 : forall x, int_of_bool x = 1 <-> x = true.
Proof. intros [|]; cbn; split; intros H; congruence. Qed.

(* ---- the readers against each other ---- *)

Lemma rd16_spec_be16 : forall b i, rd16 b i = spec_be16 b i.
Proof. reflexivity. Qed.

Lemma rd32_spec_be32 : forall b i, rd32 b i = spec_be32 b i.
Proof. reflexivity. Qed.

Lemma spec_put16_wr16 : forall v, spec_put16 v = wr16 v.
Proof. reflexivity. Qed.

Lemma spec_put32_wr32 : forall v, spec_put32 v = wr32 v.
Proof. reflexivity. Qed.

(* the uint16_t v back from the two bytes wr16 writes *)
Lemma lnk_be16_bytes : forall v, 0 <= v < 2 ^ 16 ->
  u16 (Z.lor (Z.shiftl (u8 (Z.shiftr v 8)) 8) (u8 v)) = v.
Proof.
  intros v Hv. unfold u8, u16.
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite lk_lor_mul_pow2 by (pose proof (Z.mod_pos_bound v 256 ltac:(lia)); lia).
  change (2 ^ 8) with 256. change (2 ^ 16) with 65536 in Hv.
  rewrite (Z.mod_small (v / 256) 256) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite (Z.mul_comm (v / 256) 256), <- Z.div_mod by lia.
  apply Z.mod_small. lia.
Qed.

(* the uint32_t v back from the four bytes wr32 writes *)
Lemma lnk_be32_bytes : forall v, 0 <= v < 2 ^ 32 ->
  Z.lor (u32 (Z.shiftl (u8 (Z.shiftr v 24)) 24))
    (Z.lor (u32 (Z.shiftl (u8 (Z.shiftr v 16)) 16))
       (Z.lor (u32 (Z.shiftl (u8 (Z.shiftr v 8)) 8)) (u8 v))) = v.
Proof.
  intros v Hv. unfold u8, u32.
  rewrite !Z.shiftr_div_pow2 by lia. rewrite !Z.shiftl_mul_pow2 by lia.
  pose proof (Z.mod_pos_bound v 256 ltac:(lia)) as B0.
  pose proof (Z.mod_pos_bound (v / 2 ^ 8) 256 ltac:(lia)) as B1.
  pose proof (Z.mod_pos_bound (v / 2 ^ 16) 256 ltac:(lia)) as B2.
  pose proof (Z.mod_pos_bound (v / 2 ^ 24) 256 ltac:(lia)) as B3.
  rewrite (Z.mod_small ((v / 2 ^ 24) mod 256 * 2 ^ 24)) by lia.
  rewrite (Z.mod_small ((v / 2 ^ 16) mod 256 * 2 ^ 16)) by lia.
  rewrite (Z.mod_small ((v / 2 ^ 8) mod 256 * 2 ^ 8)) by lia.
  rewrite (lk_lor_mul_pow2 ((v / 2 ^ 8) mod 256) (v mod 256) 8) by lia.
  rewrite (lk_lor_mul_pow2 ((v / 2 ^ 16) mod 256) ((v / 2 ^ 8) mod 256 * 2 ^ 8 + v mod 256) 16) by lia.
  rewrite (lk_lor_mul_pow2 ((v / 2 ^ 24) mod 256)
             ((v / 2 ^ 16) mod 256 * 2 ^ 16 + ((v / 2 ^ 8) mod 256 * 2 ^ 8 + v mod 256)) 24) by lia.
  assert (D1 : v / 2 ^ 16 = v / 2 ^ 8 / 2 ^ 8) by (rewrite Z.div_div by lia; reflexivity).
  assert (D2 : v / 2 ^ 24 = v / 2 ^ 16 / 2 ^ 8) by (rewrite Z.div_div by lia; reflexivity).
  assert (Q : v / 2 ^ 24 < 256) by (apply Z.div_lt_upper_bound; lia).
  assert (Q0 : 0 <= v / 2 ^ 24) by (apply Z.div_pos; lia).
  rewrite (Z.mod_small (v / 2 ^ 24) 256) by lia.
  pose proof (Z.div_mod v (2 ^ 8) ltac:(lia)) as M0.
  pose proof (Z.div_mod (v / 2 ^ 8) (2 ^ 8) ltac:(lia)) as M1. rewrite <- D1 in M1.
  pose proof (Z.div_mod (v / 2 ^ 16) (2 ^ 8) ltac:(lia)) as M2. rewrite <- D2 in M2.
  change (2 ^ 8) with 256 in *.
  lia.
Qed.

Lemma lnk_sum16_loop : forall b p fuel s t i, s mod 2 ^ 16 = t mod 2 ^ 16 ->
  sum16_loop b p s i fuel mod 2 ^ 16 = spec_sum_loop b p t i fuel mod 2 ^ 16.
Proof.
  intros b p fuel. induction fuel as [|f IH]; intros s t i H; cbn [sum16_loop spec_sum_loop]; [exact H|].
  apply IH. unfold u32. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
  rewrite (mod_mod_pow2 _ 16 32) by lia. rewrite Zmod_mod.
  rewrite (Z.add_mod s) by lia. rewrite H. rewrite <- Z.add_mod by lia. reflexivity.
Qed.

(* diginet_sum16's uint32_t sum and spec_sum's & 0xffff at each byte give the same uint16_t *)
Lemma diginet_sum16_spec_sum_at : forall b p n, diginet_sum16 b p n = spec_sum_at b p n.
Proof.
  intros b p n. unfold diginet_sum16, spec_sum_at, u16. change 65536 with (2 ^ 16).
  apply lnk_sum16_loop. reflexivity.
Qed.

Lemma lnk_sum_loop_ext : forall b1 b2 p1 p2 fuel s i,
  (forall k, i <= k < i + Z.of_nat fuel -> byte_at b1 (p1 + k) = byte_at b2 (p2 + k)) ->
  spec_sum_loop b1 p1 s i fuel = spec_sum_loop b2 p2 s i fuel.
Proof.
  intros b1 b2 p1 p2 fuel. induction fuel as [|f IH]; intros s i H; cbn [spec_sum_loop]; [reflexivity|].
  rewrite (H i) by lia. apply IH. intros k Hk. apply H. lia.
Qed.

(* ---- L1: diginet_frame_parse against spec_read_frame ---- *)

(* the fields of the library's frame f against spec_read_frame's w, b the buffer both read *)
Definition parse_agrees (b : list Z) (f : dgn_frame) (w : spec_frame) : Prop :=
  sf_dst w = 0 /\ sf_src w = SPEC_MAC /\ sf_body w = SPEC_BODY_AT /\
  df_dst f = map (byte_at b) (zseq 6) /\ df_src f = map (fun k => byte_at b (SPEC_MAC + k)) (zseq 6) /\
  df_ethertype f = sf_ethertype w /\ dh_numbytes (df_h f) = sf_numbytes w /\
  dh_sum (df_h f) = sf_sum w /\ dh_send_counter (df_h f) = sf_send w /\
  dh_ack_counter (df_h f) = sf_ack w /\ dh_retry (df_h f) = sf_retry w /\
  dh_cmd (df_h f) = sf_cmd w /\ dh_num_commands (df_h f) = sf_ncmds w /\
  df_body f = sf_body w /\ df_body_len f = sf_body_len w /\ df_pad_len f = sf_pad_len w /\
  df_body_sum f = sf_body_sum w /\ df_sum_matches f = int_of_bool (sf_body_sum w =? sf_sum w).

(* L1. The same code for every buffer and length, and on SPEC_OK the same fields; on any other code
   *f is left as it was. *)
Theorem frame_parse_read_frame : forall b len f0,
  fst (diginet_frame_parse b len f0) = sf_code (spec_read_frame b len) /\
  (sf_code (spec_read_frame b len) = SPEC_OK ->
   parse_agrees b (snd (diginet_frame_parse b len f0)) (spec_read_frame b len)) /\
  (sf_code (spec_read_frame b len) <> SPEC_OK -> snd (diginet_frame_parse b len f0) = f0).
Proof.
  intros b len f0.
  unfold diginet_frame_parse, spec_read_frame; cbv beta zeta.
  change rd16 with spec_be16. change rd32 with spec_be32. rewrite !diginet_sum16_spec_sum_at.
  unfold DIGINET_BODY_OFFSET, SPEC_BODY_AT, DIGINET_ETHERTYPE, SPEC_ETHERTYPE, DIGINET_ETH_HDR_LEN,
    SPEC_AT_NUMBYTES, DIGINET_HDR_LEN, SPEC_HDR, SPEC_ETH_HDR, SPEC_AT_SUM, SPEC_AT_SEND, SPEC_AT_ACK,
    SPEC_AT_RETRY, SPEC_AT_CMD, SPEC_AT_NCMDS, SPEC_MAC, DIGINET_OK, DIGINET_E_SHORT, DIGINET_E_ETHERTYPE,
    DIGINET_E_LENGTH, SPEC_OK, SPEC_E_SHORT, SPEC_E_ETHERTYPE, SPEC_E_LENGTH.
  destruct (len <? 30); cbn [fst snd sf_code];
    [split; [reflexivity | split; [intros H; discriminate H | intros _; reflexivity]] |].
  destruct (negb (spec_be16 b 12 =? 34911)); cbn [fst snd sf_code];
    [split; [reflexivity | split; [intros H; discriminate H | intros _; reflexivity]] |].
  destruct ((spec_be16 b 14 <? 16) || (len - 14 <? spec_be16 b 14)); cbn [fst snd sf_code];
    [split; [reflexivity | split; [intros H; discriminate H | intros _; reflexivity]] |].
  split; [reflexivity|]. split; [|intros H; exfalso; apply H; reflexivity].
  intros _. unfold parse_agrees.
  cbn [df_dst df_src df_ethertype df_h dh_numbytes dh_sum dh_send_counter dh_ack_counter dh_retry dh_cmd
       dh_num_commands df_body df_body_len df_pad_len df_body_sum df_sum_matches sf_dst sf_src
       sf_ethertype sf_numbytes sf_sum sf_send sf_ack sf_retry sf_cmd sf_ncmds sf_body sf_body_len
       sf_pad_len sf_body_sum].
  repeat split.
Qed.

(* L1 as stated: the library accepts exactly the frames spec_read_frame accepts *)
Corollary frame_parse_ok_iff : forall b len f0,
  fst (diginet_frame_parse b len f0) = DIGINET_OK <-> sf_code (spec_read_frame b len) = SPEC_OK.
Proof. intros b len f0. rewrite (proj1 (frame_parse_read_frame b len f0)). reflexivity. Qed.

(* ---- the bytes of a built frame ---- *)

(* the bytes diginet_frame_build and spec_build_frame write: the MACs, 0x885F, numbytes nb, the sum,
   the counters, retry, command and count, the len body bytes, pad zero bytes *)
Definition frame_layout (dst src : list Z) (nb sum send ack retry cmd ncmds : Z) (body : list Z)
    (len : Z) (pad : nat) : list Z :=
  map (byte_at dst) (zseq 6) ++ map (byte_at src) (zseq 6) ++ wr16 DIGINET_ETHERTYPE ++ wr16 nb ++
  wr16 sum ++ wr32 send ++ wr32 ack ++ wr16 retry ++ [cmd; ncmds] ++
  map (byte_at body) (zseq (Z.to_nat len)) ++ repeat 0 pad.

Lemma lnk_length_layout : forall dst src nb sum send ack retry cmd ncmds body len pad,
  Z.of_nat (length (frame_layout dst src nb sum send ack retry cmd ncmds body len pad)) =
  30 + Z.of_nat (Z.to_nat len) + Z.of_nat pad.
Proof.
  intros. unfold frame_layout, wr16, wr32.
  rewrite !length_app, !length_map, !lnk_length_zseq, repeat_length. cbn [length]. lia.
Qed.

Lemma lnk_layout_tail : forall dst src nb sum send ack retry cmd ncmds body len pad i, 0 <= i ->
  byte_at (frame_layout dst src nb sum send ack retry cmd ncmds body len pad) (30 + i) =
  byte_at (map (byte_at body) (zseq (Z.to_nat len)) ++ repeat 0 pad) i.
Proof.
  intros dst src nb sum send ack retry cmd ncmds body len pad i Hi. unfold byte_at.
  replace (Z.to_nat (30 + i)) with (30 + Z.to_nat i)%nat by lia.
  reflexivity.
Qed.

Lemma lnk_layout_dst : forall dst src nb sum send ack retry cmd ncmds body len pad i, 0 <= i < 6 ->
  byte_at (frame_layout dst src nb sum send ack retry cmd ncmds body len pad) i = byte_at dst i.
Proof.
  intros dst src nb sum send ack retry cmd ncmds body len pad i Hi.
  assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) by lia.
  destruct C as [-> | [-> | [-> | [-> | [-> | ->]]]]]; reflexivity.
Qed.

Lemma lnk_layout_src : forall dst src nb sum send ack retry cmd ncmds body len pad i, 0 <= i < 6 ->
  byte_at (frame_layout dst src nb sum send ack retry cmd ncmds body len pad) (6 + i) = byte_at src i.
Proof.
  intros dst src nb sum send ack retry cmd ncmds body len pad i Hi.
  assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) by lia.
  destruct C as [-> | [-> | [-> | [-> | [-> | ->]]]]]; reflexivity.
Qed.

(* spec_read_frame reads the layout back *)
Lemma lnk_read_layout : forall dst src sum send ack retry cmd ncmds body len pad,
  0 <= len <= 65519 -> 0 <= sum < 2 ^ 16 -> 0 <= send < 2 ^ 32 -> 0 <= ack < 2 ^ 32 ->
  0 <= retry < 2 ^ 16 ->
  spec_read_frame (frame_layout dst src (16 + len) sum send ack retry cmd ncmds body len pad)
    (30 + len + Z.of_nat pad) =
  {| sf_code := SPEC_OK; sf_dst := 0; sf_src := 6; sf_ethertype := 34911; sf_numbytes := 16 + len;
     sf_sum := sum; sf_retry := retry; sf_send := send; sf_ack := ack; sf_cmd := cmd; sf_ncmds := ncmds;
     sf_body := 30; sf_body_len := len; sf_pad_len := Z.of_nat pad; sf_body_sum := spec_sum_at body 0 len |}.
Proof.
  intros dst src sum send ack retry cmd ncmds body len pad Hl Hs Hse Hac Hre.
  remember (frame_layout dst src (16 + len) sum send ack retry cmd ncmds body len pad) as L eqn:EL.
  assert (E12 : spec_be16 L 12 = 34911) by (subst L; reflexivity).
  assert (E14 : spec_be16 L 14 = 16 + len).
  { unfold spec_be16.
    replace (byte_at L 14) with (u8 (Z.shiftr (16 + len) 8)) by (subst L; reflexivity).
    replace (byte_at L (14 + 1)) with (u8 (16 + len)) by (subst L; reflexivity).
    apply lnk_be16_bytes. lia. }
  assert (E16 : spec_be16 L 16 = sum).
  { unfold spec_be16.
    replace (byte_at L 16) with (u8 (Z.shiftr sum 8)) by (subst L; reflexivity).
    replace (byte_at L (16 + 1)) with (u8 sum) by (subst L; reflexivity).
    apply lnk_be16_bytes. lia. }
  assert (E18 : spec_be32 L 18 = send).
  { unfold spec_be32.
    replace (byte_at L 18) with (u8 (Z.shiftr send 24)) by (subst L; reflexivity).
    replace (byte_at L (18 + 1)) with (u8 (Z.shiftr send 16)) by (subst L; reflexivity).
    replace (byte_at L (18 + 2)) with (u8 (Z.shiftr send 8)) by (subst L; reflexivity).
    replace (byte_at L (18 + 3)) with (u8 send) by (subst L; reflexivity).
    apply lnk_be32_bytes. lia. }
  assert (E22 : spec_be32 L 22 = ack).
  { unfold spec_be32.
    replace (byte_at L 22) with (u8 (Z.shiftr ack 24)) by (subst L; reflexivity).
    replace (byte_at L (22 + 1)) with (u8 (Z.shiftr ack 16)) by (subst L; reflexivity).
    replace (byte_at L (22 + 2)) with (u8 (Z.shiftr ack 8)) by (subst L; reflexivity).
    replace (byte_at L (22 + 3)) with (u8 ack) by (subst L; reflexivity).
    apply lnk_be32_bytes. lia. }
  assert (E26 : spec_be16 L 26 = retry).
  { unfold spec_be16.
    replace (byte_at L 26) with (u8 (Z.shiftr retry 8)) by (subst L; reflexivity).
    replace (byte_at L (26 + 1)) with (u8 retry) by (subst L; reflexivity).
    apply lnk_be16_bytes. lia. }
  assert (E28 : byte_at L 28 = cmd) by (subst L; reflexivity).
  assert (E29 : byte_at L 29 = ncmds) by (subst L; reflexivity).
  assert (ES : spec_sum_at L 30 len = spec_sum_at body 0 len).
  { unfold spec_sum_at. f_equal. apply lnk_sum_loop_ext. intros k Hk. subst L.
    rewrite lnk_layout_tail by lia.
    rewrite lnk_byte_at_app_l by (rewrite length_map, lnk_length_zseq; lia).
    rewrite lnk_byte_at_map_zseq by lia. rewrite Z.add_0_l. reflexivity. }
  unfold spec_read_frame; cbv beta zeta.
  unfold SPEC_BODY_AT, SPEC_ETHERTYPE, SPEC_HDR, SPEC_ETH_HDR, SPEC_AT_NUMBYTES, SPEC_AT_SUM, SPEC_AT_SEND,
    SPEC_AT_ACK, SPEC_AT_RETRY, SPEC_AT_CMD, SPEC_AT_NCMDS, SPEC_MAC.
  rewrite E12, E14, E16, E18, E22, E26, E28, E29, Z.eqb_refl.
  replace (30 + len + Z.of_nat pad <? 30) with false by (symmetry; apply Z.ltb_ge; lia).
  replace ((16 + len <? 16) || (30 + len + Z.of_nat pad - 14 <? 16 + len)) with false
    by (symmetry; apply orb_false_iff; split; apply Z.ltb_ge; lia).
  replace (16 + len - 16) with len by lia.
  rewrite ES. cbn [negb]. f_equal. lia.
Qed.

(* what spec_read_frame reads from the bytes of a frame of length out built from these fields, and
   the bytes themselves: the MACs, the body, zeros after it *)
Definition built_frame (bytes : list Z) (out : Z) (dst src : list Z) (send ack retry cmd ncmds : Z)
    (body : list Z) (len sum : Z) : Prop :=
  Z.of_nat (length bytes) = out /\
  spec_read_frame bytes out =
    {| sf_code := SPEC_OK; sf_dst := 0; sf_src := SPEC_MAC; sf_ethertype := SPEC_ETHERTYPE;
       sf_numbytes := SPEC_HDR + len; sf_sum := sum; sf_retry := retry; sf_send := send; sf_ack := ack;
       sf_cmd := cmd; sf_ncmds := ncmds; sf_body := SPEC_BODY_AT; sf_body_len := len;
       sf_pad_len := out - SPEC_BODY_AT - len; sf_body_sum := spec_sum_at body 0 len |} /\
  (forall i, 0 <= i < SPEC_MAC -> byte_at bytes i = byte_at dst i) /\
  (forall i, 0 <= i < SPEC_MAC -> byte_at bytes (SPEC_MAC + i) = byte_at src i) /\
  (forall i, 0 <= i < len -> byte_at bytes (SPEC_BODY_AT + i) = byte_at body i) /\
  (forall i, SPEC_BODY_AT + len <= i < out -> byte_at bytes i = 0).

Lemma lnk_layout_built : forall dst src sum send ack retry cmd ncmds body len pad,
  0 <= len <= DIGINET_MAX_BODY_LEN -> 0 <= sum < 2 ^ 16 -> 0 <= send < 2 ^ 32 -> 0 <= ack < 2 ^ 32 ->
  0 <= retry < 2 ^ 16 ->
  built_frame (frame_layout dst src (16 + len) sum send ack retry cmd ncmds body len pad)
    (30 + len + Z.of_nat pad) dst src send ack retry cmd ncmds body len sum.
Proof.
  intros dst src sum send ack retry cmd ncmds body len pad Hl Hs Hse Hac Hre.
  unfold DIGINET_MAX_BODY_LEN in Hl.
  assert (Lb : length (map (byte_at body) (zseq (Z.to_nat len))) = Z.to_nat len)
    by (rewrite length_map; apply lnk_length_zseq).
  unfold built_frame. split; [|split; [|split; [|split; [|split]]]].
  - rewrite lnk_length_layout. lia.
  - rewrite lnk_read_layout by lia. unfold SPEC_MAC, SPEC_HDR, SPEC_BODY_AT, SPEC_ETHERTYPE. f_equal. lia.
  - intros i Hi. apply lnk_layout_dst. unfold SPEC_MAC in Hi. exact Hi.
  - intros i Hi. apply lnk_layout_src. unfold SPEC_MAC in Hi. exact Hi.
  - intros i Hi. unfold SPEC_BODY_AT. rewrite lnk_layout_tail by lia.
    rewrite lnk_byte_at_app_l by (rewrite Lb; lia). apply lnk_byte_at_map_zseq; lia.
  - intros i Hi. unfold SPEC_BODY_AT in Hi. replace i with (30 + (i - 30)) by lia.
    rewrite lnk_layout_tail by lia. rewrite lnk_byte_at_app_r by (rewrite Lb; lia).
    apply lnk_byte_at_repeat0.
Qed.

(* ---- L2: diginet_frame_build, then spec_read_frame ---- *)

(* the frame diginet_frame_build writes for a body it accepts, in a buffer large enough *)
Lemma frame_build_layout : forall cap dst src h bd n mode,
  0 <= n <= DIGINET_MAX_BODY_LEN -> diginet_body_check bd n = DIGINET_OK ->
  Z.max 60 (30 + n) <= cap -> mode = DIGINET_SUM_BODY \/ mode = DIGINET_SUM_ZERO ->
  diginet_frame_build cap dst src h bd n mode =
  (Z.max 60 (30 + n),
   frame_layout dst src (16 + n) (if mode =? DIGINET_SUM_ZERO then 0 else spec_sum_at bd 0 n)
     (dh_send_counter h) (dh_ack_counter h) (dh_retry h) (dh_cmd h) (dh_num_commands h) bd n
     (Z.to_nat (Z.max 60 (30 + n) - (30 + n)))).
Proof.
  intros cap dst src h bd n mode Hn Hb Hc Hm.
  assert (Em : (mode =? DIGINET_SUM_BODY) || (mode =? DIGINET_SUM_ZERO) = true)
    by (destruct Hm as [E|E]; rewrite E; reflexivity).
  assert (Es : (if mode =? DIGINET_SUM_BODY then diginet_sum16 bd 0 n else 0) =
               (if mode =? DIGINET_SUM_ZERO then 0 else spec_sum_at bd 0 n))
    by (destruct Hm as [E|E]; rewrite E; [exact (diginet_sum16_spec_sum_at bd 0 n) | reflexivity]).
  assert (Eo : (if DIGINET_BODY_OFFSET + n <? DIGINET_MIN_FRAME_LEN then DIGINET_MIN_FRAME_LEN
                else DIGINET_BODY_OFFSET + n) = Z.max 60 (30 + n))
    by (unfold DIGINET_BODY_OFFSET, DIGINET_MIN_FRAME_LEN; destruct (Z.ltb_spec (30 + n) 60); lia).
  assert (Eu : u16 (DIGINET_HDR_LEN + n) = 16 + n)
    by (unfold u16, DIGINET_HDR_LEN; unfold DIGINET_MAX_BODY_LEN in Hn; apply Z.mod_small; lia).
  unfold diginet_frame_build; cbv zeta.
  rewrite Em. cbn [negb].
  replace (DIGINET_MAX_BODY_LEN <? n) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite Hb, Z.eqb_refl. cbn [negb].
  rewrite Eo.
  replace (cap <? Z.max 60 (30 + n)) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite Eu, Es. reflexivity.
Qed.

(* L2. A body of n <= 1484 bytes that diginet_body_check accepts, a buffer of cap >= max (60, 30 + n)
   bytes and a valid mode: diginet_frame_build answers out = max (60, 30 + n) and writes out bytes,
   which spec_read_frame reads as a frame with h's counters, retry, command and count, the body bd,
   zeros after it, and the body's sum or 0 *)
Theorem frame_build_read_frame : forall cap dst src h bd n mode,
  0 <= n <= DIGINET_MAX_BODY_LEN -> diginet_body_check bd n = DIGINET_OK ->
  Z.max 60 (30 + n) <= cap -> mode = DIGINET_SUM_BODY \/ mode = DIGINET_SUM_ZERO ->
  0 <= dh_send_counter h < 2 ^ 32 -> 0 <= dh_ack_counter h < 2 ^ 32 -> 0 <= dh_retry h < 2 ^ 16 ->
  fst (diginet_frame_build cap dst src h bd n mode) = Z.max 60 (30 + n) /\
  built_frame (snd (diginet_frame_build cap dst src h bd n mode)) (Z.max 60 (30 + n)) dst src
    (dh_send_counter h) (dh_ack_counter h) (dh_retry h) (dh_cmd h) (dh_num_commands h) bd n
    (if mode =? DIGINET_SUM_ZERO then 0 else spec_sum_at bd 0 n).
Proof.
  intros cap dst src h bd n mode Hn Hb Hc Hm Hs Ha Hr.
  rewrite (frame_build_layout cap dst src h bd n mode Hn Hb Hc Hm). cbn [fst snd]. split; [reflexivity|].
  remember (Z.to_nat (Z.max 60 (30 + n) - (30 + n))) as pad eqn:Hpad.
  replace (Z.max 60 (30 + n)) with (30 + n + Z.of_nat pad) by lia.
  apply lnk_layout_built; try lia.
  destruct Hm as [E|E]; rewrite E; cbn.
  - unfold spec_sum_at, u16. apply Z.mod_pos_bound. lia.
  - lia.
Qed.

(* L2, the refusal side: a body diginet_body_check refuses is refused *)
Theorem frame_build_refused : forall cap dst src h bd n mode,
  n <= DIGINET_MAX_BODY_LEN -> mode = DIGINET_SUM_BODY \/ mode = DIGINET_SUM_ZERO ->
  diginet_body_check bd n <> DIGINET_OK ->
  fst (diginet_frame_build cap dst src h bd n mode) = DIGINET_E_REFUSED.
Proof.
  intros cap dst src h bd n mode Hn Hm Hb.
  assert (Em : (mode =? DIGINET_SUM_BODY) || (mode =? DIGINET_SUM_ZERO) = true)
    by (destruct Hm as [E|E]; rewrite E; reflexivity).
  unfold diginet_frame_build. rewrite Em. cbn [negb].
  replace (DIGINET_MAX_BODY_LEN <? n) with false by (symmetry; apply Z.ltb_ge; lia).
  destruct (Z.eqb_spec (diginet_body_check bd n) DIGINET_OK); [contradiction | reflexivity].
Qed.

(* L2, the length side: a body past 1484 bytes *)
Theorem frame_build_too_long : forall cap dst src h bd n mode,
  DIGINET_MAX_BODY_LEN < n -> mode = DIGINET_SUM_BODY \/ mode = DIGINET_SUM_ZERO ->
  fst (diginet_frame_build cap dst src h bd n mode) = DIGINET_E_LENGTH.
Proof.
  intros cap dst src h bd n mode Hn Hm.
  assert (Em : (mode =? DIGINET_SUM_BODY) || (mode =? DIGINET_SUM_ZERO) = true)
    by (destruct Hm as [E|E]; rewrite E; reflexivity).
  unfold diginet_frame_build. rewrite Em. cbn [negb].
  replace (DIGINET_MAX_BODY_LEN <? n) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

(* and a buffer too short for a body it accepts *)
Theorem frame_build_no_space : forall cap dst src h bd n mode,
  0 <= n <= DIGINET_MAX_BODY_LEN -> diginet_body_check bd n = DIGINET_OK ->
  cap < Z.max 60 (30 + n) -> mode = DIGINET_SUM_BODY \/ mode = DIGINET_SUM_ZERO ->
  fst (diginet_frame_build cap dst src h bd n mode) = DIGINET_E_SPACE.
Proof.
  intros cap dst src h bd n mode Hn Hb Hc Hm.
  assert (Em : (mode =? DIGINET_SUM_BODY) || (mode =? DIGINET_SUM_ZERO) = true)
    by (destruct Hm as [E|E]; rewrite E; reflexivity).
  assert (Eo : (if DIGINET_BODY_OFFSET + n <? DIGINET_MIN_FRAME_LEN then DIGINET_MIN_FRAME_LEN
                else DIGINET_BODY_OFFSET + n) = Z.max 60 (30 + n))
    by (unfold DIGINET_BODY_OFFSET, DIGINET_MIN_FRAME_LEN; destruct (Z.ltb_spec (30 + n) 60); lia).
  unfold diginet_frame_build; cbv zeta. rewrite Em. cbn [negb].
  replace (DIGINET_MAX_BODY_LEN <? n) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite Hb, Z.eqb_refl. cbn [negb]. rewrite Eo.
  replace (cap <? Z.max 60 (30 + n)) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

(* ---- L7: spec_build_frame, then spec_read_frame ---- *)

Lemma spec_build_frame_layout : forall dst src send ack retry cmd ncmds body len zero_sum,
  0 <= len <= SPEC_MAX_BODY ->
  spec_build_frame dst src send ack retry cmd ncmds body len zero_sum =
  (Z.max 60 (30 + len),
   frame_layout dst src (16 + len) (if zero_sum =? 0 then spec_sum_at body 0 len else 0) send ack retry
     cmd ncmds body len (Z.to_nat (Z.max 60 (30 + len) - (30 + len)))).
Proof.
  intros dst src send ack retry cmd ncmds body len zero_sum Hl.
  assert (Eo : (if SPEC_BODY_AT + len <? SPEC_MIN_FRAME then SPEC_MIN_FRAME else SPEC_BODY_AT + len) =
               Z.max 60 (30 + len))
    by (unfold SPEC_BODY_AT, SPEC_MIN_FRAME; destruct (Z.ltb_spec (30 + len) 60); lia).
  assert (Eu : u32 (SPEC_HDR + len) = 16 + len)
    by (unfold u32, SPEC_HDR; unfold SPEC_MAX_BODY in Hl; apply Z.mod_small; lia).
  unfold spec_build_frame; cbv zeta. rewrite Eo, Eu.
  replace (Z.max 60 (30 + len) - SPEC_BODY_AT - len) with (Z.max 60 (30 + len) - (30 + len))
    by (unfold SPEC_BODY_AT; lia).
  reflexivity.
Qed.

(* L7. For len <= SPEC_MAX_BODY, spec_build_frame answers n = max (60, 30 + len) and writes n bytes,
   which spec_read_frame reads as a frame with these fields, the body, zeros after it, and the
   body's sum (zero_sum = 0, as build_and_receive passes, fuzz_transport.c:1031) or 0 *)
Theorem spec_build_frame_read_frame : forall dst src send ack retry cmd ncmds body len zero_sum,
  0 <= len <= SPEC_MAX_BODY -> 0 <= send < 2 ^ 32 -> 0 <= ack < 2 ^ 32 -> 0 <= retry < 2 ^ 16 ->
  fst (spec_build_frame dst src send ack retry cmd ncmds body len zero_sum) = Z.max 60 (30 + len) /\
  built_frame (snd (spec_build_frame dst src send ack retry cmd ncmds body len zero_sum))
    (Z.max 60 (30 + len)) dst src send ack retry cmd ncmds body len
    (if zero_sum =? 0 then spec_sum_at body 0 len else 0).
Proof.
  intros dst src send ack retry cmd ncmds body len zero_sum Hl Hs Ha Hr.
  rewrite (spec_build_frame_layout dst src send ack retry cmd ncmds body len zero_sum Hl).
  cbn [fst snd]. split; [reflexivity|].
  remember (Z.to_nat (Z.max 60 (30 + len) - (30 + len))) as pad eqn:Hpad.
  replace (Z.max 60 (30 + len)) with (30 + len + Z.of_nat pad) by lia.
  unfold SPEC_MAX_BODY in Hl.
  apply lnk_layout_built; try (unfold DIGINET_MAX_BODY_LEN; lia); try lia.
  destruct (zero_sum =? 0).
  - unfold spec_sum_at, u16. apply Z.mod_pos_bound. lia.
  - lia.
Qed.

(* ---- L3: diginet_body_check is the harness's system test ---- *)

(* F0 13 xx 70 at j *)
Definition sys_hit_at (b : list Z) (j : Z) : bool :=
  (byte_at b j =? 240) && (byte_at b (j + 1) =? 19) && (byte_at b (j + 3) =? 112).

(* diginet_codec.c:59-62's scan and spec.h:266-268's loop are the same loop *)
Lemma lnk_prefix_scan_loop : forall b len fuel i, 0 <= i ->
  system_prefix_scan b len i fuel = (0 <=? system_at_loop b len i fuel).
Proof.
  intros b len fuel. induction fuel as [|f IH]; intros i Hi;
    cbn [system_prefix_scan system_at_loop]; [reflexivity|].
  unfold DIGINET_SYSEX_MAKER, DIGINET_FN_SYSTEM, SPEC_MAKER, SPEC_FN_SYSTEM.
  destruct (i + 3 <? len); [|reflexivity].
  destruct ((byte_at b i =? 240) && (byte_at b (i + 1) =? 19) && (byte_at b (i + 3) =? 112)).
  - symmetry. apply Z.leb_le. exact Hi.
  - apply IH. lia.
Qed.

Lemma lnk_system_at_loop_hit : forall b len fuel i j, 0 <= i <= j -> j + 3 < len ->
  (Z.to_nat (j - i) < fuel)%nat -> sys_hit_at b j = true -> 0 <= system_at_loop b len i fuel.
Proof.
  intros b len fuel. induction fuel as [|f IH]; intros i j Hij Hj Hf Hh; [lia|].
  cbn [system_at_loop]. unfold SPEC_MAKER, SPEC_FN_SYSTEM.
  destruct (Z.ltb_spec (i + 3) len); [|lia].
  destruct ((byte_at b i =? 240) && (byte_at b (i + 1) =? 19) && (byte_at b (i + 3) =? 112)) eqn:E; [lia|].
  destruct (Z.eq_dec i j) as [->|Hne]; [unfold sys_hit_at in Hh; congruence|].
  apply (IH (i + 1) j); [lia | lia | lia | exact Hh].
Qed.

Lemma lnk_system_at_loop_found : forall b len fuel i, 0 <= system_at_loop b len i fuel ->
  exists j, i <= j /\ j + 3 < len /\ sys_hit_at b j = true.
Proof.
  intros b len fuel. induction fuel as [|f IH]; intros i H; cbn [system_at_loop] in H; [lia|].
  unfold SPEC_MAKER, SPEC_FN_SYSTEM in H.
  destruct (Z.ltb_spec (i + 3) len) as [L|L]; [|lia].
  destruct ((byte_at b i =? 240) && (byte_at b (i + 1) =? 19) && (byte_at b (i + 3) =? 112)) eqn:E.
  - exists i. split; [lia|]. split; [exact L | exact E].
  - destruct (IH (i + 1) H) as (j & H1 & H2 & H3). exists j. split; [lia|]. split; assumption.
Qed.

Lemma lnk_msg_channel_sysex_len : forall b c m0 st d run r m' c',
  msg_channel b c m0 st d run = (r, m', c') -> dm_sysex_len m' = dm_sysex_len m0.
Proof.
  intros b c m0 st d run r m' c' E. unfold msg_channel in E. cbv zeta in E.
  destruct (dc_len c <? d + channel_data_len st); [inversion E; reflexivity|].
  destruct (first_high b d 0 (Z.to_nat (channel_data_len st))); inversion E; reflexivity.
Qed.

(* a message diginet_msg_next returns with a payload of 3 bytes or more is a sysex F0 .. F7 that
   starts at the cursor and whose F7 is at least 4 bytes further *)
Lemma lnk_msg_next_sysex : forall b c m r m' c', diginet_msg_next b c m = (r, m', c') -> r = 1 ->
  3 <= dm_sysex_len m' ->
  dc_pos c + 3 < dc_len c /\ byte_at b (dc_pos c) = 240 /\ dm_sysex m' = dc_pos c + 1.
Proof.
  intros b c m r m' c' E Hr Hs. unfold diginet_msg_next in E; cbv zeta in E.
  destruct (dc_len c <=? dc_pos c); [inversion E; subst; discriminate|].
  destruct (Z.eqb_spec (byte_at b (dc_pos c)) 240) as [Hf|Hf].
  - destruct (Z.leb_spec (dc_len c)
                (msg_scan_f7 b (dc_len c) (dc_pos c + 1) (Z.to_nat (dc_len c - (dc_pos c + 1))))) as [L|L].
    + inversion E; subst. discriminate.
    + inversion E; subst. cbn [dm_sysex_len dm_sysex] in *. split; [lia|]. split; [exact Hf | reflexivity].
  - destruct (negb (Z.land (byte_at b (dc_pos c)) 128 =? 0)).
    + destruct (240 <=? byte_at b (dc_pos c)).
      * inversion E; subst. cbn in Hs. lia.
      * apply lnk_msg_channel_sysex_len in E. rewrite E in Hs. cbn in Hs. lia.
    + destruct (dc_status c =? 0).
      * inversion E; subst. cbn in Hs. lia.
      * apply lnk_msg_channel_sysex_len in E. rewrite E in Hs. cbn in Hs. lia.
Qed.

Lemma lnk_body_check_loop_hit : forall fuel b c m, 0 <= dc_pos c ->
  body_check_loop b c m fuel = Some true -> exists j, 0 <= j /\ j + 3 < dc_len c /\ sys_hit_at b j = true.
Proof.
  induction fuel as [|f IH]; intros b c m Hp H; cbn [body_check_loop] in H; [discriminate H|].
  destruct (diginet_msg_next b c m) as [[r m'] c'] eqn:E.
  pose proof (diginet_msg_next_progress b c m Hp) as P. rewrite E in P. cbn [moves] in P.
  destruct (r =? 0) eqn:R0; [discriminate H|].
  destruct ((r =? 1) && (dm_status m' =? 240) && (3 <=? dm_sysex_len m') &&
            (byte_at b (dm_sysex m') =? DIGINET_SYSEX_MAKER) &&
            (byte_at b (dm_sysex m' + 2) =? DIGINET_FN_SYSTEM)) eqn:C.
  - rewrite !andb_true_iff in C. destruct C as [[[[C1 C2] C3] C4] C5].
    apply Z.eqb_eq in C1. apply Z.leb_le in C3. apply Z.eqb_eq in C4, C5.
    destruct (lnk_msg_next_sysex b c m r m' c' E C1 C3) as (H1 & H2 & H3).
    exists (dc_pos c). split; [exact Hp|]. split; [exact H1|].
    unfold sys_hit_at. rewrite H3 in C4, C5.
    replace (dc_pos c + 1 + 2) with (dc_pos c + 3) in C5 by lia.
    rewrite H2, C4, C5. reflexivity.
  - apply Z.eqb_neq in R0. destruct P as [[P1 _]|(_ & P2 & P3)]; [contradiction|].
    destruct (IH b c' m' ltac:(lia) H) as (j & J1 & J2 & J3).
    exists j. split; [exact J1|]. rewrite <- P2. split; assumption.
Qed.

(* the cursor loop of diginet_body_check refuses only what its prefix scan refuses too *)
Lemma diginet_body_check_scan : forall b len,
  diginet_body_check b len =
  if system_prefix_scan b len 0 (Z.to_nat len) then DIGINET_E_REFUSED else DIGINET_OK.
Proof.
  intros b len. unfold diginet_body_check.
  destruct (body_check_loop b (diginet_cursor_init len) dgn_msg_zero (S (Z.to_nat len))) as [[|]|] eqn:E;
    try reflexivity.
  pose proof (lnk_body_check_loop_hit (S (Z.to_nat len)) b (diginet_cursor_init len) dgn_msg_zero
                ltac:(cbn; lia) E) as (j & J1 & J2 & J3).
  cbn [diginet_cursor_init dc_len] in J2.
  rewrite lnk_prefix_scan_loop by lia.
  replace (0 <=? system_at_loop b len 0 (Z.to_nat len)) with true; [reflexivity|].
  symmetry. apply Z.leb_le. apply (lnk_system_at_loop_hit b len (Z.to_nat len) 0 j); [lia | lia | lia | exact J3].
Qed.

(* L3. diginet_body_check accepts exactly the bodies in which spec_system_at finds no F0 13 xx 70, and
   answers DIGINET_OK or DIGINET_E_REFUSED, for every list and length *)
Theorem body_check_system_at : forall b n,
  (diginet_body_check b n = DIGINET_OK <-> spec_system_at b n < 0) /\
  (diginet_body_check b n = DIGINET_OK \/ diginet_body_check b n = DIGINET_E_REFUSED).
Proof.
  intros b n. rewrite diginet_body_check_scan, lnk_prefix_scan_loop by lia. unfold spec_system_at.
  destruct (Z.leb_spec 0 (system_at_loop b n 0 (Z.to_nat n))) as [L|L].
  - split; [split; [intros H; discriminate H | intros H; lia] | right; reflexivity].
  - split; [split; [intros _; exact L | intros _; reflexivity] | left; reflexivity].
Qed.

(* L3, the prefix: no F0 13 xx 70 in the first n bytes, none in the first k <= n *)
Theorem spec_system_at_prefix : forall b n, spec_system_at b n < 0 ->
  forall k, 0 <= k <= n -> spec_system_at b k < 0.
Proof.
  intros b n Hn k Hk. unfold spec_system_at in *.
  destruct (Z_lt_le_dec (system_at_loop b k 0 (Z.to_nat k)) 0) as [L|L]; [exact L|exfalso].
  destruct (lnk_system_at_loop_found b k (Z.to_nat k) 0 L) as (j & H1 & H2 & H3).
  pose proof (lnk_system_at_loop_hit b n (Z.to_nat n) 0 j ltac:(lia) ltac:(lia) ltac:(lia) H3). lia.
Qed.

Lemma lnk_system_at_loop_ext : forall b1 b2 len fuel i, 0 <= i ->
  (forall k, 0 <= k < len -> byte_at b1 k = byte_at b2 k) ->
  system_at_loop b1 len i fuel = system_at_loop b2 len i fuel.
Proof.
  intros b1 b2 len fuel. induction fuel as [|f IH]; intros i Hi H; cbn [system_at_loop]; [reflexivity|].
  destruct (Z.ltb_spec (i + 3) len); [|reflexivity].
  rewrite (H i), (H (i + 1)), (H (i + 3)) by lia. rewrite (IH (i + 1) ltac:(lia) H). reflexivity.
Qed.

(* spec_system_at (b, n) reads b[0 .. n) only *)
Theorem spec_system_at_ext : forall b1 b2 n, (forall k, 0 <= k < n -> byte_at b1 k = byte_at b2 k) ->
  spec_system_at b1 n = spec_system_at b2 n.
Proof. intros b1 b2 n H. unfold spec_system_at. apply lnk_system_at_loop_ext; [lia | exact H]. Qed.

Lemma byte_at_skipn : forall l k i, 0 <= k -> 0 <= i -> byte_at (skipn (Z.to_nat k) l) i = byte_at l (k + i).
Proof. intros l k i Hk Hi. unfold byte_at. rewrite nth_skipn. f_equal. lia. Qed.

(* check_sent_frame's system test (fuzz_transport.c:406) on a frame the library builds: the n body
   bytes from 30 hold no F0 13 xx 70 *)
Corollary frame_build_no_system : forall cap dst src h bd n mode,
  0 <= n <= DIGINET_MAX_BODY_LEN -> diginet_body_check bd n = DIGINET_OK ->
  Z.max 60 (30 + n) <= cap -> mode = DIGINET_SUM_BODY \/ mode = DIGINET_SUM_ZERO ->
  0 <= dh_send_counter h < 2 ^ 32 -> 0 <= dh_ack_counter h < 2 ^ 32 -> 0 <= dh_retry h < 2 ^ 16 ->
  spec_system_at (skipn 30 (snd (diginet_frame_build cap dst src h bd n mode))) n < 0.
Proof.
  intros cap dst src h bd n mode Hn Hb Hc Hm Hs Ha Hr.
  destruct (frame_build_read_frame cap dst src h bd n mode Hn Hb Hc Hm Hs Ha Hr) as (_ & Hf).
  destruct Hf as (_ & _ & _ & _ & Hbody & _).
  rewrite (spec_system_at_ext _ bd n).
  - exact (proj1 (proj1 (body_check_system_at bd n)) Hb).
  - intros k Hk. change 30%nat with (Z.to_nat 30). rewrite byte_at_skipn by lia. apply Hbody. lia.
Qed.

(* ---- L4: diginet_announce_parse ---- *)

Lemma lnk_strz_len_loop_range : forall b p fuel n, 0 <= n <= 9 -> n <= strz_len_loop b p n fuel <= 9.
Proof.
  intros b p fuel. induction fuel as [|f IH]; intros n Hn; cbn [strz_len_loop]; [lia|].
  unfold SPEC_ANN_FIELD. destruct (Z.ltb_spec n 9); cbn [andb]; [|lia].
  destruct (negb (byte_at b (p + n) =? 0)); [specialize (IH (n + 1) ltac:(lia)); lia | lia].
Qed.

Lemma lnk_strz_len_loop_nz : forall b p fuel n j, n <= j < strz_len_loop b p n fuel -> byte_at b (p + j) <> 0.
Proof.
  intros b p fuel. induction fuel as [|f IH]; intros n j Hj; cbn [strz_len_loop] in Hj; [lia|].
  destruct ((n <? SPEC_ANN_FIELD) && negb (byte_at b (p + n) =? 0)) eqn:E; [|lia].
  destruct (Z.eq_dec j n) as [->|Hne].
  - apply andb_true_iff in E. destruct E as [_ E]. apply negb_true_iff, Z.eqb_neq in E. exact E.
  - apply (IH (n + 1)). lia.
Qed.

Lemma lnk_strz_range : forall b p, 0 <= spec_strz_len b p <= 9.
Proof. intros b p. exact (lnk_strz_len_loop_range b p 9 0 ltac:(lia)). Qed.

Lemma lnk_strz_nz : forall b p j, 0 <= j < spec_strz_len b p -> byte_at b (p + j) <> 0.
Proof. intros b p j Hj. exact (lnk_strz_len_loop_nz b p 9 0 j Hj). Qed.

Lemma lnk_copy_stop : forall dst i j (v : Z), 0 <= i <= 9 -> 0 <= j -> (10 <= length dst)%nat ->
  byte_at (list_set dst (Z.to_nat i) 0) j =
  if (i <=? j) && (j <? i) then v else if j =? i then 0 else byte_at dst j.
Proof.
  intros dst i j v Hi Hj Hd. rewrite lnk_byte_at_list_set by lia.
  replace ((i <=? j) && (j <? i)) with false
    by (destruct (Z.leb_spec i j), (Z.ltb_spec j i); try reflexivity; lia).
  reflexivity.
Qed.

Lemma lnk_copy_strz_loop_at : forall fuel dst b p i j, 0 <= i <= 9 -> 0 <= j -> (10 <= length dst)%nat ->
  byte_at (copy_strz_loop dst b p 9 10 i fuel) j =
  if (i <=? j) && (j <? strz_len_loop b p i fuel) then byte_at b (p + j)
  else if j =? strz_len_loop b p i fuel then 0 else byte_at dst j.
Proof.
  induction fuel as [|f IH]; intros dst b p i j Hi Hj Hd; cbn [copy_strz_loop strz_len_loop].
  - apply lnk_copy_stop; assumption.
  - unfold SPEC_ANN_FIELD.
    replace (i + 1 <? 10) with (i <? 9)
      by (destruct (Z.ltb_spec (i + 1) 10), (Z.ltb_spec i 9); try reflexivity; lia).
    destruct (Z.ltb_spec i 9) as [Hi9|Hi9]; cbn [andb].
    + destruct (byte_at b (p + i) =? 0) eqn:Hz; cbn [negb].
      * apply lnk_copy_stop; assumption.
      * pose proof (lnk_strz_len_loop_range b p f (i + 1) ltac:(lia)) as R.
        rewrite IH by (rewrite ?lnk_length_list_set; lia).
        rewrite lnk_byte_at_list_set by lia.
        destruct (Z.eqb_spec j i) as [->|Hne].
        -- replace ((i + 1 <=? i) && (i <? strz_len_loop b p (i + 1) f)) with false
             by (destruct (Z.leb_spec (i + 1) i); [lia | reflexivity]).
           replace ((i <=? i) && (i <? strz_len_loop b p (i + 1) f)) with true
             by (destruct (Z.leb_spec i i), (Z.ltb_spec i (strz_len_loop b p (i + 1) f)); try reflexivity; lia).
           destruct (Z.eqb_spec i (strz_len_loop b p (i + 1) f)); [lia | reflexivity].
        -- replace (i + 1 <=? j) with (i <=? j)
             by (destruct (Z.leb_spec (i + 1) j), (Z.leb_spec i j); try reflexivity; lia).
           reflexivity.
    + apply lnk_copy_stop; assumption.
Qed.

(* the field copy_strz (dst, 10, b + p, 9) leaves: b's bytes before spec_strz_len's NUL, the NUL,
   then dst's bytes *)
Lemma copy_strz_z_at : forall dst b p j, (10 <= length dst)%nat -> 0 <= j ->
  byte_at (copy_strz_z dst 10 b p 9) j =
  if j <? spec_strz_len b p then byte_at b (p + j)
  else if j =? spec_strz_len b p then 0 else byte_at dst j.
Proof.
  intros dst b p j Hd Hj. unfold copy_strz_z, spec_strz_len. change (Z.to_nat 9) with 9%nat.
  rewrite lnk_copy_strz_loop_at by lia. destruct (Z.leb_spec 0 j); [reflexivity | lia].
Qed.

Lemma lnk_length_copy_strz_loop : forall fuel dst b p n ds i,
  length (copy_strz_loop dst b p n ds i fuel) = length dst.
Proof.
  induction fuel as [|f IH]; intros dst b p n ds i; cbn [copy_strz_loop].
  - apply lnk_length_list_set.
  - destruct ((i <? n) && (i + 1 <? ds) && negb (byte_at b (p + i) =? 0));
      [rewrite IH|]; apply lnk_length_list_set.
Qed.

Lemma length_copy_strz_z : forall dst b p, length (copy_strz_z dst 10 b p 9) = length dst.
Proof. intros dst b p. apply lnk_length_copy_strz_loop. Qed.

(* the field the harness checks (fuzz_transport.c:544-556): with k = spec_strz_len b p <= 9, the
   first k bytes of fld are b[p .. p + k) and byte k is the NUL *)
Definition strz_field (fld b : list Z) (p : Z) : Prop :=
  0 <= spec_strz_len b p <= SPEC_ANN_FIELD /\
  (forall i, 0 <= i < spec_strz_len b p -> byte_at fld i = byte_at b (p + i)) /\
  byte_at fld (spec_strz_len b p) = 0.

Lemma strz_field_copy : forall dst b p, (10 <= length dst)%nat -> strz_field (copy_strz_z dst 10 b p 9) b p.
Proof.
  intros dst b p Hd. pose proof (lnk_strz_range b p) as R. unfold strz_field.
  split; [unfold SPEC_ANN_FIELD; lia|]. split.
  - intros i Hi. rewrite copy_strz_z_at by lia. destruct (Z.ltb_spec i (spec_strz_len b p)); [reflexivity | lia].
  - rewrite copy_strz_z_at by lia. rewrite Z.ltb_irrefl, Z.eqb_refl. reflexivity.
Qed.

(* L4. For a frame whose command is e0 or e1, diginet_announce_parse accepts exactly a body of 33
   bytes or more; then unknown is the body, unknown_len 15, and version and name hold the strings
   spec_strz_len reads at body + 15 and body + 24, each followed by its NUL. *)
Theorem announce_parse_strz : forall b f a,
  (dh_cmd (df_h f) = SPEC_CMD_E0 \/ dh_cmd (df_h f) = SPEC_CMD_E1) ->
  (10 <= length (da_version a))%nat -> (10 <= length (da_name a))%nat ->
  (fst (diginet_announce_parse b f a) = DIGINET_OK <-> SPEC_ANN_MIN <= df_body_len f) /\
  (SPEC_ANN_MIN <= df_body_len f ->
   da_unknown (snd (diginet_announce_parse b f a)) = df_body f /\
   da_unknown_len (snd (diginet_announce_parse b f a)) = SPEC_ANN_UNKNOWN /\
   strz_field (da_version (snd (diginet_announce_parse b f a))) b (df_body f + SPEC_ANN_VERSION) /\
   strz_field (da_name (snd (diginet_announce_parse b f a))) b (df_body f + SPEC_ANN_NAME)).
Proof.
  intros b f a Hc Hv Hn.
  assert (C : negb ((dh_cmd (df_h f) =? DIGINET_CMD_ANNOUNCE) ||
                    (dh_cmd (df_h f) =? DIGINET_CMD_ANNOUNCE_SESSION)) = false)
    by (destruct Hc as [E|E]; rewrite E; reflexivity).
  unfold diginet_announce_parse. rewrite C. unfold SPEC_ANN_MIN.
  destruct (Z.ltb_spec (df_body_len f) 33) as [Hl|Hl]; cbn [fst snd da_unknown da_unknown_len da_version da_name].
  - split; [split; [intros H; discriminate H | lia] | intros H; lia].
  - split; [split; [intros _; lia | intros _; reflexivity]|]. intros _.
    split; [reflexivity|]. split; [reflexivity|]. split; apply strz_field_copy; assumption.
Qed.

(* L4 as stated, for the frame diginet_frame_parse gives on a buffer spec_read_frame accepts *)
Corollary announce_parse_frame : forall b len f0 a,
  sf_code (spec_read_frame b len) = SPEC_OK ->
  (sf_cmd (spec_read_frame b len) = SPEC_CMD_E0 \/ sf_cmd (spec_read_frame b len) = SPEC_CMD_E1) ->
  (10 <= length (da_version a))%nat -> (10 <= length (da_name a))%nat ->
  (fst (diginet_announce_parse b (snd (diginet_frame_parse b len f0)) a) = DIGINET_OK <->
   SPEC_ANN_MIN <= sf_body_len (spec_read_frame b len)) /\
  (SPEC_ANN_MIN <= sf_body_len (spec_read_frame b len) ->
   da_unknown (snd (diginet_announce_parse b (snd (diginet_frame_parse b len f0)) a)) =
     sf_body (spec_read_frame b len) /\
   da_unknown_len (snd (diginet_announce_parse b (snd (diginet_frame_parse b len f0)) a)) = SPEC_ANN_UNKNOWN /\
   strz_field (da_version (snd (diginet_announce_parse b (snd (diginet_frame_parse b len f0)) a))) b
     (sf_body (spec_read_frame b len) + SPEC_ANN_VERSION) /\
   strz_field (da_name (snd (diginet_announce_parse b (snd (diginet_frame_parse b len f0)) a))) b
     (sf_body (spec_read_frame b len) + SPEC_ANN_NAME)).
Proof.
  intros b len f0 a Hc Hcmd Hv Hn.
  destruct (frame_parse_read_frame b len f0) as (_ & A & _). specialize (A Hc).
  destruct A as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Acmd & _ & Abody & Alen & _).
  rewrite <- Acmd in Hcmd. rewrite <- Abody, <- Alen.
  apply announce_parse_strz; assumption.
Qed.

(* ---- L5: diginet_personality_from_name against desk_named ---- *)

Lemma lnk_strcmp_eq : forall x y kx ky fuel i, 0 <= i <= kx -> i <= ky ->
  (forall j, i <= j < kx -> byte_at x j <> 0) -> byte_at x kx = 0 ->
  (forall j, i <= j < ky -> byte_at y j <> 0) -> byte_at y ky = 0 ->
  (Z.to_nat (Z.min kx ky - i) < fuel)%nat ->
  (strcmp_eq x y i fuel = true <-> kx = ky /\ forall j, i <= j < kx -> byte_at x j = byte_at y j).
Proof.
  intros x y kx ky fuel. induction fuel as [|f IH]; intros i Hi Hiy Hx Hxk Hy Hyk Hf; [lia|].
  cbn [strcmp_eq].
  destruct (Z.eqb_spec (byte_at x i) (byte_at y i)) as [E|E]; cbn [negb].
  - destruct (Z.eqb_spec (byte_at x i) 0) as [Z0|Z0].
    + assert (Ex : i = kx).
      { destruct (Z.eq_dec i kx) as [|Ne]; [assumption | exfalso; apply (Hx i); [lia | exact Z0]]. }
      assert (Ey : i = ky).
      { destruct (Z.eq_dec i ky) as [|Ne]; [assumption | exfalso; apply (Hy i); [lia | rewrite <- E; exact Z0]]. }
      subst kx ky. split; [intros _; split; [reflexivity | intros j Hj; lia] | intros _; reflexivity].
    + assert (Lx : i < kx) by (destruct (Z.eq_dec i kx) as [<-|]; [contradiction | lia]).
      assert (Ly : i < ky) by (destruct (Z.eq_dec i ky) as [<-|]; [rewrite <- E in Hyk; contradiction | lia]).
      specialize (IH (i + 1) ltac:(lia) ltac:(lia) ltac:(intros j Hj; apply Hx; lia) Hxk
                    ltac:(intros j Hj; apply Hy; lia) Hyk ltac:(lia)).
      rewrite IH. split.
      * intros [Hk Hj]. split; [exact Hk|]. intros j Hj'.
        destruct (Z.eq_dec j i) as [->|]; [exact E | apply Hj; lia].
      * intros [Hk Hj]. split; [exact Hk|]. intros j Hj'. apply Hj. lia.
  - split; [intros H; discriminate H|]. intros [Hk Hj]. exfalso.
    destruct (Z.eq_dec i kx) as [<-|Hne].
    + subst ky. apply E. rewrite Hxk, Hyk. reflexivity.
    + apply E. apply Hj. lia.
Qed.

(* strcmp of the copied name with a desk name s (no NUL in it, then its NUL) is desk_named's test *)
Lemma lnk_name_check_at : forall b p old s, (10 <= length old)%nat ->
  (forall j, 0 <= j < Z.of_nat (length s) -> byte_at s j <> 0) ->
  strcmp_eq (copy_strz_z old 10 b p 9) (s ++ [0]) 0 (S (length s)) =
  (spec_strz_len b p =? Z.of_nat (length s)) && bytes_eq_at b p s (spec_strz_len b p).
Proof.
  intros b p old s Hold Hs.
  pose proof (lnk_strz_range b p) as R.
  assert (Nm : forall j, 0 <= j < spec_strz_len b p -> byte_at (copy_strz_z old 10 b p 9) j = byte_at b (p + j)).
  { intros j Hj. rewrite copy_strz_z_at by lia. destruct (Z.ltb_spec j (spec_strz_len b p)); [reflexivity | lia]. }
  assert (Nk : byte_at (copy_strz_z old 10 b p 9) (spec_strz_len b p) = 0).
  { rewrite copy_strz_z_at by lia. rewrite Z.ltb_irrefl, Z.eqb_refl. reflexivity. }
  assert (Ys : forall j, 0 <= j < Z.of_nat (length s) -> byte_at (s ++ [0]) j = byte_at s j)
    by (intros j Hj; apply lnk_byte_at_app_l; lia).
  assert (Yk : byte_at (s ++ [0]) (Z.of_nat (length s)) = 0)
    by (rewrite lnk_byte_at_app_r by lia; rewrite Z.sub_diag; reflexivity).
  apply Bool.eq_true_iff_eq.
  rewrite (lnk_strcmp_eq (copy_strz_z old 10 b p 9) (s ++ [0]) (spec_strz_len b p) (Z.of_nat (length s))
             (S (length s)) 0);
    [ | lia | lia | intros j Hj; rewrite Nm by lia; apply lnk_strz_nz; lia | exact Nk
      | intros j Hj; rewrite Ys by lia; apply Hs; lia | exact Yk | lia ].
  rewrite andb_true_iff, Z.eqb_eq, lnk_bytes_eq_at_true by lia.
  split; intros [Hk Hj]; (split; [exact Hk|]); intros j Hj'.
  - rewrite <- Nm by lia. rewrite Hj by lia. apply Ys. lia.
  - rewrite Nm by lia. rewrite Hj by lia. symmetry. apply Ys. lia.
Qed.

Lemma lnk_from_name_cases : forall name, diginet_personality_from_name name =
  if strcmp_eq name (spec_c24_name ++ [0]) 0 (S (length spec_c24_name)) then Some 0
  else if strcmp_eq name (spec_pc_name ++ [0]) 0 (S (length spec_pc_name)) then Some 1 else None.
Proof. reflexivity. Qed.

Lemma lnk_from_name_range : forall name i, diginet_personality_from_name name = Some i -> i = 0 \/ i = 1.
Proof.
  intros name i. rewrite lnk_from_name_cases.
  destruct (strcmp_eq name (spec_c24_name ++ [0]) 0 (S (length spec_c24_name)));
    [intros H; injection H as <-; left; reflexivity|].
  destruct (strcmp_eq name (spec_pc_name ++ [0]) 0 (S (length spec_pc_name)));
    [intros H; injection H as <-; right; reflexivity | intros H; discriminate H].
Qed.

(* L5. The name the library reads from an announce (copy_strz of 9 bytes at body + 24 into a field
   of 10, diginet_frame.c:149) selects through diginet_personality_from_name the desk desk_named
   selects: the personality pointer is NULL exactly when desk_named is None, and otherwise the
   entry it points to is that desk. *)
Theorem personality_from_name_desk : forall b body old, (10 <= length old)%nat ->
  option_map desk_of_personality
    (match diginet_personality_from_name (copy_strz_z old 10 b (body + SPEC_ANN_NAME) 9) with
     | Some i => personality_at i | None => None end) = desk_named b body.
Proof.
  intros b body old Hold. rewrite lnk_from_name_cases.
  rewrite !lnk_name_check_at by (first [exact Hold | apply lnk_no_nul; vm_compute; reflexivity]).
  unfold desk_named, desk_name_is.
  destruct ((spec_strz_len b (body + SPEC_ANN_NAME) =? Z.of_nat (length spec_c24_name)) &&
            bytes_eq_at b (body + SPEC_ANN_NAME) spec_c24_name (spec_strz_len b (body + SPEC_ANN_NAME)));
    [reflexivity|].
  destruct ((spec_strz_len b (body + SPEC_ANN_NAME) =? Z.of_nat (length spec_pc_name)) &&
            bytes_eq_at b (body + SPEC_ANN_NAME) spec_pc_name (spec_strz_len b (body + SPEC_ANN_NAME)));
    reflexivity.
Qed.

(* L5 as stated: a personality exactly when a desk, and then the same device and strips *)
Corollary personality_from_name_desk_fields : forall b body old, (10 <= length old)%nat ->
  ((exists i, diginet_personality_from_name (copy_strz_z old 10 b (body + SPEC_ANN_NAME) 9) = Some i) <->
   (exists d, desk_named b body = Some d)) /\
  (forall i d, diginet_personality_from_name (copy_strz_z old 10 b (body + SPEC_ANN_NAME) 9) = Some i ->
   desk_named b body = Some d ->
   exists pr, personality_at i = Some pr /\ dp_device pr = d_dev d /\ dp_strips pr = d_strips d).
Proof.
  intros b body old Hold. pose proof (personality_from_name_desk b body old Hold) as M. revert M.
  destruct (diginet_personality_from_name (copy_strz_z old 10 b (body + SPEC_ANN_NAME) 9)) as [i|] eqn:E;
    intros M.
  - pose proof (lnk_from_name_range _ i E) as Hi.
    assert (P : exists pr, personality_at i = Some pr) by (destruct Hi as [->| ->]; eexists; reflexivity).
    destruct P as [pr Pr]. rewrite Pr in M. cbn [option_map] in M.
    split.
    + split; [intros _; exists (desk_of_personality pr); symmetry; exact M | intros _; exists i; reflexivity].
    + intros i' d Hi' Hd. injection Hi' as <-. exists pr. split; [exact Pr|].
      rewrite Hd in M. injection M as <-. split; reflexivity.
  - cbn [option_map] in M. split.
    + split; [intros [i Hi]; discriminate Hi | intros [d Hd]; rewrite Hd in M; discriminate M].
    + intros i d Hi. discriminate Hi.
Qed.

(* L4 then L5, as on_announce calls them (diginet_session.c:187-191): the name the parse leaves in
   a.name selects the desk desk_named selects *)
Corollary announce_personality_desk : forall b f a,
  (dh_cmd (df_h f) = SPEC_CMD_E0 \/ dh_cmd (df_h f) = SPEC_CMD_E1) -> SPEC_ANN_MIN <= df_body_len f ->
  (10 <= length (da_name a))%nat ->
  option_map desk_of_personality
    (match diginet_personality_from_name (da_name (snd (diginet_announce_parse b f a))) with
     | Some i => personality_at i | None => None end) = desk_named b (df_body f).
Proof.
  intros b f a Hc Hl Hn.
  assert (C : negb ((dh_cmd (df_h f) =? DIGINET_CMD_ANNOUNCE) ||
                    (dh_cmd (df_h f) =? DIGINET_CMD_ANNOUNCE_SESSION)) = false)
    by (destruct Hc as [E|E]; rewrite E; reflexivity).
  unfold diginet_announce_parse. rewrite C. unfold SPEC_ANN_MIN in Hl.
  replace (df_body_len f <? 33) with false by (symmetry; apply Z.ltb_ge; lia).
  cbn [snd da_name]. apply personality_from_name_desk. exact Hn.
Qed.

(* ---- L6: keepalive and OUI ---- *)

Theorem frame_is_keepalive_iff : forall b f,
  diginet_frame_is_keepalive b f = 1 <->
  dh_cmd (df_h f) = SPEC_CMD_DATA /\ df_body_len f = 1 /\ byte_at b (df_body f) = 0.
Proof.
  intros b f. unfold diginet_frame_is_keepalive.
  rewrite lnk_int_of_bool_1, !andb_true_iff, !Z.eqb_eq. unfold DIGINET_CMD_DATA, SPEC_CMD_DATA. tauto.
Qed.

Theorem mac_is_digidesign_iff : forall mac,
  diginet_mac_is_digidesign mac = 1 <-> byte_at mac 0 = 0x00 /\ byte_at mac 1 = 0xa0 /\ byte_at mac 2 = 0x7e.
Proof.
  intros mac. unfold diginet_mac_is_digidesign.
  rewrite lnk_int_of_bool_1, !andb_true_iff, !Z.eqb_eq. unfold DIGINET_OUI_0, DIGINET_OUI_1, DIGINET_OUI_2. tauto.
Qed.

(* memcmp (mac, SPEC_OUI, 3) == 0, as the harness tests it (fuzz_transport.c:294) *)
Theorem mac_is_digidesign_memcmp : forall mac,
  diginet_mac_is_digidesign mac = 1 <-> forall k, 0 <= k < 3 -> byte_at mac k = byte_at SPEC_OUI k.
Proof.
  intros mac. rewrite mac_is_digidesign_iff. split.
  - intros (E0 & E1 & E2) k Hk. assert (C : k = 0 \/ k = 1 \/ k = 2) by lia.
    destruct C as [-> | [-> | ->]]; assumption.
  - intros H. split; [exact (H 0 ltac:(lia))|]. split; [exact (H 1 ltac:(lia)) | exact (H 2 ltac:(lia))].
Qed.

(* the source MAC the library copies (diginet_frame.c:76) against the bytes at sf_src *)
Corollary mac_is_digidesign_src : forall b len f0, sf_code (spec_read_frame b len) = SPEC_OK ->
  (diginet_mac_is_digidesign (df_src (snd (diginet_frame_parse b len f0))) = 1 <->
   forall k, 0 <= k < 3 -> byte_at b (sf_src (spec_read_frame b len) + k) = byte_at SPEC_OUI k).
Proof.
  intros b len f0 Hc. destruct (frame_parse_read_frame b len f0) as (_ & A & _). specialize (A Hc).
  destruct A as (_ & Hs & _ & _ & Hsrc & _). rewrite mac_is_digidesign_memcmp, Hsrc, Hs.
  split; intros H k Hk; specialize (H k Hk); rewrite lnk_byte_at_map_zseq in * by lia; exact H.
Qed.

(* ---- the list Z reading against the list byte reading of DgnSpec.v and DgnLib.v ---- *)

Lemma lnk_byte_at_map_bz : forall bb i, byte_at (map bz bb) (Z.of_nat i) = at8 bb i.
Proof.
  intros bb i. destruct (Nat.lt_ge_cases i (length bb)) as [L|L].
  - exact (holds_body_map bb i L).
  - unfold byte_at, at8. rewrite Nat2Z.id. rewrite !nth_overflow by (rewrite ?length_map; lia).
    symmetry. apply bz_b8. lia.
Qed.

Lemma lnk_bz_b8 : forall z, bz (b8 z) = z mod 256.
Proof. intros z. unfold bz, b8. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. reflexivity. Qed.

Lemma lnk_put16_wr16 : forall v, map bz (put16 v) = wr16 v.
Proof.
  intros v. unfold put16, wr16, u8. cbn [map]. rewrite !lnk_bz_b8, !Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma lnk_put32_wr32 : forall v, map bz (put32 v) = wr32 v.
Proof.
  intros v. unfold put32, wr32, u8. cbn [map]. rewrite !lnk_bz_b8, !Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma lnk_sum16_map_bz : forall body, diginet_sum16 (map bz body) 0 (Z.of_nat (length body)) = lib_sum16 body.
Proof.
  intros body. rewrite diginet_sum16_spec_sum_at, lib_sum16_eq. unfold spec_sum_at, sum16. rewrite Nat2Z.id.
  change (spec_sum_loop (map bz body) 0 0 0 (length body))
    with (spec_sum_loop (map bz body) (Z.of_nat 0) 0 (Z.of_nat 0) (length body)).
  rewrite (lk_sum_loop (map bz body) body (holds_body_map body) (length body) 0 0 0) by lia.
  cbn [Nat.add skipn]. rewrite firstn_all, Z.add_0_l. unfold u16. change 65536 with (2 ^ 16). apply Zmod_mod.
Qed.

(* the bytes of map bz bb from k, n of them, are map bz of firstn n (skipn k bb) *)
Lemma lnk_map_byte_at_window : forall bb k n, (k + n <= length bb)%nat ->
  map (fun j => byte_at (map bz bb) (Z.of_nat k + j)) (zseq n) = map bz (firstn n (skipn k bb)).
Proof.
  intros bb k n H. apply nth_ext with (d := 0) (d' := 0).
  - rewrite !length_map, lnk_length_zseq, length_firstn, length_skipn. lia.
  - intros i Hi. rewrite length_map, lnk_length_zseq in Hi.
    symmetry.
    rewrite (nth_indep _ 0 (bz (b8 0))) by (rewrite length_map, length_firstn, length_skipn; lia).
    rewrite map_nth. symmetry.
    transitivity (byte_at (map (fun j => byte_at (map bz bb) (Z.of_nat k + j)) (zseq n)) (Z.of_nat i));
      [unfold byte_at; rewrite Nat2Z.id; reflexivity|].
    rewrite lnk_byte_at_map_zseq by lia. cbv beta.
    rewrite <- Nat2Z.inj_add, lnk_byte_at_map_bz. unfold at8.
    rewrite nth_firstn. destruct (Nat.ltb_spec i n); [|lia]. rewrite nth_skipn. reflexivity.
Qed.

(* diginet_frame_parse over map bz bb, all of it, is fuzz_frame's fr_ reading of bb *)
Definition parse_fr (f : dgn_frame) (bb : list byte) : Prop :=
  df_dst f = map bz (fr_dst bb) /\ df_src f = map bz (fr_src bb) /\
  df_ethertype f = fr_ethertype bb /\ dh_numbytes (df_h f) = fr_numbytes bb /\ dh_sum (df_h f) = fr_sum bb /\
  dh_send_counter (df_h f) = fr_send bb /\ dh_ack_counter (df_h f) = fr_ack bb /\
  dh_retry (df_h f) = fr_retry bb /\ dh_cmd (df_h f) = fr_cmd bb /\ dh_num_commands (df_h f) = fr_ncmds bb /\
  df_body f = 30 /\ df_body_len f = fr_body_len bb /\ df_pad_len f = fr_pad_len bb /\
  df_body_sum f = fr_body_sum bb /\ df_sum_matches f = int_of_bool (fr_body_sum bb =? fr_sum bb).

Corollary frame_parse_fr : forall bb f0,
  fst (diginet_frame_parse (map bz bb) (Z.of_nat (length bb)) f0) = fr_code bb /\
  (fr_code bb = 0 -> parse_fr (snd (diginet_frame_parse (map bz bb) (Z.of_nat (length bb)) f0)) bb).
Proof.
  intros bb f0.
  destruct (frame_parse_read_frame (map bz bb) (Z.of_nat (length bb)) f0) as (C & A & _).
  destruct (spec_read_frame_fr (map bz bb) bb (holds_body_map bb)) as (C' & F).
  split; [rewrite C, C'; reflexivity|].
  intros H0. pose proof (fr_code_ok bb H0) as (Hl & _).
  specialize (F H0). cbv zeta in F. rewrite <- C' in H0. specialize (A H0).
  unfold parse_agrees in A. unfold parse_fr.
  destruct A as (_ & _ & _ & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18).
  destruct F as (_ & _ & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14).
  split; [rewrite A4; exact (lnk_map_byte_at_window bb 0 6 ltac:(lia))|].
  split; [rewrite A5; exact (lnk_map_byte_at_window bb 6 6 ltac:(lia))|].
  rewrite A18, F14, F5.
  repeat split; congruence.
Qed.

(* diginet_frame_build over map bz of the MACs and the body is DgnLib.v's lib_build_code and lib_frame *)
Theorem frame_build_lib : forall cap dst src h body mode,
  length dst = 6%nat -> length src = 6%nat -> mode = DIGINET_SUM_BODY \/ mode = DIGINET_SUM_ZERO ->
  0 <= dh_cmd h < 256 -> 0 <= dh_num_commands h < 256 ->
  fst (diginet_frame_build cap (map bz dst) (map bz src) h (map bz body) (Z.of_nat (length body)) mode) =
    lib_build_code body cap /\
  (0 <= lib_build_code body cap ->
   snd (diginet_frame_build cap (map bz dst) (map bz src) h (map bz body) (Z.of_nat (length body)) mode) =
   map bz (lib_frame dst src (dh_send_counter h) (dh_ack_counter h) (dh_retry h) (dh_cmd h)
             (dh_num_commands h) body mode)).
Proof.
  intros cap dst src h body mode Hd Hs Hm Hc Hn.
  assert (Em : (mode =? DIGINET_SUM_BODY) || (mode =? DIGINET_SUM_ZERO) = true)
    by (destruct Hm as [E|E]; rewrite E; reflexivity).
  assert (Eb : diginet_body_check (map bz body) (Z.of_nat (length body)) = body_check body)
    by exact (diginet_body_check_body_check (map bz body) body (holds_body_map body)).
  assert (Eo : (if DIGINET_BODY_OFFSET + Z.of_nat (length body) <? DIGINET_MIN_FRAME_LEN then DIGINET_MIN_FRAME_LEN
                else DIGINET_BODY_OFFSET + Z.of_nat (length body)) = frame_len (length body))
    by (unfold frame_len, DIGINET_BODY_OFFSET, DIGINET_MIN_FRAME_LEN;
        destruct (Z.ltb_spec (30 + Z.of_nat (length body)) 60); lia).
  assert (Ed : map (byte_at (map bz dst)) (zseq 6) = map bz dst).
  { pose proof (lnk_map_byte_at_zseq (map bz dst)) as E. rewrite length_map, Hd in E. exact E. }
  assert (Es : map (byte_at (map bz src)) (zseq 6) = map bz src).
  { pose proof (lnk_map_byte_at_zseq (map bz src)) as E. rewrite length_map, Hs in E. exact E. }
  assert (Ebd : map (byte_at (map bz body)) (zseq (length body)) = map bz body).
  { pose proof (lnk_map_byte_at_zseq (map bz body)) as E. rewrite length_map in E. exact E. }
  unfold diginet_frame_build, lib_build_code; cbv zeta. rewrite Em, Eb. cbn [negb].
  unfold DIGINET_MAX_BODY_LEN, DIGINET_OK.
  destruct (Z.ltb_spec 1484 (Z.of_nat (length body))) as [L|L].
  { split; [reflexivity | intros H; cbv beta iota in H; lia]. }
  destruct (body_check body =? 0) eqn:B; cbn [negb].
  2: { split; [reflexivity | intros H; cbv beta iota in H; lia]. }
  rewrite Eo.
  destruct (Z.ltb_spec cap (frame_len (length body))) as [C|C].
  { split; [reflexivity | intros H; cbv beta iota in H; lia]. }
  split; [reflexivity|]. intros _. cbn [snd].
  unfold lib_frame. rewrite !map_app.
  rewrite (put16_mod (dh_retry h)), (put32_mod (dh_send_counter h)), (put32_mod (dh_ack_counter h)).
  rewrite !lnk_put16_wr16, !lnk_put32_wr32, map_repeat, (bz_b8 0) by lia.
  rewrite Nat2Z.id, Ed, Es, Ebd, lnk_sum16_map_bz.
  cbn [map]. rewrite (bz_b8 (dh_cmd h)), (bz_b8 (dh_num_commands h)) by lia.
  reflexivity.
Qed.

Lemma lnk_wr16_u32 : forall x, wr16 (u32 x) = wr16 x.
Proof.
  intros x. rewrite <- !lnk_put16_wr16. unfold put16, u32.
  rewrite (b8_div_mod x 8 32), (b8_mod_w x 32) by lia. reflexivity.
Qed.

(* spec_build_frame over map bz of the MACs and the body is DgnSpec.v's build_frame (zero_sum as the
   bool zero_sum <> 0, spec.h:238), and its length frame_len *)
Theorem spec_build_frame_build_frame : forall dst src send ack retry cmd ncmds body zero_sum,
  length dst = 6%nat -> length src = 6%nat -> 0 <= cmd < 256 -> 0 <= ncmds < 256 ->
  spec_build_frame (map bz dst) (map bz src) send ack retry cmd ncmds (map bz body)
    (Z.of_nat (length body)) zero_sum =
  (frame_len (length body),
   map bz (build_frame dst src send ack retry cmd ncmds body (negb (zero_sum =? 0)))).
Proof.
  intros dst src send ack retry cmd ncmds body zero_sum Hd Hs Hc Hn.
  assert (Ed : map (byte_at (map bz dst)) (zseq 6) = map bz dst).
  { pose proof (lnk_map_byte_at_zseq (map bz dst)) as E. rewrite length_map, Hd in E. exact E. }
  assert (Es : map (byte_at (map bz src)) (zseq 6) = map bz src).
  { pose proof (lnk_map_byte_at_zseq (map bz src)) as E. rewrite length_map, Hs in E. exact E. }
  assert (Ebd : map (byte_at (map bz body)) (zseq (length body)) = map bz body).
  { pose proof (lnk_map_byte_at_zseq (map bz body)) as E. rewrite length_map in E. exact E. }
  assert (Eo : (if SPEC_BODY_AT + Z.of_nat (length body) <? SPEC_MIN_FRAME then SPEC_MIN_FRAME
                else SPEC_BODY_AT + Z.of_nat (length body)) = frame_len (length body))
    by (unfold frame_len, SPEC_BODY_AT, SPEC_MIN_FRAME;
        destruct (Z.ltb_spec (30 + Z.of_nat (length body)) 60); lia).
  assert (Esum : spec_sum_at (map bz body) 0 (Z.of_nat (length body)) = spec_sum body)
    by (rewrite <- diginet_sum16_spec_sum_at, lnk_sum16_map_bz, lib_sum16_eq, spec_sum_eq; reflexivity).
  assert (Ep : Z.to_nat (frame_len (length body) - SPEC_BODY_AT - Z.of_nat (length body)) =
               (30 - length body)%nat) by (unfold frame_len, SPEC_BODY_AT; lia).
  unfold spec_build_frame; cbv zeta. rewrite Eo, Ep. f_equal.
  unfold build_frame. rewrite !map_app.
  change spec_put16 with wr16. change spec_put32 with wr32.
  rewrite !lnk_put16_wr16, !lnk_put32_wr32, map_repeat, (bz_b8 0) by lia.
  rewrite lnk_wr16_u32, Nat2Z.id, Ed, Es, Ebd, Esum.
  cbn [map]. rewrite (bz_b8 cmd), (bz_b8 ncmds) by lia.
  destruct (zero_sum =? 0); reflexivity.
Qed.

(* spec_strz_len over map bz bb is fuzz_frame's strz_len *)
Lemma lnk_strz_len_loop_nz_run : forall B P l, (forall j, byte_at B (P + Z.of_nat j) = at8 l j) ->
  forall fuel n, (n + fuel = 9)%nat ->
  strz_len_loop B P (Z.of_nat n) fuel = Z.of_nat (n + nz_run (firstn fuel (skipn n l))).
Proof.
  intros B P l HB fuel. induction fuel as [|f IH]; intros n Hn; cbn [strz_len_loop].
  - rewrite firstn_O. cbn [nz_run]. rewrite Nat.add_0_r. reflexivity.
  - unfold SPEC_ANN_FIELD. rewrite HB.
    replace (Z.of_nat n <? 9) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
    destruct (Nat.lt_ge_cases n (length l)) as [L|L].
    + rewrite (lk_skipn_nth l n L). cbn [firstn nz_run]. unfold at8.
      destruct (Z.eqb_spec (bz (nth n l (b8 0))) 0) as [E|E]; cbn [negb].
      * f_equal. lia.
      * replace (Z.of_nat n + 1) with (Z.of_nat (S n)) by lia. rewrite IH by lia. f_equal. lia.
    + rewrite skipn_all2 by lia. rewrite firstn_nil. cbn [nz_run].
      replace (at8 l n) with 0 by (unfold at8; rewrite nth_overflow by lia; symmetry; apply bz_b8; lia).
      cbn [Z.eqb negb]. f_equal. lia.
Qed.

Lemma spec_strz_len_strz_len : forall bb p,
  spec_strz_len (map bz bb) (Z.of_nat p) = Z.of_nat (strz_len (skipn p bb)).
Proof.
  intros bb p. unfold spec_strz_len, strz_len.
  transitivity (Z.of_nat (0 + nz_run (firstn 9 (skipn 0 (skipn p bb))))); [|reflexivity].
  assert (HB : forall j, byte_at (map bz bb) (Z.of_nat p + Z.of_nat j) = at8 (skipn p bb) j)
    by (intros j; rewrite <- Nat2Z.inj_add, lnk_byte_at_map_bz, at8_skipn; reflexivity).
  exact (lnk_strz_len_loop_nz_run (map bz bb) (Z.of_nat p) (skipn p bb) HB 9 0 eq_refl).
Qed.

(* the field copy_strz_z leaves, reading at p, is DgnSpec.v's copy_strz of the bytes from p *)
Lemma copy_strz_z_copy_strz : forall src p old, length old = 10%nat ->
  copy_strz_z (map bz old) 10 (map bz src) (Z.of_nat p) 9 = map bz (copy_strz 10 9 (skipn p src) old).
Proof.
  intros src p old Ho.
  assert (Lk : (strz_len (skipn p src) <= length (skipn p src))%nat).
  { unfold strz_len. pose proof (nz_run_le (firstn 9 (skipn p src))). rewrite length_firstn in H. lia. }
  pose proof (strz_len_le (skipn p src)) as L9.
  pose proof (spec_strz_len_strz_len src p) as K.
  apply nth_ext with (d := 0) (d' := 0).
  - rewrite length_copy_strz_z, !length_map, (length_copy_strz (skipn p src) old Ho). exact Ho.
  - intros k Hk. rewrite length_copy_strz_z, length_map, Ho in Hk.
    transitivity (byte_at (copy_strz_z (map bz old) 10 (map bz src) (Z.of_nat p) 9) (Z.of_nat k));
      [unfold byte_at; rewrite Nat2Z.id; reflexivity|].
    rewrite copy_strz_z_at by (rewrite ?length_map; lia). rewrite K.
    rewrite (nth_indep _ 0 (bz (b8 0)))
      by (rewrite length_map, (length_copy_strz (skipn p src) old Ho); lia).
    rewrite map_nth. unfold copy_strz. change (copy_len 10 9 (skipn p src)) with (strz_len (skipn p src)).
    destruct (Z.ltb_spec (Z.of_nat k) (Z.of_nat (strz_len (skipn p src)))) as [Lt|Ge].
    + rewrite app_nth1 by (rewrite length_firstn; lia). rewrite nth_firstn.
      destruct (Nat.ltb_spec k (strz_len (skipn p src))); [|lia].
      rewrite <- Nat2Z.inj_add, (lnk_byte_at_map_bz src (p + k)).
      exact (eq_sym (at8_skipn src p k)).
    + rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
      replace (Nat.min (strz_len (skipn p src)) (length (skipn p src))) with (strz_len (skipn p src)) by lia.
      destruct (Z.eqb_spec (Z.of_nat k) (Z.of_nat (strz_len (skipn p src)))) as [Eq|Ne].
      * replace (k - strz_len (skipn p src))%nat with O by lia. cbn [nth]. symmetry. apply bz_b8. lia.
      * destruct (k - strz_len (skipn p src))%nat as [|t] eqn:Et; [lia|]. cbn [nth]. rewrite nth_skipn.
        replace (S (strz_len (skipn p src)) + t)%nat with k by lia. exact (lnk_byte_at_map_bz old k).
Qed.

Lemma mac_is_digidesign_oui_of : forall mac, diginet_mac_is_digidesign (map bz mac) = int_of_bool (oui_of mac).
Proof. intros mac. unfold diginet_mac_is_digidesign, oui_of. rewrite <- !lnk_byte_at_map_bz. reflexivity. Qed.

Lemma frame_is_keepalive_of : forall b f body, byte_at b (df_body f) = at8 body 0 ->
  diginet_frame_is_keepalive b f = int_of_bool (keepalive_of (dh_cmd (df_h f)) (df_body_len f) body).
Proof. intros b f body H. unfold diginet_frame_is_keepalive, keepalive_of. rewrite H. reflexivity. Qed.

Lemma announce_code_ann_code : forall b f a,
  fst (diginet_announce_parse b f a) = ann_code (dh_cmd (df_h f)) (df_body_len f).
Proof.
  intros b f a. unfold diginet_announce_parse, ann_code, ann_cmd.
  unfold DIGINET_CMD_ANNOUNCE, DIGINET_CMD_ANNOUNCE_SESSION, DIGINET_E_NOT_ANNOUNCE, DIGINET_E_LENGTH, DIGINET_OK.
  destruct (negb ((dh_cmd (df_h f) =? 224) || (dh_cmd (df_h f) =? 225))); [reflexivity|].
  destruct (df_body_len f <? 33); reflexivity.
Qed.

(* the version and name diginet_announce_parse writes are DgnSpec.v's ann_version and ann_name of
   the body bytes, for a frame f whose body is at q in map bz bb and an announce whose two fields
   held map bz old_v and map bz old_n *)
Lemma announce_parse_ann : forall bb q f old_v old_n u ul,
  df_body f = Z.of_nat q -> length old_v = 10%nat -> length old_n = 10%nat ->
  ann_code (dh_cmd (df_h f)) (df_body_len f) = 0 ->
  da_version (snd (diginet_announce_parse (map bz bb) f (DgnAnnounce (map bz old_v) (map bz old_n) u ul))) =
    map bz (ann_version (skipn q bb) old_v) /\
  da_name (snd (diginet_announce_parse (map bz bb) f (DgnAnnounce (map bz old_v) (map bz old_n) u ul))) =
    map bz (ann_name (skipn q bb) old_n).
Proof.
  intros bb q f old_v old_n u ul Hb Hv Hn Hc. revert Hc.
  unfold diginet_announce_parse, ann_code, ann_cmd.
  unfold DIGINET_CMD_ANNOUNCE, DIGINET_CMD_ANNOUNCE_SESSION.
  destruct (negb ((dh_cmd (df_h f) =? 224) || (dh_cmd (df_h f) =? 225))); [intros H; discriminate H|].
  destruct (df_body_len f <? 33); [intros H; discriminate H|]. intros _.
  cbn [snd da_version da_name]. rewrite Hb. unfold ann_version, ann_name. rewrite !skipn_skipn.
  replace (Z.of_nat q + 15) with (Z.of_nat (15 + q)) by lia.
  replace (Z.of_nat q + 24) with (Z.of_nat (24 + q)) by lia.
  split; apply copy_strz_z_copy_strz; assumption.
Qed.
