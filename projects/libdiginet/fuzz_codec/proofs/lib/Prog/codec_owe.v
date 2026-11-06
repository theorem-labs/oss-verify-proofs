From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.

(** The harness's view of fuzz_codec: what fuzz_codec.c's owe() and owed_* functions compute, and
    spec_segments of fuzz/spec.h, written from the harness's C without the library. The desk, the
    command, KEY, u8, bit_or_0 and the return codes are those of DgnSpec / DgnLib. *)

(** The owed command of a failed call: want_len 0, want_key 0, want_display 0 (fuzz_codec.c:128-131). *)
Definition noc : cmd := ([], 0, 0).

(** seven_bit (fuzz_codec.c:92-98) *)
Definition seven_bit (l : list Z) : bool := forallb (fun x => negb (Z.testbit x 7)) l.

(** owe_sysex (fuzz_codec.c:101-111) without the key: (want[0..want_len), want_display). *)
Definition owe_sx (dev fn : Z) (pl : list Z) : list Z * Z :=
  ([0xf0; 0x13; u8 dev; u8 fn] ++ pl ++ [0xf7], bit_or_0 ((u8 fn =? 0x40) || (u8 fn =? 0x30)) 1).

(** The ring payload of owe (fuzz_codec.c:179-182): for led = 2..15, bit led - 1 of b sets bit 8 - led
    of pl[1] (led <= 8) or bit 15 - led of pl[2]. *)
Definition owe_ring (b : Z) : Z * Z :=
  fold_left (fun '(p1, p2) led =>
               if Z.testbit b (led - 1) then
                 if led <=? 8 then (Z.lor p1 (2 ^ (8 - led)), p2) else (p1, Z.lor p2 (2 ^ (15 - led)))
               else (p1, p2))
            (map Z.of_nat (seq 2 14)) (0, 0).

(** owe (fuzz_codec.c:113-254): (want_rc, (want[0..want_len), want_key, want_display)) for a call
    record: kind, the desk (k->desk; None = NULL), a, b, c (unsigned), delta (int), bytes (the 24 bytes
    of the record) and n. *)
Definition owe_spec (kind : Z) (od : option desk) (a b c delta : Z) (bytes : list Z) (n : Z) : Z * cmd :=
  let needs := negb ((kind =? 1) || (kind =? 4) || (kind =? 11)) in
  match od, needs with
  | None, true => (E_ARG, noc)
  | _, _ =>
    let d := match od with Some d => d | None => c24 end in
    let rng := (E_RANGE, noc) in
    if kind =? 0 then
      if (d_strips d <=? a) || (1023 <? b) then rng
      else (0, ([0xb0; u8 a; u8 (b / 8); u8 (0x20 + a); u8 ((b mod 8) * 16)], KEY 1 a, 0))
    else if kind =? 1 then
      if (0x7f <? a) || (0x3f <? b) then rng
      else (0, ([0x90; u8 a; u8 (Z.lor (bit_or_0 (negb (c =? 0)) 0x40) b)],
                KEY 2 (Z.lor ((a * 256) mod 2 ^ 32) b), 0))
    else if kind =? 2 then
      if d_strips d <=? a then rng
      else (0, ([0x90; 0x09; u8 (Z.lor (bit_or_0 (negb (c =? 0)) 0x40) a)], KEY 8 0, 0))
    else if kind =? 3 then
      if (d_strips d <=? a) || (delta <? -64) || (63 <? delta) then rng
      else (0, ([0xb0; u8 (Z.lor 0x40 a); u8 (delta + 64)], KEY 8 0, 0))
    else if kind =? 4 then
      if (delta <? -64) || (63 <? delta) then rng
      else (0, ([0xb0; 0x5c; u8 (delta + 64)], KEY 8 0, 0))
    else if kind =? 5 then
      if (d_strips d <=? a) || negb (Z.shiftr b 15 =? 0) then rng
      else
        let '(p1, p2) := owe_ring b in
        let '(bs, dp) := owe_sx (d_dev d) 0x00 [u8 (Z.lor a (bit_or_0 (Z.testbit b 0) 0x40)); p1; p2] in
        (0, (bs, KEY 3 a, dp))
    else if kind =? 6 then
      if (0x20 <=? a) || (14 <? b) then rng
      else
        let mask := (2 ^ b - 1) mod 2 ^ 32 in
        let ch := u8 (Z.lor a (bit_or_0 (negb (c =? 0)) 0x20)) in
        let '(bs, dp) := owe_sx (d_dev d) 0x10 [ch; u8 (Z.shiftr mask 7); u8 (Z.land mask 0x7f)] in
        (0, (bs, KEY 4 ch, dp))
    else if (kind =? 7) || (kind =? 8) then
      let addr := if kind =? 7 then a else d_counter d in
      if ((kind =? 7) && (d_strips d <=? a)) || (0x7f <? b) then rng
      else let '(bs, dp) := owe_sx (d_dev d) 0x20 [u8 addr; u8 b] in (0, (bs, KEY 5 addr, dp))
    else if kind =? 9 then
      if (0x7f <? a) || negb (seven_bit (firstn (Z.to_nat (d_chars d)) bytes)) then rng
      else
        let '(bs, dp) := owe_sx (d_dev d) 0x40 ([u8 a; 0] ++ firstn (Z.to_nat (d_chars d)) bytes) in
        (0, (bs, KEY 7 a, dp))
    else if kind =? 10 then
      if (0x7f <? b) || negb (seven_bit (firstn 8 bytes)) then rng
      else
        let '(bs, dp) := owe_sx (d_dev d) 0x30 ([d_counter d; u8 b] ++ rev (firstn 8 bytes)) in
        (0, (bs, KEY 6 (d_counter d), dp))
    else
      if 0x7f <? a then (E_ARG, noc)
      else if b =? 0x70 then (E_REFUSED, noc)
      else if 0x7f <? b then rng
      else if 24 <? n + 5 then (E_SPACE, noc)
      else if negb (seven_bit (firstn (Z.to_nat n) bytes)) then rng
      else let '(bs, dp) := owe_sx (u8 a) (u8 b) (firstn (Z.to_nat n) bytes) in (0, (bs, 0, dp))
  end.

(** The fields of a call record as LLVMFuzzerTestOneInput's reader leaves them (fuzz_codec.c:572-646):
    a, b, c unsigned, delta an int, 24 bytes, n at most 24; RING's b a u16 (fuzz_u16), COUNTER's b a u8
    (fuzz_u8, or the dots of a counter text), SYSEX's a and b u8. *)
Definition reader_ok (kind a b c delta : Z) (bytes : list Z) (n : Z) : Prop :=
  0 <= a < 2 ^ 32 /\ 0 <= b < 2 ^ 32 /\ 0 <= c < 2 ^ 32 /\ - 2 ^ 31 <= delta < 2 ^ 31 /\
  length bytes = 24%nat /\ Forall (fun x => 0 <= x < 256) bytes /\ 0 <= n <= 24 /\
  (kind = 5 -> b < 2 ^ 16) /\ (kind = 10 -> b < 256) /\ (kind = 11 -> a < 256 /\ b < 256).

(** The desk of a text operation (fuzz_codec.c:623-626, :635-638): Control|24 when the personality is
    none. *)
Definition text_desk (od : option desk) : desk := match od with Some d => d | None => c24 end.

(** ---- the text helpers ---- *)

(** owed_scribble_text (fuzz_codec.c:351-366), over a C string as in DgnLib: t the text from its
    current byte, k the output slots left; (the output bytes, the text bytes used). *)
Fixpoint scr_owe (t : list Z) (k : nat) : list Z * Z :=
  match t, k with
  | _, O => ([], 0)
  | [], S _ => (repeat 0x20 k, 0)
  | x :: t', S k' =>
    if x =? 0 then (repeat 0x20 k, 0)
    else
      let y := match t' with y :: _ => y | [] => 0 end in
      if (x =? 0x2e) && (0x31 <=? y) && (y <=? 0x39) then
        let '(o, u) := scr_owe (tl t') k' in ((y - 26) :: o, u + 2)
      else
        let '(o, u) := scr_owe t' k' in ((if x <? 0x80 then x else 0x3f) :: o, u + 1)
  end.
Definition owed_scribble_text_spec (t : list Z) (n : Z) : list Z * Z := scr_owe t (Z.to_nat n).

(** The bytes of the call record after a scribble text of chars characters (fuzz_codec.c:629,
    check_text_scribble's memset of the 24 bytes to 0xa5 and the text's characters). *)
Definition scribble_bytes (t : list Z) (chars : Z) : list Z :=
  fst (owed_scribble_text_spec t chars) ++ repeat 0xa5 (Z.to_nat (24 - chars)).

(** GLYPH of owed_seg7 (fuzz_codec.c:374-381): each character and its segments, a..g. *)
Definition glyph : list (Z * list Z) :=
  [(0x30, [0x61; 0x62; 0x63; 0x64; 0x65; 0x66]);       (* '0' "abcdef" *)
   (0x31, [0x62; 0x63]);                               (* '1' "bc" *)
   (0x32, [0x61; 0x62; 0x64; 0x65; 0x67]);             (* '2' "abdeg" *)
   (0x33, [0x61; 0x62; 0x63; 0x64; 0x67]);             (* '3' "abcdg" *)
   (0x34, [0x62; 0x63; 0x66; 0x67]);                   (* '4' "bcfg" *)
   (0x35, [0x61; 0x63; 0x64; 0x66; 0x67]);             (* '5' "acdfg" *)
   (0x36, [0x61; 0x63; 0x64; 0x65; 0x66; 0x67]);       (* '6' "acdefg" *)
   (0x37, [0x61; 0x62; 0x63]);                         (* '7' "abc" *)
   (0x38, [0x61; 0x62; 0x63; 0x64; 0x65; 0x66; 0x67]); (* '8' "abcdefg" *)
   (0x39, [0x61; 0x62; 0x63; 0x64; 0x66; 0x67]);       (* '9' "abcdfg" *)
   (0x41, [0x61; 0x62; 0x63; 0x65; 0x66; 0x67]);       (* 'A' "abcefg" *)
   (0x62, [0x63; 0x64; 0x65; 0x66; 0x67]);             (* 'b' "cdefg" *)
   (0x43, [0x61; 0x64; 0x65; 0x66]);                   (* 'C' "adef" *)
   (0x64, [0x62; 0x63; 0x64; 0x65; 0x67]);             (* 'd' "bcdeg" *)
   (0x45, [0x61; 0x64; 0x65; 0x66; 0x67]);             (* 'E' "adefg" *)
   (0x46, [0x61; 0x65; 0x66; 0x67]);                   (* 'F' "aefg" *)
   (0x48, [0x62; 0x63; 0x65; 0x66; 0x67]);             (* 'H' "bcefg" *)
   (0x68, [0x63; 0x65; 0x66; 0x67]);                   (* 'h' "cefg" *)
   (0x4a, [0x62; 0x63; 0x64; 0x65]);                   (* 'J' "bcde" *)
   (0x4c, [0x64; 0x65; 0x66]);                         (* 'L' "def" *)
   (0x6f, [0x63; 0x64; 0x65; 0x67]);                   (* 'o' "cdeg" *)
   (0x50, [0x61; 0x62; 0x65; 0x66; 0x67]);             (* 'P' "abefg" *)
   (0x72, [0x65; 0x67]);                               (* 'r' "eg" *)
   (0x53, [0x61; 0x63; 0x64; 0x66; 0x67]);             (* 'S' "acdfg" *)
   (0x55, [0x62; 0x63; 0x64; 0x65; 0x66]);             (* 'U' "bcdef" *)
   (0x59, [0x62; 0x63; 0x64; 0x66; 0x67]);             (* 'Y' "bcdfg" *)
   (0x5a, [0x61; 0x62; 0x64; 0x65; 0x67]);             (* 'Z' "abdeg" *)
   (0x2d, [0x67]);                                     (* '-' "g" *)
   (0x20, [])].                                        (* ' ' "" *)

(** The match test of owed_seg7 (fuzz_codec.c:384-386) for glyph character g and c. *)
Definition glyph_match (g c : Z) : bool :=
  (c =? g) ||
  (negb ((g =? 0x48) || (g =? 0x68)) &&
   (((0x41 <=? g) && (g <=? 0x5a)) || ((0x61 <=? g) && (g <=? 0x7a))) &&
   (Z.lor c 0x20 =? Z.lor g 0x20)).

(** The segment loop of owed_seg7 (fuzz_codec.c:389-391). *)
Definition segs_val (s : list Z) : Z := fold_left (fun v ch => Z.lor v (2 ^ (6 - (ch - 0x61)))) s 0.

Fixpoint owed_seg7_go (gs : list (Z * list Z)) (c : Z) : Z :=
  match gs with
  | [] => -1
  | (g, s) :: gs' => if glyph_match g c then segs_val s else owed_seg7_go gs' c
  end.

(** owed_seg7 (fuzz_codec.c:368-395); c in [0, 256), the unsigned char its callers pass. *)
Definition owed_seg7_spec (c : Z) : Z := owed_seg7_go glyph c.

(** The first loop of owed_counter_text (fuzz_codec.c:407-417): as ct1_lib, with owed_seg7 and
    dot[n] = (ch == '.'). *)
Fixpoint ct1_owe (t : list Z) (n : Z) (s dot : list Z) : option (Z * list Z * list Z) :=
  match t with
  | [] => Some (n, s, dot)
  | ch :: t' =>
    if ch =? 0 then Some (n, s, dot)
    else if (ch =? 0x2e) && (0 <? n) && (nth (Z.to_nat (n - 1)) dot 0 =? 0)
    then ct1_owe t' n s (upd_at dot (n - 1) 1)
    else
      let v := owed_seg7_spec (if ch =? 0x2e then 0x20 else ch) in
      if (v <? 0) || (n =? 8) then None
      else ct1_owe t' (n + 1) (s ++ [v]) (upd_at dot n (if ch =? 0x2e then 1 else 0))
  end.

(** owed_counter_text (fuzz_codec.c:402-429): (rc, seg, dots); its second loop is DgnLib's ct2. *)
Definition owed_counter_text_spec (t : list Z) : Z * list Z * Z :=
  match ct1_owe t 0 [] (repeat 0 8) with
  | None => (E_RANGE, [], 0)
  | Some (n, s, dot) => ct2 n s dot
  end.

(** The bytes of the call record after an owed counter text (fuzz_codec.c:641-646): the 8 digits,
    then the 0xa5 that check_text_counter's memset left. *)
Definition counter_bytes (seg : list Z) : list Z := seg ++ repeat 0xa5 16.

(** ---- check_text_masks (fuzz_codec.c:492-519) ---- *)

(** (1u << lit) - 1 with lit = min(n, 14) *)
Definition owed_meter_mask (n : Z) : Z := 2 ^ (Z.min n 14) - 1.
(** n < 15 ? 1u << n : 0 *)
Definition owed_ring_dot (n : Z) : Z := if n <? 15 then 2 ^ n else 0.
(** n <= 15 ? (1u << n) - 1 : 0 *)
Definition owed_ring_fill (n : Z) : Z := if n <=? 15 then 2 ^ n - 1 else 0.
