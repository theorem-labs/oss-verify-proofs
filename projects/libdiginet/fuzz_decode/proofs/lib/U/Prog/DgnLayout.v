(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* The memory form, in fuzz_decode.ubsan, of the structs no frame file covers: struct diginet_event,
   struct diginet_decoder, the personalities table, and the harness's stack structs struct spec_msg, struct
   spec_event and struct owed. The UBSan twin of lib/Prog/DgnLayout.v: the same names and the same layouts (the two
   builds use one compiler, one ABI and the same headers), each field offset measured again from this image's code;
   the comment beside it names an instruction that shows it (pc: instruction). The one value that differs is the
   address of the personalities table. struct diginet_cursor and struct diginet_msg are cursor_cells
   (lib/Prog/diginet_cursor_init_c.v, a pure layout that names no image value) and msg_cells of the cursor
   contracts; dmsg_cells below is the same 40-byte layout over the DgnLib.v message.
   Source: include/diginet/diginet_codec.h:31-38, :193-211, fuzz/spec.h:291-296, :382-390,
   fuzz/fuzz_decode.c:119-125 at 835f336c. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import Cells.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib DgnDecHarness.
(* cursor_cells, the memory form of struct diginet_cursor (a pure layout, no image value) *)
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import diginet_cursor_init_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- field offsets (bytes from the start of the struct); the instructions are in the comments of the cell
   lists below ---- *)

(* struct diginet_msg *)
Definition DM_STATUS : Z := 0.  Definition DM_RUNNING : Z := 1.  Definition DM_D1 : Z := 2.
Definition DM_D2 : Z := 3.  Definition DM_SYSEX : Z := 8.  Definition DM_SYSEX_LEN : Z := 16.
Definition DM_OFFSET : Z := 24.  Definition DM_LEN : Z := 32.  Definition DM_SIZE : Z := 40.

(* struct diginet_event *)
Definition DE_KIND : Z := 0.  Definition DE_STRIP : Z := 4.  Definition DE_BUTTON : Z := 5.
Definition DE_ZONE : Z := 6.  Definition DE_ON : Z := 7.  Definition DE_RIGHT : Z := 8.
Definition DE_ADDR : Z := 9.  Definition DE_LSB_MISSING : Z := 10.  Definition DE_VALUE : Z := 12.
Definition DE_DELTA : Z := 14.  Definition DE_MASK : Z := 16.  Definition DE_SEGMENTS : Z := 18.
Definition DE_LEN : Z := 19.  Definition DE_TEXT : Z := 20.  Definition DE_SEG : Z := 29.
Definition DE_DOTS : Z := 37.  Definition DE_DEVICE : Z := 38.  Definition DE_MSG : Z := 40.
Definition DE_SIZE : Z := 80.

(* struct diginet_decoder *)
Definition DD_C : Z := 0.  Definition DD_P : Z := 32.  Definition DD_SIZE : Z := 40.

(* struct diginet_personality *)
Definition DP_DESK : Z := 0.  Definition DP_ANNOUNCE_NAME : Z := 8.  Definition DP_DEVICE : Z := 16.
Definition DP_STRIPS : Z := 17.  Definition DP_SCRIBBLE_CHARS : Z := 18.
Definition DP_COUNTER_ADDR : Z := 19.  Definition DP_SIZE : Z := 24.

(* struct spec_msg *)
Definition SM_CODE : Z := 0.  Definition SM_AT : Z := 8.  Definition SM_LEN : Z := 16.
Definition SM_NEXT : Z := 24.  Definition SM_STATUS : Z := 32.  Definition SM_RUNNING : Z := 33.
Definition SM_D1 : Z := 34.  Definition SM_D2 : Z := 35.  Definition SM_STATUS_OUT : Z := 36.
Definition SM_SYSEX_AT : Z := 40.  Definition SM_SYSEX_LEN : Z := 48.  Definition SM_SIZE : Z := 56.

(* struct spec_event *)
Definition SE_KIND : Z := 0.  Definition SE_STRIP : Z := 4.  Definition SE_BUTTON : Z := 5.
Definition SE_ZONE : Z := 6.  Definition SE_ON : Z := 7.  Definition SE_RIGHT : Z := 8.
Definition SE_ADDR : Z := 9.  Definition SE_DEVICE : Z := 10.  Definition SE_LEN : Z := 11.
Definition SE_DOTS : Z := 12.  Definition SE_VALUE : Z := 14.  Definition SE_MASK : Z := 16.
Definition SE_DELTA : Z := 18.  Definition SE_SEGMENTS : Z := 20.  Definition SE_TEXT : Z := 21.
Definition SE_SEG : Z := 29.  Definition SE_SIZE : Z := 40.

(* struct owed *)
Definition OW_M : Z := 0.  Definition OW_E : Z := 56.  Definition OW_LSB_MISSING : Z := 96.
Definition OW_NEXT : Z := 104.  Definition OW_STATUS_OUT : Z := 112.  Definition OW_SIZE : Z := 120.

(* ---- shared pieces ---- *)

(* n one-byte cells holding the elements 0 .. n - 1 of a C byte array held as a list Z *)
Definition arr_cells (n : nat) (l : list Z) : list cell :=
  map (fun i => C1 (b8 (nth i l 0))) (seq 0 n).

(* the C pointer a DgnLib.v payload offset stands for: NULL (0) for no payload, else body + off (a payload offset
   is at least 1, DgnLib.v diginet_msg_next) *)
Definition sysex_ptr (body off : Z) : Z := if off =? 0 then 0 else body + off.

(* ---- struct diginet_msg over the DgnLib.v message (40 bytes) ----
   status 0, running 1, d1 2, d2 3, padding 4..7, sysex 8, sysex_len 16, offset 24, len 32: check_cursor_message
   (a2 = the message) 0x1372c: lbu a3, 0(a2); 0x13738: lbu a4, 1(a2); 0x13744: lbu a4, 2(a2); 0x13750: lbu a4,
   3(a2); 0x13780: ld a0, 8(a2); 0x13788: ld a0, 0x10(a2); 0x13714: ld a3, 0x18(a2); 0x13720: ld a3, 0x20(a2).
   pad are the 4 padding bytes. *)
Definition dmsg_cells (body : Z) (pad : list byte) (m : dgn_msg) : list cell :=
  [ C1 (b8 (dm_status m)); C1 (b8 (dm_running m)); C1 (b8 (dm_d1 m)); C1 (b8 (dm_d2 m));
    CB 4 pad;
    C8 (Z_to_bv 64 (sysex_ptr body (dm_sysex m)));
    C8 (Z_to_bv 64 (dm_sysex_len m));
    C8 (Z_to_bv 64 (dm_offset m));
    C8 (Z_to_bv 64 (dm_len m)) ].

(* ---- struct diginet_event (80 bytes) ----
   kind 0       diginet_decoder_next 0x14064: sw a2, 0(s0); check_events_step 0x13848: lw a0, 0(a3)
   strip 4      0x141f8: sb a0, 4(s0); check_events_fields 0x13938: lbu a0, 4(s1)
   button 5     0x14088: sb a1, 5(s0)
   zone 6       0x1409c: sb a0, 6(s0)
   on 7         0x1408c: sb a2, 7(s0)
   right 8      0x1437c: sb a2, 8(s0)
   addr 9       0x14328: sb a2, 9(s0)
   lsb_missing 10   0x142d8: sb s1, 0xa(s0)
   padding 11
   value 12     0x141fc: sh a1, 0xc(s0)
   delta 14     0x142d0: sh a0, 0xe(s0)
   mask 16      0x14158: sh a3, 0x10(s0)
   segments 18  0x143a4: sb a0, 0x12(s0)
   len 19       0x14448: sb s2, 0x13(s0)
   text 20..28  0x14454: addi s0, s0, 0x14 (the memcpy destination)
   seg 29..36   0x143d8: addi a3, s0, 0x24 (the counter loop stores seg[7] .. seg[0] at 0x24 .. 0x1d);
                check_events_fields 0x13a1c: addi a0, s1, 0x1d
   dots 37      0x143dc: sb a4, 0x25(s0)
   device 38    0x140e0: sb a0, 0x26(s0)
   padding 39
   msg 40..79   0x14044: addi a0, s0, 0x28 then the memcpy of 0x28 bytes from the message (0x1404c: addi a2,
                zero, 0x28); check_events_step 0x137c8: ld a2, 0x40(a3) (msg.offset)
   size 80      diginet_decoder_next 0x1402c: addi a2, zero, 0x50 (the memset of the event)
   In this image diginet_decoder_next zeroes all 80 bytes (0x1402c-0x14038) before it copies the 40 bytes of its
   message, padding included, to 40..79: the padding bytes 11 and 39 are 0, the 4 padding bytes of msg (44..47)
   are mpad. *)
Definition event_cells (body : Z) (mpad : list byte) (e : dgn_event) : list cell :=
  [ C4 (Z_to_bv 64 (de_kind e));
    C1 (b8 (de_strip e)); C1 (b8 (de_button e)); C1 (b8 (de_zone e)); C1 (b8 (de_on e));
    C1 (b8 (de_right e)); C1 (b8 (de_addr e)); C1 (b8 (de_lsb_missing e)); C1 (b8 0);
    C2 (Z_to_bv 64 (de_value e)); C2 (Z_to_bv 64 (de_delta e)); C2 (Z_to_bv 64 (de_mask e));
    C1 (b8 (de_segments e)); C1 (b8 (de_len e)) ]
  ++ arr_cells 9 (de_text e) ++ arr_cells 8 (de_seg e)
  ++ [ C1 (b8 (de_dots e)); C1 (b8 (de_device e)); C1 (b8 0) ]
  ++ dmsg_cells body mpad (de_msg e).

(* ---- the personalities table (.data.rel.ro, 2 entries of 24 bytes) ----
   diginet_personality_of 0x13dec: auipc a0, 0xa and 0x13df0: addi a0, a0, -0x564 give 0x1d888; 0x13ddc: auipc
   a0, 0xa and 0x13de0: addi a0, a0, -0x53c give the second entry 0x1d8a0. Entry layout (struct
   diginet_personality): desk 0 (u32), padding 4..7, announce_name 8, device 16, strips 17, scribble_chars 18,
   counter_addr 19, padding 20..23; the image bytes at 0x1d888 are
   01000000 00000000 3303010000000000 01 18 04 19 00000000 and
   02000000 00000000 2a03010000000000 00 08 08 09 00000000. *)
Definition PERSONALITIES : Z := 0x1d888.
Definition NAME_CNTRL24 : Z := 0x10333.   (* "CNTRL|24" NUL *)
Definition NAME_MAINUNIT : Z := 0x1032a.  (* "MAINUNIT" NUL *)

(* the C pointer of a DgnLib.v personality index: &personalities[i], or NULL *)
Definition personality_ptr (p : option Z) : Z :=
  match p with Some i => PERSONALITIES + 24 * i | None => 0 end.

(* the 24 bytes of an entry whose announce_name is at name *)
Definition personality_cells (name : Z) (p : dgn_personality) : list cell :=
  [ C4 (Z_to_bv 64 (dp_desk p)); CB 4 [b8 0; b8 0; b8 0; b8 0]; C8 (Z_to_bv 64 name);
    C1 (b8 (dp_device p)); C1 (b8 (dp_strips p)); C1 (b8 (dp_scribble_chars p));
    C1 (b8 (dp_counter_addr p)); CB 4 [b8 0; b8 0; b8 0; b8 0] ].

(* the 48 bytes at PERSONALITIES, DgnLib.v's personalities in memory *)
Definition personalities_cells : list cell :=
  match personalities with
  | [p0; p1] => personality_cells NAME_CNTRL24 p0 ++ personality_cells NAME_MAINUNIT p1
  | _ => []
  end.

(* ---- struct diginet_decoder (40 bytes) ----
   c 0..31      diginet_decoder_init 0x13f98: mv s0, a0 and 0x13fa8: mv a0, s0 before 0x13fb4: jal
                diginet_cursor_init with a0 = d; the cursor's 25 bytes are cursor_cells, its 7 padding bytes cpad;
                diginet_decoder_next copies the 32 bytes to its peek cursor and back (0x14200..0x1420c: ld
                0..0x18(s2); 0x14278..0x14284: sd 0..0x18(s2))
   p 32         diginet_decoder_init 0x13fc8: sd s1, 0x20(s0) *)
Definition decoder_cells (body : Z) (cpad : list byte) (d : dgn_decoder) : list cell :=
  cursor_cells body (dc_len (dd_c d)) (Z.to_nat (dc_pos (dd_c d))) (dc_status (dd_c d))
  ++ [ CB 7 cpad; C8 (Z_to_bv 64 (personality_ptr (dd_p d))) ].

(* ---- the harness's stack structs (fuzz/spec.h, fuzz/fuzz_decode.c) ---- *)

(* struct spec_msg (56 bytes). spec_msg_step (out of line in this image, at 0x13464) zeroes it before it writes
   the fields (spec.h:301: 0x13494: addi a2, zero, 0x38; 0x134a0: jal memset), so its 7 padding bytes (4..7 and
   37..39) are 0.
   code 0       spec_msg_step 0x13528: sw a0, 0(s0); check_cursor_step 0x13694: lw a3, 0(a0)
   padding 4..7
   at 8         0x134ac: sd s1, 8(s0); check_cursor_message 0x13718: ld a4, 8(a1)
   len 16       0x1355c: sd a5, 0x10(s0); 0x13724: ld a4, 0x10(a1)
   next 24      0x1352c: sd s1, 0x18(s0); check_cursor_step 0x136e0: ld a3, 0x18(a0)
   status 32    0x13564: sb a3, 0x20(s0); check_cursor_message 0x13730: lbu a4, 0x20(a1)
   running 33   0x1362c: sb a2, 0x21(s0); 0x1373c: lbu a5, 0x21(a1)
   d1 34        0x13640: sb a2, 0x22(s0); 0x13748: lbu a5, 0x22(a1)
   d2 35        0x1367c: sb a2, 0x23(s0); 0x13754: lbu a5, 0x23(a1)
   status_out 36    0x134b0: sb s4, 0x24(s0); check_cursor_step 0x136ec: lbu a0, 0x24(a0)
   padding 37..39
   sysex_at 40  0x13568: sd a0, 0x28(s0); check_cursor_message 0x13764: ld a3, 0x28(a1)
   sysex_len 48 0x1356c: sd a4, 0x30(s0); 0x1378c: ld a1, 0x30(a1) *)
Definition spec_msg_cells (m : spec_msg) : list cell :=
  [ C4 (Z_to_bv 64 (sm_code m)); CB 4 [b8 0; b8 0; b8 0; b8 0];
    C8 (Z_to_bv 64 (sm_at m)); C8 (Z_to_bv 64 (sm_len m)); C8 (Z_to_bv 64 (sm_next m));
    C1 (b8 (sm_status m)); C1 (b8 (sm_running m)); C1 (b8 (sm_d1 m)); C1 (b8 (sm_d2 m));
    C1 (b8 (sm_status_out m)); CB 3 [b8 0; b8 0; b8 0];
    C8 (Z_to_bv 64 (sm_sysex_at m)); C8 (Z_to_bv 64 (sm_sysex_len m)) ].

(* struct spec_event (40 bytes), read in struct owed at 56 (check_events_fields, s0 = o):
   kind 0       check_events_step 0x1384c: lw a1, 0x38(a1); check_events_fields 0x138e0: lw a0, 0x38(s0)
   strip 4      check_events_fields 0x1393c: lbu a1, 0x3c(s0)
   button 5     0x138fc: lbu a2, 0x3d(s0)
   zone 6       0x1391c: lbu a1, 0x3e(s0)
   on 7         0x13908: lbu a2, 0x3f(s0)
   right 8      0x13ae0: lbu a1, 0x40(s0)
   addr 9       0x13a08: lbu a1, 0x41(s0)
   device 10    0x139a0: lbu a1, 0x42(s0)
   len 11       0x13a7c: lbu a0, 0x43(s0)
   dots 12      0x13a14: lbu a1, 0x44(s0)
   padding 13
   value 14     0x13948: lhu a1, 0x46(s0)
   mask 16      0x13a58: lhu a1, 0x48(s0)
   delta 18     0x13974: lhu a2, 0x4a(s0)
   segments 20  0x13af8: lbu a1, 0x4c(s0)
   text 21..28  0x13a88: addi a1, s0, 0x4d
   seg 29..36   0x13a20: addi a1, s0, 0x55
   padding 37..39
   The harness zeroes it (owed_at's memset, fuzz_decode.c:133, which the compiler merges with o->lsb_missing = 0
   at :132: LLVMFuzzerTestOneInput 0x12f34: addi a2, zero, 0x2c and 0x12f40: jal memset at o + 56 = sp + 0x50), so
   its padding bytes are 0. *)
Definition spec_event_cells (e : spec_event) : list cell :=
  [ C4 (Z_to_bv 64 (se_kind e));
    C1 (b8 (se_strip e)); C1 (b8 (se_button e)); C1 (b8 (se_zone e)); C1 (b8 (se_on e));
    C1 (b8 (se_right e)); C1 (b8 (se_addr e)); C1 (b8 (se_device e)); C1 (b8 (se_len e));
    C1 (b8 (se_dots e)); C1 (b8 0);
    C2 (Z_to_bv 64 (se_value e)); C2 (Z_to_bv 64 (se_mask e)); C2 (Z_to_bv 64 (se_delta e));
    C1 (b8 (se_segments e)) ]
  ++ arr_cells 8 (se_text e) ++ arr_cells 8 (se_seg e)
  ++ [ CB 3 [b8 0; b8 0; b8 0] ].

(* struct owed (120 bytes), the decoder loop's o at sp + 0x18 in LLVMFuzzerTestOneInput (0x12f14: addi a4, sp,
   0x18, the struct spec_msg argument of spec_msg_step):
   m 0          check_events_step 0x137b0: lw a4, 0(a1)
   e 56         check_events_step 0x1384c: lw a1, 0x38(a1)
   lsb_missing 96   check_events_fields 0x13954: lw a1, 0x60(s0); LLVMFuzzerTestOneInput 0x1319c: sw s9,
                0x78(sp)
   padding 100..103
   next 104     LLVMFuzzerTestOneInput 0x12f2c: sd s5, 0x80(sp) and 0x1321c: ld a2, 0x80(sp)
   status_out 112   0x12f30: sb s6, 0x88(sp) and 0x13220: lbu a0, 0x88(sp)
   padding 113..119; the event follows at o + 120 (0x131cc: addi a0, sp, 0x90).
   No code writes the padding bytes 100..103 and 113..119: they are p1 and p2. *)
Definition owed_cells (p1 p2 : list byte) (o : owed) : list cell :=
  spec_msg_cells (ow_m o) ++ spec_event_cells (ow_e o)
  ++ [ C4 (Z_to_bv 64 (ow_lsb_missing o)); CB 4 p1; C8 (Z_to_bv 64 (ow_next o));
       C1 (b8 (ow_status_out o)); CB 7 p2 ].

(* ---- sizes ---- *)

Lemma dmsg_cells_size : forall body pad m, cells_size (dmsg_cells body pad m) = 40%nat.
Proof. reflexivity. Qed.
Lemma event_cells_size : forall body pad e, cells_size (event_cells body pad e) = 80%nat.
Proof. reflexivity. Qed.
Lemma personalities_cells_size : cells_size personalities_cells = 48%nat.
Proof. reflexivity. Qed.
Lemma decoder_cells_size : forall body cpad d, cells_size (decoder_cells body cpad d) = 40%nat.
Proof. reflexivity. Qed.
Lemma spec_msg_cells_size : forall m, cells_size (spec_msg_cells m) = 56%nat.
Proof. reflexivity. Qed.
Lemma spec_event_cells_size : forall e, cells_size (spec_event_cells e) = 40%nat.
Proof. reflexivity. Qed.
Lemma owed_cells_size : forall p1 p2 o, cells_size (owed_cells p1 p2 o) = 120%nat.
Proof. reflexivity. Qed.
