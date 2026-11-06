(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the statements of the inlined segments of LLVMFuzzerTestOneInput (plain image,
   0x12cd4, 2568 bytes), each proved in its own file and put together by LLVMFuzzerTestOneInput.v.

   The frame is 448 bytes at Sp (= the entry sp - 0x1c0). The cells the segments read or write:
     Sp + 0x08  C8: sel (cursor loop) / the jump table base 0x103a4 (decoder loop, 0x13098)
     Sp + 0x10  C8: buf
     Sp + 0x18  C8: body + 1 (0x12dcc; the F7 scan base, 0x12e28 and 0x130d8)
     Sp + 0x20  56 bytes: struct spec_msg m (cursor loop); 120 bytes: struct owed o (decoder loop)
   The body is bb (bytes_at) at body, of length len < 2^26, below the frame. A segment's statement is in
   continuation form: the hypothesis K is the rest of the run from the segment's end state.

   cstep_stmt: the cursor loop's memset (&m, 0, 56) and the inlined spec_msg_step (0x12ddc .. 0x12ef8). At the
     end s1 = m.next, s10 = m.status_out, s4 = (m.code == 1), m = spec_msg_cells of DgnSpec.spec_msg_step.
   dstep_stmt: the decoder loop's memset (&o.m, 0, 56), the inlined spec_msg_step, o.next, o.status_out and
     memset (&o.e, 0, 44) (0x1309c ..): a step that is no message reaches 0x13180 with o = owed_at; a sysex
     message reaches 0x13228 and a channel message 0x133d0, with o = owed0 (the message, a zero event).
   dsysex_stmt: spec_event_of of a sysex message (0x13228 .. 0x13180): kind OTHER, maker, device, the jump
     table 0x103a4 on fn >> 4 (ring, meter, LEDs, counter, scribble, system).
   dchan_stmt: spec_event_of of a channel message (0x133d0 .. 0x13180): note (zone key, touch, strip button),
     control change (fader with the LSB lookahead, jog, V-Pot), OTHER. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import memset_c memcpy_c DgnLayout.
Import ListNotations.
Open Scope Z_scope.

(* the body as DgnSpec.v reads it *)
Definition bzl (bb : list byte) : list Z := map bz bb.

(* the frame's first 32 bytes: 8 unused, two words, body + 1 *)
Definition fr_head (j0 : list byte) (w8 w10 : word) (body : Z) : list cell :=
  [CB 8 j0; C8 w8; C8 w10; C8 (Z_to_bv 64 (body + 1))].

(* the owed of a message step before spec_event_of: the zero event *)
Definition owed0 (m : spec_msg) : owed := Owed m se_zero 0 (sm_next m) (sm_status_out m).

(* the padding bytes of struct owed that no code writes (DgnLayout.owed_cells p1 p2) *)
Definition ow_p1 (oj : list byte) : list byte := firstn 4 (skipn 100 oj).
Definition ow_p2 (oj : list byte) : list byte := skipn 113 oj.

(* the facts every segment keeps about its frame and the body *)
Definition seg_ok (Sp body : Z) (bb : list byte) : Prop :=
  0 <= Sp /\ Sp + 448 <= 2 ^ 63 /\ 0 < body /\ body + Z.of_nat (length bb) <= Sp /\
  Z.of_nat (length bb) < 2 ^ 26.

(* ---- the cursor loop's step, 0x12ddc .. 0x12ef8 ---- *)
Definition cstep_stmt : Prop :=
  memset_contract ->
  forall (x1 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x26 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (Sp body pos status : Z) (bb j0 mj : list byte) (w8 w10 : word) (rest : list cell)
    (Q : machine_state -> Prop),
  seg_ok Sp body bb ->
  0 <= pos <= Z.of_nat (length bb) -> 0 <= status < 256 ->
  bytes_at rsegs m body bb ->
  rw_cells rsegs m Sp (fr_head j0 w8 w10 body ++ CB 56 mj :: rest) ->
  mem_inv rsegs m ->
  (forall (r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 : word) (m' : word -> option byte),
     munch [(Sp + 32, Sp + 88)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     bytes_at rsegs m' body bb ->
     rw_cells rsegs m' Sp (fr_head j0 w8 w10 body ++
       spec_msg_cells (spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status) ++ rest) ->
     evt rsegs Q
       (MS (mkR r1 (Z_to_bv 64 Sp) x3 x4 r5 r6 r7 (Z_to_bv 64 status)
              (Z_to_bv 64 (sm_next (spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status)))
              r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 (Z.of_nat (length bb))) x19
              (Z_to_bv 64 (if sm_code (spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status) =? 1 then 1 else 0))
              (Z_to_bv 64 body) (Z_to_bv 64 (- Z.of_nat (length bb))) (Z_to_bv 64 240) (Z_to_bv 64 247)
              (Z_to_bv 64 pos)
              (Z_to_bv 64 (sm_status_out (spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status)))
              (Z_to_bv 64 241) r28 r29 r30 r31)
           F (Z_to_bv 64 0x12ef8) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 (Z_to_bv 64 status) x9 x10 x11 x12 x13 x14 x15 x16 x17
           (Z_to_bv 64 (Z.of_nat (length bb))) x19 x20 (Z_to_bv 64 body) (Z_to_bv 64 (- Z.of_nat (length bb)))
           (Z_to_bv 64 240) (Z_to_bv 64 247) (Z_to_bv 64 pos) x26 (Z_to_bv 64 241) x28 x29 x30 x31)
        F (Z_to_bv 64 0x12ddc) fc None m (seg_rom rsegs)).

(* ---- the decoder loop ---- *)

(* the end of a pass's set-up, 0x13180: o is complete; s2, s3, s5, s6, s8, s10, s11 are the loop's *)
Definition dend (Q : machine_state -> Prop) (x3 x4 x22 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (Sp body : Z) (bb j0 oj : list byte) (w10 : word) (rest : list cell)
    (o : owed) : Prop :=
  forall (r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r20 r23 r25 r28 r29 r30 r31 : word)
         (m' : word -> option byte),
    munch [(Sp + 32, Sp + 152)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    bytes_at rsegs m' body bb ->
    rw_cells rsegs m' Sp (fr_head j0 (Z_to_bv 64 0x103a4) w10 body ++ owed_cells (ow_p1 oj) (ow_p2 oj) o ++ rest) ->
    evt rsegs Q
      (MS (mkR r1 (Z_to_bv 64 Sp) x3 x4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17
             (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 (Sp + 88)) r20 (Z_to_bv 64 body) x22 r23
             (Z_to_bv 64 (- Z.of_nat (length bb))) r25 (Z_to_bv 64 247) (Z_to_bv 64 1) r28 r29 r30 r31)
          F (Z_to_bv 64 0x13180) fc None m' (seg_rom rsegs)).

(* the hand-off state of a message step (pc 0x13228 for a sysex, 0x133d0 for a channel message): o is owed0 *)
Definition dmid (Q : machine_state -> Prop) (pc : Z) (x3 x4 x22 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (Sp body : Z) (bb j0 oj : list byte) (w10 : word) (rest : list cell)
    (pos : Z) (M : spec_msg) : Prop :=
  forall (r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r25 r28 r29 r30 r31 : word) (m' : word -> option byte),
    munch [(Sp + 32, Sp + 152)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    bytes_at rsegs m' body bb ->
    (pc <> 0x13228 -> r25 = Z_to_bv 64 (sm_d1 M)) ->
    rw_cells rsegs m' Sp (fr_head j0 (Z_to_bv 64 0x103a4) w10 body ++ owed_cells (ow_p1 oj) (ow_p2 oj) (owed0 M) ++ rest) ->
    evt rsegs Q
      (MS (mkR r1 (Z_to_bv 64 Sp) x3 x4 r5 r6 r7 (Z_to_bv 64 pos)
             (Z_to_bv 64 (if pc =? 0x13228 then body + pos else sm_status M))
             r10 r11 r12 r13 r14 r15 r16 r17
             (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 (Sp + 88))
             (Z_to_bv 64 (if pc =? 0x13228 then sm_sysex_at M else sm_next M))
             (Z_to_bv 64 body) x22
             (Z_to_bv 64 (if pc =? 0x13228 then sm_sysex_len M else sm_d2 M))
             (Z_to_bv 64 (- Z.of_nat (length bb)))
             r25
             (Z_to_bv 64 247) (Z_to_bv 64 1) r28 r29 r30 r31)
          F (Z_to_bv 64 pc) fc None m' (seg_rom rsegs)).

(* the decoder loop's step, 0x1309c: the end for a step that is no message, the hand-offs for a message *)
Definition dstep_stmt : Prop :=
  memset_contract ->
  forall (x1 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x25 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (Sp body pos status : Z) (bb j0 oj : list byte) (w10 : word) (rest : list cell)
    (Q : machine_state -> Prop),
  seg_ok Sp body bb ->
  0 <= pos <= Z.of_nat (length bb) -> 0 <= status < 240 ->
  bytes_at rsegs m body bb ->
  rw_cells rsegs m Sp (fr_head j0 (Z_to_bv 64 0x103a4) w10 body ++ CB 120 oj :: rest) ->
  mem_inv rsegs m ->
  (sm_code (spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status) <> 1 ->
   dend Q x3 x4 x22 F fc m Sp body bb j0 oj w10 rest (owed_at (bzl bb) (Z.of_nat (length bb)) pos status)) ->
  (sm_code (spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status) = 1 ->
   sm_status (spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status) = 240 ->
   dmid Q 0x13228 x3 x4 x22 F fc m Sp body bb j0 oj w10 rest pos
     (spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status)) ->
  (sm_code (spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status) = 1 ->
   sm_status (spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status) <> 240 ->
   dmid Q 0x133d0 x3 x4 x22 F fc m Sp body bb j0 oj w10 rest pos
     (spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status)) ->
  evt rsegs Q
    (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 (Z_to_bv 64 pos) x9 x10 x11 x12 x13 x14 x15 x16 x17
           (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 (Sp + 88)) x20 (Z_to_bv 64 body) x22
           (Z_to_bv 64 status) (Z_to_bv 64 (- Z.of_nat (length bb))) x25 (Z_to_bv 64 247) (Z_to_bv 64 1)
           x28 x29 x30 x31)
        F (Z_to_bv 64 0x1309c) fc None m (seg_rom rsegs)).

(* spec_event_of of a message step at the hand-off pc (0x13228 sysex: dsysex_stmt; 0x133d0 channel:
   dchan_stmt), up to 0x13180 with o = owed_at *)
Definition devent_stmt (pc : Z) (is_sysex : bool) : Prop :=
  memset_contract -> memcpy_contract ->
  forall (r1 x3 x4 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 x22 r25 r28 r29 r30 r31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (Sp body pos status : Z) (bb j0 oj : list byte) (w10 : word) (rest : list cell)
    (Q : machine_state -> Prop),
  let M := spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status in
  seg_ok Sp body bb ->
  0 <= pos <= Z.of_nat (length bb) -> 0 <= status < 240 ->
  sm_code M = 1 -> (sm_status M =? 240) = is_sysex ->
  length oj = 120%nat ->
  bytes_at rsegs m body bb ->
  (is_sysex = false -> r25 = Z_to_bv 64 (sm_d1 M)) ->
  rw_cells rsegs m Sp (fr_head j0 (Z_to_bv 64 0x103a4) w10 body ++ owed_cells (ow_p1 oj) (ow_p2 oj) (owed0 M) ++ rest) ->
  mem_inv rsegs m ->
  dend Q x3 x4 x22 F fc m Sp body bb j0 oj w10 rest (owed_at (bzl bb) (Z.of_nat (length bb)) pos status) ->
  evt rsegs Q
    (MS (mkR r1 (Z_to_bv 64 Sp) x3 x4 r5 r6 r7 (Z_to_bv 64 pos)
           (Z_to_bv 64 (if is_sysex then body + pos else sm_status M))
           r10 r11 r12 r13 r14 r15 r16 r17
           (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 (Sp + 88))
           (Z_to_bv 64 (if is_sysex then sm_sysex_at M else sm_next M))
           (Z_to_bv 64 body) x22
           (Z_to_bv 64 (if is_sysex then sm_sysex_len M else sm_d2 M))
           (Z_to_bv 64 (- Z.of_nat (length bb)))
           r25
           (Z_to_bv 64 247) (Z_to_bv 64 1) r28 r29 r30 r31)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Definition dsysex_stmt : Prop := devent_stmt 0x13228 true.
Definition dchan_stmt : Prop := devent_stmt 0x133d0 false.
