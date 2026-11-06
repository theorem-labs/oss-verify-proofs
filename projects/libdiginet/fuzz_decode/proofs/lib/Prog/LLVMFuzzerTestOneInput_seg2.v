(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the statements of the set-up and the two loops of LLVMFuzzerTestOneInput (plain
   image), each proved in its own file and put together by LLVMFuzzerTestOneInput.v, over the inlined segments of
   LLVMFuzzerTestOneInput_seg.v and the callee contracts.

   The frame at Sp (448 bytes; LLVMFuzzerTestOneInput_seg.v): fr_head (32 bytes: unused, sel or the jump table base,
   buf, body + 1), 312 bytes of structs, the 13 saved registers (saved, 104 bytes). In the cursor loop the 312 bytes
   are m (56), 224 bytes of no use to it (the rest of o, ev, msg at +144, d), the cursor c (25) and its 7 padding
   bytes; in the decoder loop o (120), ev (80), msg (40, of no use), the decoder d (40), the cursor c (32, of no use).
   Callees run below Sp, down to lo.

   setup_stmt: from malloc's return (0x12d38) to the cursor loop's head (0x12ddc) after 0 passes: the NULL test,
     sd buf / sel, memcpy (buf, data + 1, n), the frame-mode tests (spec_read_frame inlined), diginet_cursor_init
     (&c, body, len) and the loop's registers. The body is some bytes bb in the copy, below the stack.
   cloop_stmt: from the cursor loop's head after k passes to its exit (0x13024).
   dsetup_stmt: from 0x13024 to the decoder loop's head (0x1309c) after 0 passes: DESK[sel % 3],
     diginet_personality_of, diginet_decoder_init (&d, p, body, len) and the loop's registers.
   dloop_stmt: from the decoder loop's head after k passes to its exit (0x13678). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import memset_c memcpy_c DgnLayout
  diginet_cursor_init_c diginet_msg_next_c diginet_personality_of_c diginet_decoder_init_c diginet_decoder_next_c
  check_cursor_step_c check_cursor_message_c check_events_step_c check_events_fields_c
  LLVMFuzzerTestOneInput_seg.
Import ListNotations.
Open Scope Z_scope.

(* the running status a cursor holds: none, or a channel status 80..EF *)
Definition lp_st (st : Z) : Prop := st = 0 \/ 0x80 <= st < 0xf0.

(* malloc (n ? n : 1), fuzz.h's fuzz_dup *)
Definition dup_size (n : Z) : Z := if n =? 0 then 1 else n.

(* the footprint of a loop: the callees' stack below Sp and the 312 bytes of structs *)
Definition loop_fp (lo Sp : Z) : list (Z * Z) := [(lo, Sp + 344)].

(* the facts of the stack below Sp the callees use *)
Definition lo_ok (lo Sp body : Z) (bb : list byte) : Prop :=
  0 <= lo /\ lo + 160 <= Sp /\ body + Z.of_nat (length bb) <= lo.

(* ---- the cursor loop ---- *)

(* the exit of the cursor loop, 0x13024: s2 = len, s5 = body; the 312 bytes are junk *)
Definition cexit (Q : machine_state -> Prop) (x3 x4 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (Sp lo body : Z) (bb j0 : list byte) (w8 w10 : word) (saved : list cell) : Prop :=
  forall (r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 : word)
         (m' : word -> option byte) (jj : list byte),
    munch (loop_fp lo Sp) m0 m' -> wmono rsegs m0 m' -> mem_inv rsegs m' -> stk rsegs m' lo Sp ->
    bytes_at rsegs m' body bb ->
    rw_cells rsegs m' Sp (fr_head j0 w8 w10 body ++ CB 312 jj :: saved) ->
    evt rsegs Q
      (MS (mkR r1 (Z_to_bv 64 Sp) x3 x4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17
             (Z_to_bv 64 (Z.of_nat (length bb))) r19 r20 (Z_to_bv 64 body) r22 r23 r24 r25 r26 r27 r28 r29 r30 r31)
          F (Z_to_bv 64 0x13024) fc None m' (seg_rom rsegs)).

Definition cloop_stmt : Prop :=
  memset_contract -> diginet_msg_next_contract -> check_cursor_step_contract -> check_cursor_message_contract ->
  cstep_stmt ->
  forall (x3 x4 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
    (Sp lo body : Z) (bb j0 : list byte) (w8 w10 : word) (saved : list cell) (Q : machine_state -> Prop),
  seg_ok Sp body bb -> lo_ok lo Sp body bb -> cells_size saved = 104%nat ->
  cexit Q x3 x4 F fc m0 Sp lo body bb j0 w8 w10 saved ->
  forall (k pos status : Z)
    (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x26 x28 x29 x30 x31 : word)
    (m : word -> option byte) (mj jA cpad : list byte),
  0 <= k <= Z.of_nat (length bb) -> 0 <= pos <= Z.of_nat (length bb) -> lp_st status ->
  munch (loop_fp lo Sp) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo Sp ->
  bytes_at rsegs m body bb ->
  rw_cells rsegs m Sp (fr_head j0 w8 w10 body ++ CB 56 mj :: CB 224 jA ::
    cursor_cells body (Z.of_nat (length bb)) (Z.to_nat pos) status ++ CB 7 cpad :: saved) ->
  evt rsegs Q
    (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 (Z_to_bv 64 status) x9 x10 x11 x12 x13 x14 x15 x16 x17
           (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 k) x20 (Z_to_bv 64 body)
           (Z_to_bv 64 (- Z.of_nat (length bb))) (Z_to_bv 64 240) (Z_to_bv 64 247) (Z_to_bv 64 pos) x26
           (Z_to_bv 64 241) x28 x29 x30 x31)
        F (Z_to_bv 64 0x12ddc) fc None m (seg_rom rsegs)).

(* ---- the decoder loop ---- *)

(* the exit of the decoder loop, 0x13678: s2 = len, s5 = body *)
Definition dexit (Q : machine_state -> Prop) (x3 x4 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (Sp lo body : Z) (bb j0 : list byte) (w10 : word) (saved : list cell) : Prop :=
  forall (r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 : word)
         (m' : word -> option byte) (jj : list byte),
    munch (loop_fp lo Sp) m0 m' -> wmono rsegs m0 m' -> mem_inv rsegs m' -> stk rsegs m' lo Sp ->
    bytes_at rsegs m' body bb ->
    rw_cells rsegs m' Sp (fr_head j0 (Z_to_bv 64 0x103a4) w10 body ++ CB 312 jj :: saved) ->
    evt rsegs Q
      (MS (mkR r1 (Z_to_bv 64 Sp) x3 x4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17
             (Z_to_bv 64 (Z.of_nat (length bb))) r19 r20 (Z_to_bv 64 body) r22 r23 r24 r25 r26 r27 r28 r29 r30 r31)
          F (Z_to_bv 64 0x13678) fc None m' (seg_rom rsegs)).

Definition dloop_stmt : Prop :=
  memset_contract -> memcpy_contract -> diginet_decoder_next_contract ->
  check_events_step_contract -> check_events_fields_contract ->
  dstep_stmt -> dsysex_stmt -> dchan_stmt ->
  forall (x3 x4 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
    (Sp lo body : Z) (bb j0 : list byte) (w10 : word) (saved : list cell) (p : option Z)
    (Q : machine_state -> Prop),
  seg_ok Sp body bb -> lo_ok lo Sp body bb -> cells_size saved = 104%nat ->
  dexit Q x3 x4 F fc m0 Sp lo body bb j0 w10 saved ->
  forall (k pos status : Z)
    (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x25 x28 x29 x30 x31 : word)
    (m : word -> option byte) (oj jE jM cpad jC : list byte),
  0 <= k <= Z.of_nat (length bb) -> 0 <= pos <= Z.of_nat (length bb) -> lp_st status ->
  munch (loop_fp lo Sp) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo Sp ->
  bytes_at rsegs m body bb ->
  rw_cells rsegs m Sp (fr_head j0 (Z_to_bv 64 0x103a4) w10 body ++ CB 120 oj :: CB 80 jE :: CB 40 jM ::
    decoder_cells body cpad (decoder_at (Z.of_nat (length bb)) (Z.to_nat pos) status p) ++ CB 32 jC :: saved) ->
  evt rsegs Q
    (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 (Z_to_bv 64 pos) x9 x10 x11 x12 x13 x14 x15 x16 x17
           (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 (Sp + 88)) x20 (Z_to_bv 64 body) (Z_to_bv 64 k)
           (Z_to_bv 64 status) (Z_to_bv 64 (- Z.of_nat (length bb))) x25 (Z_to_bv 64 247) (Z_to_bv 64 1)
           x28 x29 x30 x31)
        F (Z_to_bv 64 0x1309c) fc None m (seg_rom rsegs)).

(* ---- the set-up ---- *)

(* the cursor loop's head after 0 passes, for some body bb in the copy *)
Definition chead0 (Q : machine_state -> Prop) (x3 x4 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (Sp lo buf n : Z) (w8 : word) (saved : list cell) : Prop :=
  forall (body : Z) (bb j0 mj jA cpad : list byte)
    (r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r20 r26 r28 r29 r30 r31 : word) (m : word -> option byte),
    seg_ok Sp body bb -> lo_ok lo Sp body bb ->
    buf <= body -> body + Z.of_nat (length bb) <= buf + dup_size n ->
    munch [(lo, Sp + 448); (buf, buf + dup_size n)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
    stk rsegs m lo Sp -> bytes_at rsegs m body bb ->
    rw_cells rsegs m Sp (fr_head j0 w8 (Z_to_bv 64 buf) body ++ CB 56 mj :: CB 224 jA ::
      cursor_cells body (Z.of_nat (length bb)) 0 0 ++ CB 7 cpad :: saved) ->
    evt rsegs Q
      (MS (mkR r1 (Z_to_bv 64 Sp) x3 x4 r5 r6 r7 (Z_to_bv 64 0) r9 r10 r11 r12 r13 r14 r15 r16 r17
             (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 0) r20 (Z_to_bv 64 body)
             (Z_to_bv 64 (- Z.of_nat (length bb))) (Z_to_bv 64 240) (Z_to_bv 64 247) (Z_to_bv 64 0) r26
             (Z_to_bv 64 241) r28 r29 r30 r31)
          F (Z_to_bv 64 0x12ddc) fc None m (seg_rom rsegs)).

(* from malloc's return: s0 = size, s2 = n = size - 1, s3 = data, s4 = the sign-extended data[0], a0 = buf *)
Definition setup_stmt : Prop :=
  memcpy_contract -> diginet_cursor_init_contract ->
  forall (x1 x3 x4 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (Sp lo p buf : Z) (pl junk j : list byte) (saved : list cell) (Q : machine_state -> Prop),
  0 <= Sp -> Sp + 448 <= 2 ^ 63 -> 0 <= lo -> lo + 160 <= Sp ->
  1 <= Z.of_nat (length pl) < 2 ^ 26 -> cells_size saved = 104%nat ->
  4096 <= buf -> buf + dup_size (Z.of_nat (length pl) - 1) <= lo ->
  0 <= p -> p + Z.of_nat (length pl) <= lo ->
  buf + dup_size (Z.of_nat (length pl) - 1) <= p \/ p + Z.of_nat (length pl) <= buf ->
  bytes_at rsegs m p pl ->
  rw_cells rsegs m buf [CB (Z.to_nat (dup_size (Z.of_nat (length pl) - 1))) junk] ->
  rw_cells rsegs m Sp (CB 344 j :: saved) ->
  mem_inv rsegs m -> stk rsegs m lo Sp ->
  chead0 Q x3 x4 F fc m Sp lo buf (Z.of_nat (length pl) - 1) (sxb (nth 0 pl (Z_to_bv 8 0))) saved ->
  evt rsegs Q
    (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 (Z_to_bv 64 (Z.of_nat (length pl))) x9 (Z_to_bv 64 buf)
           x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (Z.of_nat (length pl) - 1)) (Z_to_bv 64 p)
           (sxb (nth 0 pl (Z_to_bv 8 0))) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x12d38) fc None m (seg_rom rsegs)).

(* the decoder loop's head after 0 passes *)
Definition dhead0 (Q : machine_state -> Prop) (x3 x4 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (Sp lo body : Z) (bb j0 : list byte) (w10 : word) (saved : list cell) : Prop :=
  forall (p : option Z) (oj jE jM cpad jC : list byte)
    (r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r20 r25 r28 r29 r30 r31 : word) (m : word -> option byte),
    munch (loop_fp lo Sp) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo Sp ->
    bytes_at rsegs m body bb ->
    rw_cells rsegs m Sp (fr_head j0 (Z_to_bv 64 0x103a4) w10 body ++ CB 120 oj :: CB 80 jE :: CB 40 jM ::
      decoder_cells body cpad (decoder_at (Z.of_nat (length bb)) 0 0 p) ++ CB 32 jC :: saved) ->
    evt rsegs Q
      (MS (mkR r1 (Z_to_bv 64 Sp) x3 x4 r5 r6 r7 (Z_to_bv 64 0) r9 r10 r11 r12 r13 r14 r15 r16 r17
             (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 (Sp + 88)) r20 (Z_to_bv 64 body) (Z_to_bv 64 0)
             (Z_to_bv 64 0) (Z_to_bv 64 (- Z.of_nat (length bb))) r25 (Z_to_bv 64 247) (Z_to_bv 64 1)
             r28 r29 r30 r31)
          F (Z_to_bv 64 0x1309c) fc None m (seg_rom rsegs)).

(* from the cursor loop's exit: 8(sp) holds the sign-extended sel *)
Definition dsetup_stmt : Prop :=
  diginet_personality_of_contract -> diginet_decoder_init_contract ->
  forall (r1 x3 x4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (Sp lo body : Z) (bb j0 jj : list byte) (sel : byte) (w10 : word) (saved : list cell)
    (Q : machine_state -> Prop),
  seg_ok Sp body bb -> lo_ok lo Sp body bb -> cells_size saved = 104%nat ->
  mem_inv rsegs m -> stk rsegs m lo Sp -> bytes_at rsegs m body bb ->
  rw_cells rsegs m Sp (fr_head j0 (sxb sel) w10 body ++ CB 312 jj :: saved) ->
  dhead0 Q x3 x4 F fc m Sp lo body bb j0 w10 saved ->
  evt rsegs Q
    (MS (mkR r1 (Z_to_bv 64 Sp) x3 x4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17
           (Z_to_bv 64 (Z.of_nat (length bb))) r19 r20 (Z_to_bv 64 body) r22 r23 r24 r25 r26 r27 r28 r29 r30 r31)
        F (Z_to_bv 64 0x13024) fc None m (seg_rom rsegs)).
