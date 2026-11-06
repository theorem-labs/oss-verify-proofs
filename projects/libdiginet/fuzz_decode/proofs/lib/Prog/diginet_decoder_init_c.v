(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Contract of diginet_decoder_init in fuzz_decode.plain.
   Source: src/diginet_decode.c:11-18 at 835f336c. It calls diginet_cursor_init (0x13b10) one time
   and, when p is NULL, diginet_personality_of (0x13cc0) with desk 1; neither uses the stack.
   Address 0x13e30, size 80 bytes. Stack frame: 32 bytes (ra, s0, s1 at sp - 8, sp - 16, sp - 24).
   Arguments: a0 is the address d of a struct diginet_decoder (40 bytes), a1 the personality pointer
   personality_ptr p, a2 the address body, a3 the length len. The caller is LLVMFuzzerTestOneInput: d
   in its stack frame, p from diginet_personality_of, its body and length.
   Preconditions:
   - d is not 0, and body is not 0 (the DgnLib.v model of diginet_cursor_init takes c->len = len);
     body and len are 64-bit values (0 <= body, len < 2^64);
   - p is None or Some 0 or Some 1;
   - the 40 bytes dj at d are writable (rw_cells);
   - the stack from lo to sp is writable (stk), lo + 32 <= sp, and the 40 bytes at d are not in the
     32 bytes below sp;
   - mem_inv holds.
   Result: the decoder at d is diginet_decoder_init p len (DgnLib.v) as decoder_cells gives it
   (DgnLayout.v): the cursor body, len, 0, 0; its 7 padding bytes as they were; d->p = p, or
   &personalities[0] when p is None.
   The function writes only the 40 bytes at d and the 32 bytes below sp. It writes a0..a3. It keeps
   ra, sp, gp, tp, s0..s11, t0..t6, a4..a7, the floating-point registers and fcsr, and the stack from
   lo to sp stays writable.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import DgnLayout.
Import ListNotations.
Open Scope Z_scope.

Definition DIGINET_DECODER_INIT : Z := 0x13e30.

Definition diginet_decoder_init_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (d body len lo : Z) (p : option Z) (dj : list byte),
    d <> 0 -> body <> 0 -> 0 <= body < 2^64 -> 0 <= len < 2^64 ->
    (forall i, p = Some i -> 0 <= i < 2) ->
    rw_cells rsegs m d [CB 40 dj] ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp ->
    d + 40 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= d ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' a3' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(d, d + 40); (bv_unsigned sp - 32, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         rw_cells rsegs m' d (decoder_cells body (firstn 7 (skipn 25 dj)) (diginet_decoder_init p len)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 (personality_ptr p))
               (Z_to_bv 64 body) (Z_to_bv 64 len) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_DECODER_INIT) fc None m (seg_rom rsegs)).
