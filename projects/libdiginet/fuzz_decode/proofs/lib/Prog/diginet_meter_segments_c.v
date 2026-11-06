(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Contract of diginet_meter_segments in fuzz_decode.plain.
   Source: src/diginet_codec.c:209-215 at 835f336c. The loop counts n up from 0 while bit n of mask is
   set (srlw; andi 1), at most to 14; then `(mask >> n) ? -1 : n` (srlw; seqz; addiw -1; or).
   Address 0x13df8, size 56 bytes. No stack frame, no load, no store.
   Arguments: a0 is the uint16_t mask, zero-extended by the caller. The caller is diginet_decoder_next
   (0x141ec), with a0 = (pl[1] & 0x7f) << 7 | (pl[2] & 0x7f).
   Precondition: 0 <= mask < 2^16.
   Result: a0 is diginet_meter_segments mask (DgnLib.v), an int sign-extended to 64 bits: 0..14, or
   -1. The function writes a1 and a2. It keeps all other registers and the memory.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.

(* The entry; DgnLib.v's DIGINET_METER_SEGMENTS is the constant 14 of diginet_codec.h:114. *)
Definition DIGINET_METER_SEGMENTS_PC : Z := 0x13df8.

Definition diginet_meter_segments_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mask : Z),
    0 <= mask < 2^16 ->
    evt rsegs
      (fun ms' => exists (a1' a2' : word),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (diginet_meter_segments mask)) a1' a2' a3
                       a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 mask) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_METER_SEGMENTS_PC) fc None m (seg_rom rsegs)).
