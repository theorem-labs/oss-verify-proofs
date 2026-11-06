(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the contract of diginet_meter_segments (src/diginet_codec.c:209-215) on the UBSan
   image, the leaf at 0x13f4c (14 words, no call, no frame, no UBSan check site), over lib/Spec/DgnLib.v's
   diginet_meter_segments.
   The argument is a uint16_t, so a caller passes it zero-extended: a0 = mask with 0 <= mask < 2^16 (the one caller,
   diginet_decoder_next, passes (pl[1] & 0x7f) << 7 | (pl[2] & 0x7f) from 0x14398 `or a0, a0, a1`). The loop
   0x13f50-0x13f64 tests bit n of the low 32 bits of a0 (`srlw`, `andi 1`) for n = 0..13; 0x13f70-0x13f7c returns
   (mask >> n) ? -1 : n as an int, sign-extended in a0. The function writes a0, a1 and a2 and no memory. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib.
Open Scope Z_scope.

Definition DIGINET_METER_SEGMENTS_ENTRY : Z := 0x13f4c.

Definition diginet_meter_segments_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    bv_unsigned a0 < 2 ^ 16 ->
    evt rsegs
      (fun ms' => exists a1' a2' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 (diginet_meter_segments (bv_unsigned a0))) a1' a2' a3
                       a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_METER_SEGMENTS_ENTRY) fc None m (seg_rom rsegs)).
