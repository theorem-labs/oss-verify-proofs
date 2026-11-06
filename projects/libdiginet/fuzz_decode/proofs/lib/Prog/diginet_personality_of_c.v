(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Contract of diginet_personality_of in fuzz_decode.plain.
   Source: src/diginet_codec.c:27-33 at 835f336c. The binary unrolls the loop over the two entries:
   desk 1 gives &personalities[0], desk 2 &personalities[1], any other desk NULL.
   Address 0x13cc0, size 44 bytes. No stack frame, no load, no store.
   Arguments: a0 is the enum diginet_desk desk, an int the caller sign-extends to 64 bits. The callers
   are LLVMFuzzerTestOneInput (desk = DESK[sel % 3], a lw of 0, 1 or 2) and diginet_decoder_init
   (desk = 1).
   Precondition: desk is an int (-2^31 <= desk < 2^31).
   Result: a0 is personality_ptr (diginet_personality_of desk) (DgnLayout.v, DgnLib.v): 0x1d690,
   0x1d6a8 or 0. The function writes a1 and a2. It keeps all other registers and the memory.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import DgnLayout.
Import ListNotations.
Open Scope Z_scope.

Definition DIGINET_PERSONALITY_OF : Z := 0x13cc0.

Definition diginet_personality_of_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (desk : Z),
    -2^31 <= desk < 2^31 ->
    evt rsegs
      (fun ms' => exists (a1' a2' : word),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 (personality_ptr (diginet_personality_of desk))) a1' a2' a3
                       a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 desk) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_PERSONALITY_OF) fc None m (seg_rom rsegs)).
