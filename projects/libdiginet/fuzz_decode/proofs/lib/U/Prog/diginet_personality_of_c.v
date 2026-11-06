(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the contract of diginet_personality_of (src/diginet_codec.c:27-33) on the UBSan
   image, the leaf at 0x13dcc (14 words: 13 instructions, no call, no frame, and the unimp at 0x13e00), over
   lib/Spec/DgnLib.v's diginet_personality_of.
   The binary unrolls the loop over the two entries: it compares the whole register a0 with 1 (Control|24) and 2
   (ProControl) and returns &personalities[0] (0x1d888) or &personalities[1] (0x1d8a0), else NULL. The model
   compares desk with the two dp_desk values, 1 and 2, so the contract reads desk as the unsigned value of a0: the
   result is the same for every a0 (a caller passes an enum diginet_desk, 0..2).
   The UBSan check is the null check of the address &personalities[1] (0x13de4 `beqz a0` to the unimp at 0x13e00);
   that address is the constant 0x1d8a0 (auipc / addi at 0x13ddc-0x13de0), so the check is never taken and takes no
   premise. The function writes a0 and a1 and no memory. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import DgnLayout.
Open Scope Z_scope.

Definition DIGINET_PERSONALITY_OF : Z := 0x13dcc.

Definition diginet_personality_of_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs
      (fun ms' => exists a1' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 (personality_ptr (diginet_personality_of (bv_unsigned a0)))) a1' a2 a3
                       a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_PERSONALITY_OF) fc None m (seg_rom rsegs)).
