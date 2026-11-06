(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/U/Prog/diginet_meter_segments_c.v, with its module paths changed; 8 of its 19 lines of code are new or changed and 8 lines of the source are left out. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import RateCfg.
Import ListNotations.
Open Scope Z_scope.

(** reac_rate_cfg_decide(role, hz, mask) (reac_rate_cfg.c:77-90; 84 bytes, 21 instructions at 0x14c04 in the plain
    image; reac_rate_is_closed and reac_rate_bit inlined):
      0x14c04 addi a3,zero,1; bne a0,a3,0x14c14; addi a3,zero,3; j 0x14c50;
      0x14c14 lui a0,0xb; addiw a0,a0,-0x3bc (44100); beq a1,a0,0x14c44;
              lui a0,0x17; addiw a0,a0,0x700 (96000); beq a1,a0,0x14c40;
              lui a0,0xc; addiw a0,a0,-0x480 (48000); bne a1,a0,0x14c50 (a3 = 1); addi a3,zero,2; j 0x14c44;
      0x14c40 addi a3,zero,4;
      0x14c44 and a2,a3,a2; seqz a3,a2; slli a3,a3,1;
      0x14c50 mv a0,a3; ret.
    Total: on every entry it returns decide_res (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) (Pod/RateCfg.v)
    in a0: 3 (ROLE_SLAVE) when a0 = 1 as a 64-bit word, else 1 (NOT_CLOSED) when a1 is none of the three rates as a
    64-bit word, else 2 (NOT_DRIVABLE) when the rate's bit and a2 have no common bit (64-bit and), else 0 (NONE). It
    writes a0, a3 and, on the closed path, a2; it stores nothing, reads no memory and uses no stack.

    Call site (LLVMFuzzerTestOneInput, plain): 0x14420 `jal reac_rate_cfg_decide` in the two-pass decide loop
    (0x14414 .. 0x144f0 `bnez a0,-0xdc`; s0 = 1 on the first pass, 0 on the second, 0x144ec), with
      a0 = s4 = role (0x14414 `mv a0,s4`; 0x14404 `srli s4,a1,0x3f` with a1 = flags << 62 from 0x143e8): flags
           bit 1, 0 or 1;
      a1 = s5 = asked[i] (0x14418 `mv a1,s5`): on the first pass hz (0x143fc `lw s5,0x158(sp)`) when rc = 1
           (0x143ec `beq s4,s0` with s0 = 1), else 48000 (0x143f0-0x143f4); on the second pass other (0x144e8
           `mv s5,s1`), the sign extension of the u32 at input bytes 3..6 (0x143dc-0x14400);
      a2 = s9 = mask (0x1441c `mv a2,s9`), input byte 1.
    The result goes to s6 (0x14424) and on to check_decide's a0 (0x14494), reac_rate_refuse_code's a0 (0x1449c) and
    check_code's a1 (0x144a4). No premise: the contract holds for every role, rate and mask. *)
Definition REAC_RATE_CFG_DECIDE : Z := 0x14c04.

Definition reac_rate_cfg_decide_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs
      (fun ms' => exists (a2' a3' : word),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 (decide_res (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2))) a1 a2' a3'
                       a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_RATE_CFG_DECIDE) fc None m (seg_rom rsegs)).
