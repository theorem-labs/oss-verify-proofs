(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/U/Prog/diginet_meter_segments_c.v, with its module paths changed; 8 of its 19 lines of code are new or changed and 8 lines of the source are left out. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import RateCfg.
Import ListNotations.
Open Scope Z_scope.

(** reac_rate_cfg_decide(role, hz, mask) (reac_rate_cfg.c:77-90; 84 bytes, 21 instructions at 0x14f94 in the UBSan
    image): the plain code (Prog/reac_rate_cfg_decide_c.v, 0x14c04) at another address, instruction for instruction
    (no auipc, no trap branch): `bne a0,1`, the three 64-bit rate compares of a1, the 64-bit `and` with a2, `seqz`.
    Total: on every entry it returns decide_res (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) (Pod/RateCfg.v)
    in a0. It writes a0, a3 and, on the closed path, a2; it stores nothing, reads no memory and uses no stack.

    Call site (LLVMFuzzerTestOneInput, UBSan): 0x14534 `jal reac_rate_cfg_decide` in the two-pass decide loop
    (0x1451c .. 0x14600 `bne s1,s9` with s9 = 2), with
      a0 = s4 = role (0x14528 `mv a0,s4`; 0x144fc `srli s4,a1,0x3f` with a1 = flags << 62 from 0x144e0): flags
           bit 1, 0 or 1;
      a1 = s6 = asked[i] (0x14524 `lw s6,0(s7)`, 0x1452c `mv a1,s6`; s7 = sp + 0xe8 + 4 i): the cell sp + 0xe8 holds
           hz (0x144f4 `lw a2,0x188(sp)`) when rc = 1 (0x144e4 `beq s4,s0` with s0 = 1), else 48000 (0x144e8-0x144ec),
           stored at 0x14500; the cell sp + 0xec holds other (0x144bc-0x144dc, stored at 0x14504);
      a2 = s10 = mask (0x14530 `mv a2,s10`; 0x14518 `ld s10,0x10(sp)`), input byte 1.
    The result goes to s5 (0x14538) and on to check_decide's a0 (0x145a8), reac_rate_refuse_code's a0 (0x145b0) and
    check_code's a1 (0x145b8). No premise. *)
Definition REAC_RATE_CFG_DECIDE : Z := 0x14f94.

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
