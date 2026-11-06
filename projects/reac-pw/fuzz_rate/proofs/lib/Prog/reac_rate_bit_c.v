From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import RateCfg.
Import ListNotations.
Open Scope Z_scope.

(** reac_rate_bit(hz) (reac_rate_cfg.c:30-38; 68 bytes, 17 instructions at 0x149f4 in the plain image):
      0x149f4 lui a1,0xb; addiw a1,a1,-0x3bc (44100); beq a0,a1,0x14a28;
              lui a1,0x17; addiw a1,a1,0x700 (96000); beq a0,a1,0x14a20;
              lui a1,0xc; addiw a1,a1,-0x480 (48000); bne a0,a1,0x14a30; addi a0,zero,2; ret;
      0x14a20 addi a0,zero,4; ret;  0x14a28 addi a0,zero,1; ret;  0x14a30 mv a0,zero; ret.
    Total: on every entry it returns rate_bit (bv_unsigned a0) (Pod/RateCfg.v) in a0; the compares read the whole
    64-bit a0. It writes a0 and a1, stores nothing, reads no memory and uses no stack.

    Call site (LLVMFuzzerTestOneInput, plain): 0x144b0 `jal reac_rate_bit` in the two-pass decide loop (0x14414 ..
    0x144f0 `bnez a0,-0xdc`), with a0 = s5 = asked[i] (0x144ac `mv a0,s5`); the result goes to s6 (0x144b4) and on to
    check_list's a1 (0x144d4 `mv a1,s6`). No premise: the contract holds for any a0. *)
Definition REAC_RATE_BIT : Z := 0x149f4.

Definition reac_rate_bit_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs
      (fun ms' => exists (a1' : word),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (rate_bit (bv_unsigned a0))) a1' a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_RATE_BIT) fc None m (seg_rom rsegs)).
