From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import RateCfg.
Import ListNotations.
Open Scope Z_scope.

(** reac_rate_is_closed(hz) (reac_rate_cfg.c:24-28; 52 bytes, 13 instructions at 0x149c0 in the plain image):
      0x149c0 lui a1,0xb; addiw a2,a1,-0x3bc (44100); addi a1,zero,1; beq a0,a2,0x149ec;
              lui a2,0xc; addiw a2,a2,-0x480 (48000); beq a0,a2,0x149ec;
              lui a1,0x17; addiw a1,a1,0x700 (96000); xor a0,a0,a1; seqz a1,a0;
      0x149ec mv a0,a1; ret.
    Total: on every entry it returns rate_closed (bv_unsigned a0) (Pod/RateCfg.v: 1 on 44100, 48000 or 96000, else
    0) in a0; the compares read the whole 64-bit a0. It writes a0, a1 and a2, stores nothing, reads no memory and
    uses no stack.

    Call site (LLVMFuzzerTestOneInput, plain): 0x144bc `jal reac_rate_is_closed` in the decide loop, with
    a0 = s5 = asked[i] (0x144b8 `mv a0,s5`); the result goes to s7 (0x144c0) and on to check_list's a2 (0x144d8
    `mv a2,s7`). No premise. *)
Definition REAC_RATE_IS_CLOSED : Z := 0x149c0.

Definition reac_rate_is_closed_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs
      (fun ms' => exists (a1' a2' : word),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (rate_closed (bv_unsigned a0))) a1' a2' a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_RATE_IS_CLOSED) fc None m (seg_rom rsegs)).
