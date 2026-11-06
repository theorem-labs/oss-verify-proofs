From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import RateCfg.
Import ListNotations.
Open Scope Z_scope.

(** reac_rate_best_drivable(mask) (reac_rate_cfg.c:40-47; 64 bytes, 16 instructions at 0x14a38 in the plain
    image):
      0x14a38 andi a1,a0,4; bnez a1,0x14a60; andi a1,a0,2; bnez a1,0x14a6c;
              slli a0,a0,0x3f; lui a1,0xb; srai a0,a0,0x3f; addiw a1,a1,-0x3bc; and a0,a0,a1; ret
              (all ones when bit 0 is set, so 44100, else 0);
      0x14a60 lui a0,0x17; addiw a0,a0,0x700 (96000); ret;  0x14a6c lui a0,0xc; addiw a0,a0,-0x480 (48000); ret.
    Total: on every entry it returns rate_best (bv_unsigned a0) (Pod/RateCfg.v: bits 2, 1, 0 of a0 in that order) in
    a0. It writes a0 and a1, stores nothing, reads no memory and uses no stack.

    Call site (LLVMFuzzerTestOneInput, plain): 0x144c8 `jal reac_rate_best_drivable` in the decide loop, with
    a0 = s9 = mask (0x144c4 `mv a0,s9`; input byte 1); the result goes to check_list's a4 (0x144cc `mv a4,a0`). No
    premise. *)
Definition REAC_RATE_BEST_DRIVABLE : Z := 0x14a38.

Definition reac_rate_best_drivable_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs
      (fun ms' => exists (a1' : word),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (rate_best (bv_unsigned a0))) a1' a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_RATE_BEST_DRIVABLE) fc None m (seg_rom rsegs)).
