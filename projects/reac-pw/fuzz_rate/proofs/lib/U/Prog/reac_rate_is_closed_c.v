From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import RateCfg.
Import ListNotations.
Open Scope Z_scope.

(** reac_rate_is_closed(hz) (reac_rate_cfg.c:24-28; 52 bytes, 13 instructions at 0x14d14 in the UBSan image): the
    plain code (Prog/reac_rate_is_closed_c.v, 0x149c0) at another address, instruction for instruction (no auipc, no
    trap branch): 64-bit compares of a0 with 44100 and 48000, then `xor` with 96000 and `seqz`.
    Total: on every entry it returns rate_closed (bv_unsigned a0) (Pod/RateCfg.v) in a0. It writes a0, a1 and a2,
    stores nothing, reads no memory and uses no stack.

    Call site (LLVMFuzzerTestOneInput, UBSan): 0x145d4 `jal reac_rate_is_closed` in the decide loop, with
    a0 = s5 = asked[i] (0x145d0 `mv a0,s5`); the result goes to s7 (0x145d8) and on to check_list's a2 (0x145f0
    `mv a2,s7`). No premise. *)
Definition REAC_RATE_IS_CLOSED : Z := 0x14d14.

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
