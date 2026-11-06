From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import RateCfg.
Import ListNotations.
Open Scope Z_scope.

(** reac_rate_bit(hz) (reac_rate_cfg.c:30-38; 68 bytes, 17 instructions at 0x14d48 in the UBSan image): the plain
    code (Prog/reac_rate_bit_c.v, 0x149f4) at another address, instruction for instruction (no auipc, no trap
    branch): three 64-bit compares of a0 with 44100, 96000, 48000 (lui/addiw into a1), returning 1, 4, 2 or 0.
    Total: on every entry it returns rate_bit (bv_unsigned a0) (Pod/RateCfg.v) in a0. It writes a0 and a1, stores
    nothing, reads no memory and uses no stack.

    Call site (LLVMFuzzerTestOneInput, UBSan): 0x145c8 `jal reac_rate_bit` in the two-pass decide loop (0x1451c ..
    0x14600 `bne s1,s9`), with a0 = s5 = asked[i] (0x145c0 `lw s5,0(s7)`, 0x145c4 `mv a0,s5`; s7 = sp + 0xe8 + 4 i);
    the result goes to s6 (0x145cc) and on to check_list's a1 (0x145ec `mv a1,s6`). No premise. *)
Definition REAC_RATE_BIT : Z := 0x14d48.

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
