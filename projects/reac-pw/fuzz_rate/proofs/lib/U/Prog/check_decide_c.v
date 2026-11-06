From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(** check_decide(got, want) (fuzz_rate.c:180-194; 24 bytes, 6 instructions at 0x1472c in the UBSan image):
      0x1472c bne a0,a1,0x14734; ret; 0x14734 addi sp,sp,-16; sd ra,8(sp); jal abort (0x164a4); unimp.
    The plain text with a trap after the abort call (no UBSan check in it); the same six instructions as
    reac-pw/fuzz_pin's check_row (elfdis --diff level 3).
    When a0 = a1 it returns at once, writing no register and no memory, reading no memory, using no stack.

    Call site (LLVMFuzzerTestOneInput, UBSan): 0x145ac `jal check_decide`, inside the two-pass decide loop
    (fuzz_rate.c:262-265), with
      a0 = s5 = the value reac_rate_cfg_decide returned (0x14538 `mv s5,a0` after the call at 0x14534,
           0x145a8 `mv a0,s5`);
      a1 = the harness's own expect_decide, computed inline just before the call (the closed-list scan at
           0x14580-0x1458c and 0x14598 `sllw a0,s0,a0`, 0x1459c `and a0,a0,s10`, 0x145a0 `seqz a1,a0`,
           0x145a4 `slli a1,a1,1`).
    Why the premise holds there is main's M02 segment (U/Prog/Seg/M02.v), as in the plain build
    (lib/Prog/check_decide_c.v). *)
Definition CHECK_DECIDE : Z := 0x1472c.

Definition check_decide_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a0 = a1 ->
    evt rsegs
      (fun ms' =>
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_DECIDE) fc None m (seg_rom rsegs)).
