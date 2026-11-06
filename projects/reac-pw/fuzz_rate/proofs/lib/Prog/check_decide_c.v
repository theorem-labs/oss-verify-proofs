From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(** check_decide(got, want) (fuzz_rate.c:180-194; 20 bytes, 5 instructions at 0x14608 in the plain image):
      0x14608 bne a0,a1,0x14610; ret; 0x14610 addi sp,sp,-16; sd ra,8(sp); jal abort (0x160bc).
    The same five instructions as reac-pw/fuzz_pin's check_row (elfdis --diff level 3, both builds), so this is
    pin's text with rate's addresses.
    When a0 = a1 the bne is not taken and it returns at once: it writes no register and no memory, reads no
    memory and uses no stack on that path (the abort path, 0x14610, is dead under the premise).

    Call site (LLVMFuzzerTestOneInput, plain): 0x14498 `jal check_decide`, inside the two-pass decide loop
    (fuzz_rate.c:262-265), with
      a0 = s6 = the value reac_rate_cfg_decide returned (0x14424 `mv s6,a0` after the call at 0x14420,
           0x14494 `mv a0,s6`);
      a1 = the harness's own expect_decide, computed inline just before the call (the closed-list scan at
           0x14460-0x14478 and 0x14484 `sllw a0,s8,a0`, 0x14488 `and a0,a0,s9`, 0x1448c `seqz a1,a0`,
           0x14490 `slli a1,a1,1`).
    Why the premise holds there is main's M02 segment (Prog/Seg/M02.v): reac_rate_cfg_decide's contract
    returns decide_res (Pod/RateCfg.v), the same value the inline computation forms. *)
Definition CHECK_DECIDE : Z := 0x14608.

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
