From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
Import ListNotations.
Open Scope Z_scope.

(** check_refusal(res, x) (fuzz_headamp.c:273-285; 28 bytes, 7 instructions at 0x147fc in the plain image):
      0x147fc lw a0,8(a0); lw a1,0x84(a1); bne a0,a1,0x1480c; ret;
      0x1480c addi sp,sp,-16; sd ra,8(sp); jal abort (0x15e64).
    It returns exactly when res->refusal (at res + 8) and x->refusal (at x + 0x84) are the same, the C condition of
    :283 false: the premises state it as the same four bytes w at both places. On that path it writes a0, a1, stores
    nothing and uses no stack.

    Call site (LLVMFuzzerTestOneInput, plain): 0x14144 `jal check_refusal` (the only one), reached when
    pp->corrupt = 0 and rc >= 0 (0x1412c `bltz s6` not taken), just after check_keys returned, with sp = S - 560 and
      a0 = sp + 0x150 = &res (0x1413c), a1 = sp + 0x90 = &x (0x14140).
    Why the premises hold there: as for check_keys, with the refusal word (Spec/HeadBytes.v: X_RF_OFF = 0x84):
    Prog/HeadSites.v [site_refusal]. *)
Definition CHECK_REFUSAL : Z := 0x147fc.

Definition check_refusal_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (w : list byte),
    length w = 4%nat ->
    bytes_at rsegs m (bv_unsigned a0 + 8) w -> bytes_at rsegs m (bv_unsigned a1 + X_RF_OFF) w ->
    evt rsegs
      (fun ms' => exists a0' a1' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_REFUSAL) fc None m (seg_rom rsegs)).
