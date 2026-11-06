From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
Import ListNotations.
Open Scope Z_scope.

(** check_refusal(res, x) (fuzz_headamp.c:273-285; 48 bytes, 12 instructions at 0x14ab8 in the UBSan image):
      0x14ab8 or a2,a0,a1; andi a2,a2,3; bnez a2,0x14ad4; lw a0,8(a0); lw a1,0x84(a1); bne a0,a1,0x14ad8; ret;
      0x14ad4 unimp; 0x14ad8 addi sp,sp,-16; sd ra,8(sp); jal abort (0x16364); unimp.
    The plain text (lib/Prog/check_refusal_c.v) after one UBSan check, (res | x) & 3, to the trap 0x14ad4:
    discharged by res mod 4 = 0 and x mod 4 = 0. On the path that returns it writes a0, a1, a2, stores nothing and
    uses no stack.

    Call site (LLVMFuzzerTestOneInput, UBSan): 0x147bc `jal check_refusal` (the only one), reached when
    pp->corrupt = 0 and rc >= 0, just after check_keys returned, with sp = S - 608 and
      a0 = sp + 0x178 = &res (0x147b4), a1 = sp + 0xb8 = &x (0x147b8).
    Why the premises hold there: as in the plain file: U/Prog/HeadSites.v [site_refusal]. *)
Definition CHECK_REFUSAL : Z := 0x14ab8.

Definition check_refusal_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (w : list byte),
    bv_unsigned a0 mod 4 = 0 -> bv_unsigned a1 mod 4 = 0 -> length w = 4%nat ->
    bytes_at rsegs m (bv_unsigned a0 + 8) w -> bytes_at rsegs m (bv_unsigned a1 + X_RF_OFF) w ->
    evt rsegs
      (fun ms' => exists a0' a1' a2' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_REFUSAL) fc None m (seg_rom rsegs)).
