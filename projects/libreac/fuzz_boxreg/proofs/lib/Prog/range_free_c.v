From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import Boxreg.
Open Scope Z_scope.

Definition RANGE_FREE : Z := 0x1368c.

Definition range_free_ok (bs : list byte) (base nch fabric : Z) : Prop :=
  0 <= base <= fabric - nch /\
  forall i, 0 <= i < bx_n bs -> ~ meets base nch (bx_base bs i) (bx_nch bs i).

Definition range_free_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (t base nch fabric : Z) (bs : list byte),
    a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 base -> a2 = Z_to_bv 64 nch -> a3 = Z_to_bv 64 fabric ->
    -2^31 <= base < 2^31 -> 1 <= nch <= 40 -> 1 <= fabric <= 40 ->
    bytes_at rsegs m t bs -> length bs = 288%nat ->
    boxreg_B1 bs -> boxreg_B2 bs -> boxreg_B3 bs ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m (seg_rom rsegs) /\
         ((r = Z_to_bv 64 1 /\ range_free_ok bs base nch fabric) \/
          (r = Z_to_bv 64 0 /\ ~ range_free_ok bs base nch fabric)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RANGE_FREE) fc None m (seg_rom rsegs)).
