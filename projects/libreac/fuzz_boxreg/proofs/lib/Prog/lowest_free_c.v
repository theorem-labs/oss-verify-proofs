From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import Boxreg range_free_c.
Open Scope Z_scope.

Definition LOWEST_FREE : Z := 0x136e0.
Definition LOWEST_FREE_FRAME : Z := 64.

Definition lowest_free_res (bs : list byte) (nch fabric z : Z) : Prop :=
  (z = -1 /\ forall b, 0 <= b <= fabric - nch -> ~ range_free_ok bs b nch fabric) \/
  (0 <= z <= fabric - nch /\ range_free_ok bs z nch fabric /\
   forall b, 0 <= b < z -> ~ range_free_ok bs b nch fabric).

Definition lowest_free_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo t nch fabric : Z) (bs : list byte),
    a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 nch -> a2 = Z_to_bv 64 fabric ->
    1 <= nch <= 40 -> 1 <= fabric <= 40 ->
    bytes_at rsegs m t bs -> length bs = 288%nat ->
    boxreg_B1 bs -> boxreg_B2 bs -> boxreg_B3 bs ->
    stk rsegs m lo (bv_unsigned sp) -> lo + LOWEST_FREE_FRAME <= bv_unsigned sp ->
    (t + 288 <= bv_unsigned sp - LOWEST_FREE_FRAME \/ bv_unsigned sp <= t) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - LOWEST_FREE_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         exists z, r = Z_to_bv 64 z /\ lowest_free_res bs nch fabric z)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 LOWEST_FREE) fc None m (seg_rom rsegs)).
