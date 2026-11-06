From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import Boxreg.
Open Scope Z_scope.

Definition LOWEST_FREE_BASE : Z := 0x139a4.

Definition slice_meets (bs : list byte) (b k : Z) : Prop :=
  exists i, 0 <= i < bx_n bs /\ meets b k (bx_base bs i) (bx_nch bs i).

Definition lowest_free (bs : list byte) (k res : Z) : Prop :=
  (res = -1 /\ forall b, 0 <= b -> b + k <= bx_fabric bs -> slice_meets bs b k) \/
  (0 <= res /\ res + k <= bx_fabric bs /\ ~ slice_meets bs res k /\
   forall b, 0 <= b < res -> slice_meets bs b k).

Definition lowest_free_base_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r k : Z) (bs : list byte),
    a0 = Z_to_bv 64 r -> a1 = Z_to_bv 64 k ->
    1 <= k < 2^31 ->
    bytes_at rsegs m r bs -> length bs = 288%nat ->
    boxreg_B1 bs -> boxreg_B2 bs -> boxreg_B3 bs ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' res a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 res a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m (seg_rom rsegs) /\
         exists z, res = Z_to_bv 64 z /\ lowest_free bs k z)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 LOWEST_FREE_BASE) fc None m (seg_rom rsegs)).
