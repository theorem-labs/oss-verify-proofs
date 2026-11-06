From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import Boxreg lowest_free_base_c.
Open Scope Z_scope.

Definition RANGE_TAKEN : Z := 0x13cb0.

Definition range_taken_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r b k : Z) (bs : list byte),
    a0 = Z_to_bv 64 r -> a1 = Z_to_bv 64 b -> a2 = Z_to_bv 64 k ->
    bytes_at rsegs m r bs -> length bs = 288%nat -> r mod 4 = 0 ->
    boxreg_B1 bs -> bx_fabric bs <= 40 ->
    (forall i, 0 <= i < bx_n bs ->
       0 <= bx_base bs i /\ 0 <= bx_nch bs i /\ bx_base bs i + bx_nch bs i <= bx_fabric bs) ->
    0 <= b -> 0 <= k -> b + k <= bx_fabric bs ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' res a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 res a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m (seg_rom rsegs) /\
         ((slice_meets bs b k /\ res = Z_to_bv 64 1) \/ (~ slice_meets bs b k /\ res = Z_to_bv 64 0)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RANGE_TAKEN) fc None m (seg_rom rsegs)).
