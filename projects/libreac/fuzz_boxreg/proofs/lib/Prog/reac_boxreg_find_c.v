From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import Boxreg.
Open Scope Z_scope.

Definition REAC_BOXREG_FIND : Z := 0x137bc.
Definition REAC_BOXREG_FIND_FRAME : Z := 48.

Definition first_mac (bs M : list byte) (i : Z) : Prop :=
  0 <= i < bx_n bs /\ bx_mac bs i = M /\ forall j, 0 <= j < i -> bx_mac bs j <> M.

Definition find_result (bs M : list byte) (z : Z) : Prop :=
  (M = zero6 /\ z = -1) \/
  (M <> zero6 /\ first_mac bs M z) \/
  (M <> zero6 /\ z = -1 /\ forall i, 0 <= i < bx_n bs -> bx_mac bs i <> M).

Definition reac_boxreg_find_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo r p : Z) (bs M : list byte),
    a0 = Z_to_bv 64 r -> a1 = Z_to_bv 64 p ->
    bytes_at rsegs m r bs -> length bs = 288%nat -> boxreg_B1 bs ->
    bytes_at rsegs m p M -> length M = 6%nat ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_BOXREG_FIND_FRAME <= bv_unsigned sp ->
    (r + 288 <= bv_unsigned sp - REAC_BOXREG_FIND_FRAME \/ bv_unsigned sp <= r) ->
    (p + 6 <= bv_unsigned sp - REAC_BOXREG_FIND_FRAME \/ bv_unsigned sp <= p) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' res a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 res a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_BOXREG_FIND_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         bytes_at rsegs m' r bs /\ bytes_at rsegs m' p M /\
         exists z, res = Z_to_bv 64 z /\ find_result bs M z)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BOXREG_FIND) fc None m (seg_rom rsegs)).
