From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import RcModel RcBox.
Import ListNotations.
Open Scope Z_scope.

Definition BUILD_DT1_SINGLE : Z := 0x15040.

Definition build_dt1_single_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ob D : list byte),
    stk rsegs m (bv_unsigned sp - 32) (bv_unsigned sp) ->
    bv_unsigned a3 <= 9 ->
    bv_unsigned a0 <> 0 -> bv_unsigned a0 + 32 <= 2^64 ->
    rw_cells rsegs m (bv_unsigned a0) [CB 32 ob] ->
    bv_unsigned a2 + bv_unsigned a3 <= 2^64 ->
    length D = Z.to_nat (bv_unsigned a3) ->
    bytes_at rsegs m (bv_unsigned a2) D ->
    (bv_unsigned a2 + bv_unsigned a3 <= bv_unsigned a0 \/ bv_unsigned a0 + 32 <= bv_unsigned a2) ->
    (bv_unsigned sp <= bv_unsigned a0 \/ bv_unsigned a0 + 32 <= bv_unsigned sp - 32) ->
    (bv_unsigned sp <= bv_unsigned a2 \/ bv_unsigned a2 + bv_unsigned a3 <= bv_unsigned sp - 32) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ bytes_at rsegs m' (bv_unsigned a0) (dt1_out (Z.to_nat (bv_unsigned a3)) (bv_unsigned a1) D ob)
         /\ psum (skipn 16 (dt1_out (Z.to_nat (bv_unsigned a3)) (bv_unsigned a1) D ob))
                 (Z.to_nat (bv_unsigned a3) + 5) mod 128 = 0
         /\ psum (dt1_out (Z.to_nat (bv_unsigned a3)) (bv_unsigned a1) D ob) 32 mod 256 = 0
         /\ munch [(bv_unsigned sp - 32, bv_unsigned sp);
                   (bv_unsigned a0, bv_unsigned a0 + 22 + bv_unsigned a3);
                   (bv_unsigned a0 + 31, bv_unsigned a0 + 32)] m m'
         /\ wmono rsegs m m'
         /\ mem_inv rsegs m'
         /\ stk rsegs m' (bv_unsigned sp - 32) (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 BUILD_DT1_SINGLE) fc None m (seg_rom rsegs)).
