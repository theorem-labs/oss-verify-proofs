From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcBox.
Import ListNotations.
Open Scope Z_scope.

Definition NAME_FIELD : Z := 0x16138.

Definition name_field_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (name : word) (nb junk : list byte),
    stk rsegs m (bv_unsigned sp - 32) (bv_unsigned sp) ->
    bv_unsigned a0 <> 0 -> bv_unsigned a0 mod 8 = 0 -> bv_unsigned a0 + 288 <= 2^64 ->
    bytes_at rsegs m (bv_unsigned a0 + 280) (le8 name) ->
    bv_unsigned a1 + 16 <= 2^64 ->
    rw_cells rsegs m (bv_unsigned a1) [CB 16 junk] ->
    (bv_unsigned name = 0 /\ nb = [] \/
     bv_unsigned name <> 0 /\ name_ok nb /\ bv_unsigned name + Z.of_nat (length nb) <= 2^64 /\
     bytes_at rsegs m (bv_unsigned name) nb) ->
    (bv_unsigned sp <= bv_unsigned a0 + 280 \/ bv_unsigned a0 + 288 <= bv_unsigned sp - 32) ->
    (bv_unsigned sp <= bv_unsigned name \/ bv_unsigned name + Z.of_nat (length nb) <= bv_unsigned sp - 32) ->
    (bv_unsigned sp <= bv_unsigned a1 \/ bv_unsigned a1 + 16 <= bv_unsigned sp - 32) ->
    (bv_unsigned a1 + 16 <= bv_unsigned a0 + 280 \/ bv_unsigned a0 + 288 <= bv_unsigned a1) ->
    (bv_unsigned a1 + 16 <= bv_unsigned name \/ bv_unsigned name + Z.of_nat (length nb) <= bv_unsigned a1) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ bytes_at rsegs m' (bv_unsigned a1) (nmf nb)
         /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + 16)] m m'
         /\ wmono rsegs m m'
         /\ mem_inv rsegs m'
         /\ stk rsegs m' (bv_unsigned sp - 32) (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 NAME_FIELD) fc None m (seg_rom rsegs)).
