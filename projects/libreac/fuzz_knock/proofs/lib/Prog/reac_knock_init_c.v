From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Prog Require Import reac_knock_struct.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_KNOCK_INIT : Z := 0x12d50.
Definition REAC_KNOCK_INIT_FRAME : Z := 32.

Definition reac_knock_init_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (junk : list byte),
    rw_cells rsegs m (bv_unsigned a0) [CB 40 junk] ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + REAC_KNOCK_INIT_FRAME <= bv_unsigned sp ->
    bv_unsigned sp <= bv_unsigned a0 ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_KNOCK_INIT_FRAME, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 40)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         rw_cells rsegs m' (bv_unsigned a0)
           (knock_cells 0 (Z_to_bv 64 0) a1 (Z_to_bv 64 (bv_unsigned a1 + L_NS)) (Z_to_bv 64 0) 0 (Z_to_bv 64 0)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_KNOCK_INIT) fc None m (seg_rom rsegs)).
