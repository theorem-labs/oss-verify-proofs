From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import Boxreg.
Open Scope Z_scope.

Definition CHECK : Z := 0x13454.
Definition CHECK_FRAME : Z := 112.
Definition ZERO_ADDR : Z := 0x10392.

Definition check_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo r fabric : Z) (bs : list byte),
    a0 = Z_to_bv 64 r -> a1 = Z_to_bv 64 fabric ->
    bytes_at rsegs m r bs -> boxreg_B16 bs -> bx_fabric bs = fabric ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + CHECK_FRAME <= bv_unsigned sp ->
    (r + 288 <= bv_unsigned sp - CHECK_FRAME \/ bv_unsigned sp <= r) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         mem_inv rsegs m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK) fc None m (seg_rom rsegs)).
