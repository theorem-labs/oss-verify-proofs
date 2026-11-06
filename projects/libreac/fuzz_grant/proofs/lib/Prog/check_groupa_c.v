From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel GrantSweepModel.
Open Scope Z_scope.

Definition CHECK_GROUPA : Z := 0x13a74.
Definition CHECK_GROUPA_FRAME : Z := 224.

Definition check_groupa_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (row ch p t lo : Z) (T : list byte),
    a0 = Z_to_bv 64 row -> a1 = Z_to_bv 64 ch -> a2 = Z_to_bv 64 p -> a3 = Z_to_bv 64 t ->
    a4 = Z_to_bv 64 (eff T t ch p) ->
    bv_unsigned sp mod 16 = 0 ->
    0 <= ch < 48 -> 0 <= p < 3 ->
    length T = 460%nat -> bytes_at rsegs m t T ->
    (t + 460 <= bv_unsigned sp - CHECK_GROUPA_FRAME \/ bv_unsigned sp <= t) ->
    bytes_at rsegs m row (GA ch p (eff T t ch p)) ->
    (row + 34 <= bv_unsigned sp - CHECK_GROUPA_FRAME \/ bv_unsigned sp <= row) ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + CHECK_GROUPA_FRAME <= bv_unsigned sp ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_GROUPA_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_GROUPA) fc None m (seg_rom rsegs)).
