From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import GrantSweepModel.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_CTRL_IDENTITY_POLL_BLOCK : Z := 0x1448c.
Definition REAC_CTRL_IDENTITY_POLL_BLOCK_FRAME : Z := 16.

Definition poll_ok (i : Z) (out : word) : bool := (0 <=? i) && (i <=? 5) && negb (bv_unsigned out =? 0).

Definition reac_ctrl_identity_poll_block_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (i lo : Z) (junk : list byte),
    a0 = Z_to_bv 64 i -> -2^31 <= i < 2^31 ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + REAC_CTRL_IDENTITY_POLL_BLOCK_FRAME <= bv_unsigned sp ->
    (poll_ok i a1 = true ->
       rw_cells rsegs m (bv_unsigned a1) [CB 34 junk] /\
       (bv_unsigned a1 + 34 <= lo \/ bv_unsigned sp <= bv_unsigned a1)) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_CTRL_IDENTITY_POLL_BLOCK_FRAME, bv_unsigned sp);
                (bv_unsigned a1, bv_unsigned a1 + 34)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         if poll_ok i a1
         then r = Z_to_bv 64 0 /\ rw_cells rsegs m' (bv_unsigned a1) [CB 34 (GB i)]
         else r = Z_to_bv 64 (-1) /\ m' = m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_IDENTITY_POLL_BLOCK) fc None m (seg_rom rsegs)).
