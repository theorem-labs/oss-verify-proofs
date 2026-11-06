From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import GrantSweepModel.
Import ListNotations.
Open Scope Z_scope.

Definition CTRL_LAY_BLOCK : Z := 0x147b8.
Definition CTRL_FINISH : Z := 0x14918.
Definition CTRL_LAY_BLOCK_STACK : Z := 192.

Definition ctrl_lay_block_need : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f lo ch p v : Z) (blk : list byte),
    a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 CTRL_ROW -> a2 = Z_to_bv 64 0 ->
    0 < f -> f + 50 <= 2^64 -> bv_unsigned a3 <> 0 -> bv_unsigned sp mod 16 = 0 ->
    0 <= ch < 256 -> 0 <= p < 256 -> 0 <= v < 256 ->
    bytes_at rsegs m (bv_unsigned a3) (bl [ch; p; v]) ->
    rw_cells rsegs m (f + 18) [CB 32 blk] ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CTRL_LAY_BLOCK_STACK <= bv_unsigned sp ->
    (f + 50 <= lo \/ bv_unsigned sp <= f + 18) ->
    (bv_unsigned a3 + 3 <= lo \/ bv_unsigned sp <= bv_unsigned a3) ->
    (bv_unsigned a3 + 3 <= f + 18 \/ f + 50 <= bv_unsigned a3) ->
    bytes_at rsegs m CTRL_ROW CTRL_ROW_BYTES ->
    (CTRL_ROW + 24 <= bv_unsigned sp - CTRL_LAY_BLOCK_STACK \/ bv_unsigned sp <= CTRL_ROW) ->
    (CTRL_ROW + 24 <= f + 18 \/ f + 50 <= CTRL_ROW) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CTRL_LAY_BLOCK_STACK, bv_unsigned sp); (f + 18, f + 50)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         bytes_at rsegs m' CTRL_ROW CTRL_ROW_BYTES /\
         rw_cells rsegs m' (f + 18) [CB 32 (bl (lay_z ch p v))])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CTRL_LAY_BLOCK) fc None m (seg_rom rsegs)).

Definition CTRL_FINISH_STACK : Z := 16.

Definition ctrl_finish_need : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f lo : Z) (blk : list byte),
    a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 CTRL_ROW ->
    0 < f -> f + 50 <= 2^64 ->
    rw_cells rsegs m (f + 18) [CB 32 blk] ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CTRL_FINISH_STACK <= bv_unsigned sp ->
    (f + 50 <= lo \/ bv_unsigned sp <= f + 18) ->
    bytes_at rsegs m CTRL_ROW CTRL_ROW_BYTES ->
    (CTRL_ROW + 24 <= bv_unsigned sp - CTRL_FINISH_STACK \/ bv_unsigned sp <= CTRL_ROW) ->
    (CTRL_ROW + 24 <= f + 18 \/ f + 50 <= CTRL_ROW) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CTRL_FINISH_STACK, bv_unsigned sp); (f + 18, f + 50)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         bytes_at rsegs m' CTRL_ROW CTRL_ROW_BYTES /\
         rw_cells rsegs m' (f + 18) [CB 32 (finish_bytes blk)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CTRL_FINISH) fc None m (seg_rom rsegs)).
