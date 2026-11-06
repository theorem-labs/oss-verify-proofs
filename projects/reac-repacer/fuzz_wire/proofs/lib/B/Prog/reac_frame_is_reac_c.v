From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import AsanKA.
Open Scope Z_scope.

(* The entry of reac_frame_is_reac in fuzz_wire.asan-ubsan (the function's first instruction, +0x0). *)
Definition REAC_FRAME_IS_REAC : Z := 0x8183c.
(* Its frame: +0x0 `addi sp, sp, -16` and +0x84 `addi sp, sp, 16`. *)
Definition REAC_FRAME_IS_REAC_FRAME : Z := 16.

Definition is_reac_byte (bs : list byte) (i : nat) : Z := bv_unsigned (nth i bs (Z_to_bv 8 0)).

Definition is_reac_result (frame len : Z) (bs : list byte) : Z :=
  if (frame =? 0) || (len <? 14) then 0
  else if (is_reac_byte bs 12 =? 0x88) && (is_reac_byte bs 13 =? 0x19) then 1 else 0.

Definition reac_frame_is_reac_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) ->
    lo + REAC_FRAME_IS_REAC_FRAME <= bv_unsigned sp ->
    (bv_unsigned a0 <> 0 -> 14 <= bv_unsigned a1 ->
       (14 <= length bs)%nat /\ bytes_at rsegs m (bv_unsigned a0) bs /\
       off_stk sp REAC_FRAME_IS_REAC_FRAME (bv_unsigned a0) 14 /\
       app_mem (bv_unsigned sp - REAC_FRAME_IS_REAC_FRAME) /\ app_mem (bv_unsigned sp - 1) /\
       asan_cells m /\ shadow_rw m /\
       off_stk sp REAC_FRAME_IS_REAC_FRAME GOT_CELL_K 8 /\
       off_stk sp REAC_FRAME_IS_REAC_FRAME CELL_K 8 /\
       addressable m (bv_unsigned a0 + 12) 2) ->
    evt rsegs
      (fun ms' => exists (a1' a2' a3' a4' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 (is_reac_result (bv_unsigned a0) (bv_unsigned a1) bs)) a1' a2' a3' a4'
                       a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_FRAME_IS_REAC_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_FRAME_IS_REAC) fc None m (seg_rom rsegs)).
