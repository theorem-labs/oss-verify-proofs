From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_scene.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import reac_scene_struct.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_CTRL_SCENE_BUILD : Z := 0x15798.
Definition REAC_CTRL_SCENE_BUILD_FRAME : Z := 32.

Definition reac_ctrl_scene_build_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (junk macb : list byte),
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + REAC_CTRL_SCENE_BUILD_FRAME <= bv_unsigned sp ->
    (scene_ok a0 a1 a2 = true ->
       rw_cells rsegs m (bv_unsigned a0) [CB 8904 junk] /\
       bytes_at rsegs m (bv_unsigned a2) macb /\ length macb = 6%nat /\
       (bv_unsigned a0 + 8904 <= lo \/ bv_unsigned sp <= bv_unsigned a0) /\
       bv_unsigned sp <= bv_unsigned a2 /\
       (bv_unsigned a2 + 6 <= bv_unsigned a0 \/ bv_unsigned a0 + 8904 <= bv_unsigned a2)) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_CTRL_SCENE_BUILD_FRAME, bv_unsigned sp);
                (bv_unsigned a0, bv_unsigned a0 + 8904)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         if scene_ok a0 a1 a2
         then a0' = Z_to_bv 64 0 /\ rw_cells rsegs m' (bv_unsigned a0) [CB 8904 (scene0 macb)]
         else a0' = Z_to_bv 64 (-1) /\
              munch [(bv_unsigned sp - REAC_CTRL_SCENE_BUILD_FRAME, bv_unsigned sp)] m m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_SCENE_BUILD) fc None m (seg_rom rsegs)).
