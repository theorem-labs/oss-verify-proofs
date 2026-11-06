From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_HEADAMP_TX_ARM_SCENE : Z := 0x14b8c.

Definition arm_w (base width : Z) : Z := if 48 <? base + width then 48 - base else width.

Definition arm_T (T : list byte) (base width : Z) : list byte :=
  upd_bytes
    (upd_bytes
       (upd_bytes
          (upd_bytes
             (upd_bytes
                (upd_bytes
                   (upd_bytes
                      (upd_bytes T 436 (le1 (Z_to_bv 64 base)))
                      437 (le1 (Z_to_bv 64 (arm_w base width))))
                   440 (le4 (Z_to_bv 64 0)))
                444 (le4 (Z_to_bv 64 0)))
             448 (le1 (Z_to_bv 64 0)))
          449 (le1 (Z_to_bv 64 base)))
       450 (le1 (Z_to_bv 64 (arm_w base width))))
    456 (le4 (Z_to_bv 64 0)).

Definition reac_headamp_tx_arm_scene_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (t base width : Z) (T : list byte),
    a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 base -> a2 = Z_to_bv 64 width ->
    0 <= base < 256 -> 0 <= width < 256 ->
    length T = 460%nat -> bytes_at rsegs m t T -> wr_at rsegs m t 460 ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         if (width =? 0) || (48 <=? base)
         then m' = m
         else bytes_at rsegs m' t (arm_T T base width) /\ munch [(t, t + 460)] m m' /\ wmono rsegs m m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_HEADAMP_TX_ARM_SCENE) fc None m (seg_rom rsegs)).
