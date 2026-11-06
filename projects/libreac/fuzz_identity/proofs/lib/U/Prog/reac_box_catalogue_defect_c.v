From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require reac_box_catalogue_defect_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_BOX_CATALOGUE_DEFECT : Z := 0x148b8.
Definition REAC_BOX_CATALOGUE_DEFECT_FRAME : Z := 16.

Definition reac_box_catalogue_defect_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo e i o d I O P : Z) (sP sd : list byte),
    a0 = Z_to_bv 64 e -> a1 = Z_to_bv 64 i -> a2 = Z_to_bv 64 o -> a3 = Z_to_bv 64 d ->
    0 <= e < 2^64 -> -2^31 <= i < 2^31 -> -2^31 <= o < 2^31 -> 0 <= d < 2^64 ->
    -2^31 <= I < 2^31 -> -2^31 <= O < 2^31 -> 0 <= P < 2^64 ->
    (e <> 0 ->
       bytes_at rsegs m (e + 8) (le8 (Z_to_bv 64 P)) /\
       bytes_at rsegs m (e + 16) (le4 (Z_to_bv 64 I)) /\
       bytes_at rsegs m (e + 20) (le4 (Z_to_bv 64 O)) /\
       e mod 8 = 0 /\
       (e + 24 <= bv_unsigned sp - REAC_BOX_CATALOGUE_DEFECT_FRAME \/ bv_unsigned sp <= e + 8)) ->
    (e <> 0 -> P <> 0 ->
       bytes_at rsegs m P (sP ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) sP /\
       (P + Z.of_nat (length sP) + 1 <= bv_unsigned sp - REAC_BOX_CATALOGUE_DEFECT_FRAME \/ bv_unsigned sp <= P)) ->
    (d <> 0 ->
       bytes_at rsegs m d (sd ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) sd /\
       (d + Z.of_nat (length sd) + 1 <= bv_unsigned sp - REAC_BOX_CATALOGUE_DEFECT_FRAME \/ bv_unsigned sp <= d)) ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + REAC_BOX_CATALOGUE_DEFECT_FRAME <= bv_unsigned sp ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1
                       (Z_to_bv 64 (Prog.reac_box_catalogue_defect_c.CATALOGUE_DEFECT_MASK e i o d I O P sP sd))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_BOX_CATALOGUE_DEFECT_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BOX_CATALOGUE_DEFECT) fc None m (seg_rom rsegs)).
