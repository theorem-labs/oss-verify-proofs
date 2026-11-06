From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib Require Import Img0.
Open Scope Z_scope.

Definition REAC_FRAME_IS_REAC : Z := 0x13860.

Definition is_reac_byte (bs : list byte) (i : nat) : Z := bv_unsigned (nth i bs (Z_to_bv 8 0)).

Definition is_reac_result (frame len : Z) (bs : list byte) : Z :=
  if (frame =? 0) || (len <? 14) then 0
  else if (is_reac_byte bs 12 =? 0x88) && (is_reac_byte bs 13 =? 0x19) then 1 else 0.

Definition reac_frame_is_reac_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte),
    (bv_unsigned a0 <> 0 -> 14 <= bv_unsigned a1 ->
       (14 <= length bs)%nat /\ bytes_at rsegs m (bv_unsigned a0) bs) ->
    evt rsegs
      (fun ms' => exists a1' a2' a3' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 (is_reac_result (bv_unsigned a0) (bv_unsigned a1) bs)) a1' a2' a3'
                       a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_FRAME_IS_REAC) fc None m (seg_rom rsegs)).
