From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcBox RcSynth.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_BOX_MODEL_BLOCK : Z := 0x14e50.
Definition JOIN_0013 : Z := 0x106c4.

Definition reac_box_model_block_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (p b o : Z) (row nb : list byte) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (if (p =? 0) || (o =? 0) then -1 else rc row b))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ (if (p =? 0) || (o =? 0) then munch [(bv_unsigned sp - 160, bv_unsigned sp)] m m'
        else bytes_at rsegs m' o (synth row b nb) /\
             munch [(bv_unsigned sp - 160, bv_unsigned sp); (o, o + 32)] m m')
    /\ wmono rsegs m m'
    /\ mem_inv rsegs m'
    /\ stk rsegs m' (bv_unsigned sp - 160) (bv_unsigned sp).

Definition reac_box_model_block_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p b o : Z) (row nb ob : list byte),
    a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 b -> a2 = Z_to_bv 64 o ->
    0 <= p < 2^64 -> 0 <= b < 2^64 -> 0 <= o < 2^64 ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m (bv_unsigned sp - 160) (bv_unsigned sp) ->
    (p <> 0 -> p mod 8 = 0 /\ length row = 296%nat /\ bytes_at rsegs m p row /\
               (bv_unsigned sp <= p \/ p + 296 <= bv_unsigned sp - 160) /\
               (o = 0 \/ o + 32 <= p \/ p + 296 <= o)) ->
    (p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
               name_ok nb /\ bytes_at rsegs m (rname row) nb /\
               (bv_unsigned sp <= rname row \/ rname row + Z.of_nat (length nb) <= bv_unsigned sp - 160) /\
               (o = 0 \/ o + 32 <= rname row \/ rname row + Z.of_nat (length nb) <= o)) ->
    (o <> 0 -> rw_cells rsegs m o [CB 32 ob] /\
               (bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - 160) /\
               (o + 32 <= JOIN_0013 \/ JOIN_0013 + 64 <= o)) ->
    mem_inv rsegs m ->
    evt rsegs
      (reac_box_model_block_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o row nb)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BOX_MODEL_BLOCK) fc None m (seg_rom rsegs)).
