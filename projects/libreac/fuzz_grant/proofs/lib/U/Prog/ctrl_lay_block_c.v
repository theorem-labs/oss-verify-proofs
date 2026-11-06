From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import RcModel RcBox RcSynth RcLay.
Import ListNotations.
Open Scope Z_scope.

Definition CTRL_LAY_BLOCK : Z := 0x147b8.
Definition CTRL_LAY_BLOCK_K : Z := 192.

Definition ctrl_lay_block_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p f md g : Z)
         (fr ob tb mb nb gb : list byte),
    a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 f -> a2 = Z_to_bv 64 md -> a3 = Z_to_bv 64 g ->
    0 <= p < 2^64 -> 0 <= f < 2^64 -> 0 <= md < 2^64 -> 0 <= g < 2^64 ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) ->
    ly_dj (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) (p + 18) (p + 50) ->
    ly_dj (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) f (f + 24) ->
    (ly_k fr = 2 -> ly_dj (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) (ly_tm fr) (ly_tm fr + 32)) ->
    (g <> 0 -> ly_al fr <> 0 ->
       ly_dj (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) g (g + ly_al fr)) ->
    (3 <= ly_k fr <= 9 -> md <> 0 ->
       ly_dj (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) md (md + 296) /\
       ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
          ly_dj (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) (rname mb) (rname mb + Z.of_nat (length nb)))) ->
    f mod 8 = 0 -> f + 24 <= 2^64 -> length fr = 24%nat -> bytes_at rsegs m f fr ->
    ly_k fr <= 9 -> ly_ao fr + ly_al fr <= 32 ->
    (ly_k fr = 2 -> ly_tm fr + 32 <= 2^64 /\ length tb = 32%nat /\ ro_bytes rsegs (ly_tm fr) tb) ->
    p <> 0 -> p + 50 <= 2^64 -> rw_cells rsegs m (p + 18) [CB 32 ob] ->
    ly_dj (p + 18) (p + 50) f (f + 24) ->
    (ly_k fr = 2 -> ly_dj (p + 18) (p + 50) (ly_tm fr) (ly_tm fr + 32)) ->
    (3 <= ly_k fr <= 9 -> md <> 0 -> ly_dj (p + 18) (p + 50) md (md + 296)) ->
    (3 <= ly_k fr <= 9 -> md <> 0 -> (ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
       ly_dj (p + 18) (p + 50) (rname mb) (rname mb + Z.of_nat (length nb))) ->
    (3 <= ly_k fr <= 9 -> md <> 0 ->
       md mod 8 = 0 /\ length mb = 296%nat /\ bytes_at rsegs m md mb /\
       ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
          name_ok nb /\ bytes_at rsegs m (rname mb) nb)) ->
    (g <> 0 -> ly_al fr <> 0 ->
       Z.of_nat (length gb) = ly_al fr /\ bytes_at rsegs m g gb /\ ly_dj (p + 18) (p + 50) g (g + ly_al fr)) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(p + 18, p + 50); (bv_unsigned sp - CTRL_LAY_BLOCK_K, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) /\
         rw_cells rsegs m' (p + 18)
           [CB 32 (ly_lay (ly_k fr) tb (ly_Z md mb nb (ly_bb (ly_k fr))) g (ly_ao fr) (ly_al fr) gb)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CTRL_LAY_BLOCK) fc None m (seg_rom rsegs)).
