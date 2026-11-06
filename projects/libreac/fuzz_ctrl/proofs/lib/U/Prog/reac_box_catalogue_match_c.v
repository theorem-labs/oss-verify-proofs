From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcParse RcMatch.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_BOX_CATALOGUE_MATCH : Z := 0x14d4c.
Definition CM_T : Z := 0x1fcc8.
Definition CM_K : Z := 240.

Definition reac_box_catalogue_match_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f len S : Z) (fb : list byte),
    a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 len -> sp = Z_to_bv 64 S ->
    0 <= f < 2^64 -> 0 <= len < 2^64 -> S < 2^64 -> S mod 16 = 0 ->
    CM_K <= S -> stk rsegs m (S - CM_K) S ->
    (forall a, S - CM_K <= a < S -> seg_rom rsegs (wa a) = None) ->
    length fb = 50%nat ->
    (50 <= len -> 0 < f /\ f + 50 <= 2^64 /\ bytes_at rsegs m f fb /\ (f + 50 <= S - CM_K \/ S <= f)) ->
    (forall a, CM_T <= a < CM_T + 3256 -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (want CM_T len fb))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(S - CM_K, S)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' (S - CM_K) S)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BOX_CATALOGUE_MATCH) fc None m (seg_rom rsegs)).
