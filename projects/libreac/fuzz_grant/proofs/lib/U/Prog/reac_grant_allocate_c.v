From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import GrantModel.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_GRANT_ALLOCATE : Z := 0x15330.

Definition reac_grant_allocate_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o base w : Z),
    a0 = Z_to_bv 64 o -> a1 = Z_to_bv 64 base -> a2 = Z_to_bv 64 w ->
    int32 base -> int32 w ->
    (0 <= base -> 1 <= w <= 40 -> base + w <= 2^31 - 1) ->
    (o = 0 \/ (0 < o /\ o + 2 <= 2^64 /\ wr_at rsegs m o 2)) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         if negb (o =? 0) && fits base w
         then r = Z_to_bv 64 0 /\ bytes_at rsegs m' o (le1 (Z_to_bv 64 base) ++ le1 (Z_to_bv 64 w)) /\
              munch [(o, o + 2)] m m' /\ wmono rsegs m m'
         else r = Z_to_bv 64 (-1) /\ m' = m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_GRANT_ALLOCATE) fc None m (seg_rom rsegs)).
