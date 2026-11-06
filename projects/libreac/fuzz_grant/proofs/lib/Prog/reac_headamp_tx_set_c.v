From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_HEADAMP_TX_SET : Z := 0x14ac4.

Definition set_T (T : list byte) (ch p v : Z) : list byte :=
  upd_bytes
    (upd_bytes
       (upd_bytes
          (upd_bytes T (Z.to_nat (3 * ch + p)) (le1 (Z_to_bv 64 v)))
          (Z.to_nat (144 + 3 * ch + p)) (le1 (Z_to_bv 64 1)))
       (Z.to_nat (288 + 3 * ch + p)) (le1 (Z_to_bv 64 1)))
    432 (le4 (Z_to_bv 64 1)).

Definition reac_headamp_tx_set_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (t ch p v : Z) (T : list byte),
    a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 ch -> a2 = Z_to_bv 64 p -> a3 = Z_to_bv 64 v ->
    0 <= ch < 256 -> 0 <= p < 256 -> 0 <= v < 256 ->
    length T = 460%nat -> bytes_at rsegs m t T -> wr_at rsegs m t 460 ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         if (ch <? 48) && legalb p v
         then r = Z_to_bv 64 0 /\ bytes_at rsegs m' t (set_T T ch p v) /\
              munch [(t, t + 460)] m m' /\ wmono rsegs m m'
         else r = Z_to_bv 64 (-1) /\ m' = m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_HEADAMP_TX_SET) fc None m (seg_rom rsegs)).
