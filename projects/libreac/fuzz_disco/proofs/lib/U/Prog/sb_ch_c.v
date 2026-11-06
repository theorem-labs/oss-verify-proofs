From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition SB_CH : Z := 0x15380.

Definition sb_rec (p cap n over : word) : list byte := le8 p ++ le8 cap ++ le8 n ++ le4 over.

Definition sb_ch_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p cap n over : word),
    bv_unsigned a0 mod 8 = 0 ->
    bytes_at rsegs m (bv_unsigned a0) (sb_rec p cap n over) ->
    wr_at rsegs m (bv_unsigned a0) 28 ->
    bv_unsigned n <= 2^64 - 2 ->
    (bv_unsigned n + 1 < bv_unsigned cap ->
       bv_unsigned p <> 0 /\ bv_unsigned p + bv_unsigned n < 2^64 /\
       wr_at rsegs m (bv_unsigned p + bv_unsigned n) 1 /\
       (bv_unsigned p + bv_unsigned n + 1 <= bv_unsigned a0 \/ bv_unsigned a0 + 28 <= bv_unsigned p + bv_unsigned n)) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         ((bv_unsigned cap <= bv_unsigned n + 1 /\
           munch [(bv_unsigned a0 + 24, bv_unsigned a0 + 28)] m m' /\
           bytes_at rsegs m' (bv_unsigned a0) (sb_rec p cap n (Z_to_bv 64 1))) \/
          (bv_unsigned n + 1 < bv_unsigned cap /\
           munch [(bv_unsigned a0 + 16, bv_unsigned a0 + 24);
                  (bv_unsigned p + bv_unsigned n, bv_unsigned p + bv_unsigned n + 1)] m m' /\
           bytes_at rsegs m' (bv_unsigned a0) (sb_rec p cap (Z_to_bv 64 (bv_unsigned n + 1)) over) /\
           bytes_at rsegs m' (bv_unsigned p + bv_unsigned n) (le1 a1))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SB_CH) fc None m (seg_rom rsegs)).
