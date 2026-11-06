From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import HeadampModel GrantModel GrantSweepModel
  BuildSweepModel GroupaNeeds_c.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_GRANT_BUILD_SWEEP : Z := 0x15380.
Definition REAC_GRANT_BUILD_SWEEP_FRAME : Z := 2128.

Definition reac_grant_build_sweep_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (s mx al t base w lo : Z)
         (T junk : list byte),
    a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 mx -> a2 = Z_to_bv 64 al -> a3 = Z_to_bv 64 t ->
    0 <= s < 2^64 -> -2^31 <= mx < 2^31 -> 0 <= al < 2^64 ->
    bv_unsigned sp mod 16 = 0 ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_GRANT_BUILD_SWEEP_FRAME <= bv_unsigned sp ->
    (al <> 0 -> 0 <= base < 256 /\ 0 <= w < 256 /\
                bytes_at rsegs m al [Z_to_bv 8 base; Z_to_bv 8 w] /\
                (al + 2 <= bv_unsigned sp - REAC_GRANT_BUILD_SWEEP_FRAME \/ bv_unsigned sp <= al)) ->
    length T = 460%nat -> bytes_at rsegs m t T -> t mod 4 = 0 ->
    (t + 460 <= bv_unsigned sp - REAC_GRANT_BUILD_SWEEP_FRAME \/ bv_unsigned sp <= t) ->
    tx_set01 T -> tx_legal T ->
    bytes_at rsegs m IM4_ROW IM4_ROW_BYTES ->
    (IM4_ROW + 24 <= bv_unsigned sp - REAC_GRANT_BUILD_SWEEP_FRAME \/ bv_unsigned sp <= IM4_ROW) ->
    (bsw_ok s al mx base w = true ->
       rw_cells rsegs m s [CB (Z.to_nat (34 * (8 + 3 * w))) junk] /\
       (s + 34 * (8 + 3 * w) <= bv_unsigned sp - REAC_GRANT_BUILD_SWEEP_FRAME \/ bv_unsigned sp <= s) /\
       (s + 34 * (8 + 3 * w) <= IM4_ROW \/ IM4_ROW + 24 <= s)) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         bytes_at rsegs m' IM4_ROW IM4_ROW_BYTES /\
         if bsw_ok s al mx base w
         then r = Z_to_bv 64 (8 + 3 * w) /\
              munch [(bv_unsigned sp - REAC_GRANT_BUILD_SWEEP_FRAME, bv_unsigned sp);
                     (s, s + 34 * (8 + 3 * w))] m m' /\
              rw_cells rsegs m' s
                [CB (Z.to_nat (34 * (8 + 3 * w)))
                    (SWEEP base (Z.to_nat w) (sweep_vals T t base (Z.to_nat w)))]
         else r = Z_to_bv 64 (-1) /\
              munch [(bv_unsigned sp - REAC_GRANT_BUILD_SWEEP_FRAME, bv_unsigned sp)] m m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_GRANT_BUILD_SWEEP) fc None m (seg_rom rsegs)).
