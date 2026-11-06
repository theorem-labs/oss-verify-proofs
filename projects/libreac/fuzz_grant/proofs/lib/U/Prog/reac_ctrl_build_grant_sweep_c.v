From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import HeadampModel GrantModel GrantSweepModel.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_CTRL_BUILD_GRANT_SWEEP : Z := 0x144ec.
Definition REAC_CTRL_BUILD_GRANT_SWEEP_FRAME : Z := 1632.
Definition REAC_CTRL_BUILD_GRANT_SWEEP_STACK : Z := 1856.

Definition sweep_ok (sw vals : word) (M base w : Z) : bool :=
  negb (bv_unsigned sw =? 0) && negb (bv_unsigned vals =? 0) && (1 <=? w) && (base + w <=? 48) &&
  (8 + 3 * w <=? M).

Definition sweep_pre (m : word -> option byte) (sw vals : word) (sp : word) (lo base w : Z)
    (junk vl : list byte) : Prop :=
  rw_cells rsegs m (bv_unsigned sw) [CB (Z.to_nat (34 * (8 + 3 * w))) junk] /\
  bytes_at rsegs m (bv_unsigned vals) vl /\
  length vl = Z.to_nat (3 * w) /\
  vals_legal (Z.to_nat w) vl /\
  (bv_unsigned sw + 34 * (8 + 3 * w) <= lo \/ bv_unsigned sp <= bv_unsigned sw) /\
  (bv_unsigned vals + 3 * w <= lo \/ bv_unsigned sp <= bv_unsigned vals) /\
  (bv_unsigned vals + 3 * w <= bv_unsigned sw \/ bv_unsigned sw + 34 * (8 + 3 * w) <= bv_unsigned vals) /\
  (bv_unsigned sw + 34 * (8 + 3 * w) <= CTRL_ROW \/ CTRL_ROW + 24 <= bv_unsigned sw).

Definition bgs_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (sw vals : word) (M base w lo : Z) (vl : list byte) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                    (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    wmono rsegs m m' /\
    mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp) /\
    bytes_at rsegs m' CTRL_ROW CTRL_ROW_BYTES /\
    if sweep_ok sw vals M base w
    then r = Z_to_bv 64 (8 + 3 * w) /\
         munch [(bv_unsigned sp - REAC_CTRL_BUILD_GRANT_SWEEP_STACK, bv_unsigned sp);
                (bv_unsigned sw, bv_unsigned sw + 34 * (8 + 3 * w))] m m' /\
         rw_cells rsegs m' (bv_unsigned sw) [CB (Z.to_nat (34 * (8 + 3 * w))) (SWEEP base (Z.to_nat w) vl)]
    else r = Z_to_bv 64 (-1) /\
         munch [(bv_unsigned sp - REAC_CTRL_BUILD_GRANT_SWEEP_FRAME, bv_unsigned sp)] m m'.

Definition reac_ctrl_build_grant_sweep_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (M base w lo : Z) (junk vl : list byte),
    a1 = Z_to_bv 64 M -> a2 = Z_to_bv 64 base -> a3 = Z_to_bv 64 w ->
    int32 M -> int32 w -> 0 <= base < 256 ->
    (bv_unsigned a0 <> 0 -> bv_unsigned a4 <> 0 -> 1 <= w -> base + w <= 2^31 - 1) ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + REAC_CTRL_BUILD_GRANT_SWEEP_STACK <= bv_unsigned sp ->
    bv_unsigned sp mod 16 = 0 ->
    bytes_at rsegs m CTRL_ROW CTRL_ROW_BYTES ->
    (CTRL_ROW + 24 <= bv_unsigned sp - REAC_CTRL_BUILD_GRANT_SWEEP_STACK \/ bv_unsigned sp <= CTRL_ROW) ->
    (sweep_ok a0 a4 M base w = true -> sweep_pre m a0 a4 sp lo base w junk vl) ->
    evt rsegs (bgs_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m a0 a4 M base w lo vl)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_BUILD_GRANT_SWEEP) fc None m (seg_rom rsegs)).
