From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel GrantSweepModel GroupaModel.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_CTRL_PARSE : Z := 0x13ba4.
Definition REAC_CTRL_PARSE_FRAME : Z := 80.

Definition reac_ctrl_parse_need : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f o lo ch p v : Z) (junk : list byte),
    a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 50 -> a2 = Z_to_bv 64 o ->
    bv_unsigned sp mod 16 = 0 ->
    0 < f -> f + 50 <= 2^64 -> 0 < o -> o mod 4 = 0 -> o + 36 <= 2^64 ->
    0 <= ch < 48 -> 0 <= p < 3 -> 0 <= v < 256 ->
    bytes_at rsegs m f (F50 ch p v) ->
    rw_cells rsegs m o [CB 36 junk] ->
    (o + 36 <= f \/ f + 50 <= o) ->
    (f + 50 <= bv_unsigned sp - REAC_CTRL_PARSE_FRAME \/ bv_unsigned sp <= f) ->
    bv_unsigned sp <= o ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_CTRL_PARSE_FRAME <= bv_unsigned sp ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte) (b1 b2 : list byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 6) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_CTRL_PARSE_FRAME, bv_unsigned sp); (o, o + 36)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         rw_cells rsegs m' o [CB 30 b1; C1 (Z_to_bv 8 ch); C1 (Z_to_bv 8 p); C1 (Z_to_bv 8 v); CB 3 b2])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_PARSE) fc None m (seg_rom rsegs)).

Definition REAC_CTRL_BUILD_GRANT_SWEEP : Z := 0x13f64.
Definition REAC_CTRL_BUILD_GRANT_SWEEP_STACK : Z := 1888.

Definition reac_ctrl_build_grant_sweep_need : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (s mx base w V lo : Z) (vals junk : list byte),
    a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 mx -> a2 = Z_to_bv 64 base -> a3 = Z_to_bv 64 w -> a4 = Z_to_bv 64 V ->
    bv_unsigned sp mod 16 = 0 ->
    0 < s < 2^64 -> -2^31 <= mx < 2^31 -> 0 <= base < 256 -> 1 <= w -> base + w <= 48 ->
    0 < V -> V + 3 * w <= 2^64 ->
    bytes_at rsegs m V vals -> length vals = Z.to_nat (3 * w) -> vals_legal (Z.to_nat w) vals ->
    (V + 3 * w <= bv_unsigned sp - REAC_CTRL_BUILD_GRANT_SWEEP_STACK \/ bv_unsigned sp <= V) ->
    (8 + 3 * w <= mx ->
       rw_cells rsegs m s [CB (Z.to_nat (34 * (8 + 3 * w))) junk] /\
       (s + 34 * (8 + 3 * w) <= bv_unsigned sp - REAC_CTRL_BUILD_GRANT_SWEEP_STACK \/ bv_unsigned sp <= s) /\
       (V + 3 * w <= s \/ s + 34 * (8 + 3 * w) <= V) /\
       (s + 34 * (8 + 3 * w) <= CTRL_ROW \/ CTRL_ROW + 24 <= s)) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_CTRL_BUILD_GRANT_SWEEP_STACK <= bv_unsigned sp ->
    mem_inv rsegs m ->
    bytes_at rsegs m CTRL_ROW CTRL_ROW_BYTES ->
    (CTRL_ROW + 24 <= bv_unsigned sp - REAC_CTRL_BUILD_GRANT_SWEEP_STACK \/ bv_unsigned sp <= CTRL_ROW) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         bytes_at rsegs m' CTRL_ROW CTRL_ROW_BYTES /\
         if 8 + 3 * w <=? mx
         then r = Z_to_bv 64 (8 + 3 * w) /\
              munch [(bv_unsigned sp - REAC_CTRL_BUILD_GRANT_SWEEP_STACK, bv_unsigned sp);
                     (s, s + 34 * (8 + 3 * w))] m m' /\
              rw_cells rsegs m' s [CB (Z.to_nat (34 * (8 + 3 * w))) (SWEEP base (Z.to_nat w) vals)]
         else r = Z_to_bv 64 (-1) /\
              munch [(bv_unsigned sp - REAC_CTRL_BUILD_GRANT_SWEEP_STACK, bv_unsigned sp)] m m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_BUILD_GRANT_SWEEP) fc None m (seg_rom rsegs)).
