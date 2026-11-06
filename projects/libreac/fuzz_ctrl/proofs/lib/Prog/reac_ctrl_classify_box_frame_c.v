From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
Require Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcParse RcClassify.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_CTRL_CLASSIFY_BOX_FRAME : Z := 0x14018.
Definition REAC_CTRL_CLASSIFY_BOX_FRAME_K : Z := 128.

Definition reac_ctrl_classify_box_frame_ev (c : option Z) (vb : list byte) : list byte :=
  match c with Some e => le4 (Z_to_bv 64 e) | None => vb end.

Definition reac_ctrl_classify_box_frame_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n u o v S : Z) (fr us junk vb : list byte),
    a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 u -> a3 = Z_to_bv 64 o -> a4 = Z_to_bv 64 v ->
    sp = Z_to_bv 64 S ->
    0 <= f < 2^64 -> 0 <= n < 2^64 -> 0 <= u < 2^64 -> 0 <= o < 2^64 -> 0 <= v < 2^64 -> S < 2^64 ->
    S mod 16 = 0 ->
    REAC_CTRL_CLASSIFY_BOX_FRAME_K <= S -> stk rsegs m (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S ->
    length fr = 50%nat ->
    (50 <= n -> 0 < f /\ f + 50 <= 2^64 /\ bytes_at rsegs m f fr /\
                (f + 50 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= f)) ->
    o <> 0 -> o mod 4 = 0 -> o + 36 <= 2^64 -> rw_cells rsegs m o [CB 36 junk] ->
    (o + 36 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= o) ->
    (50 <= n -> o + 36 <= f \/ f + 50 <= o) -> (o + 36 <= u \/ u + 6 <= o) ->
    length us = 6%nat ->
    (50 <= n -> u + 6 <= 2^64 /\ bytes_at rsegs m u us /\
                (u + 6 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= u)) ->
    v <> 0 -> v mod 4 = 0 -> v + 4 <= 2^64 -> rw_cells rsegs m v [CB 4 vb] ->
    (v + 4 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= v) ->
    (v + 4 <= o \/ o + 36 <= v) -> (v + 4 <= f \/ f + 50 <= v) -> (v + 4 <= u \/ u + 6 <= v) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (cl_r (classify n fr us)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(o, o + 36); (v, v + 4); (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K, S)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S /\
         rw_cells rsegs m' o [CB 36 (snd (ctrlparse n fr))] /\
         rw_cells rsegs m' v [CB 4 (reac_ctrl_classify_box_frame_ev (classify n fr us) vb)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_CLASSIFY_BOX_FRAME) fc None m (seg_rom rsegs)).
