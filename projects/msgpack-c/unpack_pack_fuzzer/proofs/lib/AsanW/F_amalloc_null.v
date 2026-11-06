(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase ABytes.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import StepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AKit AKit2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition AOOM : Z := 0x15bd20.

Lemma allocN_spec : forall RNG spA gp tp t0 t1 t2 s0x s1x a1 a2 a3 a4 a5 a6 a7 s2x s3x s4x s5x s6x s7x s8x s9x s10x s11x t3 t4 t5 t6
    (s0A s1A s2A s3A s4A s5A s6 s7 s8 s9 s10 s11 rav : word) (w1 w2 : word) (fr0 : list byte) (oomb : byte)
    (F : bvmap 5 word) fc (m : amem) (lo : Z),
  stk asegs m lo (bv_unsigned spA + -128) -> ATOP <= lo -> lo <= bv_unsigned spA - 128 ->
  mem_inv asegs m ->
  rw_cells asegs m AOOM [C1 oomb; C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m (bv_unsigned spA + -128)
     [CB 8 fr0; C8 w1; C8 w2; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5A;
      C8 s4A; C8 s3A; C8 s2A; C8 s1A; C8 s0A; C8 rav] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned spA - lo) ->
  evtF asegs RNG (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR rav spA gp tp t0' t1' t2' s0A s1A (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2A s3A s4A s5A s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc rav) fc None m' (seg_rom asegs)
      /\ munch [(AOOM, AOOM + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned spA)
      /\ rw_cells asegs m' AOOM [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)])
    (MS (mkR (Z_to_bv 64 0x3cf68) (Z_to_bv 64 (bv_unsigned spA + -128)) gp tp t0 t1 t2 s0x s1x (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
              s2x s3x s4x s5x s6x s7x s8x s9x s10x s11x t3 t4 t5 t6)
        F (Z_to_bv 64 0x3cf68) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI OOMC FRa RIMG RSTK. atop_facts. unfold AOOM in *.
  word_range spA SPR.
  pose proof (munch_refl [(0x15bd20, 0x15bd20 + 1)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  step.
  step. if_lit.
  step.
  do 2 step.
  step.
  step.
  step.
  step. lstep.
  step. step.
  step. if_lit.
  do 2 step.
  step.
  do 13 step. zstep. step.
  release_frame FRa ST (bv_unsigned spA).
  finish.
Qed.

Lemma icptN_spec : forall RNG sp gp tp t0 t1 t2 s0x s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (rav s0v s1v s2v s3v s4v s5v s0i : word) (F : bvmap 5 word) fc (m : amem) (lo : Z) (junk2 : list byte) (e0 : word),
  stk asegs m lo (bv_unsigned sp + -2144) -> ATOP <= lo -> lo <= bv_unsigned sp - 2160 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  rw_cells asegs m AERRNO [C4 e0] ->
  rw_cells asegs m (bv_unsigned sp + -2144) [C8 s0i; C8 (Z_to_bv 64 0x5e728)] ->
  (exists csA, rw_cells asegs m (bv_unsigned sp + -2128) csA /\ cells_size csA = 16%nat) ->
  (exists csT, rw_cells asegs m (bv_unsigned sp + -2112) csT /\ cells_size csT = 2040%nat) ->
  rw_cells asegs m (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR rav sp gp tp t0' t1' t2' s0v s1v (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc rav) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 2160, bv_unsigned sp - 2144); (AERRNO, AERRNO + 4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' AERRNO [C4 (Z_to_bv 64 12)])
    (MS (mkR (Z_to_bv 64 0x3cc98) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 s0x s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3cc98) fc None m (seg_rom asegs)).
Proof.
  intros until e0. intros ST CEIL LO MI -> ERR FR16 [csA [FRA SZA]] [csT [FRT SZT]] FRS RIMG RSTK. atop_facts. unfold AERRNO, ATP in *. change (6343808 - 164) with 6343644 in *.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 2160, bv_unsigned sp - 2144); (6343644, 6343644 + 4)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  step. if_lit.
  step.
  step.
  carve_frame 16%nat ST.
  do 2 step.
  step.
  step. zstep. step.
  step.
  step.
  do 3 step.
  step.
  do 4 step.
  zstep. do 7 step. zstep. step.
  release_frame FR ST (bv_unsigned sp + -2144).
  release_frame FR16 ST (bv_unsigned sp + -2128).
  pose proof (rw_cells_forget asegs _ _ _ FRA) as [jA FRA']. rewrite SZA in FRA'. clear FRA.
  release_frame FRA' ST (bv_unsigned sp + -2112).
  pose proof (rw_cells_forget asegs _ _ _ FRT) as [jT FRT']. rewrite SZT in FRT'. clear FRT.
  release_frame FRT' ST (bv_unsigned sp + -72).
  release_frame FRS ST (bv_unsigned sp).
  finish.
Qed.
End CANSEC1.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr.
Import AProto.TwinB ABase.TwinB ABytes.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import AKit.TwinB AKit2.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition AOOM : Z := 0x15dee0.

Lemma allocN_spec : forall RNG spA gp tp t0 t1 t2 s0x s1x a1 a2 a3 a4 a5 a6 a7 s2x s3x s4x s5x s6x s7x s8x s9x s10x s11x t3 t4 t5 t6
    (s0A s1A s2A s3A s4A s5A s6 s7 s8 s9 s10 s11 rav : word) (w1 w2 : word) (fr0 : list byte) (oomb : byte)
    (F : bvmap 5 word) fc (m : amem) (lo : Z),
  stk bsegs m lo (bv_unsigned spA + -128) -> ATOP <= lo -> lo <= bv_unsigned spA - 128 ->
  mem_inv bsegs m ->
  rw_cells bsegs m AOOM [C1 oomb; C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m (bv_unsigned spA + -128)
     [CB 8 fr0; C8 w1; C8 w2; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5A;
      C8 s4A; C8 s3A; C8 s2A; C8 s1A; C8 s0A; C8 rav] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned spA - lo) ->
  evtF bsegs RNG (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR rav spA gp tp t0' t1' t2' s0A s1A (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2A s3A s4A s5A s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc rav) fc None m' (seg_rom bsegs)
      /\ munch [(AOOM, AOOM + 1)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned spA)
      /\ rw_cells bsegs m' AOOM [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)])
    (MS (mkR (Z_to_bv 64 0x3d8f8) (Z_to_bv 64 (bv_unsigned spA + -128)) gp tp t0 t1 t2 s0x s1x (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
              s2x s3x s4x s5x s6x s7x s8x s9x s10x s11x t3 t4 t5 t6)
        F (Z_to_bv 64 0x3d8f8) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST CEIL LO MI OOMC FRa RIMG RSTK. atop_facts. unfold AOOM in *.
  word_range spA SPR.
  pose proof (munch_refl [(0x15dee0, 0x15dee0 + 1)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  step.
  step. if_lit.
  step.
  do 2 step.
  step.
  step.
  step.
  step. lstep.
  step. step.
  step. if_lit.
  do 2 step.
  step.
  do 13 step. zstep. step.
  release_frame FRa ST (bv_unsigned spA).
  finish.
Qed.

Lemma icptN_spec : forall RNG sp gp tp t0 t1 t2 s0x s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (rav s0v s1v s2v s3v s4v s5v s0i : word) (F : bvmap 5 word) fc (m : amem) (lo : Z) (junk2 : list byte) (e0 : word),
  stk bsegs m lo (bv_unsigned sp + -2144) -> ATOP <= lo -> lo <= bv_unsigned sp - 2160 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  rw_cells bsegs m AERRNO [C4 e0] ->
  rw_cells bsegs m (bv_unsigned sp + -2144) [C8 s0i; C8 (Z_to_bv 64 0x5f0b8)] ->
  (exists csA, rw_cells bsegs m (bv_unsigned sp + -2128) csA /\ cells_size csA = 16%nat) ->
  (exists csT, rw_cells bsegs m (bv_unsigned sp + -2112) csT /\ cells_size csT = 2040%nat) ->
  rw_cells bsegs m (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR rav sp gp tp t0' t1' t2' s0v s1v (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc rav) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - 2160, bv_unsigned sp - 2144); (AERRNO, AERRNO + 4)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ rw_cells bsegs m' AERRNO [C4 (Z_to_bv 64 12)])
    (MS (mkR (Z_to_bv 64 0x3d628) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 s0x s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3d628) fc None m (seg_rom bsegs)).
Proof.
  intros until e0. intros ST CEIL LO MI -> ERR FR16 [csA [FRA SZA]] [csT [FRT SZT]] FRS RIMG RSTK. atop_facts. unfold AERRNO, ATP in *. change (6352448 - 164) with 6352284 in *.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 2160, bv_unsigned sp - 2144); (6352284, 6352284 + 4)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  step. if_lit.
  step.
  step.
  carve_frame 16%nat ST.
  do 2 step.
  step.
  step. zstep. step.
  step.
  step.
  do 3 step.
  step.
  do 4 step.
  zstep. do 7 step. zstep. step.
  release_frame FR ST (bv_unsigned sp + -2144).
  release_frame FR16 ST (bv_unsigned sp + -2128).
  pose proof (rw_cells_forget bsegs _ _ _ FRA) as [jA FRA']. rewrite SZA in FRA'. clear FRA.
  release_frame FRA' ST (bv_unsigned sp + -2112).
  pose proof (rw_cells_forget bsegs _ _ _ FRT) as [jT FRT']. rewrite SZT in FRT'. clear FRT.
  release_frame FRT' ST (bv_unsigned sp + -72).
  release_frame FRS ST (bv_unsigned sp).
  finish.
Qed.
End CANSEC1.
End TwinB.
