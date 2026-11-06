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
Lemma ricptN_spec : forall RNG ra0 sp gp tp t0 t1 t2 s0x s1x a1 a2 a3 a4 a5 a6 a7 s2x s3x s4x s5x s6x s7 s8 s9 s10 s11 t3 t4 t5 t6
    (rav s0v s1v s2v s3v s4v s5v s6v spv s4r s3r s2r s1r s0r : word) (F : bvmap 5 word) fc (m : amem) (lo : Z) (junk2 junkR : list byte) (e0 : word),
  stk asegs m lo (bv_unsigned sp + -2208) -> ATOP <= lo -> lo <= bv_unsigned sp - 2208 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  rw_cells asegs m AERRNO [C4 e0] ->
  rw_cells asegs m (bv_unsigned sp + -2208) [C8 s4r; C8 s3r; C8 s2r; C8 s1r; C8 s0r; C8 (Z_to_bv 64 0x3d6ec)] ->
  rw_cells asegs m (bv_unsigned sp + -2160) [CB 8 junkR; C8 (Z_to_bv 64 0x5e9c8)] ->
  (exists csA, rw_cells asegs m (bv_unsigned sp + -2144) csA /\ cells_size csA = 8%nat) ->
  (exists csS, rw_cells asegs m (bv_unsigned sp + -2136) csS /\ cells_size csS = 16%nat) ->
  (exists csT, rw_cells asegs m (bv_unsigned sp + -2120) csT /\ cells_size csT = 2040%nat) ->
  rw_cells asegs m (bv_unsigned sp + -80) [C8 spv; CB 8 junk2; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR rav sp gp tp t0' t1' t2' s0v s1v (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc rav) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 2176, bv_unsigned sp - 2160); (AERRNO, AERRNO + 4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' AERRNO [C4 (Z_to_bv 64 12)])
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp t0 t1 t2 s0x s1x (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
              s2x s3x s4x s5x s6x s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3d768) fc None m (seg_rom asegs)).
Proof.
  intros until e0. intros ST CEIL LO MI -> ERR FRR FRa [csA [FRA SZA]] [csS [FRS SZS]] [csT [FRT SZT]] FRI RIMG RSTK. atop_facts.
  unfold AERRNO, ATP in *. change (6343808 - 164) with 6343644 in *.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 2176, bv_unsigned sp - 2160); (6343644, 6343644 + 4)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  step.
  step. if_lit.
  step. do 6 step. zstep. step.
  step. if_lit.
  step.
  do 2 step.
  step.
  step. zstep. step.
  step.
  step.
  do 3 step.
  step.
  step.
  step. zstep. step.
  zstep. do 8 step. zstep. step.
  release_frame FRR ST (bv_unsigned sp + -2160).
  release_frame FRa ST (bv_unsigned sp + -2144).
  pose proof (rw_cells_forget asegs _ _ _ FRA) as [jA FRA']. rewrite SZA in FRA'. clear FRA.
  release_frame FRA' ST (bv_unsigned sp + -2136).
  pose proof (rw_cells_forget asegs _ _ _ FRS) as [jS FRS']. rewrite SZS in FRS'. clear FRS.
  release_frame FRS' ST (bv_unsigned sp + -2120).
  pose proof (rw_cells_forget asegs _ _ _ FRT) as [jT FRT']. rewrite SZT in FRT'. clear FRT.
  release_frame FRT' ST (bv_unsigned sp + -80).
  release_frame FRI ST (bv_unsigned sp).
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
Lemma ricptN_spec : forall RNG ra0 sp gp tp t0 t1 t2 s0x s1x a1 a2 a3 a4 a5 a6 a7 s2x s3x s4x s5x s6x s7 s8 s9 s10 s11 t3 t4 t5 t6
    (rav s0v s1v s2v s3v s4v s5v s6v spv s4r s3r s2r s1r s0r : word) (F : bvmap 5 word) fc (m : amem) (lo : Z) (junk2 junkR : list byte) (e0 : word),
  stk bsegs m lo (bv_unsigned sp + -2208) -> ATOP <= lo -> lo <= bv_unsigned sp - 2208 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  rw_cells bsegs m AERRNO [C4 e0] ->
  rw_cells bsegs m (bv_unsigned sp + -2208) [C8 s4r; C8 s3r; C8 s2r; C8 s1r; C8 s0r; C8 (Z_to_bv 64 0x3e07c)] ->
  rw_cells bsegs m (bv_unsigned sp + -2160) [CB 8 junkR; C8 (Z_to_bv 64 0x5f358)] ->
  (exists csA, rw_cells bsegs m (bv_unsigned sp + -2144) csA /\ cells_size csA = 8%nat) ->
  (exists csS, rw_cells bsegs m (bv_unsigned sp + -2136) csS /\ cells_size csS = 16%nat) ->
  (exists csT, rw_cells bsegs m (bv_unsigned sp + -2120) csT /\ cells_size csT = 2040%nat) ->
  rw_cells bsegs m (bv_unsigned sp + -80) [C8 spv; CB 8 junk2; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR rav sp gp tp t0' t1' t2' s0v s1v (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc rav) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - 2176, bv_unsigned sp - 2160); (AERRNO, AERRNO + 4)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ rw_cells bsegs m' AERRNO [C4 (Z_to_bv 64 12)])
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp t0 t1 t2 s0x s1x (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
              s2x s3x s4x s5x s6x s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3e0f8) fc None m (seg_rom bsegs)).
Proof.
  intros until e0. intros ST CEIL LO MI -> ERR FRR FRa [csA [FRA SZA]] [csS [FRS SZS]] [csT [FRT SZT]] FRI RIMG RSTK. atop_facts.
  unfold AERRNO, ATP in *. change (6352448 - 164) with 6352284 in *.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 2176, bv_unsigned sp - 2160); (6352284, 6352284 + 4)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  step.
  step. if_lit.
  step. do 6 step. zstep. step.
  step. if_lit.
  step.
  do 2 step.
  step.
  step. zstep. step.
  step.
  step.
  do 3 step.
  step.
  step.
  step. zstep. step.
  zstep. do 8 step. zstep. step.
  release_frame FRR ST (bv_unsigned sp + -2160).
  release_frame FRa ST (bv_unsigned sp + -2144).
  pose proof (rw_cells_forget bsegs _ _ _ FRA) as [jA FRA']. rewrite SZA in FRA'. clear FRA.
  release_frame FRA' ST (bv_unsigned sp + -2136).
  pose proof (rw_cells_forget bsegs _ _ _ FRS) as [jS FRS']. rewrite SZS in FRS'. clear FRS.
  release_frame FRS' ST (bv_unsigned sp + -2120).
  pose proof (rw_cells_forget bsegs _ _ _ FRT) as [jT FRT']. rewrite SZT in FRT'. clear FRT.
  release_frame FRT' ST (bv_unsigned sp + -80).
  release_frame FRI ST (bv_unsigned sp).
  finish.
Qed.
End CANSEC1.
End TwinB.
