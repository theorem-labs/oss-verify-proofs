(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg AProto ABase AQConst.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AKit AKit2.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Lemma run_free_hooks_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 32 ->
  mem_inv asegs m ->
  rw_cells asegs m AFHOOK [C8 (Z_to_bv 64 0)] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (fun ms' => exists m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6cd00) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI HK RIMG RSTK. unfold AFHOOK in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  carve_frame 32%nat ST.
  do 4 step.
  step.
  step. step. step.
  step. if_lit.
  step. step. step.
  step. zstep. step. step. if_lit.
  step.
  do 5 step.
  release_frame FR ST (bv_unsigned sp). finish.
Qed.
End CANSEC1.
