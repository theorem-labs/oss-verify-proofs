(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg AProto ABase.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AKit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition rz2log_post (res : Z) (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 a4 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma rz2log16_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 16 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 16 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (rz2log_post 0 ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x427b4) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> RIMG RSTK. atop_facts.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  carve_frame 16%nat ST.
  do 2 step.
  zstep. step. zstep. step. if_lit.
  step. zstep. step. if_lit.
  zstep. zstep. step. if_lit.
  zstep. step. step. step. zstep. zstep. zstep. zstep. zstep.
  lstep. zstep. step. step. if_lit.
  step. zstep. step. if_lit.
  do 4 step.
  release_frame FR ST (bv_unsigned sp). finish.
Qed.

Lemma rz2log2048_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 16 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 2048 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (rz2log_post 7 ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x427b4) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> RIMG RSTK. atop_facts.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  carve_frame 16%nat ST.
  do 2 step.
  zstep. step. zstep. step. if_lit.
  step. zstep. step. if_lit.
  zstep. zstep. step. if_lit.
  zstep. step. step. step. zstep. zstep. zstep. zstep. zstep.
  lstep. zstep. step. step. if_lit.
  step. zstep. step. if_lit.
  do 4 step.
  release_frame FR ST (bv_unsigned sp). finish.
Qed.

Definition ARSSLIM : Z := 0x15abe2.
Lemma rss_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem),
  rw_cells asegs m ARSSLIM [C1 (Z_to_bv 8 0)] ->
  rng_aimg RNG ->
  evtF asegs RNG (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                      F (ret_pc ra) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6aa28) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros C RIMG. unfold ARSSLIM in *.
  step. lstep. zstep. step. apply evtF_done. reflexivity.
Qed.

Lemma can_poison_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem),
  rw_cells asegs m ACANPOISON [C1 (Z_to_bv 8 1)] ->
  rng_aimg RNG ->
  evtF asegs RNG (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                      F (ret_pc ra) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5fbf0) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros C RIMG. unfold ACANPOISON in *.
  step. lstep. step. zstep. step. apply evtF_done. reflexivity.
Qed.

Definition ALSAN_TLSOFF : Z := 0xd0de8.
Definition ALSAN_CNT : Z := 0x65bb48.
Lemma lsan_disabled_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem),
  tp = Z_to_bv 64 ATP ->
  rw_cells asegs m ALSAN_TLSOFF [C8 (Z_to_bv 64 0x10)] ->
  rw_cells asegs m ALSAN_CNT [C4 (Z_to_bv 64 0)] ->
  rng_aimg RNG ->
  evtF asegs RNG (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                      F (ret_pc ra) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x8c034) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros -> C1 C2 RIMG. unfold ALSAN_TLSOFF, ALSAN_CNT, ATP in *.
  step. step. zstep. lstep. zstep. step. apply evtF_done. reflexivity.
Qed.

Definition AMHOOKS : Z := 0x16a440.
Lemma run_malloc_hooks_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 32 ->
  mem_inv asegs m ->
  rw_cells asegs m AMHOOKS [C8 (Z_to_bv 64 0)] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (fun ms' => exists a0' a2' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6cc44) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI HK RIMG RSTK. unfold AMHOOKS in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  carve_frame 32%nat ST.
  do 5 step.
  do 2 step.
  step. step.
  step. zstep. step. step. if_lit.
  do 6 step.
  release_frame FR ST (bv_unsigned sp). finish.
Qed.
End CANSEC1.
