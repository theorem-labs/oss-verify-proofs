(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import AKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition rz2log_post (res : Z) (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 a4 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Lemma rz2log16_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 16 ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 16 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (rz2log_post 0 ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x38e64) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> RIMG RSTK. atop_facts.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  word_range sp SPR.
  carve_frame 16%nat ST.
  do 2 step.                                   (* [comment removed for export] *)
  zstep. step. zstep. step. if_lit.           (* [comment removed for export] *)
  step. zstep. step. if_lit.                  (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                 (* [comment removed for export] *)
  zstep. step. step. step. zstep. zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
  lstep. zstep. step. step. if_lit.           (* [comment removed for export] *)
  step. zstep. step. if_lit.                  (* [comment removed for export] *)
  do 4 step.                                  (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp). finish.
Qed.

Lemma rz2log2048_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 16 ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 2048 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (rz2log_post 7 ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x38e64) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> RIMG RSTK. atop_facts.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  word_range sp SPR.
  carve_frame 16%nat ST.
  do 2 step.                                   (* [comment removed for export] *)
  zstep. step. zstep. step. if_lit.           (* [comment removed for export] *)
  step. zstep. step. if_lit.                  (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                 (* [comment removed for export] *)
  zstep. step. step. step. zstep. zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
  lstep. zstep. step. step. if_lit.           (* [comment removed for export] *)
  step. zstep. step. if_lit.                  (* [comment removed for export] *)
  do 4 step.                                  (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp). finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ARSSLIM : Z := 0x151f62.
Lemma rss_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem),
  rw_cells bsegs m ARSSLIM [C1 (Z_to_bv 8 0)] ->
  rng_aimg RNG ->
  evtF bsegs RNG (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                      F (ret_pc ra) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6093c) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros C RIMG. unfold ARSSLIM in *.
  step. lstep. zstep. step. apply evtF_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma can_poison_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem),
  rw_cells bsegs m ACANPOISON [C1 (Z_to_bv 8 1)] ->
  rng_aimg RNG ->
  evtF bsegs RNG (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                      F (ret_pc ra) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x55d54) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros C RIMG. unfold ACANPOISON in *.
  step. lstep. step. zstep. step. apply evtF_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ALSAN_TLSOFF : Z := 0xc7f60.   (* [comment removed for export] *)
Definition ALSAN_CNT : Z := 0x602cc0.       (* [comment removed for export] *)
Lemma lsan_disabled_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem),
  tp = Z_to_bv 64 ATP ->
  rw_cells bsegs m ALSAN_TLSOFF [C8 (Z_to_bv 64 0x10)] ->                       (* [comment removed for export] *)
  rw_cells bsegs m ALSAN_CNT [C4 (Z_to_bv 64 0)] ->
  rng_aimg RNG ->
  evtF bsegs RNG (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                      F (ret_pc ra) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x81f48) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros -> C1 C2 RIMG. unfold ALSAN_TLSOFF, ALSAN_CNT, ATP in *.
  step. step. zstep. lstep. zstep. step. apply evtF_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AMHOOKS : Z := 0x1617c0.
Lemma run_malloc_hooks_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 32 ->
  mem_inv bsegs m ->
  rw_cells bsegs m AMHOOKS [C8 (Z_to_bv 64 0)] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (fun ms' => exists a0' a2' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x62b58) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST CEIL LO MI HK RIMG RSTK. unfold AMHOOKS in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  word_range sp SPR.
  carve_frame 32%nat ST.
  do 5 step.                                   (* [comment removed for export] *)
  do 2 step.                                   (* [comment removed for export] *)
  step. step.                                  (* [comment removed for export] *)
  step. zstep. step. step. if_lit.            (* [comment removed for export] *)
  do 6 step.                                   (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp). finish.
Qed.
End CANSEC1.
(* [comment removed for export] *)
