(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables BzArr BzCMem BzCStream BzCState BzCSortF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM BzCBlock. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gtU_post (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (A2 Bud : Z) (a2 : zarr) (r : bool * Z)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 x12 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 x12 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch [(Bud, Bud + 4)] m m' /\ wmono segs m m' /\ mem_inv segs m'
    /\ a0 = Z_to_bv 64 (Z.b2z (fst r))
    /\ u8arr segs m' A2 (zb8 a2 ARR2_SIZE) /\ rw_cells segs m' Bud [C4 (Z_to_bv 64 (snd r))].

Definition gtU_spec (I : cimg) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A2 qoff n i1 i2 budget Bud : Z) (a2z : zarr),
  let segs := ci_segs I in
  a0 = Z_to_bv 64 i1 -> a1 = Z_to_bv 64 i2 -> a2 = Z_to_bv 64 A2 -> a3 = Z_to_bv 64 (A2 + qoff) -> a4 = Z_to_bv 64 n -> a5 = Z_to_bv 64 Bud ->
  u8arr segs m A2 (zb8 a2z ARR2_SIZE) -> rw_cells segs m Bud [C4 (Z_to_bv 64 budget)] -> mem_inv segs m ->
  zbok a2z -> 0 <= i1 <= n + 14 -> 0 <= i2 <= n + 14 -> 10000 <= n <= NBLOCKMAX + 19 -> n + 34 <= qoff <= n + 35 ->
  (A2 + qoff) mod 2 = 0 -> 0 < A2 -> A2 + ARR2_SIZE <= CEIL -> 0 < Bud -> Bud + 4 <= 18446744073709551616 -> Bud mod 4 = 0 ->
  apart A2 ARR2_SIZE Bud 4 ->
  -2147483648 <= snd (mainGtU i1 i2 a2z qoff n budget) -> budget < 2147483648 ->
  evt segs (gtU_post segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A2 Bud a2z (mainGtU i1 i2 a2z qoff n budget) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (ci_mainGtU I)) fc None m (seg_rom segs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition blockSort_post2 (segs : list Segment) (cx : cctx) (g : eg) (e : est)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (W : list (Z * Z))
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch W m m' /\ wmono segs m m' /\ mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp)
    /\ let e' := fst (fst (fst (blockSort e znew))) in
       let g' := EG (g_aie g) true (g_mtf g) (g_bs g) (g_zbits g) in
       rw_cells segs m' (c_E cx) (EHEAD1 cx g' e') /\ rw_cells segs m' (c_E cx + 640) (EHEAD2 cx g' e') /\ amem cx segs e' m'.
Definition blockSort_spec2 (BSFACTS : est -> Prop) (I : cimg) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cx : cctx) (g : eg) (e : est) (lo : Z) (sv : word),
  let segs := ci_segs I in
  a0 = Z_to_bv 64 (c_E cx) ->
  rw_cells segs m (c_E cx) (EHEAD1 cx g e) -> rw_cells segs m (c_E cx + 640) (EHEAD2 cx g e) -> amem cx segs e m ->
  cimg_mem I m sv -> mem_inv segs m ->
  stk segs m lo (bv_unsigned sp) -> lo + BS_STACK <= bv_unsigned sp -> CEIL <= lo -> bv_unsigned sp mod 16 = 0 ->
  cctx_ok cx -> cctx_sep cx -> cctx_img I cx -> est_ok e -> 1 <= e_nblock e <= NBLOCKMAX + 9 ->
  BSFACTS e ->
  evt segs (blockSort_post2 segs cx g e ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo (blockSort_W cx (bv_unsigned sp)) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (ci_blockSort I)) fc None m (seg_rom segs)).

End ACeilS1.
