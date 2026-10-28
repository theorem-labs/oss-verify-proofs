(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables BzArr BzCMem BzCStream BzCState BzCSortF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCHuff BzCMtf. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCBlock. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArrD BzCLemmas1 CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpArith. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCutBsw CmpCutMS CmpSdTac. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzSepTac.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cctx_ok (cx : cctx) : Prop :=
  let E := c_E cx in let A1 := c_A1 cx in let A2 := c_A2 cx in let FT := c_FT cx in let bz := c_bz cx in let Fb := c_Fb cx in
  0 < E /\ E + ESTATE_SIZE <= CEIL /\ 0 < A1 /\ A1 + ARR1_SIZE <= CEIL /\
  0 < A2 /\ A2 + ARR2_SIZE <= CEIL /\ 0 < FT /\ FT + 4 * FTAB_WORDS <= CEIL /\
  True /\ True /\ True /\ True /\
  E mod 16 = 0 /\ A1 mod 16 = 0 /\ A2 mod 16 = 0 /\ FT mod 16 = 0 /\ True /\ True /\
  Z.of_nat (length (c_J cx)) = ESTATE_SIZE /\ True.

Definition cctx_img (I : cimg) (cx : cctx) : Prop :=
  img_apart (ci_hi I) (c_E cx) ESTATE_SIZE /\ img_apart (ci_hi I) (c_A1 cx) ARR1_SIZE /\ img_apart (ci_hi I) (c_A2 cx) ARR2_SIZE /\
  img_apart (ci_hi I) (c_FT cx) (4 * FTAB_WORDS) /\ True /\ True.

Definition cctx_sep (cx : cctx) : Prop :=
  let E := c_E cx in let A1 := c_A1 cx in let A2 := c_A2 cx in let FT := c_FT cx in let bz := c_bz cx in let Fb := c_Fb cx in
  apart E ESTATE_SIZE A1 ARR1_SIZE /\ apart E ESTATE_SIZE A2 ARR2_SIZE /\ apart E ESTATE_SIZE FT (4 * FTAB_WORDS) /\
  True /\ True /\
  apart A1 ARR1_SIZE A2 ARR2_SIZE /\ apart A1 ARR1_SIZE FT (4 * FTAB_WORDS) /\ True /\ True /\
  apart A2 ARR2_SIZE FT (4 * FTAB_WORDS) /\ True /\ True /\
  True /\ True /\
  True.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bsW8_spec (I : cimg) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cx : cctx) (g : eg) (e : est) (v lo : Z),
  let segs := ci_segs I in
  a0 = Z_to_bv 64 (c_E cx) -> a1 = Z_to_bv 64 v -> 0 <= v < 256 ->
  rw_cells segs m (c_E cx) (EHEAD1 cx g e) -> rw_cells segs m (c_E cx + 640) (EHEAD2 cx g e) ->
  u8arr segs m (c_A2 cx) (zb8 (zbl (e_arr2 e) (e_nblock e) (e_bw e)) ARR2_SIZE) ->
  mem_inv segs m -> stk segs m lo (bv_unsigned sp) -> CEIL <= lo ->
  cctx_ok cx -> cctx_sep cx -> g_bs g = true -> g_zbits g = Z_to_bv 64 (c_A2 cx + e_nblock e) -> bw_ok (e_bw e) ->
  0 <= e_nblock e -> e_nblock e + bw_numZ (e_bw e) + 4 <= ARR2_SIZE ->
  evt segs (bsW8_post segs cx g e v ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo (bsW8_W cx e) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (ci_bsW8 I)) fc None m (seg_rom segs)).

Definition fallbackSort_spec (FSFACTS : zarr -> zarr -> zarr -> Z -> Prop) (I : cimg) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cx : cctx) (e : est) (nblock lo : Z) (sv : word),
  let segs := ci_segs I in
  a0 = Z_to_bv 64 (c_A1 cx) -> a1 = Z_to_bv 64 (c_A2 cx) -> a2 = Z_to_bv 64 (c_FT cx) -> a3 = Z_to_bv 64 nblock -> a4 = Z_to_bv 64 0 ->
  u8arr segs m (c_A1 cx) (zb8 (e_arr1 e) ARR1_SIZE) -> u8arr segs m (c_A2 cx) (zb8 (e_arr2 e) ARR2_SIZE) ->
  u32arr segs m (c_FT cx) (zw32 (e_ftab e) FTAB_WORDS) -> cimg_mem I m sv ->
  mem_inv segs m -> stk segs m lo (bv_unsigned sp) -> lo + FS_FRAME <= bv_unsigned sp -> CEIL <= lo -> bv_unsigned sp mod 16 = 0 ->
  cctx_ok cx -> cctx_sep cx -> cctx_img I cx ->
  zbok (e_arr1 e) -> zbok (e_arr2 e) -> (forall i, 0 <= zget (e_ftab e) i < 4294967296) ->
  1 <= nblock <= NBLOCKMAX + 19 ->
  FSFACTS (e_arr1 e) (e_arr2 e) (e_ftab e) nblock ->
  evt segs (fallbackSort_post segs cx e nblock ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo (fallbackSort_W cx (bv_unsigned sp)) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (ci_fallbackSort I)) fc None m (seg_rom segs)).

(* [comment removed for export] *)

(* [comment removed for export] *)

Definition compressBlock_spec (CBFACTS : est -> Prop) (I : cimg) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cx : cctx) (g : eg) (e : est) (is_last : bool) (lo : Z) (sv : word),
  let segs := ci_segs I in
  a0 = Z_to_bv 64 (c_E cx) -> a1 = Z_to_bv 64 (if is_last then 1 else 0) ->
  emem cx segs g e m -> amem cx segs e m -> cimg_mem I m sv -> mem_inv segs m ->
  stk segs m lo (bv_unsigned sp) -> lo + CB_STACK <= bv_unsigned sp -> CEIL <= lo -> bv_unsigned sp mod 16 = 0 ->
  cctx_ok cx -> cctx_sep cx -> cctx_img I cx -> cb_pre g e -> CBFACTS e ->
  evt segs (compressBlock_post segs I cx g e is_last sv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo (compressBlock_W cx (bv_unsigned sp)) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (ci_compressBlock I)) fc None m (seg_rom segs)).

Definition add_pair_spec (I : cimg) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cx : cctx) (g : eg) (e : est) (lo : Z) (sv : word),
  let segs := ci_segs I in
  a0 = Z_to_bv 64 (c_E cx) ->
  rw_cells segs m (c_E cx) (EHEAD1 cx g e) -> rw_cells segs m (c_E cx + 640) (EHEAD2 cx g e) ->
  u8arr segs m (c_E cx + 128) (ovb (e_inUse e) (jseg (c_J cx) 128 256) 256) ->
  u8arr segs m (c_A2 cx) (zb8 (e_arr2 e) ARR2_SIZE) -> cimg_mem I m sv ->
  mem_inv segs m -> stk segs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp -> CEIL <= lo ->
  cctx_ok cx -> cctx_sep cx -> cctx_img I cx ->
  0 <= e_state_in_ch e < 256 -> 1 <= e_state_in_len e <= 255 -> 0 <= e_blockCRC e < 4294967296 ->
  0 <= e_nblock e -> e_nblock e + 5 <= ARR2_SIZE -> zdefr (e_inUse e) 0 256 -> zbok (e_arr2 e) ->
  evt segs (add_pair_post segs cx g e ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo (add_pair_W cx e) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (ci_add_pair I)) fc None m (seg_rom segs)).

Definition bsPutUInt32_specS (I : cimg) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cx : cctx) (g : eg) (e : est) (u lo : Z),
  let segs := ci_segs I in
  a0 = Z_to_bv 64 (c_E cx) -> a1 = sx32 (Z_to_bv 64 u) -> 0 <= u < 4294967296 ->
  rw_cells segs m (c_E cx) (EHEAD1 cx g e) -> rw_cells segs m (c_E cx + 640) (EHEAD2 cx g e) ->
  u8arr segs m (c_A2 cx) (zb8 (zbl (e_arr2 e) (e_nblock e) (e_bw e)) ARR2_SIZE) ->
  mem_inv segs m -> stk segs m lo (bv_unsigned sp) -> CEIL <= lo ->
  cctx_ok cx -> cctx_sep cx -> g_bs g = true -> g_zbits g = Z_to_bv 64 (c_A2 cx + e_nblock e) -> bw_ok (e_bw e) ->
  0 <= e_nblock e -> e_nblock e + bw_numZ (e_bw e) + 16 <= ARR2_SIZE ->
  evt segs (bsPutUInt32_post segs cx g e u ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo (bsPutUInt32_W cx e) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (ci_bsPutUInt32 I)) fc None m (seg_rom segs)).

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

(* [comment removed for export] *)
Ltac openCX3 CX SEP USP1 :=
  let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
  let U := fresh "USPL" in pose proof USP1 as U; bz_ceil; bz_params; unfold CEIL in U;
  cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb);
  let S := fresh "SP" in pose proof SEP as S; unfold cctx_sep, apart, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE in S; cbv zeta in S;
  cps_destruct S as (?AEA1 & ?AEA2 & _ & _ & _ & ?AA12 & _); hide_disj.
