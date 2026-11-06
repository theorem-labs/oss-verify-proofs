(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables BzIncs BzArr BzCMem BzCStream BzCState BzCSortF BzCSortM BzCHuff BzCMtf BzCBlock BzArrD BzCLemmas1 CmpMem CmpCut CmpCutMS AsanKit AsanCut.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition B0C : acimg :=
  ACI (CI b0segs 0xd13e0 [] 0xcdab0 0x81668 0xcda98 0xccd30 0xa8d70 0xa7e6c 0xa70c4 0xa4c28 0xa0988 0x89970 0x8b19c 0x8b418 0x88fa4 0x82470 0x81ff0 0x62b000)
      0xcce38 0xd6538 0xcce90 0xd6540.

Definition hbAssignCodes_aspecF (I : acimg) (fr : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (Ecode Elen cb lb minLen maxLen alphaSize NC NL lo : Z) (code len : zarr) (Jc Jl : list byte),
  let segs := aci_segs I in
  let W := [(Ecode + 4 * cb, Ecode + 4 * (cb + alphaSize)); (bv_unsigned sp - fr, bv_unsigned sp)] in
  a0 = Z_to_bv 64 (Ecode + 4 * cb) -> a1 = Z_to_bv 64 (Elen + lb) ->
  a2 = Z_to_bv 64 minLen -> a3 = Z_to_bv 64 maxLen -> a4 = Z_to_bv 64 alphaSize ->
  u32arr segs m Ecode (ovw code Jc NC) -> u8arr segs m Elen (ovb len Jl NL) -> mem_inv segs m ->
  stk segs m lo (bv_unsigned sp) -> lo + fr <= bv_unsigned sp ->
  0 <= cb -> cb + alphaSize <= NC -> 0 <= lb -> lb + alphaSize <= NL -> 0 <= alphaSize <= 258 ->
  1 <= minLen <= 32 -> 0 <= maxLen <= 17 -> Ecode mod 4 = 0 -> 0 < Ecode -> Ecode + 4 * NC <= CEIL -> 0 < Elen -> Elen + NL <= CEIL ->
  apart Ecode (4 * NC) Elen NL ->
  bv_unsigned sp <= Ecode \/ Ecode + 4 * NC <= bv_unsigned sp - fr -> bv_unsigned sp <= Elen \/ Elen + NL <= bv_unsigned sp - fr ->
  (forall i, 0 <= i < alphaSize -> zdef len (lb + i) = true /\ minLen <= zget len (lb + i) <= maxLen) ->
  aconsts I m -> aci_hi I <= lo -> aci_hi I <= Ecode -> aci_hi I <= Elen ->
  shzW segs W m Ecode (Ecode + 4 * NC) -> shzW segs W m Elen (Elen + NL) ->
  evt segs (hbAssignCodes_post segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
              Ecode (hbAssignCodes code len cb lb minLen maxLen alphaSize) Jc NC lo W m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (ci_hbAssignCodes (aci_c I))) fc None m (seg_rom segs)).


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gtU_apostF (fr : Z) (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (A2 Bud : Z) (a2 : zarr) (r : bool * Z) (lo : Z)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 x12 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 x12 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch [(Bud, Bud + 4); (bv_unsigned sp - fr, bv_unsigned sp)] m m' /\ wmono segs m m' /\ mem_inv segs m'
    /\ stk segs m' lo (bv_unsigned sp)
    /\ a0 = Z_to_bv 64 (Z.b2z (fst r))
    /\ u8arr segs m' A2 (zb8 a2 ARR2_SIZE) /\ rw_cells segs m' Bud [C4 (Z_to_bv 64 (snd r))].

Definition gtU_aspecF (I : acimg) (fr : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A2 qoff n i1 i2 budget Bud lo : Z) (a2z : zarr),
  let segs := aci_segs I in
  let W := [(Bud, Bud + 4); (bv_unsigned sp - fr, bv_unsigned sp)] in
  a0 = Z_to_bv 64 i1 -> a1 = Z_to_bv 64 i2 -> a2 = Z_to_bv 64 A2 -> a3 = Z_to_bv 64 (A2 + qoff) -> a4 = Z_to_bv 64 n -> a5 = Z_to_bv 64 Bud ->
  u8arr segs m A2 (zb8 a2z ARR2_SIZE) -> rw_cells segs m Bud [C4 (Z_to_bv 64 budget)] -> mem_inv segs m ->
  zbok a2z -> 0 <= i1 <= n + 14 -> 0 <= i2 <= n + 14 -> 10000 <= n <= NBLOCKMAX + 19 -> n + 34 <= qoff <= n + 35 ->
  (A2 + qoff) mod 2 = 0 -> 0 < A2 -> A2 + ARR2_SIZE <= CEIL -> 0 < Bud -> Bud + 4 <= 18446744073709551616 -> Bud mod 4 = 0 ->
  apart A2 ARR2_SIZE Bud 4 ->
  -2147483648 <= snd (mainGtU i1 i2 a2z qoff n budget) -> budget < 2147483648 ->
  (* [comment removed for export] *)
  stk segs m lo (bv_unsigned sp) -> lo + fr <= bv_unsigned sp ->
  bv_unsigned sp <= A2 \/ A2 + ARR2_SIZE <= bv_unsigned sp - fr -> bv_unsigned sp <= Bud \/ Bud + 4 <= bv_unsigned sp - fr ->
  aconsts I m -> aci_hi I <= lo -> aci_hi I <= A2 -> aci_hi I <= Bud ->
  shzW segs W m A2 (A2 + ARR2_SIZE) -> shpW segs W m Bud (Bud + 4) ->
  evt segs (gtU_apostF fr segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A2 Bud a2z (mainGtU i1 i2 a2z qoff n budget) lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (ci_mainGtU (aci_c I))) fc None m (seg_rom segs)).

Definition add_pair_aspecF (I : acimg) (fr : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cx : cctx) (g : eg) (e : est) (lo : Z) (sv : word),
  let segs := aci_segs I in
  let W := add_pair_W cx e ++ [(bv_unsigned sp - fr, bv_unsigned sp)] in
  a0 = Z_to_bv 64 (c_E cx) ->
  rw_cells segs m (c_E cx) (EHEAD1 cx g e) -> rw_cells segs m (c_E cx + 640) (EHEAD2 cx g e) ->
  u8arr segs m (c_E cx + 128) (ovb (e_inUse e) (jseg (c_J cx) 128 256) 256) ->
  u8arr segs m (c_A2 cx) (zb8 (e_arr2 e) ARR2_SIZE) -> acimg_mem I m sv ->
  mem_inv segs m -> stk segs m lo (bv_unsigned sp) -> lo + fr <= bv_unsigned sp -> CEIL <= lo ->
  cctx_ok cx -> cctx_sep cx -> cctx_img (aci_c I) cx ->
  0 <= e_state_in_ch e < 256 -> 1 <= e_state_in_len e <= 255 -> 0 <= e_blockCRC e < 4294967296 ->
  0 <= e_nblock e -> e_nblock e + 5 <= ARR2_SIZE -> zdefr (e_inUse e) 0 256 -> zbok (e_arr2 e) ->
  (* [comment removed for export] *)
  aconsts I m -> cctx_sh segs cx W m -> cimg_sh I W m ->
  evt segs (add_pair_post segs cx g e ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo W m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (ci_add_pair (aci_c I))) fc None m (seg_rom segs)).

Definition bsW8_aspecF (I : acimg) (fr : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cx : cctx) (g : eg) (e : est) (v lo : Z),
  let segs := aci_segs I in
  let W := bsW8_W cx e ++ [(bv_unsigned sp - fr, bv_unsigned sp)] in
  a0 = Z_to_bv 64 (c_E cx) -> a1 = Z_to_bv 64 v -> 0 <= v < 256 ->
  rw_cells segs m (c_E cx) (EHEAD1 cx g e) -> rw_cells segs m (c_E cx + 640) (EHEAD2 cx g e) ->
  u8arr segs m (c_A2 cx) (zb8 (zbl (e_arr2 e) (e_nblock e) (e_bw e)) ARR2_SIZE) ->
  mem_inv segs m -> stk segs m lo (bv_unsigned sp) -> lo + fr <= bv_unsigned sp -> CEIL <= lo ->
  cctx_ok cx -> cctx_sep cx -> g_bs g = true -> g_zbits g = Z_to_bv 64 (c_A2 cx + e_nblock e) -> bw_ok (e_bw e) ->
  0 <= e_nblock e -> e_nblock e + bw_numZ (e_bw e) + 4 <= ARR2_SIZE ->
  (* [comment removed for export] *)
  aconsts I m -> cctx_sh segs cx W m ->
  evt segs (bsW8_post segs cx g e v ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo W m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (ci_bsW8 (aci_c I))) fc None m (seg_rom segs)).

Definition bsPutUInt32_aspecSF (I : acimg) (fr : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cx : cctx) (g : eg) (e : est) (u lo : Z),
  let segs := aci_segs I in
  let W := bsPutUInt32_W cx e ++ [(bv_unsigned sp - fr, bv_unsigned sp)] in
  a0 = Z_to_bv 64 (c_E cx) -> a1 = sx32 (Z_to_bv 64 u) -> 0 <= u < 4294967296 ->
  rw_cells segs m (c_E cx) (EHEAD1 cx g e) -> rw_cells segs m (c_E cx + 640) (EHEAD2 cx g e) ->
  u8arr segs m (c_A2 cx) (zb8 (zbl (e_arr2 e) (e_nblock e) (e_bw e)) ARR2_SIZE) ->
  mem_inv segs m -> stk segs m lo (bv_unsigned sp) -> lo + fr <= bv_unsigned sp -> CEIL <= lo ->
  cctx_ok cx -> cctx_sep cx -> g_bs g = true -> g_zbits g = Z_to_bv 64 (c_A2 cx + e_nblock e) -> bw_ok (e_bw e) ->
  0 <= e_nblock e -> e_nblock e + bw_numZ (e_bw e) + 16 <= ARR2_SIZE ->
  (* [comment removed for export] *)
  aconsts I m -> cctx_sh segs cx W m ->
  evt segs (bsPutUInt32_post segs cx g e u ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo W m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (ci_bsPutUInt32 (aci_c I))) fc None m (seg_rom segs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)       (* [comment removed for export] *)
(* [comment removed for export] *)       (* [comment removed for export] *)
(* [comment removed for export] *)  (* [comment removed for export] *)
(* [comment removed for export] *)      (* [comment removed for export] *)
(* [comment removed for export] *)   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition B0_INCS : Z := 0xd18e0.
Definition b0_incs (m : word -> option byte) : Prop := rw_cells b0segs m B0_INCS [CB 56 BzIncs.incs_bytes].

End ACeilS1.
