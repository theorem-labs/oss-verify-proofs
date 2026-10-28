(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCLemmas1 CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCutSM CmpCutSmA.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCutSD CmpCut0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition MS3 (cx : cctx) (g : eg) (e : est) (nG nSel : Z) (usp : Z) (sv : word) (W : s3w)
                (m0 : word -> option byte) (i16 : list byte) (b : bw) (m : word -> option byte) : Prop :=
  rw_cells s0segs m (c_E cx) (EHEAD1 cx g (est_set_bw e b)) /\
  rw_cells s0segs m (c_E cx + 640) (EHEAD2 cx g (est_set_bw e b)) /\
  u8arr s0segs m (c_A2 cx) (zb8 (zbl (e_arr2 e) (e_nblock e) b) ARR2_SIZE) /\
  u8arr s0segs m (c_A1 cx) (zb8 (e_arr1 e) ARR1_SIZE) /\
  u8arr s0segs m (c_E cx + 128) (ovb (e_inUse e) (jseg (c_J cx) 128 256) 256) /\
  u8arr s0segs m (c_E cx + 19706) (ovb (e_selectorMtf e) (jseg (c_J cx) 19706 18002) 18002) /\
  u8arr s0segs m (c_E cx + 1704) (ovb (e_selector e) (jseg (c_J cx) 1704 18002) 18002) /\
  u8arr s0segs m (c_E cx + 37708) (ovb (e_len e) (jseg (c_J cx) 37708 1548) 1548) /\
  u32arr s0segs m (c_E cx + 39256) (ovw (e_code e) (jseg (c_J cx) 39256 6192) 1548) /\
  rw_cells s0segs m (usp + 8) (sd_lo3 cx e nG sv W) /\
  rw_cells s0segs m (usp + 560) (sd_hi3 cx e nG nSel W) /\
  u8arr s0segs m (usp + 872) i16 /\
  mem_inv s0segs m /\
  munch (sdW3 cx usp) m0 m /\ wmono s0segs m0 m.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition S0_smD_spec (SDF : est -> Z -> Z -> Prop) : Prop :=
  forall (Q : machine_state -> Prop) (cx : cctx) (g : eg) (e0 : est) (c0 f0 p0 i0 h0 w0 q0 : zarr)
         (m : word -> option byte) (sv : word) (W : s3w) (i16 : list byte)
         (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
  let e := est_C e0 c0 f0 p0 h0 w0 q0 in
  let eD := est_D e0 c0 f0 p0 i0 h0 w0 q0 in
  let nG := smA_ng e0 in let nSel := smB_nsel e0 c0 f0 h0 w0 q0 in
  let E := c_E cx in let usp := bv_unsigned sp in
  g_mtf g = true -> g_bs g = true -> g_zbits g = Z_to_bv 64 (c_A2 cx + e_nblock e0) ->
  cctx_ok cx -> cctx_sep cx -> CEIL <= usp -> usp + 1008 <= 18446744073709551616 ->
  0 <= e_nblock e0 -> e_nblock e0 + bw_numZ (e_bw eD) <= ARR2_SIZE -> bw_ok (e_bw e0) ->
  Z.of_nat (length i16) = 16 -> SDF e nG nSel ->
  MS3 cx g e nG nSel usp sv W m i16 (e_bw e0) m ->
  (forall (m' : word -> option byte) (i16' : list byte)
          (ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' : word),
     MS3 cx g e nG nSel usp sv W m i16' (e_bw eD) m' -> Z.of_nat (length i16') = 16 -> bw_ok (e_bw eD) ->
     evt s0segs Q (MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 E) s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
                       F (Z_to_bv 64 0x19190) fc None m' (seg_rom s0segs))) ->
  evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 nG) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x17474) fc None m (seg_rom s0segs)).

End ACeilS1.
