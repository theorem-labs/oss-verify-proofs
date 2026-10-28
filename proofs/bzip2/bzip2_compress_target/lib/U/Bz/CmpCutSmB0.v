(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCutSM CmpCutSmA.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCutSmB CmpCut0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition S0_smB_spec (SMBFACTS : est -> zarr -> zarr -> zarr -> zarr -> zarr -> Prop) : Prop :=
  forall (Q : machine_state -> Prop) (cx : cctx) (g : eg) (e : est) (cost0 fave0 heap0 weight0 parent0 : zarr)
         (m : word -> option byte) (sv w24 w56 w584 : word) (J184 J616 J888 : list byte) (lo : Z)
         (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
  let E := c_E cx in let A1 := c_A1 cx in let usp := bv_unsigned sp in
  let A := sm_alpha e in let nG := smA_ng e in let it := smB_it e cost0 fave0 heap0 weight0 parent0 in
  g_mtf g = true -> w56 = Z_to_bv 64 (E + 51648) ->
  emem cx s0segs g (est_A e) m -> amem cx s0segs (est_A e) m -> cimg_mem S0C m sv ->
  rw_cells s0segs m (usp + 8) (smA_slots3 cx e usp sv w24 w56) ->
  u8arr s0segs m (usp + 184) J184 -> Z.of_nat (length J184) = 392 ->
  rw_cells s0segs m (usp + 576) [C8 (Z_to_bv 64 999999999); C8 w584; C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
  u8arr s0segs m (usp + 616) J616 -> Z.of_nat (length J616) = 24 ->
  u8arr s0segs m (usp + 888) J888 -> Z.of_nat (length J888) = 12 ->
  stk s0segs m lo usp -> lo + HM_FRAME <= usp -> CEIL <= lo -> usp mod 16 = 0 ->
  mem_inv s0segs m -> cctx_ok cx -> cctx_sep cx -> cctx_img S0C cx -> usp + 1008 <= 18446744073709551616 ->
  SMBFACTS e cost0 fave0 heap0 weight0 parent0 ->
  (forall m' (w584' : word) (J184' J616' J888' : list byte) (ra t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
     emem cx s0segs g (est_B e cost0 fave0 heap0 weight0 parent0) m' -> amem cx s0segs (est_A e) m' -> cimg_mem S0C m' sv ->
     rw_cells s0segs m' (usp + 8) (smB_slots3 cx e usp sv w24 w56) ->
     u8arr s0segs m' (usp + 184) J184' -> Z.of_nat (length J184') = 392 ->
     rw_cells s0segs m' (usp + 576) [C8 (Z_to_bv 64 999999999); C8 w584'; C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
     u8arr s0segs m' (usp + 616) J616' -> Z.of_nat (length J616') = 24 ->
     u8arr s0segs m' (usp + 888) J888' -> Z.of_nat (length J888') = 12 ->
     stk s0segs m' lo usp -> mem_inv s0segs m' -> munch (smB_W3 cx usp) m m' -> wmono s0segs m m' ->
     evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 (E + 45448 + 1032 * nG)) (Z_to_bv 64 4) (Z_to_bv 64 4) a2 a3 a4 a5 a6 a7
                            (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 A1) (Z_to_bv 64 (it_nSel it)) (Z_to_bv 64 (usp + 616)) (Z_to_bv 64 (E + 37708 + 258 * nG))
                            (Z_to_bv 64 (usp + 616 + 4 * nG)) (Z_to_bv 64 (usp + 888 + 2 * nG)) (Z_to_bv 64 A) (Z_to_bv 64 (-1)) (Z_to_bv 64 1032) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x172f0) fc None m' (seg_rom s0segs))) ->
  evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7
                         (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 A1) s4 (Z_to_bv 64 (usp + 616)) s6 (Z_to_bv 64 (usp + 616 + 4 * nG))
                         (Z_to_bv 64 (usp + 888 + 2 * nG)) (Z_to_bv 64 A) (Z_to_bv 64 (-1)) (Z_to_bv 64 1032) t3 t4 t5 t6)
                    F (Z_to_bv 64 0x160e8) fc None m (seg_rom s0segs)).

(* [comment removed for export] *)

End ACeilS1.
