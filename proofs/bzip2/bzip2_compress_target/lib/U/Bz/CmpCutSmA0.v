(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCutSM.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCutSmA CmpCut0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition S0_smA_spec (SMAFACTS : est -> Prop) : Prop :=
  forall (Q : machine_state -> Prop) (cx : cctx) (g : eg) (e : est) (m : word -> option byte) (sv : word)
         (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w136 w144 w152 w160 w168 w176 : word)
         (w576 w584 w592 w600 w608 : word)
         (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
  let E := c_E cx in let A1 := c_A1 cx in let A2 := c_A2 cx in let usp := bv_unsigned sp in
  let A := sm_alpha e in let nG := smA_ng e in
  g_mtf g = true ->
  emem cx s0segs g e m -> amem cx s0segs e m -> cimg_mem S0C m sv ->
  rw_cells s0segs m (usp + 8)
    [C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88; C8 w96; C8 w104; C8 w112; C8 w120;
     C8 (Z_to_bv 64 (E + 37708)); C8 w136; C8 w144; C8 w152; C8 w160; C8 w168; C8 w176] ->
  rw_cells s0segs m (usp + 576) [C8 w576; C8 w584; C8 w592; C8 w600; C8 w608] ->
  mem_inv s0segs m -> cctx_ok cx -> cctx_sep cx -> cctx_img S0C cx -> CEIL <= usp -> usp + 1008 <= 18446744073709551616 ->
  SMAFACTS e ->
  (forall m' (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 : word),
     emem cx s0segs g (est_A e) m' -> amem cx s0segs (est_A e) m' -> cimg_mem S0C m' sv ->
     rw_cells s0segs m' (usp + 8) (smA_slots3 cx e usp sv w24 w56) ->
     rw_cells s0segs m' (usp + 576) [C8 (Z_to_bv 64 999999999); C8 w584; C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
     mem_inv s0segs m' -> munch (smA_W3 cx usp) m m' -> wmono s0segs m m' ->
     evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7
                            (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 A1) s4 (Z_to_bv 64 (usp + 616)) s6 (Z_to_bv 64 (usp + 616 + 4 * nG))
                            (Z_to_bv 64 (usp + 888 + 2 * nG)) (Z_to_bv 64 A) (Z_to_bv 64 (-1)) (Z_to_bv 64 1032) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x160e8) fc None m' (seg_rom s0segs))) ->
  evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7
                         s2 s3 s4 (Z_to_bv 64 (E + 672)) (Z_to_bv 64 A1) (Z_to_bv 64 (E + 128)) s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x15d90) fc None m (seg_rom s0segs)).

                    (* [comment removed for export] *)

(* [comment removed for export] *)

End ACeilS1.
