(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCutSM CmpCutSmA CmpCutSmB.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCutSmC CmpCut0 CmpCutSD0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Definition S0_smC_spec (SDF : est -> Z -> Z -> Prop) : Prop :=
  forall (Q : machine_state -> Prop) (cx : cctx) (e0 : est) (c0 f0 p0 h0 w0 q0 : zarr)
         (m : word -> option byte) (sv w24 w56 w584 : word) (J184 i16 : list byte) (lo : Z)
         (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
  let e := est_C e0 c0 f0 p0 h0 w0 q0 in let it := smB_it e0 c0 f0 h0 w0 q0 in
  let E := c_E cx in let usp := bv_unsigned sp in
  let nG := smA_ng e0 in let nSel := smB_nsel e0 c0 f0 h0 w0 q0 in
  u8arr s0segs m (E + 1704) (ovb (it_sel it) (jseg (c_J cx) 1704 18002) 18002) ->
  u8arr s0segs m (E + 19706) (ovb (e_selectorMtf e0) (jseg (c_J cx) 19706 18002) 18002) ->
  u8arr s0segs m (E + 37708) (ovb (it_len it) (jseg (c_J cx) 37708 1548) 1548) ->
  u32arr s0segs m (E + 39256) (ovw (e_code e0) (jseg (c_J cx) 39256 6192) 1548) ->
  rw_cells s0segs m (usp + 8) (smB_slots3 cx e0 usp sv w24 w56) ->
  u8arr s0segs m (usp + 184) J184 -> Z.of_nat (length J184) = 392 ->
  rw_cells s0segs m (usp + 576) [C8 (Z_to_bv 64 999999999); C8 w584; C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e0))] ->
  u8arr s0segs m (usp + 872) i16 -> Z.of_nat (length i16) = 16 ->
  stk s0segs m lo usp -> lo + 16 <= usp -> CEIL <= lo ->
  mem_inv s0segs m -> cctx_ok cx -> cctx_sep cx -> usp + 1008 <= 18446744073709551616 ->
  SDF e nG nSel ->
  (forall m' (J184' i16' : list byte) (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
     u8arr s0segs m' (E + 1704) (ovb (it_sel it) (jseg (c_J cx) 1704 18002) 18002) ->
     u8arr s0segs m' (E + 19706) (ovb (snd (smC_pm e0 c0 f0 p0 h0 w0 q0)) (jseg (c_J cx) 19706 18002) 18002) ->
     u8arr s0segs m' (E + 37708) (ovb (it_len it) (jseg (c_J cx) 37708 1548) 1548) ->
     u32arr s0segs m' (E + 39256) (ovw (smC_code e0 c0 f0 h0 w0 q0) (jseg (c_J cx) 39256 6192) 1548) ->
     rw_cells s0segs m' (usp + 8) (smB_slots3 cx e0 usp sv w24 w56) ->
     u8arr s0segs m' (usp + 184) J184' -> Z.of_nat (length J184') = 376 ->
     rw_cells s0segs m' (usp + 560) (smC_hi3 cx e0 nSel) ->
     u8arr s0segs m' (usp + 872) i16' -> Z.of_nat (length i16') = 16 ->
     stk s0segs m' lo usp -> mem_inv s0segs m' -> munch (smC_W3 cx usp) m m' -> wmono s0segs m m' ->
     evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 nG) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x17474) fc None m' (seg_rom s0segs))) ->
  evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 nSel) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x172f0) fc None m (seg_rom s0segs)).

(* [comment removed for export] *)

End ACeilS1.
