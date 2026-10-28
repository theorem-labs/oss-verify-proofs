(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs X_aexdefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition VECX_DEPTH : Z := 2400.

Definition VECX_W : list (Z * Z) := [(AEX_VEC_OBJ, AEX_VEC_OBJ + 24)].

Section Stmt.
Variable RT : rt_sig.
Variable PMc : Model -> Prop.

Definition kcont (Σ' : rts RT) (K : config -> Prop) (ms' : machine_state) : Prop := cps bsegs (ASTA RT Σ' PMc (eq ms')) K.

Definition vecx_stmt : Prop :=
  forall (Σ : rts RT) (K : config -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (A8 lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 AEX_VEC_OBJ -> tp = Z_to_bv 64 TP_A ->
  In (A8, 8) (rt_live RT Σ) -> A8 mod 16 = 0 ->
  rw_cells bsegs m AEX_VEC_OBJ [C8 (Z_to_bv 64 A8); C8 (Z_to_bv 64 (A8 + 8)); C8 (Z_to_bv 64 (A8 + 8))] ->
  ART RT Σ m -> mem_inv bsegs m ->
  call_ok RT Σ m sp lo -> lo + RT_STACK + VECX_DEPTH <= bv_unsigned sp ->
  bv_unsigned s0 <= bv_unsigned sp - 16 ->
  0 <= bv_unsigned ra < 2^64 ->
  (forall (Σ' : rts RT) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (m' : mem),
     rt_after_f RT Σ' (bv_unsigned sp) lo m m' ->
     rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ) (bv_unsigned sp) VECX_W m m' ->
     rw_cells bsegs m' AEX_VEC_OBJ [C8 (Z_to_bv 64 A8); C8 (Z_to_bv 64 A8); C8 (Z_to_bv 64 (A8 + 8))] ->
     rt_live RT Σ' = live_remove A8 (rt_live RT Σ) -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ' = rt_credit RT Σ ->
     kcont Σ' K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  cps bsegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                      F (Z_to_bv 64 X_VECDTOR) fc None m (seg_rom bsegs)))) K.
End Stmt.
