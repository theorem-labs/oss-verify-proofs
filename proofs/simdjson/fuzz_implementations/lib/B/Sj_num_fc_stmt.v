(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjNumber.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.U Require Import Sj_num_kitn.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_iface Sj_num_bdefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section FCStmt.
Variable RT : rt_sig.
Variable PMc : Model -> Prop.

Definition fcb_stmt : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (A FIRST LAST OUT lo p n : Z) (txt : list byte) (v0 : word),
  tp = Z_to_bv 64 B_TP -> frm0 fc ->
  (length (rt_frames RT Σ) + FFB_FRAMES <= FRAMES_MAX)%nat -> rt_frames RT Σ <> [] -> FFB_CREDIT <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + SPB_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  In (p, n) (rt_live RT Σ) -> p mod 8 = 0 -> p <= A -> LAST + 8 <= p + n -> A + Z.of_nat (length txt) <= p + n ->
  bytes_at bsegs m A txt -> Z.of_nat (length txt) < 2147483648 -> A <= FIRST -> FIRST < LAST -> LAST <= A + Z.of_nat (length txt) ->
  rw_cells bsegs m OUT [C8 v0] -> OUT mod 8 = 0 -> bv_unsigned sp <= OUT -> OUT + 8 <= USTACK_TOP ->
  (forall (Σ' : rts RT) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' (v : word), frm0 fc' ->
     rt_after RT Σ' (bv_unsigned sp) lo m m' -> rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) OUT 8 m m' ->
     rw_cells bsegs m' OUT [C8 v] ->
     rt_frames RT Σ' = rt_frames RT Σ -> rt_live RT Σ' = rt_live RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ - FFB_CREDIT <= rt_credit RT Σ' ->
     aevt RT PMc Σ' K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F' (ret_pc ra) fc' None m' (seg_rom bsegs))) ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) (Z_to_bv 64 OUT) (Z_to_bv 64 53) (Z_to_bv 64 0xA0000002E) (Z_to_bv 64 1)
                           a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 B_FROMCHARS) fc None m (seg_rom bsegs)).
End FCStmt.
