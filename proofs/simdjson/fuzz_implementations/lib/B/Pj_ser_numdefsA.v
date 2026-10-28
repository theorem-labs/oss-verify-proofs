(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep Frame.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_libiface Sj_akit Sj_acps Sj_hkit Sj_num_akit
     Pj_rtkA Pj_defsA Pj_ser_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition PJ_ITOA_STACK_A : Z := 112 + RT_STACK.

Section WithRT.
Variable RT : rt_sig.
Variable PMc : Model -> Prop.
Notation aevt := (aevt RT PMc).

Definition itoa_cpsA (pc : Z) : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (DST q lo v : Z) (fN : Z) (kN : nat)
         (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (junk : list byte),
  fdfs_only PMc -> mat_stable PMc ->
  In (fN, kN) (rt_frames RT Σ) -> fN <= DST -> DST + 24 <= fN + fs_size kN - 8 -> DST mod 8 = 0 ->
  rw_cells bsegs m DST [CB 24 junk] -> bytes_at bsegs m (shad DST) (repeat z8 3) ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo q -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + PJ_ITOA_STACK_A <= q ->
  q + 16 <= USTACK_TOP -> q mod 16 = 0 -> 0 <= v < 2^64 ->
  Z.of_nat (length (rt_frames RT Σ)) + 1 <= FRAMES_TOT -> 1 <= rt_credit RT Σ ->
  (forall (Σ' : rts RT) (e : Z) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (m' : mem) (nb : list byte),
     ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' lo q ->
     rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_credit RT Σ - 1 <= rt_credit RT Σ' ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(DST, DST + 24)] m m' ->
     DST < e <= DST + 20 -> rw_cells bsegs m' DST [CB 24 nb] ->
     aevt Σ' K (MS (mkR ra (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 (wz e) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz DST) (wz v) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz pc) fc None m (seg_rom bsegs)).
End WithRT.
