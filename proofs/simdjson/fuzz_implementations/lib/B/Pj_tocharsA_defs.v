(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_libiface Sj_akit Sj_acps Sj_hkit Sj_num_akit Pj_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition DBOX_ENTRY_B : Z := 0xc009c.
Definition FMT_ENTRY_B : Z := 0xc062c.

Definition DBOX_STACK_B : Z := 192 + RT_STACK.
Definition FMT_STACK_B : Z := 80 + RT_STACK.

Section WithRT.
Variable RT : rt_sig.
Variable PMc : Model -> Prop.

Definition dbox_cpsB : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (p lo NB sg fN : Z) (kN : nat)
         (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (nb : list byte) (c0 c1 : word),
  fdfs_only PMc -> mat_stable PMc ->
  In (fN, kN) (rt_frames RT Σ) -> fN <= NB -> NB + 40 <= fN + fs_size kN - 8 -> NB mod 8 = 0 ->
  u8arr bsegs m NB nb -> length nb = 40%nat -> bytes_at bsegs m (shad NB) (repeat z8 5) -> 0 <= sg <= 1 ->
  rw_cells bsegs m (p + 8) [C4 c0; C4 c1] ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo p -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + DBOX_STACK_B <= p ->
  p + 48 <= USTACK_TOP -> p mod 16 = 0 -> frm0 fc ->
  Z.of_nat (length (rt_frames RT Σ)) + 1 <= FRAMES_TOT -> 1 <= rt_credit RT Σ ->
  (forall (Σ' : rts RT) (n e : Z) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' (nb' : list byte),
     frm0 fc' -> ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' lo p ->
     rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_credit RT Σ - 1 <= rt_credit RT Σ' ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) p [(NB, NB + 40); (p + 8, p + 16)] m m' ->
     1 <= n <= 20 -> SF_EMIN <= e <= SF_EMAX ->
     rw_cells bsegs m' (p + 8) [C4 (wz (e mod 4294967296)); C4 (wz n)] -> u8arr bsegs m' NB nb' -> length nb' = 40%nat ->
     bytes_at bsegs m' (shad NB) (repeat z8 5) ->
     aevt RT PMc Σ' K (MS (mkR ra (wz p) gp (wz TPV_A) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                       F' (ret_pc ra) fc' None m' (seg_rom bsegs))) ->
  aevt RT PMc Σ K (MS (mkR ra (wz p) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (NB + sg)) (wz (p + 12)) (wz (p + 8)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz DBOX_ENTRY_B) fc None m (seg_rom bsegs)).

Definition fmt_cpsB : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (p lo NB sg n e fN : Z) (kN : nat)
         (ra gp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (nb : list byte),
  fdfs_only PMc -> mat_stable PMc ->
  In (fN, kN) (rt_frames RT Σ) -> fN <= NB -> NB + 40 <= fN + fs_size kN - 8 -> NB mod 8 = 0 ->
  u8arr bsegs m NB nb -> length nb = 40%nat -> bytes_at bsegs m (shad NB) (repeat z8 5) -> 0 <= sg <= 1 ->
  1 <= n <= 20 -> SF_EMIN <= e <= SF_EMAX ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo p -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + FMT_STACK_B <= p ->
  p + 48 <= USTACK_TOP -> p mod 16 = 0 ->
  (forall (e' : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m' (nb' : list byte),
     ART RT Σ m' -> mem_inv bsegs m' -> stk bsegs m' lo p ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) p [(NB, NB + 40)] m m' ->
     NB + sg < e' <= NB + sg + 26 -> u8arr bsegs m' NB nb' -> length nb' = 40%nat ->
     aevt RT PMc Σ K (MS (mkR ra (wz p) gp (wz TPV_A) t0' t1' t2' s0 s1 (wz e') a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                      F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt RT PMc Σ K (MS (mkR ra (wz p) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (NB + sg)) (wz n) (wz e) (wz (-4)) (wz 15) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz FMT_ENTRY_B) fc None m (seg_rom bsegs)).
End WithRT.
