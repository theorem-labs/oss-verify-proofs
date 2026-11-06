(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec Image FP.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit D_iface D_defs D_libiface Lept_iface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition e_numaCreate : Z := 0x91a5c.
Definition e_numaDestroy : Z := 0x91cb8.
Definition e_numaAddNumber : Z := 0x91e0c.
Definition e_numaGetCount : Z := 0x92370.
Definition e_numaGetIValue : Z := 0x92654.
Definition e_numaSort : Z := 0x931d4.
(* [comment removed for export] *)
Definition RA_NUMACREATE_CALLOC1 : Z := 0x91aa4.
Definition numaCreate_trace_ok (ch : list Z) : Prop := Forall (fun r => 4096 <= r < 2^64) ch.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition RO_SIGN_TAB : Z := 0x239e8.          (* [comment removed for export] *)
Definition RO_HALF : Z := 0x10390.
Definition D_ONE : word := Z_to_bv 64 0x3ff0000000000000.
Definition D_MONE : word := Z_to_bv 64 0xbff0000000000000.
Definition D_HALF : word := Z_to_bv 64 0x3fe0000000000000.
(* [comment removed for export] *)
Definition RO_GUARD_LO : Z := 0x103b0.
Definition RO_GUARD_HI : Z := 0x10338.
Definition D_GUARD_LO : word := Z_to_bv 64 0xc1e0000000200000.
Definition D_GUARD_HI : word := Z_to_bv 64 0x41e0000000000000.
Definition ED_RO (m : mem) : Prop :=
  ro_cells asegs m RO_SIGN_TAB [C8 D_ONE; C8 D_MONE] /\ ro_cells asegs m RO_HALF [C8 D_HALF]
  /\ ro_cells asegs m RO_GUARD_LO [C8 D_GUARD_LO] /\ ro_cells asegs m RO_GUARD_HI [C8 D_GUARD_HI].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ival_w (k : Z) : word := fcvt_s_w RNE (Z_to_bv 64 k).
(* [comment removed for export] *)
Definition FZERO_W : word := nan_box (Z_to_bv 32 0).
(* [comment removed for export] *)
Definition fa0 : bv 5 := Z_to_bv 5 10.
Definition fa1 : bv 5 := Z_to_bv 5 11.
Definition freg_is (F : bvmap 5 word) (r : bv 5) (v : word) : Prop := reg_get F r = v.
Definition EDGE_VALS : list Z := [45; 75; 115; 185].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition numa_cells (cap n arr : Z) (pad : list byte) : list cell :=
  [C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 n); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0x3f800000); CB 4 pad; C8 (Z_to_bv 64 arr)].
(* [comment removed for export] *)
Definition numa_arr_cells (cap : Z) (vals : list word) (junk : list byte) : list cell :=
  map C4 vals ++ [CB (Z.to_nat (4 * cap - 4 * Z.of_nat (length vals))) junk].
Definition numa_obj (live : list (Z * Z)) (m : mem) (na cap arr : Z) (vals : list word) : Prop :=
  (exists pad, rw_cells asegs m na (numa_cells cap (Z.of_nat (length vals)) arr pad))
  /\ (exists junk, rw_cells asegs m arr (numa_arr_cells cap vals junk))
  /\ chunk live na 32 /\ chunk live arr (4 * cap) /\ arr <> na
  /\ 1 <= cap <= 25600 /\ Z.of_nat (length vals) <= cap.
(* [comment removed for export] *)
Definition numa_live (na cap arr : Z) (live : list (Z * Z)) : list (Z * Z) := (arr, 4 * cap) :: (na, 32) :: live.
(* [comment removed for export] *)
Definition numa_gone (na arr : Z) (live : list (Z * Z)) : list (Z * Z) := live_remove na (live_remove arr live).
(* [comment removed for export] *)
Definition LOC_LO : Z := -1.
Definition LOC_HI : Z := 20000.
Definition loc_ok (k : Z) : Prop := LOC_LO <= k <= LOC_HI.
Definition numa_ints (vals : list word) (ks : list Z) : Prop := vals = map ival_w ks /\ Forall loc_ok ks.
Definition numa_cap (n : Z) : Z := if n =? 0 then 50 else n.


Section GqNuma.
Variable RT : rt_sig.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition numaCreate_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (n : Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  s32 a0 n -> 0 <= n <= 16128 ->
  uctx m sp s0 ras -> numaCreate_trace_ok ras ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 0 2 (mcost (4 * numa_cap n)) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_numaCreate m)))
    (fun c => exists (Σ' : rts RT) (na arr : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 na) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ numa_obj (rt_live RT Σ') m' na (numa_cap n) arr []) c
       /\ rt_live RT Σ' = numa_live na (numa_cap n) arr (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - mcost (4 * numa_cap n) <= rt_credit RT Σ').

Definition numaDestroy_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pna na cap arr : Z) (vals : list word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pna -> optrF RT Σ m pna 8 -> rw_cells asegs m pna [C8 (Z_to_bv 64 na)] ->
  numa_obj (rt_live RT Σ) m na cap arr vals ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 0 0 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_numaDestroy m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pna, pna + 8)] m m' /\ rw_cells asegs m' pna [C8 (Z_to_bv 64 0)]) c
       /\ rt_live RT Σ' = numa_gone na arr (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ <= rt_credit RT Σ').

Definition numaAddNumber_fast_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (na cap arr : Z) (vals : list word) (v : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 na -> freg_is F fa0 v ->
  numa_obj (rt_live RT Σ) m na cap arr vals -> Z.of_nat (length vals) < cap ->
  lenv RT Σ m sp lo (LSTK 5) -> lres RT Σ 0 0 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_numaAddNumber m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
          /\ lpost RT Σ Σ' m m' sp lo
          /\ keeps RT Σ Σ' sp [(na, na + 32); (arr, arr + 4 * cap)] m m'
          /\ numa_obj (rt_live RT Σ') m' na cap arr (vals ++ [v])) c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ <= rt_credit RT Σ').


End GqNuma.
