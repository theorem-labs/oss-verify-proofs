(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS NodesA Arr FP.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface Km_setelem Km_iface Pm_iface Pm_iface2 Pm_iface4 Cf_iface RT_fk Bi_iface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition e_rasteropUniLow : Z := 0xaf9c4.

Section RopuIface.
Variable RT : rt_sig.

(* [comment removed for export] *)
Definition rasteropUniLow_clr_case (dxm : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (datad dpixw dpixh dwpl dx dy dw dh : Z),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 datad -> a1 = Z_to_bv 64 dpixw -> a2 = Z_to_bv 64 dpixh -> a3 = Z_to_bv 64 8 -> a4 = Z_to_bv 64 dwpl ->
  a5 = Z_to_bv 64 dx -> a6 = Z_to_bv 64 dy -> a7 = Z_to_bv 64 dw ->
  rw_cells asegs m (bv_unsigned sp) [C8 (Z_to_bv 64 dh); C8 (Z_to_bv 64 PIX_CLR)] ->
  0 <= dx -> 0 <= dy -> 0 < dw -> 0 < dh -> dx + dw <= dpixw -> dy + dh <= dpixh -> 0 < dpixw <= 20000 -> 0 < dpixh <= 20000 ->
  0 < dwpl -> 8 * dpixw <= 32 * dwpl -> 4 * (dwpl * dpixh) <= 0x4000000 ->
  chunk (rt_live RT Σ) datad (4 * (dwpl * dpixh)) ->
  lenv RT Σ m sp lo (LSTK 1) -> lres RT Σ 0 0 0 ->
  dx mod 4 = dxm ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_rasteropUniLow m)))
    (fun c => ASTA RT Σ PMc (fun ms => exists (v : word) (m' : mem), ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v F m' ms
          /\ lpost RT Σ Σ m m' sp lo
          /\ keeps RT Σ Σ sp [(datad, datad + 4 * (dwpl * dpixh))] m m') c).

Definition rasteropUniLow_clr_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (datad dpixw dpixh dwpl dx dy dw dh : Z),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 datad -> a1 = Z_to_bv 64 dpixw -> a2 = Z_to_bv 64 dpixh -> a3 = Z_to_bv 64 8 -> a4 = Z_to_bv 64 dwpl ->
  a5 = Z_to_bv 64 dx -> a6 = Z_to_bv 64 dy -> a7 = Z_to_bv 64 dw ->
  (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned sp) [C8 (Z_to_bv 64 dh); C8 (Z_to_bv 64 PIX_CLR)] ->
  0 <= dx -> 0 <= dy -> 0 < dw -> 0 < dh -> dx + dw <= dpixw -> dy + dh <= dpixh -> 0 < dpixw <= 20000 -> 0 < dpixh <= 20000 ->
  0 < dwpl -> 8 * dpixw <= 32 * dwpl -> 4 * (dwpl * dpixh) <= 0x4000000 ->
  chunk (rt_live RT Σ) datad (4 * (dwpl * dpixh)) ->
  lenv RT Σ m sp lo (LSTK 1) -> lres RT Σ 0 0 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_rasteropUniLow m)))
    (fun c => ASTA RT Σ PMc (fun ms => exists (v : word) (m' : mem), ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v F m' ms
          /\ lpost RT Σ Σ m m' sp lo
          /\ keeps RT Σ Σ sp [(datad, datad + 4 * (dwpl * dpixh))] m m') c).

End RopuIface.
