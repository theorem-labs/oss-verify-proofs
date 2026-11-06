(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Image.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_lits Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit D_iface D_defs
  Gq_numa Gq_gaps Gq_iface Gq_thr_iface Gq_thr2_iface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section GqQtabCase.
Variable RT : rt_sig.

Definition qtab_case (al : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (ras : list Z) (na arr ptab pcmap : Z) (x1 x2 : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 na -> a1 = Z_to_bv 64 8 -> a2 = Z_to_bv 64 ptab -> a3 = Z_to_bv 64 pcmap ->
  numa_obj (rt_live RT Σ) m na 50 arr (map ival_w EDGE_VALS) ->
  optrS RT Σ sp s0 ptab 8 -> optrF RT Σ m pcmap 8 -> rw_cells asegs m ptab [C8 x1] -> rw_cells asegs m pcmap [C8 x2] -> ptab <> pcmap ->
  uctx m sp s0 ras -> Forall (fun f => In (f :: bv_unsigned ra :: ras) CLIENT_TRACES) QTAB_RAS ->
  lenv RT Σ m sp lo (LSTK 6) -> lres RT Σ 1 3 QTAB_COST ->
  bv_unsigned sp mod 32 = al ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_makeGrayQuantTableArb m)))
    (fun c => exists (Σ' : rts RT) (tab cmap carr : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
          /\ lpost RT Σ Σ' m m' sp lo
          /\ keepsL RT (rt_live RT Σ) Σ sp [(ptab, ptab + 8); (pcmap, pcmap + 8)] m m'
          /\ rw_cells asegs m' ptab [C8 (Z_to_bv 64 tab)] /\ rw_cells asegs m' pcmap [C8 (Z_to_bv 64 cmap)]
          /\ u32arr asegs m' tab (map (Z_to_bv 64) QTAB_VALS)
          /\ cmap_obj (rt_live RT Σ') m' cmap (mkCmapv carr 8 256 5)
          /\ numa_obj (rt_live RT Σ') m' na 50 arr (map ival_w EDGE_VALS)) c
       /\ rt_live RT Σ' = (tab, 1024) :: (carr, 1024) :: (cmap, 24) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - QTAB_COST <= rt_credit RT Σ').

Lemma qtab_of_cases : qtab_case 0 -> qtab_case 16 -> makeGrayQuantTableArb_gq_cps RT.
Proof.
  intros C0 C16. unfold makeGrayQuantTableArb_gq_cps.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo ras na arr ptab pcmap x1 x2
    FDO MST TP A0 A1 A2 A3 NOBJ OP1 OP2 PC1 PC2 NE UC TRS ENV RES.
  assert (AL : bv_unsigned sp mod 32 = 0 \/ bv_unsigned sp mod 32 = 16).
  { destruct ENV as (_ & _ & _ & _ & _ & _ & _ & _ & SPA & _). Z.div_mod_to_equations; lia. }
  destruct AL as [AL|AL]; [eapply C0| eapply C16]; eassumption.
Qed.
End GqQtabCase.
