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
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_lits Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit D_iface D_defs
  Gq_numa Gq_gaps Gq_iface Gq_thr_iface Gq_parse_kit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section GqParseCase.
Variable RT : rt_sig.

Definition parse_case (al : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 LIT_EDGEVALS -> a1 = Z_to_bv 64 LIT_SEPS ->
  uctx m sp s0 ras ->
  Forall (fun f => In (f :: bv_unsigned ra :: ras) CLIENT_TRACES \/ In [f] CLIENT_TRACES) PARSE_RAS ->
  numaCreate_trace_ok (bv_unsigned ra :: ras) ->
  lenv RT Σ m sp lo (LSTK 7) -> lres RT Σ 2 4 PARSE_COST ->
  bv_unsigned sp mod 32 = al ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_parseStringForNumbers m)))
    (fun c => exists (Σ' : rts RT) (na arr : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 na) m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ numa_obj (rt_live RT Σ') m' na 50 arr (map ival_w EDGE_VALS)) c
       /\ rt_live RT Σ' = numa_live na 50 arr (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - PARSE_COST <= rt_credit RT Σ').

Lemma parse_of_cases : parse_case 0 -> parse_case 16 -> parseStringForNumbers_gq_cps RT.
Proof.
  intros C0 C16. unfold parseStringForNumbers_gq_cps.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo ras
    FDO MST TP A0 A1 UC TRS TR ENV RES.
  assert (AL : bv_unsigned sp mod 32 = 0 \/ bv_unsigned sp mod 32 = 16).
  { destruct ENV as (_ & _ & _ & _ & _ & _ & _ & _ & SPA & _). Z.div_mod_to_equations; lia. }
  destruct AL as [AL|AL]; [eapply C0| eapply C16]; eassumption.
Qed.
End GqParseCase.
