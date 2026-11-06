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
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr FP.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_lits Lept_env LeptC_kit Lept_leaf Lept_chain LeptC_leaf Lept_objkit LeptL_kit D_iface D_defs
  Ed_fp Ed_fpkit Gq_numa Numa_kit Ed_tracekit Gq_gaps Gq_iface Gq_thr_iface Gq_parse_kit Gq_parse_kit2 Gq_thr2_iface F_atof_kit Gq_thr2_kit
  LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section NSORT.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.

(* [comment removed for export] *)
Ltac NS_STOPS := constr:([0x93408; 0x93410; 0x93414; 0x935f8; 0x90fc4; 0x90d94; 0x92064; 0x68bf8; 0x68c98]%Z).
(* [comment removed for export] *)
Ltac cmp_block := let s := NS_STOPS in nwalk s; fstep_named; try fold_regs_ns; nwalk s; fstep_named; try fold_regs_ns; flt_decide; try fold_regs_ns.

Theorem numaSort_gq_ok : numaSort_gq_cps RT.
Proof using AF GP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo na arr
    FDO MST -> -> -> -> NOBJ ENV RES.
  unfold lpost, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_numaSort, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK, NSORT_COST in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  lib_refresh RT GP.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  pose proof (numa_obj_facts _ _ _ _ _ _ NOBJ) as (_ & NCAP & NA0 & NA16 & AR0 & AR16 & INNA & INAR & NANE).
  pose proof NOBJ as ((npad & NAC) & (njunk & ARC) & _).
  unfold numa_cells, numa_arr_cells in NAC, ARC. cbn [map app length Z.of_nat Z.mul Z.sub Z.to_nat EDGE_VALS] in NAC, ARC.
  chunk_facts RT AF GP na 32. chunk_facts RT AF GP arr 200.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  assert (NAR : 0 < na /\ na + 32 < 2^47) by (clear - NA0 CKR SP0R; lia).
  assert (ARR : 0 < arr /\ arr + 200 < 2^47) by (clear - AR0 CKR0 SP0R; lia).
  hide NOBJ.
  refresh RT AF. unfold shad, SHB in *.
  change (Z.of_nat 4) with 4 in *.
  (* [comment removed for export] *)
  walk_to AF MST [(usp - 64, usp)] [0x93350; 0x935f8; 0x90fc4; 0x90d94; 0x92064; 0x68bf8; 0x68c98; 0x935dc].
  fold_regs_ns.
  (* [comment removed for export] *)
  do 8 cmp_block.
  (* [comment removed for export] *)
  let s := NS_STOPS in nwalk s.
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
  lazymatch goal with
  | AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ =>
      is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I])
  end.
  assert (PML : forall q k a, In (q, k) (rt_live RT Σ) -> q <= a < q + k -> PF a).
  { intros q k a Hq Ha. right; right; left; exists q, k; split; [exact Hq| lia]. }
  apply cps_finish; intros c Hc; subst QF; cbv beta.
  eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
  split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [split; [assumption| split; [assumption| split; [exact WM | assumption]]]| split; assumption]|].
  split; [intros a Ha _; apply AGF; exact Ha|].
  lazymatch goal with |- numa_obj _ ?mc _ _ _ _ =>
    assert (KL0 : keeps_live (rt_live RT Σ) m mc) by (intros b kk Hb a Ha; apply AGF; exact (PML b kk _ Hb Ha));
    unfold hid in NOBJ; exact (numa_obj_keep _ m mc na 50 arr _ KL0 NOBJ) end.
Qed.
End NSORT.
