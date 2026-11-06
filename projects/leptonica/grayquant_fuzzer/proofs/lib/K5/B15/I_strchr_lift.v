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
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr FP.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs D_libiface Lept_iface Lept_env LeptC_kit LeptL_kit
  R_small R_m2s R_thread I_consts I_qck I_ikit Gq_numa Gq_gaps F_atof_kit I_strchr_kit I_strchr.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma seps_in_lits : In (LITSEPS, 5) ACC_LITS.
Proof.
  assert (B : existsb (fun r => andb (Z.eqb (fst r) LITSEPS) (Z.eqb (snd r) 5)) ACC_LITS = true) by (vm_compute; reflexivity).
  apply existsb_exists in B. destruct B as ([a n] & Hin & E). cbn [fst snd] in E.
  apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. subst a n. exact Hin.
Qed.

Section Lift.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis AF_SCHR : forall Σ m, ART RT Σ m -> icells_schr m.
Hypothesis AF_SHW : forall Σ m p n, ART RT Σ m -> 0 < n -> rng_class RT Σ p n -> qc_words m p n /\ region_in_mem p n.

Theorem strchr_lift : strchr_seps_icontract RT.
Proof using AF AF_SCHR AF_SHW.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m c lo
    FDO MST -> -> C0 TP ART0 MI CO.
  destruct CO as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned).
  assert (ACC : acc asegs m LITSEPS 5).
  { pose proof (af_acc_lits RT AF Σ m ART0) as FA. rewrite Forall_forall in FA. exact (FA (LITSEPS, 5) seps_in_lits). }
  assert (QW : qc_words m LITSEPS 5).
  { apply (AF_SHW Σ m LITSEPS 5 ART0 ltac:(lia)). right; right; right. unfold LITSEPS, SEGTOP_A. lia. }
  unfold entry_st, e_strchr. rewrite ESP.
  assert (USP : bv_unsigned (Z_to_bv 64 usp) = usp) by (unfold usp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  rewrite ?USP.
  change (Z_to_bv 64 LIT_SEPS) with (Z_to_bv 64 LITSEPS). change 0x50fc4 with F_STRCHR.
  unfold STACK_WIN, RT_STACK, USTACK_TOP in *.
  apply (cps_walk_lemma RT AF _ _ _ _ MST).
  eapply evt_cut.
  { apply (istrchr_spec c ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F (frm_clear fc) m usp lo
             C0 (AF_SCHR Σ m ART0) ACC QW MI ST); unfold ISTRCHR_DEPTH; lia. }
  intros ms' PO. unfold frame_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST').
  rewrite USP in ST'.
  apply evt_done. apply cps_finish. intros cfg Hc.
  unfold icpt_post. rewrite ?USP. eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. exists m'.
  assert (ART' : ART RT Σ m').
  { apply (art_client_writes RT AF Σ m m' lo [(usp - ISTRCHR_DEPTH, usp)] ART0 MU WM); [unfold STACK_WIN; lia|].
    cbn [ivls_client]. split; [| exact I]. intros z Hz. left. unfold ISTRCHR_DEPTH in *. unfold USTACK_TOP. lia. }
  split.
  { unfold ret_st. exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F, fc.
    reflexivity. }
  split.
  { unfold rt_after. split; [exact ART'|]. split; [exact MI'|]. split; [exact WM| exact ST']. }
  split; [| exact I].
  intros a Ha _. apply MU. cbn [outside]. split; [| exact I].
  destruct (aclient_split RT AF Σ m usp (bv_unsigned a) ART0 Ha) as [H|H]; unfold ISTRCHR_DEPTH, STACK_WIN in *; lia.
Qed.

End Lift.
