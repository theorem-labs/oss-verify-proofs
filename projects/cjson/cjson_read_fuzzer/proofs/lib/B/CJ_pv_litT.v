(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pwlopts_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pwlopts_A.CJ_band3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs CJ_iface AShadow CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_pbuf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_pvalue_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pv_ctx.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pv_ctx.CJ_fp_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_fuzz_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_fuzz_iface.CJ_print_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.CJ_print_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_pv_ctx CJ_pv_common CJ_pv_cases CJ_pv_calls CJ_pv_lits ICPT_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section LITT.
  Variable Q : pvi.
  Local Notation AI := (q_ai Q).    Local Notation TI := (q_ti Q).
  Local Notation ra := (q_ra Q).    Local Notation sp := (q_sp Q).    Local Notation gp := (q_gp Q).    Local Notation tp := (q_tp Q).
  Local Notation s0 := (q_s0 Q).    Local Notation s1 := (q_s1 Q).    Local Notation s2 := (q_s2 Q).    Local Notation s3 := (q_s3 Q).
  Local Notation s4 := (q_s4 Q).    Local Notation s5 := (q_s5 Q).    Local Notation s6 := (q_s6 Q).    Local Notation s7 := (q_s7 Q).
  Local Notation s8 := (q_s8 Q).    Local Notation s9 := (q_s9 Q).    Local Notation s10 := (q_s10 Q).  Local Notation s11 := (q_s11 Q).
  Local Notation F := (q_F Q).      Local Notation m := (q_m Q).      Local Notation g := (q_g Q).
  Local Notation sp0 := (q_sp0 Q).  Local Notation SPB := (q_SPB Q).  Local Notation LR := (q_LR Q).    Local Notation B := (q_B Q).
  Local Notation LF := (q_LF Q).    Local Notation np0 := (q_np0 Q).  Local Notation BB := (q_BB Q).    Local Notation CH := (q_CH Q).
  Local Notation n := (q_n Q).      Local Notation p := (q_p Q).      Local Notation PB := (q_PB Q).    Local Notation len0 := (q_len0 Q).
  Local Notation dep := (q_dep Q).  Local Notation fw := (q_fw Q).    Local Notation lo := (q_lo Q).
  Local Notation SA := (q_SA Q).    Local Notation Fr := (q_Fr Q).
  Hypothesis PVL : pvl Q.
  Local Notation SP := (bv_unsigned sp).
  Local Notation POST := (pvalue_post AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LR B LF np0 BB CH n p PB len0 dep fw lo m g).
  Ltac lits := pose proof (pvl_lits Q PVL)
                 as ((PL1 & PL2 & PL3) & PB8 & AL & S47 & TOP & BOT & PB80 & CEIL & LO & TP & N1 & BLR & DEPN & DEP0 & PNZ
                     & CHOK & CHL & CHB & RA1 & RA2 & NPM & BBA & LEN0 & LFR & (GSA1 & GSA2) & (FAL & FLO & FHI & FNEW)
                     & SPR & RAR & S0R & (TOPR & BOTE) & CHN0);
               pose proof (Z.shiftr_div_pow2 Fr 3 ltac:(lia)) as SHFR; change (2^3) with 8 in SHFR;
               pose proof alloc_ceiling_eq as ACE; pose proof KHIGH_eqs as KHE.
  Hypothesis ENS : ensure_stmt AI TI.
  Hypothesis FLAGLOW : art_flag_low_stmt AI.
  Hypothesis MEMCPY : asan_memcpy_spec.

  Theorem pv_true_case : pv_case_at PV_TRUE_ENTRY Q.
  Proof.
    unfold pv_case_at. intros until x31. intros CTXX. lits. unfold CASE_ST, PVPOST, PV_TRUE_ENTRY, ASHBASE, SHR.
    pose proof CTXX as [CTX FRX]. pose proof CTX as (HL & HP & PBS1 & ARR & LEN & PN & ERR & MI & _).
    pose proof PN as (PN1 & PN2 & PN3).
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. zstep. zstep.
    change (Z_to_bv 64 550332) with (wz AENSURE_ENTRY). apply evt_done. cbv beta.
    eapply lscps_bind.
    { eapply (pvx_ensure Q PVL ENS) with (needed := 5); [exact CTXX| lia| rewrite unsigned_lit by lia; lia]. }
    cbv beta. intros ms2 mo2 g2 PO.
    destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & LB2 & TRS2 & B2 & np2 & errv2 & -> & RES).
    replace (ret_pc (Z_to_bv 64 0x846cc)) with (Z_to_bv 64 0x846cc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct RES as [[-> EX] | (buf' & len' & bs' & -> & BNZ & CTX2 & ROOM & LEN2)].
    - (* [comment removed for export] *)
      pose proof EX as ((_ & _) & _ & _ & MI2 & _).
      eapply lscps_step_evt. cbv beta delta [mkR]. zstep. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity].
      apply evt_done. cbv beta. eapply (pv_epi' Q PVL FLAGLOW). exact EX.
    - pose proof CTX2 as [(HL2 & HP2 & _ & _ & _ & _ & _ & MI2 & _) _].
      pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL2 (perm_in_head _ _ _ HP2)) as (R1 & _ & _ & R4). pose_perm_blk_band HL2 HP2. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. try rewrite alloc_ceiling_eq in R4.
      eapply lscps_step_evt. cbv beta delta [mkR]. zstep. if_cases K; zify_cond K; [exfalso; try rewrite Z.mod_small in K by lia; lia|].
      zstep. zstep. zstep. zstep.
      change (Z_to_bv 64 340332) with (Z_to_bv 64 AASANMEMCPY). change (Z_to_bv 64 135712) with (Z_to_bv 64 LIT_TRUE).
      eapply evt_cut.
      { eapply (pvx_memcpy_lit Q PVL MEMCPY) with (lit := lit_true);
          [exact CTX2| exact (proj2 (proj2 lit_slots))| apply lit_true_at; exact MI2| reflexivity| lia| unfold LIT_TRUE; lia| unfold LIT_TRUE; lia| reflexivity| lia]. }
      cbv beta. intros ms' PO.
      destruct PO as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m3 & bs3 & -> & CTX3 & NUL).
      replace (ret_pc (Z_to_bv 64 0x846e0)) with (Z_to_bv 64 0x846e0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      apply evt_done. cbv beta.
      eapply (pv_ret1 Q PVL FLAGLOW). eapply (pvx_exit1 Q PVL); [exact CTX3| exact NUL].
  Qed.
End LITT.


End CeilWrap.
