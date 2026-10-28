(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs R_cache_defs R_prim_defs R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_thread R_m2s RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep I_lkit RT_facts RT_release R_fs_ok R_fs4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import RT_iface2 RT_stackmalloc R_fs3 RT_iface3.
Import ListNotations.
Open Scope Z_scope.

#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GWf.

Theorem rta_stack_malloc_3w : stack_malloc3w_contract RTA.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    FDO MST -> Hcnt Htot Hcr ART0 MI0 CALL NE.
  intros T cf Hc Hkont. unfold fcount, FRAMES_MAX3, FRAMES_TOT in Hcnt, Htot. cbn [ART rt_frames rt_live rt_sp0 rt_credit RTA] in *. unfold rtA_frames, rtA_live, rtA_sp0, rtA_credit in *.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  destruct (sm_pre Σ m 3%nat lo ART0 ltac:(lia) LOW) as (FC & FH & FL & OK & NB & HH & FF & TLS & (dtvbeg & Hdb & TGA) & TC & (tb & te & TT)
    & M2S & FSOK & HLO & FSL & HD & HDL & HX & HXL & HT & HTL).
  destruct FC as ((gflag & FC & GNIL & GCR) & OFL).
  destruct gflag.
  {
    exfalso. apply NE. exact (GNIL eq_refl eq_refl). }
  apply fs_constg_false in FC.
  assert (W1 : evt bsegs (sm3_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (l_FSB (lay Σ)) (fss_hint (fs_of Σ 3))
                            (fss_flags (fs_of Σ 3)) lo m)
                 (entry_st ra sp gp (Z_to_bv 64 0x6be3e8) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                    F fc (e_stack_malloc 3) m)).
  { unfold entry_st.
    exact (stack_malloc_3_spec ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
      (l_FSB (lay Σ)) (fss_hint (fs_of Σ 3)) (fss_flags (fs_of Σ 3)) (l_DTV (lay Σ)) dtvbeg (l_TCX (lay Σ)) (l_T (lay Σ)) lo tb te
      FC FH FL OK ltac:(change (fs_cap (Z.of_nat 3)) with 2040 in NB; lia) HH FF TLS TGA TC TT M2S FSOK HLO FSL HD HDL Hdb HX HXL HT HTL ST
      ltac:(unfold RT_STACK in *; lia) ltac:(unfold USTACK_TOP in *; lia) MI0). }
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (sm_mat_stable Σ PMc MST) W1') Hc).
  intros c1 Hc1. apply Hkont. unfold sm3_post in Hc1.
  apply AST_exI in Hc1 as (jn & Hc2).
  assert (PURE : (jn < 2048)%nat /\ nth (Z.to_nat ((fss_hint (fs_of Σ 3) + Z.of_nat jn) mod 2048)) (fss_flags (fs_of Σ 3)) 1 = 0).
  { destruct Hc2 as (_ & HP & _).
    destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hj & Hfree & _).
    split; assumption. }
  destruct PURE as (Hj & Hfree).
  apply (sm_finish Σ PMc ra sp gp (Z_to_bv 64 0x6be3e8) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m 3%nat (Z.of_nat jn) lo fc _ c1 ART0 ltac:(lia)
           ltac:(change (NF (Z.of_nat 3)) with 2048; lia) Hfree Hcr (cap_3w _ Hcnt Htot) LOW LOR SPT Hc2).
  intros ms HP.
  destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & junk1 & junk2 & -> & MU & WM & MI
    & ST' & _ & _ & PH & PC & PF & FR & SH & PFr).
  exists m'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST'|]. split; [exact PH|]. split; [exact PC|]. split; [exact PF|].
  split; [exact (rw_cells_wrat m' _ _ _ FR (Z.le_refl _))|].
  split; [exact (rw_cells_last m' _ 24 junk1 sp 472 junk2 _ (fsz (Z.of_nat 3)) eq_refl FR)|].
  split; [exact (rw_cells_wrat m' _ _ _ SH (Z.le_refl _)) | exact PFr].
Qed.
