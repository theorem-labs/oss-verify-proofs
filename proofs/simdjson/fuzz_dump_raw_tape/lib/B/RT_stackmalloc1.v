(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs R_cache_defs R_prim_defs R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_thread R_m2s RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep I_lkit RT_facts RT_release R_fs_ok R_fs0 R_fs4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import RT_iface2 RT_stackmalloc R_fs1.
Import ListNotations.
Open Scope Z_scope.

#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GWf.
Definition smgc1_case : Prop :=
  forall (Σ : rts RTA) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0x6abde8 ->
  (length (rt_frames RTA Σ) < FRAMES_MAX2)%nat -> 1 <= rt_credit RTA Σ ->
  ART RTA Σ m -> mem_inv bsegs m -> call_ok RTA Σ m sp lo ->
  fs_constg (l_FSB (lay Σ)) true m -> rt_frames RTA Σ = [] -> bv_unsigned sp + 0xa0 <= rt_sp0 RTA Σ ->
  cps bsegs (ASTA RTA Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_stack_malloc_1 m)))
    (fun c => exists (Σ' : rts RTA) (f : Z),
       ASTA RTA Σ' PMc (fun ms => exists m', ret_stF fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 f) m' ms
         /\ rt_after RTA Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RTA Σ) (rt_frames RTA Σ) (bv_unsigned sp) m m'
         /\ wr_at bsegs m' f (fs_size 1 - 8) /\ wr_at bsegs m' (shad f) (fs_size 1 / 8)) c
       /\ rt_frames RTA Σ' = (f, 1%nat) :: rt_frames RTA Σ /\ rt_live RTA Σ' = rt_live RTA Σ /\ rt_sp0 RTA Σ' = rt_sp0 RTA Σ
       /\ rt_credit RTA Σ' = rt_credit RTA Σ - 1 /\ 0 < f /\ f mod 64 = 0 /\ f + fs_size 1 < USTACK_TOP).

Section GC.
Hypothesis SMGC1 : smgc1_case.
Theorem rta_stack_malloc_1 : stack_malloc1_contract RTA.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    FDO MST -> Hlen Hcr ART0 MI0 CALL TOPC.
  intros T cf Hc Hkont. cbn [ART rt_frames rt_live rt_sp0 rt_credit RTA] in *. unfold rtA_frames, rtA_live, rtA_sp0, rtA_credit in *.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  destruct (sm_pre Σ m 1%nat lo ART0 ltac:(lia) LOW) as (FC & FH & FL & OK & NB & HH & FF & TLS & (dtvbeg & Hdb & TGA) & TC & (tb & te & TT)
    & M2S & FSOK & HLO & FSL & HD & HDL & HX & HXL & HT & HTL).
  destruct FC as ((gflag & FC & GNIL & GCR) & OFL).
  destruct gflag.
  {
    exact (SMGC1 Σ PMc ra sp gp (Z_to_bv 64 0x6abde8) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
             FDO MST eq_refl Hlen Hcr ART0 MI0 CALL FC (GNIL eq_refl eq_refl) (TOPC (GNIL eq_refl eq_refl)) T cf Hc Hkont). }
  apply fs_constg_false in FC.
  assert (W1 : evt bsegs (sm1_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (l_FSB (lay Σ)) (fss_hint (fs_of Σ 1))
                            (fss_flags (fs_of Σ 1)) lo m)
                 (entry_st ra sp gp (Z_to_bv 64 0x6abde8) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                    F fc e_stack_malloc_1 m)).
  { unfold entry_st.
    exact (stack_malloc_1_spec ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
      (l_FSB (lay Σ)) (fss_hint (fs_of Σ 1)) (fss_flags (fs_of Σ 1)) (l_DTV (lay Σ)) dtvbeg (l_TCX (lay Σ)) (l_T (lay Σ)) lo tb te
      FC FH FL OK ltac:(change (fs_cap (Z.of_nat 1)) with 4096 in NB; lia) HH FF TLS TGA TC TT M2S FSOK HLO FSL HD HDL Hdb HX HXL HT HTL ST
      ltac:(unfold RT_STACK in *; lia) ltac:(unfold USTACK_TOP in *; lia) MI0). }
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (sm_mat_stable Σ PMc MST) W1') Hc).
  intros c1 Hc1. apply Hkont. unfold sm1_post in Hc1.
  apply AST_exI in Hc1 as (jn & Hc2).
  assert (PURE : (jn < Z.to_nat 8192)%nat /\ nth (Z.to_nat ((fss_hint (fs_of Σ 1) + Z.of_nat jn) mod 8192)) (fss_flags (fs_of Σ 1)) 1 = 0).
  { destruct Hc2 as (_ & HP & _).
    destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hj & Hfree & _).
    split; assumption. }
  destruct PURE as (Hj & Hfree).
  apply (sm_finish Σ PMc ra sp gp (Z_to_bv 64 0x6abde8) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m 1%nat (Z.of_nat jn) lo fc _ c1 ART0 ltac:(lia)
           ltac:(change (NF (Z.of_nat 1)) with 8192; lia) Hfree Hcr (cap_1 _ Hlen) LOW LOR SPT Hc2).
  intros ms HP.
  destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & junk1 & junk2 & -> & MU & WM & MI
    & ST' & _ & _ & PH & PC & PF & FR & SH & PFr).
  exists m'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST'|]. split; [exact PH|]. split; [exact PC|]. split; [exact PF|].
  split; [exact (rw_cells_wrat m' _ _ _ FR (Z.le_refl _))|].
  split; [exact (rw_cells_last m' _ 24 junk1 sp 88 junk2 _ (fsz (Z.of_nat 1)) eq_refl FR)|].
  split; [exact (rw_cells_wrat m' _ _ _ SH (Z.le_refl _)) | exact PFr].
Qed.
End GC.
