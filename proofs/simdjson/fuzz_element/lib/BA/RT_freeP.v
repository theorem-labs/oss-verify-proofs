(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState ITree Nodes PropExec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_defs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs R_prim_defs R_glue_defs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import R_m2s R_thread. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_poison R_prim_kit R_depot_defs R_quar_defs R_qrec_defs R_qrecycle R_qdorec R_qcbrec R_mmapordie R_flushshadow R_secdealloc_p3 R_qput RT_state RT_rep RT_frame RT_trans RT_sep RT_freelift RT_geo0 RT_fkit RT_freestate RT_sys_stmt RT_drain_defs RT_drain_pure RT_drain_led RT_drain_kit RT_drain_geo RT_drain_ldefs RT_drain_loop RT_facts0 RT_freeA RT_freeA2 RT_freeE RT_freeS RT_freeZ RT_freestmt RT_malsec_rev RT_dsec_defs RT_dsec_art2 RT_dsec RT_freeP_defs RT_freeP_cli RT_freeP_evt RT_freeP_run RT_freeP_ret RT_freeP_fin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GW}.
Theorem free_pass_ok : munmap_node -> madvise_node -> free_pass_stmt.
Proof.
  intros MN AN Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo k s
    FDO MST -> -> ART0 MI0 CALL UWOK Hk Hq Hbig.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA). cbn [rt_sp0 RTA] in LOW. unfold rtA_sp0 in LOW.
  assert (HLO : l_ACEIL (lay Σ) <= lo) by (clear - LOW; unfold l_ACEIL, STACK_WIN in *; lia).
  assert (HLO2 : lo + 0x10000 <= bv_unsigned sp) by (clear - LOR; unfold RT_STACK in *; lia).
  assert (Husp : bv_unsigned sp + 16 <= USTACK_TOP) by exact SPT.
  pose proof (ART_wf Σ m ART0) as HW0. pose proof (geo_of_wf Σ HW0) as HG0.
  set (usp := bv_unsigned sp) in *.

  apply (cps_seq asegs _ (ASTA RTA Σ PMc (segP_post Σ k s ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m))).
  { apply (dl_evt Σ PMc _ _ MST). intros ms <-.
    exact (segP_evt Σ k s ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
             ART0 MI0 CALL UWOK Hk Hq Hbig). }
  unfold ASTA, segP_post.
  apply cps_AST_ex; intros tr. apply cps_AST_ex; intros x0. apply cps_AST_ex; intros x1. apply cps_AST_ex; intros x2.
  apply cps_AST_ex; intros x3. apply cps_AST_ex; intros x4. apply cps_AST_ex; intros x5. apply cps_AST_ex; intros x6.
  apply cps_AST_ex; intros x7. apply cps_AST_ex; intros x8. apply cps_AST_ex; intros x9. apply cps_AST_ex; intros x10.
  apply cps_AST_ex; intros x11. apply cps_AST_ex; intros x12. apply cps_AST_ex; intros m4.
  intros TT cf Hc1 HK.
  pose proof Hc1 as (_ & (_ & HAK & CK & Htr & MI4 & WM4 & ST4 & RP4 & ICF & FR4) & _ & _).
  destruct (fe_dep Σ m tr ART0 Htr) as (Dok & Dinv).
  set (D' := fst (depot_put (dep Σ) tr)) in *.
  set (Σd := pass_d Σ k s D') in *. set (Σ2 := pass_s Σ k s D').
  pose proof (pass_wf Σ m k s D' ART0 Hk Hq Dok Dinv) as HW2.
  assert (HGd : geo_ok Σd) by exact (pass_d_geo Σ k s D' HG0).
  assert (Hkd : nth_error (sec Σd) k = Some s) by exact Hk.
  assert (HLOd : l_ACEIL (lay Σd) <= lo) by exact HLO.
  assert (Hdepd : depot_ok (dep Σd) (l_DNB (lay Σd)) (l_SSB (lay Σd)) (l_ACEIL (lay Σd))) by exact Dok.
  assert (HQBd : Forall (fun b0 => exists j0, nth_error (r_st (pr Σd 24)) j0 = Some CkBatch /\ fst b0 = p_abeg (l_SB (lay Σd)) 24 j0) (ql Σd ++ qg Σd))
    by (destruct HW0 as (_ & _ & _ & _ & (_ & _ & QB & _) & _); exact QB).
  assert (Hlived : liveP Σd s (live_remove (s_ubeg s) (live Σ))) by exact (liveP_remove Σ s (proj1 (proj2 (proj2 HW0)))).
  assert (ST4' : stk asegs m4 lo (usp - 2096 - 112)) by (replace (usp - 2096 - 112) with (usp + -2208) by (clear; lia); exact ST4).
  assert (FR4' : qput_frame m4 (usp - 2096 - 112) (Z_to_bv 64 (l_T (lay Σd) + 208)) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 0x83030)
                   (Z_to_bv 64 usp) (Z_to_bv 64 (s_mb s + 6128 + 16)) (Z_to_bv 64 0x82fc0) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2128))
                   (Z_to_bv 64 (usp + -81)) s6)
    by (replace (usp - 2096 - 112) with (usp + -2208) by (clear; lia); exact FR4).

  assert (Hc1' : ASTA RTA Σd PMc (eq (pp_ms Σd s usp gp s7 s8 s9 s10 s11 F fc m4 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)) cf).
  { unfold ASTA. eapply AST_conseq; [exact Hc1 | |].
    - intros ms (E & _). rewrite E. unfold pp_ms. replace (usp - 2096 - 112) with (usp + -2208) by (clear; lia). reflexivity.
    - intros mo (HM & HP'). split; [|exact HP']. apply (artm_maps Σ); [reflexivity | reflexivity | reflexivity | exact HM]. }
  refine (cps_realizes asegs _ _ TT cf _ Hc1' HK). clear Hc1 Hc1' HK TT cf.

  apply (cps_seq asegs _ (ASTA RTA Σd PMc (svc_madP Σd k s usp lo gp s7 s8 s9 s10 s11 F fc m4))).
  { apply (dl_evt Σd PMc _ _ MST). intros ms0 <-.
    exact (pp_run1 Σd k s usp lo gp s7 s8 s9 s10 s11 F fc (live_remove (s_ubeg s) (live Σ)) m4 _ _ _ _ _ _ _ _ _ _
             x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 HGd Hkd HAK CK MI4 ST4' HLOd HLO2 Husp Hdepd HQBd Hlived FR4'). }
  apply (cps_seq asegs _ (ASTA RTA Σd PMc (fun ms => exists ms0, svc_madP Σd k s usp lo gp s7 s8 s9 s10 s11 F fc m4 ms0 /\ ms = nretA ms0 (mad_effP s)))).
  {
    pose proof (ds_mad_geo Σd k s HGd Hkd) as (R1 & R2 & R3 & R5 & R6).
    apply (AN Σd PMc (svc_madP Σd k s usp lo gp s7 s8 s9 s10 s11 F fc m4)
             (fun ms => exists ms0, svc_madP Σd k s usp lo gp s7 s8 s9 s10 s11 F fc m4 ms0 /\ ms = nretA ms0 (mad_effP s))
             (pbeg (shad (s_mb s))) (pend (shad (s_mb s + smsz (s_n s)))) FDO MST (proj1 HGd) R1 R2 R3 R5 R6).
    intros ms Hms. pose proof Hms as (t0' & t1' & t2' & a4' & a5' & a6' & t3' & t4' & t5' & t6' & mA & ws & lst & muw & mudw & -> & _).
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    eexists. split; [exact Hms | reflexivity]. }
  apply (cps_seq asegs _ (ASTA RTA Σd PMc (svc_munP Σd k s usp lo gp s7 s8 s9 s10 s11 F fc (live_remove (s_ubeg s) (live Σ)) m4
                                              (Z_to_bv 64 (l_T (lay Σd) + 208)) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 0x83030)
                                              (Z_to_bv 64 usp) (Z_to_bv 64 (s_mb s + 6128 + 16)) (Z_to_bv 64 0x82fc0) (Z_to_bv 64 1)
                                              (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (usp + -81)) s6))).
  { apply (dl_evt Σd PMc _ _ MST). intros ms (ms0 & Hms0 & ->).
    exact (pp_run2 Σd k s usp lo gp s7 s8 s9 s10 s11 F fc (live_remove (s_ubeg s) (live Σ)) m4 _ _ _ _ _ _ _ _ _ _
             HGd Hkd HAK CK MI4 ST4' HLOd HLO2 Husp Hdepd HQBd Hlived FR4' ms0 Hms0). }
  apply (cps_seq asegs _ (ASTA RTA Σ2 PMc (fun ms => exists ms0,
           svc_munP Σd k s usp lo gp s7 s8 s9 s10 s11 F fc (live_remove (s_ubeg s) (live Σ)) m4
             (Z_to_bv 64 (l_T (lay Σd) + 208)) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 0x83030)
             (Z_to_bv 64 usp) (Z_to_bv 64 (s_mb s + 6128 + 16)) (Z_to_bv 64 0x82fc0) (Z_to_bv 64 1)
             (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (usp + -81)) s6 ms0 /\ ms = nretA ms0 (mun_effP s)))).
  {
    pose proof (dk_map Σd HGd k s Hkd) as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9).
    pose proof HGd as (HL & _ & HSW & _). pose proof HSW as (_ & _ & _ & SW4 & _).
    pose proof (proj1 (Forall_forall _ _) SW4 s (nth_error_In _ _ Hkd)) as (_ & (G1 & G2 & _) & _).
    destruct HW0 as (_ & _ & _ & _ & _ & _ & (B1 & B2 & B3 & B4 & B5) & _).
    intros T cf Hcf HK. pose proof Hcf as (_ & _ & (HAM & _) & _). cbn [ARTM RTA] in HAM.
    apply (MN Σd Σ2 PMc (svc_munP Σd k s usp lo gp s7 s8 s9 s10 s11 F fc (live_remove (s_ubeg s) (live Σ)) m4
               (Z_to_bv 64 (l_T (lay Σd) + 208)) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 0x83030)
               (Z_to_bv 64 usp) (Z_to_bv 64 (s_mb s + 6128 + 16)) (Z_to_bv 64 0x82fc0) (Z_to_bv 64 1)
               (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (usp + -81)) s6) (fun ms => exists ms0,
             svc_munP Σd k s usp lo gp s7 s8 s9 s10 s11 F fc (live_remove (s_ubeg s) (live Σ)) m4
               (Z_to_bv 64 (l_T (lay Σd) + 208)) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 0x83030)
               (Z_to_bv 64 usp) (Z_to_bv 64 (s_mb s + 6128 + 16)) (Z_to_bv 64 0x82fc0) (Z_to_bv 64 1)
               (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (usp + -81)) s6 ms0 /\ ms = nretA ms0 (mun_effP s))
             (s_mb s) (smsz (s_n s)) FDO MST eq_refl eq_refl); [| | | exact HL | change (aw Σd) with (aw Σ); clear - B1 B3; lia | exact B4 | exact M8 | | clear - M1; lia | exact G2 | exact M2 | | exact Hcf | exact HK].
    + change (In (secmap s) (map secmap (rev (sec Σd)))). apply in_map. apply (proj1 (in_rev _ _)). exact (nth_error_In _ _ Hkd).
    + exact (ds_perm Σd k s (cfg_model cf) Hkd HGd HAM).
    + pose proof (secsum_recs Σd k s Hkd) as E. unfold rt_eager. change (secsum Σd) with (fold_right (fun s0 acc => smsz (s_n s0) + acc) 0 (sec Σd)) in E.
      change (fold_right (fun s0 acc => smsz (s_n s0) + acc) 0 (sec Σ2)) with (secsum (recs Σd k)).
      change (sum_cls (fun c => r_muser (pr Σ2 c) + r_mfa (pr Σ2 c)) 31) with (sum_cls (fun c => r_muser (pr Σd c) + r_mfa (pr Σd c)) 31).
      change (sec_nres Σ2) with (sec_nres Σd). rewrite E. clear; lia.
    + unfold smsz, pg_up. apply Z.mod_divide; [clear; lia|]. exists (((needed (s_n s) + rz_size (s_n s) + 4095) / 4096) + 1). clear; lia.
    + intros ms Hms. pose proof Hms as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & t3' & t4' & t5' & t6' & m' & -> & _).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. eexists. split; [exact Hms | reflexivity]. }

  apply (cps_seq asegs _ (ASTA RTA Σ2 PMc (pp_post Σd k lo ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                                            (live_remove (s_ubeg s) (live Σ)) m4))).
  { apply (dl_evt Σ2 PMc _ _ MST). intros ms (ms0 & Hms0 & ->).
    exact (pp_ret Σd k s lo ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (live_remove (s_ubeg s) (live Σ)) m4
             HGd Hkd HW2 HLOd HLO2 Husp Hdepd HQBd Hlived ICF ms0 Hms0). }
  intros T cf Hcf HK. apply HK. clear HK. unfold free_postF.
  unfold ASTA, pp_post in Hcf. apply AST_exI in Hcf as [v Hcf].
  exists Σ2, v. split; [|split; [(cbn [rt_live RTA]; unfold rtA_live; etransitivity; [|apply vis_live_remove];  reflexivity) | split; [reflexivity | split; [reflexivity | reflexivity]]]].
  unfold ASTA. eapply AST_conseq; [exact Hcf | | intros mo H; exact H].
  intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & ART' & MI' & ST' & RP').
  exists m'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F; reflexivity|].
  split; [split; [exact ART' | split; [exact MI' | exact ST']]|].
  intros a Ha. cbn [rt_live rt_frames RTA] in Ha. unfold rtA_live, rtA_frames in Ha. apply aclient_vis in Ha. rewrite (RP' a Ha). exact (RP4 a Ha).
Qed.

End GWIN.
