(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep ZBridge.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import LhPure.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit Fz_G_pkit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_G_kit Fz_ckit Th_mutex Fz_T_lock Fz_env Fz_M_malloc Fz_T_sk Fz_K_hash Fz_K_rep Fz_K_sk Fz_I2_ppis Fz_K_pstw Fz_K_pstw2 Fz_K_pstrs Fz_I2_ppi2a Fz_I2_ppi2b Fz_I2_ppisn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section PPI.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis GO_ppitab : GOBJ PPI_TAB 48.
Hypothesis GO_provider : GOBJ A_PROVIDER 9.
Hypothesis GO_version : GOBJ A_VERSION 8.
Hypothesis GO_fips : GOBJ A_FIPS 5.
Hypothesis GO_output : GOBJ A_OUTPUT 7.
Hypothesis GO_input : GOBJ A_INPUT 6.
Hypothesis GO_structure : GOBJ A_STRUCTURE 10.
Hypothesis GO_yes : GOBJ A_YES 4.
Hypothesis GO_no : GOBJ A_NO 3.
Hypothesis C_PSTR_F : pstr_first_stmt RT GOBJ.
Hypothesis C_PSTR_R : pstr_room_stmt RT GOBJ.
Hypothesis C_PSTR_G : pstr_grow_stmt RT GOBJ.

(* [comment removed for export] *)
Ltac lv_in LV := rewrite LV; cbn [app In]; repeat first [left; reflexivity | right]; assumption.

Theorem ossl_property_parse_init_cps : ossl_property_parse_init_stmt RT.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary ps pk pl1 pb1 pl2 pb2 pq1 pq2
         FDO MST -> TPV ART0 MI0 CALL HSTK CTX UWC CGH Hfr Hlen Hcr POS ENV CELL INps INpk INl1 INb1 INl2 INb2 INq1 INq2 Aps Apk Al1 Ab1 Al2 Ab2 Aq1 Aq2 NL NB NQ
         PSC LKC L1C B1C L2C B2C Q1C Q2C.
  intros T c HA Hk.
  assert (PC : PPI_COST = 8) by (vm_compute; reflexivity).
  assert (HCR : 8 <= rt_credit RT Σ) by (rewrite <- PC; exact Hcr).
  set (PSD := [(ps, 48); (pk, 40); (pl1, 104); (pb1, 128); (pl2, 104); (pb2, 128); (pq1, 56); (pq2, 56)]).
  assert (HPSD : incl PSD (rt_live RT Σ)).
  { intros x Hx. unfold PSD in Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [assumption|]). destruct Hx. }
  destruct (ppi_num RT AF Σ m sp lo ART0 CALL HSTK) as (LOW & _ & HLOS & SPT & SPH & SPA & EU1).
  assert (LV0 : rt_live RT Σ = [] ++ rt_live RT Σ) by reflexivity.
  (* [comment removed for export] *)
  assert (PSC0 : rw_cells asegs m ps (psd_cells pk pl1 pl2 0 0 pq1 pq2)).
  { apply (rw_cells_recast m ps _ _ PSC); [cbn; repeat first [exact I | reflexivity | split] | reflexivity]. }
  assert (REPa0 : plh_rep m pl1 pb1 0 (nb16 [] [] [] [] [])).
  { rewrite <- nb16_empty. apply (plh_rep_of_cells m pl1 pb1 L1C B1C Al1 Ab1). intros E.
    pose proof (live_ne_apart2 RT AF Σ m (pl1, 104) (pb1, 128) ART0 INl1 INb1 ltac:(intros X; discriminate X)) as Y. cbn [fst snd] in Y. clear - E Y. lia. }
  assert (REPb0 : plh_rep m pl2 pb2 0 (nb16 [] [] [] [] [])).
  { rewrite <- nb16_empty. apply (plh_rep_of_cells m pl2 pb2 L2C B2C Al2 Ab2). intros E.
    pose proof (live_ne_apart2 RT AF Σ m (pl2, 104) (pb2, 128) ART0 INl2 INb2 ltac:(intros X; discriminate X)) as Y. cbn [fst snd] in Y. clear - E Y. lia. }
  pose proof (ppi_step RT GOBJ AF AFP Σ PMc m ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo outer canary PSD FDO MST ART0 CALL HSTK CTX UWC CGH Hfr Hlen HCR HPSD) as STEP.
  pose proof (ppi_call RT GOBJ AF AFP Σ PMc m ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo outer canary PSD FDO MST ART0 CALL HSTK CTX UWC CGH Hfr Hlen HCR HPSD) as CALLK.
  pose proof (ppi_seg_cells RT AF Σ m sp lo ART0 CALL HSTK) as SEGC.
  pose proof (ppi_seg_static RT AF Σ m sp lo ART0 CALL HSTK) as SEGS.
  pose proof (ppi_seg_plh RT AF Σ m sp lo ART0 CALL HSTK) as SEGP.
  pose proof (ppi_pre RT GOBJ PMc ra sp tp lo outer canary FDO MST) as PRE.
  assert (LO80 : lo <= bv_unsigned sp - 80) by (clear - HSTK; unfold RT_STACK in *; lia).
  assert (LOa : lo <= bv_unsigned sp - 80) by exact LO80.
  assert (UTX : forall (Σx : rts RT) (mx : mem), ART RT Σx mx -> img_untouched mx) by (intros Σx mx Hx; exact (proj2 (proj2 (proj2 (proj2 (af_client_consts RT AF Σx mx Hx)))))).
  (* [comment removed for export] *)
  apply (ppi_enter RT GOBJ AF AFP Σ PMc m ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo outer canary PSD FDO MST ART0 CALL HSTK CTX UWC CGH Hfr Hlen HCR HPSD
           t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc lb T c GO_ppitab MI0 ENV HA).
  clear HA. intros m1 j c1 Hc1 STD1 MU1.
  pose proof (SEGS m m1 _ _ _ _ MU1 LOa CELL ltac:(unfold CTX_PSD, SEGTOP_A; cbn; clear; lia)) as CELL1.
  pose proof (SEGC Σ m m1 _ _ ps 48 _ _ ART0 eq_refl INps MU1 LOa PSC0 ltac:(unfold psd_cells; cbn; clear; lia)) as PSC1.
  pose proof (SEGC Σ m m1 _ _ pk 40 _ _ ART0 eq_refl INpk MU1 LOa LKC ltac:(unfold mutex_cells; cbn; clear; lia)) as LKC1.
  pose proof (SEGC Σ m m1 _ _ pq1 56 _ _ ART0 eq_refl INq1 MU1 LOa Q1C ltac:(cbn; clear; lia)) as Q1C1.
  pose proof (SEGC Σ m m1 _ _ pq2 56 _ _ ART0 eq_refl INq2 MU1 LOa Q2C ltac:(cbn; clear; lia)) as Q2C1.
  assert (INCa1 : incl (plh_L pl1 pb1 (nb16 [] [] [] [] [])) (rt_live RT Σ)) by (intros x Hx; cbn in Hx; repeat (destruct Hx as [<-|Hx]; [assumption|]); destruct Hx).
  assert (INCb1 : incl (plh_L pl2 pb2 (nb16 [] [] [] [] [])) (rt_live RT Σ)) by (intros x Hx; cbn in Hx; repeat (destruct Hx as [<-|Hx]; [assumption|]); destruct Hx).
  pose proof (SEGP Σ m m1 _ _ _ _ _ _ ART0 eq_refl INCa1 MU1 LOa REPa0) as REPa1.
  pose proof (SEGP Σ m m1 _ _ _ _ _ _ ART0 eq_refl INCb1 MU1 LOa REPb0) as REPb1.
  clear PSC PSC0 REPa0 REPb0 L1C B1C L2C B2C CELL LKC.
  (* [comment removed for export] *)
  pose proof STD1 as (ART1 & _).
  assert (HLW1 : incl (pstr_L true ps pk pl1 pl2 pq1 pq2 pb1 (nb16 [] [] [] [] [])) (rt_live RT Σ)).
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [lv_in LV0|]). destruct Hx. }
  eapply (STEP Σ m1 [] [] 0 lb j SITE_ppi_name 1 A_PROVIDER 0 PPI_TAB PPI_TAB_SH 1 (rt_live RT Σ) (pstr_L true ps pk pl1 pl2 pq1 pq2 pb1 (nb16 [] [] [] [] []))
            (ppi_Qfirst RT canary true s_provider ps pk pl1 pl2 0 0 pq1 pq2 pb1 0 (nb16 [] [] [] [] []) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 2146284) (Z_to_bv 64 2146368) (Z_to_bv 64 2146328))
            SITE_ppi_name 1 A_VERSION (-8) (PPI_TAB + 8) (PPI_TAB_SH + 1) STD1).
  { cbn [length]. clear. lia. }
  { clear. lia. }
  { unfold PPI_SITES. wp_in_lit. }
  { unfold PPI_CALLS. wp_in_lit. }
  { unfold SITE_ppi_name. clear. lia. }
  { reflexivity. }
  { exact LV0. }
  { exact (fun e He => He). }
  { exact HLW1. }
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [first [left; unfold PSD; solve [wp_in_lit] | right; solve [wp_in_lit]]|]). destruct Hx. }
  { intros u0 u1 u2 u4 u5 u6 u7 v3 v4 v5 v6 F1 fc1 GP.
    eapply cps_conseq; [eapply (C_PSTR_F Σ PMc (Z_to_bv 64 SITE_ppi_name) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0 u1 u2 sp (Z_to_bv 64 PPI_CTX) (Z_to_bv 64 PPI_CTX) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 A_PROVIDER) u4 u5 u6 u7 (Z_to_bv 64 0) (Z_to_bv 64 PPI_TAB) (Z_to_bv 64 PPI_TAB_SH) (Z_to_bv 64 (-48)) s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F1 fc1 m1 lo (bv_unsigned ra :: outer) lb canary true A_PROVIDER A_PROVIDER (Z.of_nat (length s_provider) + 1) s_provider (repeat (Z_to_bv 8 0) 7) ps pk pl1 pl2 0 0 pq1 pq2 pb1 0 (nb16 [] [] [] [] []))
                       | intros c0 H0; exact H0
                       | intros c0 H0; exact (ppi_of_first RT PMc sp gp tp s6 s7 s8 s9 s10 s11 lo canary Σ m1 SITE_ppi_name 0 PPI_TAB PPI_TAB_SH true s_provider ps pk pl1 pl2 0 0 pq1 pq2 pb1 0 (nb16 [] [] [] [] []) _ _ _ _ _ c0 H0)].
    - apply (PRE Σ m1 SITE_ppi_name lb true A_PROVIDER s_provider 7%nat ps pk pl1 pl2 0 0 pq1 pq2 pb1 0 (nb16 [] [] [] [] []) TPV GP lit_provider GO_provider CELL1
               ltac:(lv_in LV0) Aps PSC1 ltac:(clear; lia) ltac:(clear; lia) ltac:(lv_in LV0) Apk LKC1 REPa1 INCa1 ltac:(clear; lia)).
      + rewrite hash_provider, bk_provider. cbn [nth nb16]. repeat (constructor; [vm_compute; intros HH; discriminate HH|]). constructor.
      + cbn [q_of]. lv_in LV0.
      + cbn [q_of]. clear - Aq1. Z.div_mod_to_equations. lia.
    - exact Q1C1.
  }
  { intros u0 u1 u2 u1' u2' u3' u4 u5 u6 u7 v3 v4 v5 v6 F1 fc1 Σx mx ARTx MIx STx.
    exact (ppi_w1 sp gp tp u0 u1 u2 u1' u2' u3' u4 u5 u6 u7 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F1 fc1 mx lo STx LO80 HLOS SPH (UTX Σx mx ARTx) (ppi_tab_sh RT GOBJ AFP Σx mx 1 ARTx GO_ppitab ltac:(clear; lia)) MIx). }
  { exact Hc1. }
  clear Hc1. intros Σ1 NEW m1r m2 ? ? ? ? ? ? ? ? ? ? ? F2 fc2 c2 Hc2 STD2 ART1r PRES1 HQ LV1 SP01 MU2.
  destruct HQ as (r1 & D1 & n1 & junk1 & -> & (ENV1r & CELL1r & PSC1r & LKC1r & REPa1r) & Q1C1r & D1C1r & BKr1 & BKd1 & BKn1).
  change (Z.of_nat (length s_provider) + 16) with 24 in *. cbn [app] in STD2, LV1. change (0 + 1) with 1 in STD2.
  assert (EB : pstr_bks (nb16 [] [] [] [] []) s_provider n1 = (nb16 [] [(n1, H_PROVIDER)] [] [] [])) by (unfold pstr_bks; rewrite hash_provider, bk_provider; reflexivity).
  rewrite EB in REPa1r. clear EB. unfold psd_bump in PSC1r. cbn [t_of q_of] in REPa1r, Q1C1r.
  change (0 + 1) with 1 in PSC1r.
  change (0 + 1) with 1 in REPa1r.
  assert (ND1 : D1 <> ps).
  { pose proof (live_ne_apart2 RT AF Σ1 m1r (D1, 32) (ps, 48) ART1r ltac:(lv_in LV1) ltac:(lv_in LV1) ltac:(intros X; discriminate X)) as Y. cbn [fst snd] in Y. clear - Y. lia. }
  pose proof (SEGS m1r m2 _ _ _ _ MU2 LOa CELL1r ltac:(unfold CTX_PSD, SEGTOP_A; cbn; clear; lia)) as CELL2.
  pose proof (SEGC Σ1 m1r m2 _ _ ps 48 _ _ ART1r SP01 ltac:(lv_in LV1) MU2 LOa PSC1r ltac:(unfold psd_cells; cbn; clear; lia)) as PSC2.
  pose proof (SEGC Σ1 m1r m2 _ _ pk 40 _ _ ART1r SP01 ltac:(lv_in LV1) MU2 LOa LKC1r ltac:(unfold mutex_cells; cbn; clear; lia)) as LKC2.
  pose proof (SEGC Σ1 m1r m2 _ _ pq1 56 _ _ ART1r SP01 ltac:(lv_in LV1) MU2 LOa Q1C1r ltac:(unfold sk_cells; cbn; clear; lia)) as Q1C2.
  pose proof (SEGC Σ1 m1r m2 _ _ D1 32 _ _ ART1r SP01 ltac:(lv_in LV1) MU2 LOa D1C1r ltac:(cbn; clear; lia)) as D1C2.
  assert (INCa2 : incl (plh_L pl1 pb1 (nb16 [] [(n1, H_PROVIDER)] [] [] [])) (rt_live RT Σ1)).
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [lv_in LV1|]). destruct Hx. }
  pose proof (SEGP Σ1 m1r m2 _ _ _ _ _ _ ART1r SP01 INCa2 MU2 LOa REPa1r) as REPa2.
  assert (INCbB : incl (plh_L pl2 pb2 (nb16 [] [] [] [] [])) (rt_live RT Σ)).
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [lv_in LV0|]). destruct Hx. }
  assert (NOTb : forall x, In x (plh_L pl2 pb2 (nb16 [] [] [] [] [])) -> ~ In x (pstr_L true ps pk pl1 pl2 pq1 pq2 pb1 (nb16 [] [] [] [] []))).
  { intros x Hx. cbn [plh_L nb16 concat app map In fst] in Hx. repeat (destruct Hx as [<-|Hx]; [exact ltac:(cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst]; intros HH; repeat (destruct HH as [HH|HH]; [apply pair_equal_spec in HH; destruct HH as [HHa HHn]; first [discriminate HHn | (revert HHn; clear; lia) | congruence]|]); exact HH)|]). destruct Hx. }
  pose proof (ppi_keep_plh RT GOBJ AF AFP Σ m1 m1r (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp + -64) (pstr_L true ps pk pl1 pl2 pq1 pq2 pb1 (nb16 [] [] [] [] [])) pl2 pb2 0 (nb16 [] [] [] [] []) ART1 PRES1 (fun e He => He) HLW1 REPb1 INCbB NOTb) as REPb1r.
  clear INCbB NOTb.
  assert (INCb2 : incl (plh_L pl2 pb2 (nb16 [] [] [] [] [])) (rt_live RT Σ1)).
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [lv_in LV1|]). destruct Hx. }
  pose proof (SEGP Σ1 m1r m2 _ _ _ _ _ _ ART1r SP01 INCb2 MU2 LOa REPb1r) as REPb2.
  pose proof (ppi_keep_cells RT GOBJ AF AFP Σ m1 m1r (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp + -64) (pstr_L true ps pk pl1 pl2 pq1 pq2 pb1 (nb16 [] [] [] [] [])) pq2 56 pq2 _ ART1 PRES1 (fun e He => He) HLW1 ltac:(lv_in LV0) ltac:(clear; lia) ltac:(cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst]; intros HH; repeat (destruct HH as [HH|HH]; [apply pair_equal_spec in HH; destruct HH as [HHa HHn]; first [discriminate HHn | (revert HHn; clear; lia) | congruence]|]); exact HH) Q2C1 ltac:(clear; lia) ltac:(unfold sk_cells; cbn; clear; lia)) as Q2C1r.
  pose proof (SEGC Σ1 m1r m2 _ _ pq2 56 _ _ ART1r SP01 ltac:(lv_in LV1) MU2 LOa Q2C1r ltac:(unfold sk_cells; cbn; clear; lia)) as Q2C2.
  clear CELL1r PSC1r LKC1r REPa1r REPb1r Q1C1r Q2C1r ENV1r PRES1 HLW1 CELL1 PSC1 LKC1 REPa1 REPb1 Q1C1 Q2C1 INCa1 INCb1 STD1.

  (* [comment removed for export] *)
  pose proof STD2 as (ART2 & _).
  assert (HLW2 : incl ((D1, 8 * 4) :: pstr_L true ps pk pl1 pl2 pq1 pq2 pb1 (nb16 [] [(n1, H_PROVIDER)] [] [] [])) (rt_live RT Σ1)).
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [lv_in LV1|]). destruct Hx. }
  eapply (STEP Σ1 m2 [(n1, 24); (D1, 32); (r1, 24)] [(n1, 24); (D1, 32); (r1, 24)] 1 (Z_to_bv 8 1) j SITE_ppi_name 1 A_VERSION (-8) (PPI_TAB + 8) (PPI_TAB_SH + 1) 2 (rt_live RT Σ1) ((D1, 8 * 4) :: pstr_L true ps pk pl1 pl2 pq1 pq2 pb1 (nb16 [] [(n1, H_PROVIDER)] [] [] []))
            (ppi_Qroom RT canary true s_version ps pk pl1 pl2 1 0 pq1 pq2 pb1 1 (nb16 [] [(n1, H_PROVIDER)] [] [] []) D1 1 4 (Z_to_bv 64 0) (Z_to_bv 64 2146284) (Z_to_bv 64 2146368) (Z_to_bv 64 2146328))
            SITE_ppi_name 1 A_FIPS (-16) (PPI_TAB + 16) (PPI_TAB_SH + 2) STD2).
  { cbn [length]. clear. lia. }
  { clear. lia. }
  { unfold PPI_SITES. wp_in_lit. }
  { unfold PPI_CALLS. wp_in_lit. }
  { unfold SITE_ppi_name. clear. lia. }
  { reflexivity. }
  { exact LV1. }
  { exact (fun e He => He). }
  { exact HLW2. }
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [first [left; unfold PSD; solve [wp_in_lit] | right; solve [wp_in_lit]]|]). destruct Hx. }
  { intros u0 u1 u2 u4 u5 u6 u7 v3 v4 v5 v6 F1 fc1 GP.
    eapply cps_conseq; [eapply (C_PSTR_R Σ1 PMc (Z_to_bv 64 SITE_ppi_name) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0 u1 u2 sp (Z_to_bv 64 PPI_CTX) (Z_to_bv 64 PPI_CTX) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 A_VERSION) u4 u5 u6 u7 (Z_to_bv 64 (-8)) (Z_to_bv 64 (PPI_TAB + 8)) (Z_to_bv 64 (PPI_TAB_SH + 1)) (Z_to_bv 64 (-48)) s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F1 fc1 m2 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary true A_VERSION A_VERSION (Z.of_nat (length s_version) + 1) s_version (repeat (Z_to_bv 8 0) 0) ps pk pl1 pl2 1 0 pq1 pq2 pb1 1 (nb16 [] [(n1, H_PROVIDER)] [] [] []) D1 1 4 1)
                       | intros c0 H0; exact H0
                       | intros c0 H0; exact (ppi_of_room RT PMc sp gp tp s6 s7 s8 s9 s10 s11 lo canary Σ1 m2 SITE_ppi_name (-8) (PPI_TAB + 8) (PPI_TAB_SH + 1) true s_version ps pk pl1 pl2 1 0 pq1 pq2 pb1 1 (nb16 [] [(n1, H_PROVIDER)] [] [] []) D1 1 4 _ _ _ _ c0 H0)].
    - apply (PRE Σ1 m2 SITE_ppi_name (Z_to_bv 8 1) true A_VERSION s_version 0%nat ps pk pl1 pl2 1 0 pq1 pq2 pb1 1 (nb16 [] [(n1, H_PROVIDER)] [] [] []) TPV GP lit_version GO_version CELL2
               ltac:(lv_in LV1) Aps PSC2 ltac:(clear; lia) ltac:(clear; lia) ltac:(lv_in LV1) Apk LKC2 REPa2 INCa2 ltac:(clear; lia)).
      + rewrite hash_version, bk_version. cbn [nth nb16]. repeat (constructor; [vm_compute; intros HH; discriminate HH|]). constructor.
      + cbn [q_of]. lv_in LV1.
      + cbn [q_of]. clear - Aq1. Z.div_mod_to_equations. lia.
    - exact Q1C2.
    - clear. lia.
    - clear. lia.
    - clear. lia.
    - clear. lia.
    - lv_in LV1.
    - destruct BKd1 as (_ & X & _). clear - X. Z.div_mod_to_equations. lia.
    - exact ND1.
    - exact D1C2.
  }
  { intros u0 u1 u2 u1' u2' u3' u4 u5 u6 u7 v3 v4 v5 v6 F1 fc1 Σx mx ARTx MIx STx.
    exact (ppi_w2 sp gp tp u0 u1 u2 u1' u2' u3' u4 u5 u6 u7 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F1 fc1 mx lo STx LO80 HLOS SPH (UTX Σx mx ARTx) (ppi_tab_sh RT GOBJ AFP Σx mx 2 ARTx GO_ppitab ltac:(clear; lia)) MIx). }
  { exact Hc2. }
  clear Hc2. intros Σ2 NEW m2r m3 ? ? ? ? ? ? ? ? ? ? ? F3 fc3 c3 Hc3 STD3 ART2r PRES2 HQ LV2 SP02 MU3.
  destruct HQ as (r2 & n2 & junk2 & -> & (ENV2r & CELL2r & PSC2r & LKC2r & REPa2r) & Q1C2r & D1C2r & BKr2 & BKn2).
  change (Z.of_nat (length s_version) + 16) with 23 in *. cbn [app] in STD3, LV2. change (1 + 1) with 2 in STD3.
  rewrite LV1 in LV2.
  assert (EB : pstr_bks (nb16 [] [(n1, H_PROVIDER)] [] [] []) s_version n2 = (nb16 [] [(n1, H_PROVIDER); (n2, H_VERSION)] [] [] [])) by (unfold pstr_bks; rewrite hash_version, bk_version; reflexivity).
  rewrite EB in REPa2r. clear EB. unfold psd_bump in PSC2r. cbn [t_of q_of] in REPa2r, Q1C2r.
  change (1 + 1) with 2 in PSC2r.
  change (1 + 1) with 2 in REPa2r.
  change (1 + 1) with 2 in Q1C2r.
  change (Z.to_nat (8 * 4)) with 32%nat in D1C2r.
  pose proof (SEGS m2r m3 _ _ _ _ MU3 LOa CELL2r ltac:(unfold CTX_PSD, SEGTOP_A; cbn; clear; lia)) as CELL3.
  pose proof (SEGC Σ2 m2r m3 _ _ ps 48 _ _ ART2r SP02 ltac:(lv_in LV2) MU3 LOa PSC2r ltac:(unfold psd_cells; cbn; clear; lia)) as PSC3.
  pose proof (SEGC Σ2 m2r m3 _ _ pk 40 _ _ ART2r SP02 ltac:(lv_in LV2) MU3 LOa LKC2r ltac:(unfold mutex_cells; cbn; clear; lia)) as LKC3.
  pose proof (SEGC Σ2 m2r m3 _ _ pq1 56 _ _ ART2r SP02 ltac:(lv_in LV2) MU3 LOa Q1C2r ltac:(unfold sk_cells; cbn; clear; lia)) as Q1C3.
  pose proof (SEGC Σ2 m2r m3 _ _ D1 32 _ _ ART2r SP02 ltac:(lv_in LV2) MU3 LOa D1C2r ltac:(cbn; clear; lia)) as D1C3.
  assert (INCa3 : incl (plh_L pl1 pb1 (nb16 [] [(n1, H_PROVIDER); (n2, H_VERSION)] [] [] [])) (rt_live RT Σ2)).
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [lv_in LV2|]). destruct Hx. }
  pose proof (SEGP Σ2 m2r m3 _ _ _ _ _ _ ART2r SP02 INCa3 MU3 LOa REPa2r) as REPa3.
  assert (INCbB : incl (plh_L pl2 pb2 (nb16 [] [] [] [] [])) (rt_live RT Σ1)).
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [lv_in LV1|]). destruct Hx. }
  assert (NOTb : forall x, In x (plh_L pl2 pb2 (nb16 [] [] [] [] [])) -> ~ In x ((D1, 8 * 4) :: pstr_L true ps pk pl1 pl2 pq1 pq2 pb1 (nb16 [] [(n1, H_PROVIDER)] [] [] []))).
  { intros x Hx. cbn [plh_L nb16 concat app map In fst] in Hx. repeat (destruct Hx as [<-|Hx]; [exact ltac:(cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst]; intros HH; repeat (destruct HH as [HH|HH]; [apply pair_equal_spec in HH; destruct HH as [HHa HHn]; first [discriminate HHn | (revert HHn; clear; lia) | congruence]|]); exact HH)|]). destruct Hx. }
  pose proof (ppi_keep_plh RT GOBJ AF AFP Σ1 m2 m2r (rt_live RT Σ1) (rt_frames RT Σ1) (bv_unsigned sp + -64) ((D1, 8 * 4) :: pstr_L true ps pk pl1 pl2 pq1 pq2 pb1 (nb16 [] [(n1, H_PROVIDER)] [] [] [])) pl2 pb2 0 (nb16 [] [] [] [] []) ART2 PRES2 (fun e He => He) HLW2 REPb2 INCbB NOTb) as REPb2r.
  clear INCbB NOTb.
  assert (INCb3 : incl (plh_L pl2 pb2 (nb16 [] [] [] [] [])) (rt_live RT Σ2)).
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [lv_in LV2|]). destruct Hx. }
  pose proof (SEGP Σ2 m2r m3 _ _ _ _ _ _ ART2r SP02 INCb3 MU3 LOa REPb2r) as REPb3.
  pose proof (ppi_keep_cells RT GOBJ AF AFP Σ1 m2 m2r (rt_live RT Σ1) (rt_frames RT Σ1) (bv_unsigned sp + -64) ((D1, 8 * 4) :: pstr_L true ps pk pl1 pl2 pq1 pq2 pb1 (nb16 [] [(n1, H_PROVIDER)] [] [] [])) pq2 56 pq2 _ ART2 PRES2 (fun e He => He) HLW2 ltac:(lv_in LV1) ltac:(clear; lia) ltac:(cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst]; intros HH; repeat (destruct HH as [HH|HH]; [apply pair_equal_spec in HH; destruct HH as [HHa HHn]; first [discriminate HHn | (revert HHn; clear; lia) | congruence]|]); exact HH) Q2C2 ltac:(clear; lia) ltac:(unfold sk_cells; cbn; clear; lia)) as Q2C2r.
  pose proof (SEGC Σ2 m2r m3 _ _ pq2 56 _ _ ART2r SP02 ltac:(lv_in LV2) MU3 LOa Q2C2r ltac:(unfold sk_cells; cbn; clear; lia)) as Q2C3.
  clear CELL2r PSC2r LKC2r REPa2r REPb2r Q1C2r Q2C2r ENV2r PRES2 HLW2 CELL2 PSC2 LKC2 REPa2 REPb2 Q1C2 Q2C2 INCa2 INCb2 STD2.

  (* [comment removed for export] *)
  pose proof STD3 as (ART3 & _).
  assert (HLW3 : incl ((D1, 8 * 4) :: pstr_L true ps pk pl1 pl2 pq1 pq2 pb1 (nb16 [] [(n1, H_PROVIDER); (n2, H_VERSION)] [] [] [])) (rt_live RT Σ2)).
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [lv_in LV2|]). destruct Hx. }
  eapply (STEP Σ2 m3 [(n2, 24); (r2, 23); (n1, 24); (D1, 32); (r1, 24)] [(n2, 24); (r2, 23); (n1, 24); (D1, 32); (r1, 24)] 2 (Z_to_bv 8 1) j SITE_ppi_name 1 A_FIPS (-16) (PPI_TAB + 16) (PPI_TAB_SH + 2) 3 (rt_live RT Σ2) ((D1, 8 * 4) :: pstr_L true ps pk pl1 pl2 pq1 pq2 pb1 (nb16 [] [(n1, H_PROVIDER); (n2, H_VERSION)] [] [] []))
            (ppi_Qroom RT canary true s_fips ps pk pl1 pl2 2 0 pq1 pq2 pb1 2 (nb16 [] [(n1, H_PROVIDER); (n2, H_VERSION)] [] [] []) D1 2 4 (Z_to_bv 64 0) (Z_to_bv 64 2146284) (Z_to_bv 64 2146368) (Z_to_bv 64 2146328))
            SITE_ppi_name 1 A_OUTPUT (-24) (PPI_TAB + 24) (PPI_TAB_SH + 3) STD3).
  { cbn [length]. clear. lia. }
  { clear. lia. }
  { unfold PPI_SITES. wp_in_lit. }
  { unfold PPI_CALLS. wp_in_lit. }
  { unfold SITE_ppi_name. clear. lia. }
  { reflexivity. }
  { exact LV2. }
  { exact (fun e He => He). }
  { exact HLW3. }
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [first [left; unfold PSD; solve [wp_in_lit] | right; solve [wp_in_lit]]|]). destruct Hx. }
  { intros u0 u1 u2 u4 u5 u6 u7 v3 v4 v5 v6 F1 fc1 GP.
    eapply cps_conseq; [eapply (C_PSTR_R Σ2 PMc (Z_to_bv 64 SITE_ppi_name) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0 u1 u2 sp (Z_to_bv 64 PPI_CTX) (Z_to_bv 64 PPI_CTX) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 A_FIPS) u4 u5 u6 u7 (Z_to_bv 64 (-16)) (Z_to_bv 64 (PPI_TAB + 16)) (Z_to_bv 64 (PPI_TAB_SH + 2)) (Z_to_bv 64 (-48)) s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F1 fc1 m3 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary true A_FIPS A_FIPS (Z.of_nat (length s_fips) + 1) s_fips (repeat (Z_to_bv 8 0) 3) ps pk pl1 pl2 2 0 pq1 pq2 pb1 2 (nb16 [] [(n1, H_PROVIDER); (n2, H_VERSION)] [] [] []) D1 2 4 0)
                       | intros c0 H0; exact H0
                       | intros c0 H0; exact (ppi_of_room RT PMc sp gp tp s6 s7 s8 s9 s10 s11 lo canary Σ2 m3 SITE_ppi_name (-16) (PPI_TAB + 16) (PPI_TAB_SH + 2) true s_fips ps pk pl1 pl2 2 0 pq1 pq2 pb1 2 (nb16 [] [(n1, H_PROVIDER); (n2, H_VERSION)] [] [] []) D1 2 4 _ _ _ _ c0 H0)].
    - apply (PRE Σ2 m3 SITE_ppi_name (Z_to_bv 8 1) true A_FIPS s_fips 3%nat ps pk pl1 pl2 2 0 pq1 pq2 pb1 2 (nb16 [] [(n1, H_PROVIDER); (n2, H_VERSION)] [] [] []) TPV GP lit_fips GO_fips CELL3
               ltac:(lv_in LV2) Aps PSC3 ltac:(clear; lia) ltac:(clear; lia) ltac:(lv_in LV2) Apk LKC3 REPa3 INCa3 ltac:(clear; lia)).
      + rewrite hash_fips, bk_fips. cbn [nth nb16]. repeat (constructor; [vm_compute; intros HH; discriminate HH|]). constructor.
      + cbn [q_of]. lv_in LV2.
      + cbn [q_of]. clear - Aq1. Z.div_mod_to_equations. lia.
    - exact Q1C3.
    - clear. lia.
    - clear. lia.
    - clear. lia.
    - clear. lia.
    - lv_in LV2.
    - destruct BKd1 as (_ & X & _). clear - X. Z.div_mod_to_equations. lia.
    - exact ND1.
    - exact D1C3.
  }
  { intros u0 u1 u2 u1' u2' u3' u4 u5 u6 u7 v3 v4 v5 v6 F1 fc1 Σx mx ARTx MIx STx.
    exact (ppi_w3 sp gp tp u0 u1 u2 u1' u2' u3' u4 u5 u6 u7 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F1 fc1 mx lo STx LO80 HLOS SPH (UTX Σx mx ARTx) (ppi_tab_sh RT GOBJ AFP Σx mx 3 ARTx GO_ppitab ltac:(clear; lia)) MIx). }
  { exact Hc3. }
  clear Hc3. intros Σ3 NEW m3r m4 ? ? ? ? ? ? ? ? ? ? ? F4 fc4 c4 Hc4 STD4 ART3r PRES3 HQ LV3 SP03 MU4.
  destruct HQ as (r3 & n3 & junk3 & -> & (ENV3r & CELL3r & PSC3r & LKC3r & REPa3r) & Q1C3r & D1C3r & BKr3 & BKn3).
  change (Z.of_nat (length s_fips) + 16) with 20 in *. cbn [app] in STD4, LV3. change (2 + 1) with 3 in STD4.
  rewrite LV2 in LV3.
  assert (EB : pstr_bks (nb16 [] [(n1, H_PROVIDER); (n2, H_VERSION)] [] [] []) s_fips n3 = (nb16 [] [(n1, H_PROVIDER); (n2, H_VERSION)] [] [] [(n3, H_FIPS)])) by (unfold pstr_bks; rewrite hash_fips, bk_fips; reflexivity).
  rewrite EB in REPa3r. clear EB. unfold psd_bump in PSC3r. cbn [t_of q_of] in REPa3r, Q1C3r.
  change (2 + 1) with 3 in PSC3r.
  change (2 + 1) with 3 in REPa3r.
  change (2 + 1) with 3 in Q1C3r.
  change (Z.to_nat (8 * 4)) with 32%nat in D1C3r.
  pose proof (SEGS m3r m4 _ _ _ _ MU4 LOa CELL3r ltac:(unfold CTX_PSD, SEGTOP_A; cbn; clear; lia)) as CELL4.
  pose proof (SEGC Σ3 m3r m4 _ _ ps 48 _ _ ART3r SP03 ltac:(lv_in LV3) MU4 LOa PSC3r ltac:(unfold psd_cells; cbn; clear; lia)) as PSC4.
  pose proof (SEGC Σ3 m3r m4 _ _ pk 40 _ _ ART3r SP03 ltac:(lv_in LV3) MU4 LOa LKC3r ltac:(unfold mutex_cells; cbn; clear; lia)) as LKC4.
  pose proof (SEGC Σ3 m3r m4 _ _ pq1 56 _ _ ART3r SP03 ltac:(lv_in LV3) MU4 LOa Q1C3r ltac:(unfold sk_cells; cbn; clear; lia)) as Q1C4.
  pose proof (SEGC Σ3 m3r m4 _ _ D1 32 _ _ ART3r SP03 ltac:(lv_in LV3) MU4 LOa D1C3r ltac:(cbn; clear; lia)) as D1C4.
  assert (INCa4 : incl (plh_L pl1 pb1 (nb16 [] [(n1, H_PROVIDER); (n2, H_VERSION)] [] [] [(n3, H_FIPS)])) (rt_live RT Σ3)).
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [lv_in LV3|]). destruct Hx. }
  pose proof (SEGP Σ3 m3r m4 _ _ _ _ _ _ ART3r SP03 INCa4 MU4 LOa REPa3r) as REPa4.
  assert (INCbB : incl (plh_L pl2 pb2 (nb16 [] [] [] [] [])) (rt_live RT Σ2)).
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [lv_in LV2|]). destruct Hx. }
  assert (NOTb : forall x, In x (plh_L pl2 pb2 (nb16 [] [] [] [] [])) -> ~ In x ((D1, 8 * 4) :: pstr_L true ps pk pl1 pl2 pq1 pq2 pb1 (nb16 [] [(n1, H_PROVIDER); (n2, H_VERSION)] [] [] []))).
  { intros x Hx. cbn [plh_L nb16 concat app map In fst] in Hx. repeat (destruct Hx as [<-|Hx]; [exact ltac:(cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst]; intros HH; repeat (destruct HH as [HH|HH]; [apply pair_equal_spec in HH; destruct HH as [HHa HHn]; first [discriminate HHn | (revert HHn; clear; lia) | congruence]|]); exact HH)|]). destruct Hx. }
  pose proof (ppi_keep_plh RT GOBJ AF AFP Σ2 m3 m3r (rt_live RT Σ2) (rt_frames RT Σ2) (bv_unsigned sp + -64) ((D1, 8 * 4) :: pstr_L true ps pk pl1 pl2 pq1 pq2 pb1 (nb16 [] [(n1, H_PROVIDER); (n2, H_VERSION)] [] [] [])) pl2 pb2 0 (nb16 [] [] [] [] []) ART3 PRES3 (fun e He => He) HLW3 REPb3 INCbB NOTb) as REPb3r.
  clear INCbB NOTb.
  assert (INCb4 : incl (plh_L pl2 pb2 (nb16 [] [] [] [] [])) (rt_live RT Σ3)).
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [lv_in LV3|]). destruct Hx. }
  pose proof (SEGP Σ3 m3r m4 _ _ _ _ _ _ ART3r SP03 INCb4 MU4 LOa REPb3r) as REPb4.
  pose proof (ppi_keep_cells RT GOBJ AF AFP Σ2 m3 m3r (rt_live RT Σ2) (rt_frames RT Σ2) (bv_unsigned sp + -64) ((D1, 8 * 4) :: pstr_L true ps pk pl1 pl2 pq1 pq2 pb1 (nb16 [] [(n1, H_PROVIDER); (n2, H_VERSION)] [] [] [])) pq2 56 pq2 _ ART3 PRES3 (fun e He => He) HLW3 ltac:(lv_in LV2) ltac:(clear; lia) ltac:(cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst]; intros HH; repeat (destruct HH as [HH|HH]; [apply pair_equal_spec in HH; destruct HH as [HHa HHn]; first [discriminate HHn | (revert HHn; clear; lia) | congruence]|]); exact HH) Q2C3 ltac:(clear; lia) ltac:(unfold sk_cells; cbn; clear; lia)) as Q2C3r.
  pose proof (SEGC Σ3 m3r m4 _ _ pq2 56 _ _ ART3r SP03 ltac:(lv_in LV3) MU4 LOa Q2C3r ltac:(unfold sk_cells; cbn; clear; lia)) as Q2C4.
  clear CELL3r PSC3r LKC3r REPa3r REPb3r Q1C3r Q2C3r ENV3r PRES3 HLW3 CELL3 PSC3 LKC3 REPa3 REPb3 Q1C3 Q2C3 INCa3 INCb3 STD3.

  (* [comment removed for export] *)
  pose proof STD4 as (ART4 & _).
  assert (HLW4 : incl ((D1, 8 * 4) :: pstr_L true ps pk pl1 pl2 pq1 pq2 pb1 (nb16 [] [(n1, H_PROVIDER); (n2, H_VERSION)] [] [] [(n3, H_FIPS)])) (rt_live RT Σ3)).
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [lv_in LV3|]). destruct Hx. }
  eapply (STEP Σ3 m4 [(n3, 24); (r3, 20); (n2, 24); (r2, 23); (n1, 24); (D1, 32); (r1, 24)] [(n3, 24); (r3, 20); (n2, 24); (r2, 23); (n1, 24); (D1, 32); (r1, 24)] 3 (Z_to_bv 8 1) j SITE_ppi_name 1 A_OUTPUT (-24) (PPI_TAB + 24) (PPI_TAB_SH + 3) 4 (rt_live RT Σ3) ((D1, 8 * 4) :: pstr_L true ps pk pl1 pl2 pq1 pq2 pb1 (nb16 [] [(n1, H_PROVIDER); (n2, H_VERSION)] [] [] [(n3, H_FIPS)]))
            (ppi_Qroom RT canary true s_output ps pk pl1 pl2 3 0 pq1 pq2 pb1 3 (nb16 [] [(n1, H_PROVIDER); (n2, H_VERSION)] [] [] [(n3, H_FIPS)]) D1 3 4 (Z_to_bv 64 0) (Z_to_bv 64 2146284) (Z_to_bv 64 2146368) (Z_to_bv 64 2146328))
            SITE_ppi_name 1 A_INPUT (-32) (PPI_TAB + 32) (PPI_TAB_SH + 4) STD4).
  { cbn [length]. clear. lia. }
  { clear. lia. }
  { unfold PPI_SITES. wp_in_lit. }
  { unfold PPI_CALLS. wp_in_lit. }
  { unfold SITE_ppi_name. clear. lia. }
  { reflexivity. }
  { exact LV3. }
  { exact (fun e He => He). }
  { exact HLW4. }
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [first [left; unfold PSD; solve [wp_in_lit] | right; solve [wp_in_lit]]|]). destruct Hx. }
  { intros u0 u1 u2 u4 u5 u6 u7 v3 v4 v5 v6 F1 fc1 GP.
    eapply cps_conseq; [eapply (C_PSTR_R Σ3 PMc (Z_to_bv 64 SITE_ppi_name) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0 u1 u2 sp (Z_to_bv 64 PPI_CTX) (Z_to_bv 64 PPI_CTX) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 A_OUTPUT) u4 u5 u6 u7 (Z_to_bv 64 (-24)) (Z_to_bv 64 (PPI_TAB + 24)) (Z_to_bv 64 (PPI_TAB_SH + 3)) (Z_to_bv 64 (-48)) s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F1 fc1 m4 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary true A_OUTPUT A_OUTPUT (Z.of_nat (length s_output) + 1) s_output (repeat (Z_to_bv 8 0) 1) ps pk pl1 pl2 3 0 pq1 pq2 pb1 3 (nb16 [] [(n1, H_PROVIDER); (n2, H_VERSION)] [] [] [(n3, H_FIPS)]) D1 3 4 0)
                       | intros c0 H0; exact H0
                       | intros c0 H0; exact (ppi_of_room RT PMc sp gp tp s6 s7 s8 s9 s10 s11 lo canary Σ3 m4 SITE_ppi_name (-24) (PPI_TAB + 24) (PPI_TAB_SH + 3) true s_output ps pk pl1 pl2 3 0 pq1 pq2 pb1 3 (nb16 [] [(n1, H_PROVIDER); (n2, H_VERSION)] [] [] [(n3, H_FIPS)]) D1 3 4 _ _ _ _ c0 H0)].
    - apply (PRE Σ3 m4 SITE_ppi_name (Z_to_bv 8 1) true A_OUTPUT s_output 1%nat ps pk pl1 pl2 3 0 pq1 pq2 pb1 3 (nb16 [] [(n1, H_PROVIDER); (n2, H_VERSION)] [] [] [(n3, H_FIPS)]) TPV GP lit_output GO_output CELL4
               ltac:(lv_in LV3) Aps PSC4 ltac:(clear; lia) ltac:(clear; lia) ltac:(lv_in LV3) Apk LKC4 REPa4 INCa4 ltac:(clear; lia)).
      + rewrite hash_output, bk_output. cbn [nth nb16]. repeat (constructor; [vm_compute; intros HH; discriminate HH|]). constructor.
      + cbn [q_of]. lv_in LV3.
      + cbn [q_of]. clear - Aq1. Z.div_mod_to_equations. lia.
    - exact Q1C4.
    - clear. lia.
    - clear. lia.
    - clear. lia.
    - clear. lia.
    - lv_in LV3.
    - destruct BKd1 as (_ & X & _). clear - X. Z.div_mod_to_equations. lia.
    - exact ND1.
    - exact D1C4.
  }
  { intros u0 u1 u2 u1' u2' u3' u4 u5 u6 u7 v3 v4 v5 v6 F1 fc1 Σx mx ARTx MIx STx.
    exact (ppi_w4 sp gp tp u0 u1 u2 u1' u2' u3' u4 u5 u6 u7 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F1 fc1 mx lo STx LO80 HLOS SPH (UTX Σx mx ARTx) (ppi_tab_sh RT GOBJ AFP Σx mx 4 ARTx GO_ppitab ltac:(clear; lia)) MIx). }
  { exact Hc4. }
  clear Hc4. intros Σ4 NEW m4r m5 ? ? ? ? ? ? ? ? ? ? ? F5 fc5 c5 Hc5 STD5 ART4r PRES4 HQ LV4 SP04 MU5.
  destruct HQ as (r4 & n4 & junk4 & -> & (ENV4r & CELL4r & PSC4r & LKC4r & REPa4r) & Q1C4r & D1C4r & BKr4 & BKn4).
  change (Z.of_nat (length s_output) + 16) with 22 in *. cbn [app] in STD5, LV4. change (3 + 1) with 4 in STD5.
  rewrite LV3 in LV4.
  assert (EB : pstr_bks (nb16 [] [(n1, H_PROVIDER); (n2, H_VERSION)] [] [] [(n3, H_FIPS)]) s_output n4 = (nb16 [(n4, H_OUTPUT)] [(n1, H_PROVIDER); (n2, H_VERSION)] [] [] [(n3, H_FIPS)])) by (unfold pstr_bks; rewrite hash_output, bk_output; reflexivity).
  rewrite EB in REPa4r. clear EB. unfold psd_bump in PSC4r. cbn [t_of q_of] in REPa4r, Q1C4r.
  change (3 + 1) with 4 in PSC4r.
  change (3 + 1) with 4 in REPa4r.
  change (3 + 1) with 4 in Q1C4r.
  change (Z.to_nat (8 * 4)) with 32%nat in D1C4r.
  pose proof (SEGS m4r m5 _ _ _ _ MU5 LOa CELL4r ltac:(unfold CTX_PSD, SEGTOP_A; cbn; clear; lia)) as CELL5.
  pose proof (SEGC Σ4 m4r m5 _ _ ps 48 _ _ ART4r SP04 ltac:(lv_in LV4) MU5 LOa PSC4r ltac:(unfold psd_cells; cbn; clear; lia)) as PSC5.
  pose proof (SEGC Σ4 m4r m5 _ _ pk 40 _ _ ART4r SP04 ltac:(lv_in LV4) MU5 LOa LKC4r ltac:(unfold mutex_cells; cbn; clear; lia)) as LKC5.
  pose proof (SEGC Σ4 m4r m5 _ _ pq1 56 _ _ ART4r SP04 ltac:(lv_in LV4) MU5 LOa Q1C4r ltac:(unfold sk_cells; cbn; clear; lia)) as Q1C5.
  pose proof (SEGC Σ4 m4r m5 _ _ D1 32 _ _ ART4r SP04 ltac:(lv_in LV4) MU5 LOa D1C4r ltac:(cbn; clear; lia)) as D1C5.
  assert (INCa5 : incl (plh_L pl1 pb1 (nb16 [(n4, H_OUTPUT)] [(n1, H_PROVIDER); (n2, H_VERSION)] [] [] [(n3, H_FIPS)])) (rt_live RT Σ4)).
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [lv_in LV4|]). destruct Hx. }
  pose proof (SEGP Σ4 m4r m5 _ _ _ _ _ _ ART4r SP04 INCa5 MU5 LOa REPa4r) as REPa5.
  assert (INCbB : incl (plh_L pl2 pb2 (nb16 [] [] [] [] [])) (rt_live RT Σ3)).
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [lv_in LV3|]). destruct Hx. }
  assert (NOTb : forall x, In x (plh_L pl2 pb2 (nb16 [] [] [] [] [])) -> ~ In x ((D1, 8 * 4) :: pstr_L true ps pk pl1 pl2 pq1 pq2 pb1 (nb16 [] [(n1, H_PROVIDER); (n2, H_VERSION)] [] [] [(n3, H_FIPS)]))).
  { intros x Hx. cbn [plh_L nb16 concat app map In fst] in Hx. repeat (destruct Hx as [<-|Hx]; [exact ltac:(cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst]; intros HH; repeat (destruct HH as [HH|HH]; [apply pair_equal_spec in HH; destruct HH as [HHa HHn]; first [discriminate HHn | (revert HHn; clear; lia) | congruence]|]); exact HH)|]). destruct Hx. }
  pose proof (ppi_keep_plh RT GOBJ AF AFP Σ3 m4 m4r (rt_live RT Σ3) (rt_frames RT Σ3) (bv_unsigned sp + -64) ((D1, 8 * 4) :: pstr_L true ps pk pl1 pl2 pq1 pq2 pb1 (nb16 [] [(n1, H_PROVIDER); (n2, H_VERSION)] [] [] [(n3, H_FIPS)])) pl2 pb2 0 (nb16 [] [] [] [] []) ART4 PRES4 (fun e He => He) HLW4 REPb4 INCbB NOTb) as REPb4r.
  clear INCbB NOTb.
  assert (INCb5 : incl (plh_L pl2 pb2 (nb16 [] [] [] [] [])) (rt_live RT Σ4)).
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [lv_in LV4|]). destruct Hx. }
  pose proof (SEGP Σ4 m4r m5 _ _ _ _ _ _ ART4r SP04 INCb5 MU5 LOa REPb4r) as REPb5.
  pose proof (ppi_keep_cells RT GOBJ AF AFP Σ3 m4 m4r (rt_live RT Σ3) (rt_frames RT Σ3) (bv_unsigned sp + -64) ((D1, 8 * 4) :: pstr_L true ps pk pl1 pl2 pq1 pq2 pb1 (nb16 [] [(n1, H_PROVIDER); (n2, H_VERSION)] [] [] [(n3, H_FIPS)])) pq2 56 pq2 _ ART4 PRES4 (fun e He => He) HLW4 ltac:(lv_in LV3) ltac:(clear; lia) ltac:(cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst]; intros HH; repeat (destruct HH as [HH|HH]; [apply pair_equal_spec in HH; destruct HH as [HHa HHn]; first [discriminate HHn | (revert HHn; clear; lia) | congruence]|]); exact HH) Q2C4 ltac:(clear; lia) ltac:(unfold sk_cells; cbn; clear; lia)) as Q2C4r.
  pose proof (SEGC Σ4 m4r m5 _ _ pq2 56 _ _ ART4r SP04 ltac:(lv_in LV4) MU5 LOa Q2C4r ltac:(unfold sk_cells; cbn; clear; lia)) as Q2C5.
  clear CELL4r PSC4r LKC4r REPa4r REPb4r Q1C4r Q2C4r ENV4r PRES4 HLW4 CELL4 PSC4 LKC4 REPa4 REPb4 Q1C4 Q2C4 INCa4 INCb4 STD4.

  (* [comment removed for export] *)
  pose proof STD5 as (ART5 & _).
  assert (EBASE5 : live_remove D1 (rt_live RT Σ4) = [(n4, 24); (r4, 22); (n3, 24); (r3, 20); (n2, 24); (r2, 23); (n1, 24); (r1, 24)] ++ rt_live RT Σ).
  { apply (ppi_live_remove_unique RT AF Σ4 m5 [(n4, 24); (r4, 22); (n3, 24); (r3, 20); (n2, 24); (r2, 23); (n1, 24)] D1 32 ([(r1, 24)] ++ rt_live RT Σ) ART5 LV4 ltac:(clear; lia)).
    apply Forall_app. split; [repeat constructor; cbn [snd]; clear; lia|]. cbn [app]. repeat (constructor; [cbn [snd]; clear; lia|]). exact POS. }
  assert (HLW5 : incl (pstr_L true ps pk pl1 pl2 pq1 pq2 pb1 (nb16 [(n4, H_OUTPUT)] [(n1, H_PROVIDER); (n2, H_VERSION)] [] [] [(n3, H_FIPS)])) (rt_live RT Σ4)).
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [lv_in LV4|]). destruct Hx. }
  eapply (STEP Σ4 m5 [(n4, 24); (r4, 22); (n3, 24); (r3, 20); (n2, 24); (r2, 23); (n1, 24); (D1, 32); (r1, 24)] [(n4, 24); (r4, 22); (n3, 24); (r3, 20); (n2, 24); (r2, 23); (n1, 24); (r1, 24)] 4 (Z_to_bv 8 1) j SITE_ppi_name 1 A_INPUT (-32) (PPI_TAB + 32) (PPI_TAB_SH + 4) 5 (live_remove D1 (rt_live RT Σ4)) (pstr_L true ps pk pl1 pl2 pq1 pq2 pb1 (nb16 [(n4, H_OUTPUT)] [(n1, H_PROVIDER); (n2, H_VERSION)] [] [] [(n3, H_FIPS)]))
            (ppi_Qgrow RT canary true s_input ps pk pl1 pl2 4 0 pq1 pq2 pb1 4 (nb16 [(n4, H_OUTPUT)] [(n1, H_PROVIDER); (n2, H_VERSION)] [] [] [(n3, H_FIPS)]) (Z_to_bv 64 0) (Z_to_bv 64 2146284) (Z_to_bv 64 2146368) (Z_to_bv 64 2146328))
            SITE_ppi_name 1 A_STRUCTURE (-40) (PPI_TAB + 40) (PPI_TAB_SH + 5) STD5).
  { cbn [length]. clear. lia. }
  { clear. lia. }
  { unfold PPI_SITES. wp_in_lit. }
  { unfold PPI_CALLS. wp_in_lit. }
  { unfold SITE_ppi_name. clear. lia. }
  { reflexivity. }
  { exact EBASE5. }
  { exact (fun e He => live_remove_sub _ _ _ He). }
  { exact HLW5. }
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [first [left; unfold PSD; solve [wp_in_lit] | right; solve [wp_in_lit]]|]). destruct Hx. }
  { intros u0 u1 u2 u4 u5 u6 u7 v3 v4 v5 v6 F1 fc1 GP.
    eapply cps_conseq; [eapply (C_PSTR_G Σ4 PMc (Z_to_bv 64 SITE_ppi_name) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0 u1 u2 sp (Z_to_bv 64 PPI_CTX) (Z_to_bv 64 PPI_CTX) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 A_INPUT) u4 u5 u6 u7 (Z_to_bv 64 (-32)) (Z_to_bv 64 (PPI_TAB + 32)) (Z_to_bv 64 (PPI_TAB_SH + 4)) (Z_to_bv 64 (-48)) s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F1 fc1 m5 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary true A_INPUT A_INPUT (Z.of_nat (length s_input) + 1) s_input (repeat (Z_to_bv 8 0) 2) ps pk pl1 pl2 4 0 pq1 pq2 pb1 4 (nb16 [(n4, H_OUTPUT)] [(n1, H_PROVIDER); (n2, H_VERSION)] [] [] [(n3, H_FIPS)]) D1)
                       | intros c0 H0; exact H0
                       | intros c0 H0; exact (ppi_of_grow RT PMc sp gp tp s6 s7 s8 s9 s10 s11 lo canary Σ4 m5 SITE_ppi_name (-32) (PPI_TAB + 32) (PPI_TAB_SH + 4) true s_input ps pk pl1 pl2 4 0 pq1 pq2 pb1 4 (nb16 [(n4, H_OUTPUT)] [(n1, H_PROVIDER); (n2, H_VERSION)] [] [] [(n3, H_FIPS)]) D1 _ _ _ _ c0 H0)].
    - apply (PRE Σ4 m5 SITE_ppi_name (Z_to_bv 8 1) true A_INPUT s_input 2%nat ps pk pl1 pl2 4 0 pq1 pq2 pb1 4 (nb16 [(n4, H_OUTPUT)] [(n1, H_PROVIDER); (n2, H_VERSION)] [] [] [(n3, H_FIPS)]) TPV GP lit_input GO_input CELL5
               ltac:(lv_in LV4) Aps PSC5 ltac:(clear; lia) ltac:(clear; lia) ltac:(lv_in LV4) Apk LKC5 REPa5 INCa5 ltac:(clear; lia)).
      + rewrite hash_input, bk_input. cbn [nth nb16]. repeat (constructor; [vm_compute; intros HH; discriminate HH|]). constructor.
      + cbn [q_of]. lv_in LV4.
      + cbn [q_of]. clear - Aq1. Z.div_mod_to_equations. lia.
    - exact Q1C5.
    - lv_in LV4.
    - exact D1C5.
  }
  { intros u0 u1 u2 u1' u2' u3' u4 u5 u6 u7 v3 v4 v5 v6 F1 fc1 Σx mx ARTx MIx STx.
    exact (ppi_w5 sp gp tp u0 u1 u2 u1' u2' u3' u4 u5 u6 u7 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F1 fc1 mx lo STx LO80 HLOS SPH (UTX Σx mx ARTx) (ppi_tab_sh RT GOBJ AFP Σx mx 5 ARTx GO_ppitab ltac:(clear; lia)) MIx). }
  { exact Hc5. }
  clear Hc5. intros Σ5 NEW m5r m6 ? ? ? ? ? ? ? ? ? ? ? F6 fc6 c6 Hc6 STD6 ART5r PRES5 HQ LV5 SP05 MU6.
  destruct HQ as (r5 & D5 & n5 & junk5 & -> & (ENV5r & CELL5r & PSC5r & LKC5r & REPa5r) & Q1C5r & D1C5r & BKr5 & BKd5 & BKn5).
  change (Z.of_nat (length s_input) + 16) with 21 in *. cbn [app] in STD6, LV5. change (4 + 1) with 5 in STD6.
  rewrite EBASE5 in LV5. cbn [app] in LV5.
  assert (EB : pstr_bks (nb16 [(n4, H_OUTPUT)] [(n1, H_PROVIDER); (n2, H_VERSION)] [] [] [(n3, H_FIPS)]) s_input n5 = (nb16 [(n4, H_OUTPUT)] [(n1, H_PROVIDER); (n2, H_VERSION); (n5, H_INPUT)] [] [] [(n3, H_FIPS)])) by (unfold pstr_bks; rewrite hash_input, bk_input; reflexivity).
  rewrite EB in REPa5r. clear EB. unfold psd_bump in PSC5r. cbn [t_of q_of] in REPa5r, Q1C5r.
  change (4 + 1) with 5 in PSC5r.
  change (4 + 1) with 5 in REPa5r.
  assert (ND5 : D5 <> ps).
  { intros X. apply (ppi_fresh_pre RT AF Σ5 m5r [(n5, 24); (D5, 48); (r5, 21)] ([(n4, 24); (r4, 22); (n3, 24); (r3, 20); (n2, 24); (r2, 23); (n1, 24); (r1, 24)] ++ rt_live RT Σ) (D5, 48) ART5r LV5 ltac:(right; left; reflexivity) ltac:(cbn [snd]; clear; lia)).
    rewrite X. cbn [app In]. repeat first [left; reflexivity | right]. assumption. }
  pose proof (SEGS m5r m6 _ _ _ _ MU6 LOa CELL5r ltac:(unfold CTX_PSD, SEGTOP_A; cbn; clear; lia)) as CELL6.
  pose proof (SEGC Σ5 m5r m6 _ _ ps 48 _ _ ART5r SP05 ltac:(lv_in LV5) MU6 LOa PSC5r ltac:(unfold psd_cells; cbn; clear; lia)) as PSC6.
  pose proof (SEGC Σ5 m5r m6 _ _ pk 40 _ _ ART5r SP05 ltac:(lv_in LV5) MU6 LOa LKC5r ltac:(unfold mutex_cells; cbn; clear; lia)) as LKC6.
  pose proof (SEGC Σ5 m5r m6 _ _ pq1 56 _ _ ART5r SP05 ltac:(lv_in LV5) MU6 LOa Q1C5r ltac:(unfold sk_cells; cbn; clear; lia)) as Q1C6.
  pose proof (SEGC Σ5 m5r m6 _ _ D5 48 _ _ ART5r SP05 ltac:(lv_in LV5) MU6 LOa D1C5r ltac:(cbn; clear; lia)) as D1C6.
  assert (INCa6 : incl (plh_L pl1 pb1 (nb16 [(n4, H_OUTPUT)] [(n1, H_PROVIDER); (n2, H_VERSION); (n5, H_INPUT)] [] [] [(n3, H_FIPS)])) (rt_live RT Σ5)).
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [lv_in LV5|]). destruct Hx. }
  pose proof (SEGP Σ5 m5r m6 _ _ _ _ _ _ ART5r SP05 INCa6 MU6 LOa REPa5r) as REPa6.
  assert (INCbB : incl (plh_L pl2 pb2 (nb16 [] [] [] [] [])) (live_remove D1 (rt_live RT Σ4))).
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [lv_in EBASE5|]). destruct Hx. }
  assert (NOTb : forall x, In x (plh_L pl2 pb2 (nb16 [] [] [] [] [])) -> ~ In x (pstr_L true ps pk pl1 pl2 pq1 pq2 pb1 (nb16 [(n4, H_OUTPUT)] [(n1, H_PROVIDER); (n2, H_VERSION)] [] [] [(n3, H_FIPS)]))).
  { intros x Hx. cbn [plh_L nb16 concat app map In fst] in Hx. repeat (destruct Hx as [<-|Hx]; [exact ltac:(cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst]; intros HH; repeat (destruct HH as [HH|HH]; [apply pair_equal_spec in HH; destruct HH as [HHa HHn]; first [discriminate HHn | (revert HHn; clear; lia) | congruence]|]); exact HH)|]). destruct Hx. }
  pose proof (ppi_keep_plh RT GOBJ AF AFP Σ4 m5 m5r (live_remove D1 (rt_live RT Σ4)) (rt_frames RT Σ4) (bv_unsigned sp + -64) (pstr_L true ps pk pl1 pl2 pq1 pq2 pb1 (nb16 [(n4, H_OUTPUT)] [(n1, H_PROVIDER); (n2, H_VERSION)] [] [] [(n3, H_FIPS)])) pl2 pb2 0 (nb16 [] [] [] [] []) ART5 PRES5 (fun e He => live_remove_sub _ _ _ He) HLW5 REPb5 INCbB NOTb) as REPb5r.
  clear INCbB NOTb.
  assert (INCb6 : incl (plh_L pl2 pb2 (nb16 [] [] [] [] [])) (rt_live RT Σ5)).
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [lv_in LV5|]). destruct Hx. }
  pose proof (SEGP Σ5 m5r m6 _ _ _ _ _ _ ART5r SP05 INCb6 MU6 LOa REPb5r) as REPb6.
  pose proof (ppi_keep_cells RT GOBJ AF AFP Σ4 m5 m5r (live_remove D1 (rt_live RT Σ4)) (rt_frames RT Σ4) (bv_unsigned sp + -64) (pstr_L true ps pk pl1 pl2 pq1 pq2 pb1 (nb16 [(n4, H_OUTPUT)] [(n1, H_PROVIDER); (n2, H_VERSION)] [] [] [(n3, H_FIPS)])) pq2 56 pq2 _ ART5 PRES5 (fun e He => live_remove_sub _ _ _ He) HLW5 ltac:(lv_in EBASE5) ltac:(clear; lia) ltac:(cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst]; intros HH; repeat (destruct HH as [HH|HH]; [apply pair_equal_spec in HH; destruct HH as [HHa HHn]; first [discriminate HHn | (revert HHn; clear; lia) | congruence]|]); exact HH) Q2C5 ltac:(clear; lia) ltac:(unfold sk_cells; cbn; clear; lia)) as Q2C5r.
  pose proof (SEGC Σ5 m5r m6 _ _ pq2 56 _ _ ART5r SP05 ltac:(lv_in LV5) MU6 LOa Q2C5r ltac:(unfold sk_cells; cbn; clear; lia)) as Q2C6.
  clear CELL5r PSC5r LKC5r REPa5r REPb5r Q1C5r Q2C5r ENV5r PRES5 HLW5 CELL5 PSC5 LKC5 REPa5 REPb5 Q1C5 Q2C5 INCa5 INCb5 STD5.

  (* [comment removed for export] *)
  pose proof STD6 as (ART6 & _).
  assert (HLW6 : incl ((D5, 8 * 6) :: pstr_L true ps pk pl1 pl2 pq1 pq2 pb1 (nb16 [(n4, H_OUTPUT)] [(n1, H_PROVIDER); (n2, H_VERSION); (n5, H_INPUT)] [] [] [(n3, H_FIPS)])) (rt_live RT Σ5)).
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [lv_in LV5|]). destruct Hx. }
  eapply (STEP Σ5 m6 [(n5, 24); (D5, 48); (r5, 21); (n4, 24); (r4, 22); (n3, 24); (r3, 20); (n2, 24); (r2, 23); (n1, 24); (r1, 24)] [(n5, 24); (D5, 48); (r5, 21); (n4, 24); (r4, 22); (n3, 24); (r3, 20); (n2, 24); (r2, 23); (n1, 24); (r1, 24)] 5 (Z_to_bv 8 1) j SITE_ppi_name 1 A_STRUCTURE (-40) (PPI_TAB + 40) (PPI_TAB_SH + 5) 6 (rt_live RT Σ5) ((D5, 8 * 6) :: pstr_L true ps pk pl1 pl2 pq1 pq2 pb1 (nb16 [(n4, H_OUTPUT)] [(n1, H_PROVIDER); (n2, H_VERSION); (n5, H_INPUT)] [] [] [(n3, H_FIPS)]))
            (ppi_Qroom RT canary true s_structure ps pk pl1 pl2 5 0 pq1 pq2 pb1 5 (nb16 [(n4, H_OUTPUT)] [(n1, H_PROVIDER); (n2, H_VERSION); (n5, H_INPUT)] [] [] [(n3, H_FIPS)]) D5 5 6 (Z_to_bv 64 0) (Z_to_bv 64 2146284) (Z_to_bv 64 2146368) (Z_to_bv 64 2146328))
            SITE_ppi_val1 0 A_YES 1 (PPI_TAB + 48) (PPI_TAB_SH + 6) STD6).
  { cbn [length]. clear. lia. }
  { clear. lia. }
  { unfold PPI_SITES. wp_in_lit. }
  { unfold PPI_CALLS. wp_in_lit. }
  { unfold SITE_ppi_name. clear. lia. }
  { reflexivity. }
  { exact LV5. }
  { exact (fun e He => He). }
  { exact HLW6. }
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [first [left; unfold PSD; solve [wp_in_lit] | right; solve [wp_in_lit]]|]). destruct Hx. }
  { intros u0 u1 u2 u4 u5 u6 u7 v3 v4 v5 v6 F1 fc1 GP.
    eapply cps_conseq; [eapply (C_PSTR_R Σ5 PMc (Z_to_bv 64 SITE_ppi_name) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0 u1 u2 sp (Z_to_bv 64 PPI_CTX) (Z_to_bv 64 PPI_CTX) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 A_STRUCTURE) u4 u5 u6 u7 (Z_to_bv 64 (-40)) (Z_to_bv 64 (PPI_TAB + 40)) (Z_to_bv 64 (PPI_TAB_SH + 5)) (Z_to_bv 64 (-48)) s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F1 fc1 m6 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary true A_STRUCTURE A_STRUCTURE (Z.of_nat (length s_structure) + 1) s_structure (repeat (Z_to_bv 8 0) 6) ps pk pl1 pl2 5 0 pq1 pq2 pb1 5 (nb16 [(n4, H_OUTPUT)] [(n1, H_PROVIDER); (n2, H_VERSION); (n5, H_INPUT)] [] [] [(n3, H_FIPS)]) D5 5 6 0)
                       | intros c0 H0; exact H0
                       | intros c0 H0; exact (ppi_of_room RT PMc sp gp tp s6 s7 s8 s9 s10 s11 lo canary Σ5 m6 SITE_ppi_name (-40) (PPI_TAB + 40) (PPI_TAB_SH + 5) true s_structure ps pk pl1 pl2 5 0 pq1 pq2 pb1 5 (nb16 [(n4, H_OUTPUT)] [(n1, H_PROVIDER); (n2, H_VERSION); (n5, H_INPUT)] [] [] [(n3, H_FIPS)]) D5 5 6 _ _ _ _ c0 H0)].
    - apply (PRE Σ5 m6 SITE_ppi_name (Z_to_bv 8 1) true A_STRUCTURE s_structure 6%nat ps pk pl1 pl2 5 0 pq1 pq2 pb1 5 (nb16 [(n4, H_OUTPUT)] [(n1, H_PROVIDER); (n2, H_VERSION); (n5, H_INPUT)] [] [] [(n3, H_FIPS)]) TPV GP lit_structure GO_structure CELL6
               ltac:(lv_in LV5) Aps PSC6 ltac:(clear; lia) ltac:(clear; lia) ltac:(lv_in LV5) Apk LKC6 REPa6 INCa6 ltac:(clear; lia)).
      + rewrite hash_structure, bk_structure. cbn [nth nb16]. repeat (constructor; [vm_compute; intros HH; discriminate HH|]). constructor.
      + cbn [q_of]. lv_in LV5.
      + cbn [q_of]. clear - Aq1. Z.div_mod_to_equations. lia.
    - exact Q1C6.
    - clear. lia.
    - clear. lia.
    - clear. lia.
    - clear. lia.
    - lv_in LV5.
    - destruct BKd5 as (_ & X & _). clear - X. Z.div_mod_to_equations. lia.
    - exact ND5.
    - exact D1C6.
  }
  { intros u0 u1 u2 u1' u2' u3' u4 u5 u6 u7 v3 v4 v5 v6 F1 fc1 Σx mx ARTx MIx STx.
    exact (ppi_w6 sp gp tp u0 u1 u2 u1' u2' u3' u4 u5 u6 u7 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F1 fc1 mx lo STx LO80 HLOS SPH (UTX Σx mx ARTx) MIx). }
  { exact Hc6. }
  clear Hc6. intros Σ6 NEW m6r m7 ? ? ? ? ? ? ? ? ? ? ? F7 fc7 c7 Hc7 STD7 ART6r PRES6 HQ LV6 SP06 MU7.
  destruct HQ as (r6 & n6 & junk6 & -> & (ENV6r & CELL6r & PSC6r & LKC6r & REPa6r) & Q1C6r & D1C6r & BKr6 & BKn6).
  change (Z.of_nat (length s_structure) + 16) with 25 in *. cbn [app] in STD7, LV6. change (5 + 1) with 6 in STD7.
  rewrite LV5 in LV6.
  assert (EB : pstr_bks (nb16 [(n4, H_OUTPUT)] [(n1, H_PROVIDER); (n2, H_VERSION); (n5, H_INPUT)] [] [] [(n3, H_FIPS)]) s_structure n6 = (nb16 [(n4, H_OUTPUT)] [(n1, H_PROVIDER); (n2, H_VERSION); (n5, H_INPUT)] [] [] [(n3, H_FIPS); (n6, H_STRUCTURE)])) by (unfold pstr_bks; rewrite hash_structure, bk_structure; reflexivity).
  rewrite EB in REPa6r. clear EB. unfold psd_bump in PSC6r. cbn [t_of q_of] in REPa6r, Q1C6r.
  change (5 + 1) with 6 in PSC6r.
  change (5 + 1) with 6 in REPa6r.
  change (5 + 1) with 6 in Q1C6r.
  change (Z.to_nat (8 * 6)) with 48%nat in D1C6r.
  pose proof (SEGS m6r m7 _ _ _ _ MU7 LOa CELL6r ltac:(unfold CTX_PSD, SEGTOP_A; cbn; clear; lia)) as CELL7.
  pose proof (SEGC Σ6 m6r m7 _ _ ps 48 _ _ ART6r SP06 ltac:(lv_in LV6) MU7 LOa PSC6r ltac:(unfold psd_cells; cbn; clear; lia)) as PSC7.
  pose proof (SEGC Σ6 m6r m7 _ _ pk 40 _ _ ART6r SP06 ltac:(lv_in LV6) MU7 LOa LKC6r ltac:(unfold mutex_cells; cbn; clear; lia)) as LKC7.
  pose proof (SEGC Σ6 m6r m7 _ _ pq1 56 _ _ ART6r SP06 ltac:(lv_in LV6) MU7 LOa Q1C6r ltac:(unfold sk_cells; cbn; clear; lia)) as Q1C7.
  pose proof (SEGC Σ6 m6r m7 _ _ D5 48 _ _ ART6r SP06 ltac:(lv_in LV6) MU7 LOa D1C6r ltac:(cbn; clear; lia)) as D1C7.
  assert (INCa7 : incl (plh_L pl1 pb1 (nb16 [(n4, H_OUTPUT)] [(n1, H_PROVIDER); (n2, H_VERSION); (n5, H_INPUT)] [] [] [(n3, H_FIPS); (n6, H_STRUCTURE)])) (rt_live RT Σ6)).
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [lv_in LV6|]). destruct Hx. }
  pose proof (SEGP Σ6 m6r m7 _ _ _ _ _ _ ART6r SP06 INCa7 MU7 LOa REPa6r) as REPa7.
  assert (INCbB : incl (plh_L pl2 pb2 (nb16 [] [] [] [] [])) (rt_live RT Σ5)).
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [lv_in LV5|]). destruct Hx. }
  assert (NOTb : forall x, In x (plh_L pl2 pb2 (nb16 [] [] [] [] [])) -> ~ In x ((D5, 8 * 6) :: pstr_L true ps pk pl1 pl2 pq1 pq2 pb1 (nb16 [(n4, H_OUTPUT)] [(n1, H_PROVIDER); (n2, H_VERSION); (n5, H_INPUT)] [] [] [(n3, H_FIPS)]))).
  { intros x Hx. cbn [plh_L nb16 concat app map In fst] in Hx. repeat (destruct Hx as [<-|Hx]; [exact ltac:(cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst]; intros HH; repeat (destruct HH as [HH|HH]; [apply pair_equal_spec in HH; destruct HH as [HHa HHn]; first [discriminate HHn | (revert HHn; clear; lia) | congruence]|]); exact HH)|]). destruct Hx. }
  pose proof (ppi_keep_plh RT GOBJ AF AFP Σ5 m6 m6r (rt_live RT Σ5) (rt_frames RT Σ5) (bv_unsigned sp + -64) ((D5, 8 * 6) :: pstr_L true ps pk pl1 pl2 pq1 pq2 pb1 (nb16 [(n4, H_OUTPUT)] [(n1, H_PROVIDER); (n2, H_VERSION); (n5, H_INPUT)] [] [] [(n3, H_FIPS)])) pl2 pb2 0 (nb16 [] [] [] [] []) ART6 PRES6 (fun e He => He) HLW6 REPb6 INCbB NOTb) as REPb6r.
  clear INCbB NOTb.
  assert (INCb7 : incl (plh_L pl2 pb2 (nb16 [] [] [] [] [])) (rt_live RT Σ6)).
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [lv_in LV6|]). destruct Hx. }
  pose proof (SEGP Σ6 m6r m7 _ _ _ _ _ _ ART6r SP06 INCb7 MU7 LOa REPb6r) as REPb7.
  pose proof (ppi_keep_cells RT GOBJ AF AFP Σ5 m6 m6r (rt_live RT Σ5) (rt_frames RT Σ5) (bv_unsigned sp + -64) ((D5, 8 * 6) :: pstr_L true ps pk pl1 pl2 pq1 pq2 pb1 (nb16 [(n4, H_OUTPUT)] [(n1, H_PROVIDER); (n2, H_VERSION); (n5, H_INPUT)] [] [] [(n3, H_FIPS)])) pq2 56 pq2 _ ART6 PRES6 (fun e He => He) HLW6 ltac:(lv_in LV5) ltac:(clear; lia) ltac:(cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst]; intros HH; repeat (destruct HH as [HH|HH]; [apply pair_equal_spec in HH; destruct HH as [HHa HHn]; first [discriminate HHn | (revert HHn; clear; lia) | congruence]|]); exact HH) Q2C6 ltac:(clear; lia) ltac:(unfold sk_cells; cbn; clear; lia)) as Q2C6r.
  pose proof (SEGC Σ6 m6r m7 _ _ pq2 56 _ _ ART6r SP06 ltac:(lv_in LV6) MU7 LOa Q2C6r ltac:(unfold sk_cells; cbn; clear; lia)) as Q2C7.
  clear CELL6r PSC6r LKC6r REPa6r REPb6r Q1C6r Q2C6r ENV6r PRES6 HLW6 CELL6 PSC6 LKC6 REPa6 REPb6 Q1C6 Q2C6 INCa6 INCb6 STD6.

  (* [comment removed for export] *)
  pose proof STD7 as (ART7 & _).
  assert (HLW7 : incl (pstr_L false ps pk pl1 pl2 pq1 pq2 pb2 (nb16 [] [] [] [] [])) (rt_live RT Σ6)).
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [lv_in LV6|]). destruct Hx. }
  eapply (STEP Σ6 m7 [(n6, 24); (r6, 25); (n5, 24); (D5, 48); (r5, 21); (n4, 24); (r4, 22); (n3, 24); (r3, 20); (n2, 24); (r2, 23); (n1, 24); (r1, 24)] [(n6, 24); (r6, 25); (n5, 24); (D5, 48); (r5, 21); (n4, 24); (r4, 22); (n3, 24); (r3, 20); (n2, 24); (r2, 23); (n1, 24); (r1, 24)] 6 (Z_to_bv 8 1) j SITE_ppi_val1 0 A_YES 1 (PPI_TAB + 48) (PPI_TAB_SH + 6) 1 (rt_live RT Σ6) (pstr_L false ps pk pl1 pl2 pq1 pq2 pb2 (nb16 [] [] [] [] []))
            (ppi_Qfirst RT canary false s_yes ps pk pl1 pl2 6 0 pq1 pq2 pb2 0 (nb16 [] [] [] [] []) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 2146284) (Z_to_bv 64 2146368) (Z_to_bv 64 2146328))
            SITE_ppi_val2 0 A_NO 1 (PPI_TAB + 48) (PPI_TAB_SH + 6) STD7).
  { cbn [length]. clear. lia. }
  { clear. lia. }
  { unfold PPI_SITES. wp_in_lit. }
  { unfold PPI_CALLS. wp_in_lit. }
  { unfold SITE_ppi_val1. clear. lia. }
  { reflexivity. }
  { exact LV6. }
  { exact (fun e He => He). }
  { exact HLW7. }
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [first [left; unfold PSD; solve [wp_in_lit] | right; solve [wp_in_lit]]|]). destruct Hx. }
  { intros u0 u1 u2 u4 u5 u6 u7 v3 v4 v5 v6 F1 fc1 GP.
    eapply cps_conseq; [eapply (C_PSTR_F Σ6 PMc (Z_to_bv 64 SITE_ppi_val1) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0 u1 u2 sp (Z_to_bv 64 PPI_CTX) (Z_to_bv 64 PPI_CTX) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 A_YES) u4 u5 u6 u7 (Z_to_bv 64 1) (Z_to_bv 64 (PPI_TAB + 48)) (Z_to_bv 64 (PPI_TAB_SH + 6)) (Z_to_bv 64 (-48)) s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F1 fc1 m7 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary false A_YES A_YES (Z.of_nat (length s_yes) + 1) s_yes (repeat (Z_to_bv 8 0) 4) ps pk pl1 pl2 6 0 pq1 pq2 pb2 0 (nb16 [] [] [] [] []))
                       | intros c0 H0; exact H0
                       | intros c0 H0; exact (ppi_of_first RT PMc sp gp tp s6 s7 s8 s9 s10 s11 lo canary Σ6 m7 SITE_ppi_val1 1 (PPI_TAB + 48) (PPI_TAB_SH + 6) false s_yes ps pk pl1 pl2 6 0 pq1 pq2 pb2 0 (nb16 [] [] [] [] []) _ _ _ _ _ c0 H0)].
    - apply (PRE Σ6 m7 SITE_ppi_val1 (Z_to_bv 8 1) false A_YES s_yes 4%nat ps pk pl1 pl2 6 0 pq1 pq2 pb2 0 (nb16 [] [] [] [] []) TPV GP lit_yes GO_yes CELL7
               ltac:(lv_in LV6) Aps PSC7 ltac:(clear; lia) ltac:(clear; lia) ltac:(lv_in LV6) Apk LKC7 REPb7 INCb7 ltac:(clear; lia)).
      + rewrite hash_yes, bk_yes. cbn [nth nb16]. repeat (constructor; [vm_compute; intros HH; discriminate HH|]). constructor.
      + cbn [q_of]. lv_in LV6.
      + cbn [q_of]. clear - Aq2. Z.div_mod_to_equations. lia.
    - exact Q2C7.
  }
  { intros u0 u1 u2 u1' u2' u3' u4 u5 u6 u7 v3 v4 v5 v6 F1 fc1 Σx mx ARTx MIx STx.
    exact (ppi_w7 sp gp tp u0 u1 u2 u1' u2' u3' u4 u5 u6 u7 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F1 fc1 mx lo STx LO80 HLOS SPH (UTX Σx mx ARTx) MIx). }
  { exact Hc7. }
  clear Hc7. intros Σ7 NEW m7r m8 ? ? ? ? ? ? ? ? ? ? ? F8 fc8 c8 Hc8 STD8 ART7r PRES7 HQ LV7 SP07 MU8.
  destruct HQ as (r7 & D7 & n7 & junk7 & -> & (ENV7r & CELL7r & PSC7r & LKC7r & REPb7r) & Q2C7r & D2C7r & BKr7 & BKd7 & BKn7).
  change (Z.of_nat (length s_yes) + 16) with 19 in *. cbn [app] in STD8, LV7. change (6 + 1) with 7 in STD8.
  rewrite LV6 in LV7.
  assert (EB : pstr_bks (nb16 [] [] [] [] []) s_yes n7 = (nb16 [] [] [] [(n7, H_YES)] [])) by (unfold pstr_bks; rewrite hash_yes, bk_yes; reflexivity).
  rewrite EB in REPb7r. clear EB. unfold psd_bump in PSC7r. cbn [t_of q_of] in REPb7r, Q2C7r.
  change (0 + 1) with 1 in PSC7r.
  change (0 + 1) with 1 in REPb7r.
  assert (ND7 : D7 <> ps).
  { pose proof (live_ne_apart2 RT AF Σ7 m7r (D7, 32) (ps, 48) ART7r ltac:(lv_in LV7) ltac:(lv_in LV7) ltac:(intros X; discriminate X)) as Y. cbn [fst snd] in Y. clear - Y. lia. }
  assert (NN7_n4 : n7 <> n4).
  { intros X. apply (ppi_fresh_pre RT AF Σ7 m7r [(n7, 24); (D7, 32); (r7, 19)] ([(n6, 24); (r6, 25); (n5, 24); (D5, 48); (r5, 21); (n4, 24); (r4, 22); (n3, 24); (r3, 20); (n2, 24); (r2, 23); (n1, 24); (r1, 24)] ++ rt_live RT Σ) (n7, 24) ART7r LV7 ltac:(left; reflexivity) ltac:(cbn [snd]; clear; lia)).
    rewrite X. cbn [app In]. repeat first [left; reflexivity | right]. }
  assert (NN7_n1 : n7 <> n1).
  { intros X. apply (ppi_fresh_pre RT AF Σ7 m7r [(n7, 24); (D7, 32); (r7, 19)] ([(n6, 24); (r6, 25); (n5, 24); (D5, 48); (r5, 21); (n4, 24); (r4, 22); (n3, 24); (r3, 20); (n2, 24); (r2, 23); (n1, 24); (r1, 24)] ++ rt_live RT Σ) (n7, 24) ART7r LV7 ltac:(left; reflexivity) ltac:(cbn [snd]; clear; lia)).
    rewrite X. cbn [app In]. repeat first [left; reflexivity | right]. }
  assert (NN7_n2 : n7 <> n2).
  { intros X. apply (ppi_fresh_pre RT AF Σ7 m7r [(n7, 24); (D7, 32); (r7, 19)] ([(n6, 24); (r6, 25); (n5, 24); (D5, 48); (r5, 21); (n4, 24); (r4, 22); (n3, 24); (r3, 20); (n2, 24); (r2, 23); (n1, 24); (r1, 24)] ++ rt_live RT Σ) (n7, 24) ART7r LV7 ltac:(left; reflexivity) ltac:(cbn [snd]; clear; lia)).
    rewrite X. cbn [app In]. repeat first [left; reflexivity | right]. }
  assert (NN7_n5 : n7 <> n5).
  { intros X. apply (ppi_fresh_pre RT AF Σ7 m7r [(n7, 24); (D7, 32); (r7, 19)] ([(n6, 24); (r6, 25); (n5, 24); (D5, 48); (r5, 21); (n4, 24); (r4, 22); (n3, 24); (r3, 20); (n2, 24); (r2, 23); (n1, 24); (r1, 24)] ++ rt_live RT Σ) (n7, 24) ART7r LV7 ltac:(left; reflexivity) ltac:(cbn [snd]; clear; lia)).
    rewrite X. cbn [app In]. repeat first [left; reflexivity | right]. }
  assert (NN7_n3 : n7 <> n3).
  { intros X. apply (ppi_fresh_pre RT AF Σ7 m7r [(n7, 24); (D7, 32); (r7, 19)] ([(n6, 24); (r6, 25); (n5, 24); (D5, 48); (r5, 21); (n4, 24); (r4, 22); (n3, 24); (r3, 20); (n2, 24); (r2, 23); (n1, 24); (r1, 24)] ++ rt_live RT Σ) (n7, 24) ART7r LV7 ltac:(left; reflexivity) ltac:(cbn [snd]; clear; lia)).
    rewrite X. cbn [app In]. repeat first [left; reflexivity | right]. }
  assert (NN7_n6 : n7 <> n6).
  { intros X. apply (ppi_fresh_pre RT AF Σ7 m7r [(n7, 24); (D7, 32); (r7, 19)] ([(n6, 24); (r6, 25); (n5, 24); (D5, 48); (r5, 21); (n4, 24); (r4, 22); (n3, 24); (r3, 20); (n2, 24); (r2, 23); (n1, 24); (r1, 24)] ++ rt_live RT Σ) (n7, 24) ART7r LV7 ltac:(left; reflexivity) ltac:(cbn [snd]; clear; lia)).
    rewrite X. cbn [app In]. repeat first [left; reflexivity | right]. }
  pose proof (SEGS m7r m8 _ _ _ _ MU8 LOa CELL7r ltac:(unfold CTX_PSD, SEGTOP_A; cbn; clear; lia)) as CELL8.
  pose proof (SEGC Σ7 m7r m8 _ _ ps 48 _ _ ART7r SP07 ltac:(lv_in LV7) MU8 LOa PSC7r ltac:(unfold psd_cells; cbn; clear; lia)) as PSC8.
  pose proof (SEGC Σ7 m7r m8 _ _ pk 40 _ _ ART7r SP07 ltac:(lv_in LV7) MU8 LOa LKC7r ltac:(unfold mutex_cells; cbn; clear; lia)) as LKC8.
  pose proof (SEGC Σ7 m7r m8 _ _ pq2 56 _ _ ART7r SP07 ltac:(lv_in LV7) MU8 LOa Q2C7r ltac:(unfold sk_cells; cbn; clear; lia)) as Q2C8.
  pose proof (SEGC Σ7 m7r m8 _ _ D7 32 _ _ ART7r SP07 ltac:(lv_in LV7) MU8 LOa D2C7r ltac:(cbn; clear; lia)) as D2C8.
  assert (INCb8 : incl (plh_L pl2 pb2 (nb16 [] [] [] [(n7, H_YES)] [])) (rt_live RT Σ7)).
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [lv_in LV7|]). destruct Hx. }
  pose proof (SEGP Σ7 m7r m8 _ _ _ _ _ _ ART7r SP07 INCb8 MU8 LOa REPb7r) as REPb8.
  assert (INCaB : incl (plh_L pl1 pb1 (nb16 [(n4, H_OUTPUT)] [(n1, H_PROVIDER); (n2, H_VERSION); (n5, H_INPUT)] [] [] [(n3, H_FIPS); (n6, H_STRUCTURE)])) (rt_live RT Σ6)).
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [lv_in LV6|]). destruct Hx. }
  assert (NOTa : forall x, In x (plh_L pl1 pb1 (nb16 [(n4, H_OUTPUT)] [(n1, H_PROVIDER); (n2, H_VERSION); (n5, H_INPUT)] [] [] [(n3, H_FIPS); (n6, H_STRUCTURE)])) -> ~ In x (pstr_L false ps pk pl1 pl2 pq1 pq2 pb2 (nb16 [] [] [] [] []))).
  { intros x Hx. cbn [plh_L nb16 concat app map In fst] in Hx. repeat (destruct Hx as [<-|Hx]; [exact ltac:(cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst]; intros HH; repeat (destruct HH as [HH|HH]; [apply pair_equal_spec in HH; destruct HH as [HHa HHn]; first [discriminate HHn | (revert HHn; clear; lia) | congruence]|]); exact HH)|]). destruct Hx. }
  pose proof (ppi_keep_plh RT GOBJ AF AFP Σ6 m7 m7r (rt_live RT Σ6) (rt_frames RT Σ6) (bv_unsigned sp + -64) (pstr_L false ps pk pl1 pl2 pq1 pq2 pb2 (nb16 [] [] [] [] [])) pl1 pb1 6 (nb16 [(n4, H_OUTPUT)] [(n1, H_PROVIDER); (n2, H_VERSION); (n5, H_INPUT)] [] [] [(n3, H_FIPS); (n6, H_STRUCTURE)]) ART7 PRES7 (fun e He => He) HLW7 REPa7 INCaB NOTa) as REPa7r.
  clear INCaB NOTa.
  assert (INCa8 : incl (plh_L pl1 pb1 (nb16 [(n4, H_OUTPUT)] [(n1, H_PROVIDER); (n2, H_VERSION); (n5, H_INPUT)] [] [] [(n3, H_FIPS); (n6, H_STRUCTURE)])) (rt_live RT Σ7)).
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [lv_in LV7|]). destruct Hx. }
  pose proof (SEGP Σ7 m7r m8 _ _ _ _ _ _ ART7r SP07 INCa8 MU8 LOa REPa7r) as REPa8.
  pose proof (ppi_keep_cells RT GOBJ AF AFP Σ6 m7 m7r (rt_live RT Σ6) (rt_frames RT Σ6) (bv_unsigned sp + -64) (pstr_L false ps pk pl1 pl2 pq1 pq2 pb2 (nb16 [] [] [] [] [])) pq1 56 pq1 _ ART7 PRES7 (fun e He => He) HLW7 ltac:(lv_in LV6) ltac:(clear; lia) ltac:(cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst]; intros HH; repeat (destruct HH as [HH|HH]; [apply pair_equal_spec in HH; destruct HH as [HHa HHn]; first [discriminate HHn | (revert HHn; clear; lia) | congruence]|]); exact HH) Q1C7 ltac:(clear; lia) ltac:(unfold sk_cells; cbn; clear; lia)) as Q1C7r.
  pose proof (SEGC Σ7 m7r m8 _ _ pq1 56 _ _ ART7r SP07 ltac:(lv_in LV7) MU8 LOa Q1C7r ltac:(unfold sk_cells; cbn; clear; lia)) as Q1C8.
  pose proof (ppi_keep_cells RT GOBJ AF AFP Σ6 m7 m7r (rt_live RT Σ6) (rt_frames RT Σ6) (bv_unsigned sp + -64) (pstr_L false ps pk pl1 pl2 pq1 pq2 pb2 (nb16 [] [] [] [] [])) D5 48 D5 _ ART7 PRES7 (fun e He => He) HLW7 ltac:(lv_in LV6) ltac:(clear; lia) ltac:(cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst]; intros HH; repeat (destruct HH as [HH|HH]; [apply pair_equal_spec in HH; destruct HH as [HHa HHn]; first [discriminate HHn | (revert HHn; clear; lia) | congruence]|]); exact HH) D1C7 ltac:(clear; lia) ltac:(cbn; clear; lia)) as D1C7r.
  pose proof (SEGC Σ7 m7r m8 _ _ D5 48 _ _ ART7r SP07 ltac:(lv_in LV7) MU8 LOa D1C7r ltac:(cbn; clear; lia)) as D1C8.
  clear CELL7r PSC7r LKC7r REPa7r REPb7r Q1C7r Q2C7r ENV7r PRES7 HLW7 CELL7 PSC7 LKC7 REPa7 REPb7 Q1C7 Q2C7 INCa7 INCb7 STD7.

  (* [comment removed for export] *)
  pose proof STD8 as (ART8 & _).
  assert (HLW8 : incl ((D7, 8 * 4) :: pstr_L false ps pk pl1 pl2 pq1 pq2 pb2 (nb16 [] [] [] [(n7, H_YES)] [])) (rt_live RT Σ7)).
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [lv_in LV7|]). destruct Hx. }
  eapply (CALLK Σ7 m8 [(n7, 24); (D7, 32); (r7, 19); (n6, 24); (r6, 25); (n5, 24); (D5, 48); (r5, 21); (n4, 24); (r4, 22); (n3, 24); (r3, 20); (n2, 24); (r2, 23); (n1, 24); (r1, 24)] [(n7, 24); (D7, 32); (r7, 19); (n6, 24); (r6, 25); (n5, 24); (D5, 48); (r5, 21); (n4, 24); (r4, 22); (n3, 24); (r3, 20); (n2, 24); (r2, 23); (n1, 24); (r1, 24)] 7 (Z_to_bv 8 1) j SITE_ppi_val2 0 A_NO 1 (PPI_TAB + 48) (PPI_TAB_SH + 6) 2 (rt_live RT Σ7) ((D7, 8 * 4) :: pstr_L false ps pk pl1 pl2 pq1 pq2 pb2 (nb16 [] [] [] [(n7, H_YES)] []))
            (ppi_Qroom RT canary false s_no ps pk pl1 pl2 6 1 pq1 pq2 pb2 1 (nb16 [] [] [] [(n7, H_YES)] []) D7 1 4 (Z_to_bv 64 0) (Z_to_bv 64 2146284) (Z_to_bv 64 2146368) (Z_to_bv 64 2146328)) STD8).
  { cbn [length]. clear. lia. }
  { clear. lia. }
  { unfold PPI_SITES. wp_in_lit. }
  { unfold PPI_CALLS. wp_in_lit. }
  { unfold SITE_ppi_val2. clear. lia. }
  { reflexivity. }
  { exact LV7. }
  { exact (fun e He => He). }
  { exact HLW8. }
  { intros x Hx. cbn [pstr_L plh_L nb16 concat app map In t_of q_of fst] in Hx. repeat (destruct Hx as [<-|Hx]; [first [left; unfold PSD; solve [wp_in_lit] | right; solve [wp_in_lit]]|]). destruct Hx. }
  { intros u0 u1 u2 u4 u5 u6 u7 v3 v4 v5 v6 F1 fc1 GP.
    eapply cps_conseq; [eapply (C_PSTR_R Σ7 PMc (Z_to_bv 64 SITE_ppi_val2) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0 u1 u2 sp (Z_to_bv 64 PPI_CTX) (Z_to_bv 64 PPI_CTX) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 A_NO) u4 u5 u6 u7 (Z_to_bv 64 1) (Z_to_bv 64 (PPI_TAB + 48)) (Z_to_bv 64 (PPI_TAB_SH + 6)) (Z_to_bv 64 (-48)) s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F1 fc1 m8 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary false A_NO A_NO (Z.of_nat (length s_no) + 1) s_no (repeat (Z_to_bv 8 0) 5) ps pk pl1 pl2 6 1 pq1 pq2 pb2 1 (nb16 [] [] [] [(n7, H_YES)] []) D7 1 4 1)
                       | intros c0 H0; exact H0
                       | intros c0 H0; exact (ppi_of_room RT PMc sp gp tp s6 s7 s8 s9 s10 s11 lo canary Σ7 m8 SITE_ppi_val2 1 (PPI_TAB + 48) (PPI_TAB_SH + 6) false s_no ps pk pl1 pl2 6 1 pq1 pq2 pb2 1 (nb16 [] [] [] [(n7, H_YES)] []) D7 1 4 _ _ _ _ c0 H0)].
    - apply (PRE Σ7 m8 SITE_ppi_val2 (Z_to_bv 8 1) false A_NO s_no 5%nat ps pk pl1 pl2 6 1 pq1 pq2 pb2 1 (nb16 [] [] [] [(n7, H_YES)] []) TPV GP lit_no GO_no CELL8
               ltac:(lv_in LV7) Aps PSC8 ltac:(clear; lia) ltac:(clear; lia) ltac:(lv_in LV7) Apk LKC8 REPb8 INCb8 ltac:(clear; lia)).
      + rewrite hash_no, bk_no. cbn [nth nb16]. repeat (constructor; [vm_compute; intros HH; discriminate HH|]). constructor.
      + cbn [q_of]. lv_in LV7.
      + cbn [q_of]. clear - Aq2. Z.div_mod_to_equations. lia.
    - exact Q2C8.
    - clear. lia.
    - clear. lia.
    - clear. lia.
    - clear. lia.
    - lv_in LV7.
    - destruct BKd7 as (_ & X & _). clear - X. Z.div_mod_to_equations. lia.
    - exact ND7.
    - exact D2C8.
  }
  { exact Hc8. }
  clear Hc8. intros Σ8 NEW m8r ? ? ? ? ? ? ? ? ? ? ? ? ? ? F9 fc9 c9 Hc9 STD9 PRES8 HQ LV8 SP08.
  destruct HQ as (r8 & n8 & junk8 & -> & (ENV8r & CELL8r & PSC8r & LKC8r & REPb8r) & Q2C8r & D2C8r & BKr8 & BKn8).
  change (Z.of_nat (length s_no) + 16) with 18 in *. cbn [app] in STD9, LV8. change (7 + 1) with 8 in STD9.
  rewrite LV7 in LV8.
  assert (EB : pstr_bks (nb16 [] [] [] [(n7, H_YES)] []) s_no n8 = (nb16 [] [] [(n8, H_NO)] [(n7, H_YES)] [])) by (unfold pstr_bks; rewrite hash_no, bk_no; reflexivity).
  rewrite EB in REPb8r. clear EB. unfold psd_bump in PSC8r. cbn [t_of q_of] in REPb8r, Q2C8r.
  change (1 + 1) with 2 in PSC8r.
  change (1 + 1) with 2 in REPb8r.
  change (1 + 1) with 2 in Q2C8r.
  change (Z.to_nat (8 * 4)) with 32%nat in D2C8r.
  (* [comment removed for export] *)
  eapply (ppi_exit RT GOBJ AF AFP Σ PMc m ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo outer canary PSD FDO MST ART0 CALL HSTK CTX UWC CGH Hfr Hlen HCR HPSD
            Σ8 m8r _ 8 (Z_to_bv 8 1) j _ _ _ _ _ _ _ _ _ _ _ _ _ _ F9 fc9 T c9 STD9 Hc9).
  clear Hc9. intros c10 Hc10 ST10.
  destruct STD9 as (ART9 & MI9 & _ & _ & _ & _ & FRS9 & SP09 & CG9 & CR9 & PR9 & ENV9).
  apply Hk. exists Σ8, r1, n1, r2, n2, r3, n3, r4, n4, r5, D5, n5, r6, n6, r7, D7, n7, r8, n8.
  split.
  { eapply ASTA_conseq; [exact Hc10|]. intros ms RS. exists m8r. split; [exact RS|].
    split; [split; [exact ART9| split; [exact MI9| exact ST10]]|].
    split; [| exact ENV9].
    intros a Ha Ho. apply (PR9 a Ha). clear - Ho. unfold pstr_W, PSD, rngs. cbn [map outside fst snd] in *. tauto. }
  split; [exact LV8|]. split; [exact FRS9|]. split; [exact SP09|]. split; [rewrite PC; exact CR9|].
  destruct BKr1 as (? & ? & ?). destruct BKn1 as (? & ? & ?). destruct BKr2 as (? & ? & ?). destruct BKn2 as (? & ? & ?). destruct BKr3 as (? & ? & ?). destruct BKn3 as (? & ? & ?).
  destruct BKr4 as (? & ? & ?). destruct BKn4 as (? & ? & ?). destruct BKr5 as (? & ? & ?). destruct BKd5 as (? & ? & ?). destruct BKn5 as (? & ? & ?). destruct BKr6 as (? & ? & ?).
  destruct BKn6 as (? & ? & ?). destruct BKr7 as (? & ? & ?). destruct BKd7 as (? & ? & ?). destruct BKn7 as (? & ? & ?). destruct BKr8 as (? & ? & ?). destruct BKn8 as (? & ? & ?).
  repeat (split; [assumption|]). exact CG9.
Qed.
End PPI.
