(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState ITree Nodes.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_defs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs R_prim_defs R_glue_defs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import R_thread R_m2s. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_poison R_sec_defs R_depot_defs R_unwind_defs R_asan_defs R_allocate2 RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_freelift RT_geo0 RT_fkit RT_malstate RT_freestate RT_maltail RT_malart RT_malcore_p RT_malcore_stmt RT_sys_stmt RT_vis RT_malsec_state RT_malsec_front RT_malsec_front2 RT_malsec_rev RT_malsec_pre RT_malsec_B RT_malsec_T RT_malsec_wf RT_malsec_art.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GWf.
Section Core.
Hypothesis GN : grant_node.
Hypothesis FN : fixed_commit_pab_node.

Section Back.
Variables (Σ : rtsA) (PMc : Model -> Prop) (mX : mem) (B : Z) (gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A : word)
          (F : bvmap 5 word) (fc : bv 32) (n lo P : Z) (tr : list Z) (tb : list word) (j0 : list byte).
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis Hn : 64512 < n <= 0x20001000.
Hypothesis Hlive : Z.of_nat (length (live Σ)) < LIVE_MAX.
Hypothesis Hcr : mcost n <= credit Σ.
Hypothesis HA : ART_A Σ mX.
Hypothesis MI : mem_inv asegs mX.
Hypothesis LOW : l_ACEIL (lay Σ) <= lo.
Hypothesis LOR : lo + 0x1000 <= B + -144.
Hypothesis SPT : B + 2144 <= USTACK_TOP.
Hypothesis SPA : B mod 16 = 0.
Hypothesis Htr : tr_ok tr.
Hypothesis Htrl : (1 <= length tr <= 30)%nat.
Hypothesis TRC : trc_cells B tr mX tb.
Hypothesis AFC : af_cells B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A mX j0.
Hypothesis HG : sgrant_ok Σ P (smsz n).
#[local] Notation L := (lay Σ).
#[local] Notation msz := (smsz n).
#[local] Notation D' := (fst (depot_put (dep Σ) tr)).
#[local] Notation Σf := (mal_sec Σ P n (fst (depot_put (dep Σ) tr))).

Definition sfin (ms : machine_state) : Prop :=
  exists mA m2 : mem, bfacts Σ mX B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A n P tr tb j0 mA
    /\ munch (W_1 Σ B n P) mA m2 /\ wmono asegs mA m2 /\ smid_facts Σ n P m2
    /\ sl_post Σ m2 B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A fc n lo P tr ms.

Lemma sm_setting : forall (mA m2 : mem), bfacts Σ mX B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A n P tr tb j0 mA ->
  munch (W_1 Σ B n P) mA m2 -> wmono asegs mA m2 -> smid_facts Σ n P m2 ->
  ART_A Σ mA /\ stk asegs m2 P (P + msz) /\ stk asegs m2 (shad P) (shad (P + msz))
  /\ shdr m2 P msz (needed2 n) (Z.of_nat (length (sec Σ)))
  /\ af_cells B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A m2 j0 /\ trc_cells B tr m2 tb.
Proof using Hn HA LOW LOR SPT HG Htrl.
  intros mA m2 BF MU1 WM1 SF. destruct BF as (HAA & MIA & WMA & CLA & VIA & FRA & AFA & TRA).
  destruct SF as (HD & SK & _).
  pose proof (sb_geo Σ mX B n lo P Hn HA LOW LOR SPT HG) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14
                                                              & Q15 & Q16 & Q17 & Q18 & Q19 & Q20 & Q21).
  pose proof (rv_shad Σ mX P n HA HG Hn) as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
  assert (DS : forall a k, l_ACEIL L + 0x1000 <= a -> disjoint_from (W_1 Σ B n P) a k -> True) by (intros; exact I).
  split; [exact HAA|]. split; [exact SK|].
  split; [exact (sb_shad_stk Σ mX B n lo P Hn HA LOW LOR SPT HG m2 (vis_rep_wmono _ mA m2 VIA WM1))|].
  split; [exact HD|].
  assert (DB : forall a k, B + -144 <= a -> disjoint_from (W_1 Σ B n P) a k).
  { intros a k Ha. unfold W_1, W_1s. cbn [disjoint_from]. unfold INST, g_instance, SEGTOP_A, K_HIGH_SHADOW_hi, SHB in *.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  split; [apply (af_transport B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A tr Htrl _ mA m2 j0 AFA MU1 WM1); apply DB; lia|].
  destruct TRA as (T1 & T2 & T3). split; [|split; [|exact T3]].
  - apply (rw_cells_transport asegs _ mA m2 _ _ T1 MU1 WM1). apply DB. lia.
  - apply (u64arr_transport asegs _ mA m2 _ _ T2 MU1 WM1). apply DB. lia.
Qed.

Lemma sm_small : forall Σ1,
  cps asegs (ASTA RTA Σ1 PMc (smid Σ mX B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A F fc n lo P tr tb j0))
            (ASTA RTA Σ1 PMc sfin).
Proof using MST Hn HA LOW LOR SPT SPA Htr Htrl HG.
  intros Σ1. apply (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rt_allow RTA Σ1) _ _ _ (fl_ASTA_mat_stable Σ1 PMc MST)).
  intros ms (mA & m2 & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & BF & -> & MU1 & WM1 & MI2 & ST2 & SF).
  destruct (sm_setting mA m2 BF MU1 WM1 SF) as (HAA & SKM & SST & HDR & AF2 & TRC2).
  eapply evt_mono.
  { apply (sl_p2a Σ mA m2 B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A F fc n lo P tr j0 Hn HAA HG LOW LOR SPT SPA Htr Htrl
             MU1 WM1 SKM SST HDR _ (sl_psS Σ mA m2 B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A F fc n lo P tr j0 Hn HAA HG LOW LOR
                                      SPT SPA Htrl MU1 WM1 SKM SST)
             t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 tb MI2 ST2 AF2 TRC2). }
  intros ms' HP. exists mA, m2. split; [exact BF|]. split; [exact MU1|]. split; [exact WM1|]. split; [exact SF | exact HP].
Qed.

Lemma sm_fin : forall Σ1 c, rtA_allow Σ1 = shw P n :: rtA_allow Σ -> rt_maps Σ1 = rt_maps Σf -> rt_eager Σ1 <= rt_eager Σf -> lay Σ1 = L ->
  ASTA RTA Σ1 PMc sfin c -> core_post fc Σ PMc B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A n lo mX c.
Proof using Hn Hlive Hcr HA LOW LOR SPT SPA Htr Htrl HG.
  intros Σ1 c EA EM EE EL Hc.
  pose proof (sl_dep Σ mX tr HA Htrl) as (OK & DI & OK' & DN2 & DT).
  assert (HDinv : dep_step (dep Σ) D') by (apply dep_inv_put; [exact DI | exact Htr | lia]).
  assert (WF : rt_wf Σf) by exact (mal_sec_wf Σ mX P n D' HA HG Hn Hlive Hcr OK' HDinv).
  pose proof (sb_geo Σ mX B n lo P Hn HA LOW LOR SPT HG) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14
                                                              & Q15 & Q16 & Q17 & Q18 & Q19 & Q20 & Q21).
  pose proof (sl_sizes n Hn) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13).
  pose proof (sl_room n Hn) as (SR & SR2).
  exists Σf, (P + 4096 + 2048). split.
  - unfold ASTA in *. change (rt_allow RTA Σf) with (shw P n :: rtA_allow Σ). change (rt_allow RTA Σ1) with (rtA_allow Σ1) in Hc. rewrite EA in Hc.
    eapply AST_conseq; [exact Hc | |].
    + intros ms (mA & m2 & BF & MU1 & WM1 & SF & (m' & RS' & MUT & WMT & MI' & ST' & SLF)).
      destruct BF as (HAA & MIA & WMA & CLA & VIA & FRA & AFA & TRA).
      destruct SF as (HD & SK & SH & SC & PAD & SJ & WS).
      destruct SLF as (HH & HL & US & RZ1 & RZ2 & DR).
      pose proof (sl_mS Σ mA m2 B n lo P Hn HAA HG LOW LOR SPT MU1 m' MUT) as MUS.
      pose proof (wmono_trans asegs _ _ _ WM1 WMT) as WMS.
      pose proof (sl_shad Σ mA B n lo P Hn HAA HG LOW LOR SPT) as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16).

      assert (DT' : forall a k, P <= a -> a + k <= P + 4096 -> disjoint_from (W_T Σ B n P) a k).
      { intros a k Ha1 Ha2. unfold W_T. cbn [disjoint_from].
        pose proof (sl_apart Σ mA n P Hn HAA HG) as (A1 & _ & A3 & A4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A19 & _).
        pose proof (sl_geo Σ mA B n lo P Hn HAA HG LOW LOR SPT) as (G1 & G2 & G3 & G4 & _).
        unfold apart in *.
        split; [clear - Ha2; lia|].
        split; [clear - A19 Ha1 Ha2 H1 H3 H4 G4; unfold SEGTOP_A, SHB, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *; destruct A19; lia|].
        split; [clear - A1 Ha1 Ha2 G4; destruct A1; lia|]. split; [clear - G1 Ha1; unfold SEGTOP_A in *; lia|].
        split; [clear - A3 Ha1 Ha2 G4; destruct A3; lia|]. split; [clear - A4 Ha1 Ha2 G4; destruct A4; lia|].
        split; [clear - G3 G4 Ha2; lia | exact I]. }
      assert (HD' : shdr m' P msz (needed2 n) (Z.of_nat (length (sec Σ)))).
      { unfold shdr in *. apply (rw_cells_transport asegs _ m2 m' _ _ HD MUT WMT). cs_size. apply DT'; lia. }
      assert (SH' : bytes_at asegs m' (shad P) (farun 512)).
      { destruct SH as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
        apply (bytes_at_transport asegs _ m2 m' _ _ Hb MUT). rewrite repeat_length. unfold W_T. cbn [disjoint_from].
        pose proof (sl_apart Σ mA n P Hn HAA HG) as (A1 & _ & A3 & A4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A17 & A18 & A19 & A20 & _).
        repeat match goal with |- _ /\ _ => split end; try exact I; unfold SEGTOP_A, SHB, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *;

          first [ clear - A19 H1 H2 H3 H4 Q13; destruct A19; lia | clear - A20 H2 H3 H4 Q9 Q13; destruct A20; lia
                | clear - A17 H2 H3 H4 Q13; assert (M8 : 512 <= msz / 8) by (apply Z.div_le_lower_bound; lia);
                  destruct A17; change (2 ^ 20) with 1048576; lia
                | clear - A18 H2 H3 H4 Q13; assert (M8 : 512 <= msz / 8) by (apply Z.div_le_lower_bound; lia);
                  destruct A18; change (2 ^ 23) with 8388608; lia
                | clear - H2 H3 H4 Q8 Q13; lia | lia ]. }
      assert (IMGT : forall a k, 0x10000 <= a -> a + k <= INST + 0x2d0 -> disjoint_from (W_T Σ B n P) a k).
      { intros a k Ha1 Ha2. unfold W_T. cbn [disjoint_from].
        pose proof (sl_geo Σ mA B n lo P Hn HAA HG LOW LOR SPT)
          as (G1 & _ & G3 & G4 & _ & _ & G7 & _ & _ & _ & _ & G12 & _ & _ & _ & _ & G17 & G18 & G19 & G20 & _).
        pose proof (sl_objs Σ mA B n lo P Hn HAA HG LOW LOR SPT) as (_ & _ & _ & O4).
        unfold INST, g_instance, SEGTOP_A, SHB in *.
        split; [clear - G1 Ha2; lia|]. split; [clear - H1 H3 Ha2; lia|]. split; [clear - O4 Ha1 Ha2; destruct O4; lia|].
        split; [clear - Ha2; lia|]. split; [clear - G17 Ha2; lia|]. split; [clear - G19 Ha2; lia|]. split; [clear - G7 Ha2; lia | exact I]. }
      unfold sec_core, sec_pad, sec_junk in SC, PAD, SJ. destruct SC as (C1 & C2 & C3).
      destruct SJ as ((b & jj & w1 & w2 & w3 & w4 & J1) & (bl & Hbl & J2) & (ga & gm & J3)).
      assert (SC' : sec_core m' (l_PAB L) 0x4000 (Z.of_nat (length (sec Σ)) + 1)).
      { split; [|split].
        - apply (rw_cells_transport asegs _ m2 m' _ _ C1 MUT WMT). cs_size. apply IMGT; unfold i_sec_chunks, INST, g_instance; lia.
        - apply (rw_cells_transport asegs _ m2 m' _ _ C2 MUT WMT). cs_size. apply IMGT; unfold i_sec_nres, INST, g_instance; lia.
        - apply (rw_cells_transport asegs _ m2 m' _ _ C3 MUT WMT). cs_size. apply IMGT; unfold i_sec_mutex, INST, g_instance; lia. }
      assert (PAD' : sec_pad m').
      { apply (rw_cells_transport asegs _ m2 m' _ _ PAD MUT WMT). cs_size. apply IMGT; unfold i_sec_mutex, INST, g_instance; lia. }
      assert (SJ' : sec_junk m').
      { split; [exists b, jj, w1, w2, w3, w4; apply (rw_cells_transport asegs _ m2 m' _ _ J1 MUT WMT); cs_size; apply IMGT;
                unfold i_sec_sorted, INST, g_instance; lia|].
        split; [exists bl; split; [exact Hbl|]; apply (u64arr_transport asegs _ m2 m' _ _ J2 MUT WMT); rewrite Hbl; apply IMGT;
                unfold i_sec_bylog, INST, g_instance; lia|].
        exists ga, gm. apply (rw_cells_transport asegs _ m2 m' _ _ J3 MUT WMT). cs_size. apply IMGT; unfold i_gstat_alloc, INST, g_instance; lia. }
      assert (WS' : exists ws, u64arr asegs m' (l_PAB L) ws /\ Z.of_nat (length ws) = 0x4000
                             /\ firstn (length (sec Σ) + 1) ws = map (fun s => Z_to_bv 64 (s_mb s)) (sec Σ ++ [sec_new P n])).
      { destruct WS as (ws & W1 & W2 & W3). exists ws. split; [|split; [exact W2 | exact W3]].
        apply (u64arr_transport asegs _ m2 m' _ _ W1 MUT WMT). rewrite W2. unfold W_T. cbn [disjoint_from].
        pose proof (sl_apart Σ mA n P Hn HAA HG) as (_ & _ & _ & _ & _ & A6 & _ & _ & _ & _ & _ & _ & A13 & _ & A15 & A16 & _ & _ & _ & _ & _ & A22).
        repeat match goal with |- _ /\ _ => split end; try exact I; unfold SEGTOP_A, SHB, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, apart in *;

          first [ clear - A6 Q20; destruct A6; lia | clear - A22 H1 H2 H3 H4 Q13 Q20; destruct A22; lia | clear - A13 Q20; destruct A13; lia
                | clear - A15 Q20; destruct A15; lia | clear - A16 Q20; destruct A16; lia | lia ]. }
      assert (SKm : stk asegs m' P (P + msz)) by exact (stk_wmono m2 m' _ _ SK WMT).
      assert (SSm : stk asegs m' (shad P) (shad (P + msz)))
        by exact (stk_wmono mA m' _ _ (sb_shad_stk Σ mX B n lo P Hn HA LOW LOR SPT HG mA VIA) WMS).
      assert (HH' : ahdr m' (P + 4096 + 2032) n) by exact HH.
      assert (ART' : ART_A Σf m').
      { apply (mal_sec_ART Σ mA B n lo P D' Hn HAA HG LOW LOR SPT WF m' MUS WMS VIA HD' SKm SSm HH' HL SH' RZ1 US RZ2 SC' PAD' SJ' WS' DR).
        exact (mc_hash1 (dep Σ) tr DI). }
      exists m'. split; [exact RS'|]. split; [exact ART'|]. split; [exact MI'|].
      split; [exact (wmono_trans asegs _ _ _ WMA WMS)|]. split; [exact ST'|].
      split.
      { intros a Ha. rewrite (MUS a (ms_client Σ mA B n lo P D' Hn HAA HG LOW LOR SPT WF (bv_unsigned a) Ha)). exact (CLA a Ha). }
      split.
      { apply (stk_wr_at' m' _ _). pose proof (proj2 (stk_split asegs m' P (P + 4096 + 2048) (P + msz) SKm ltac:(lia))) as X.
        exact (proj1 (stk_split asegs m' (P + 4096 + 2048) (P + 4096 + 2048 + n) (P + msz) X ltac:(lia))). }
      apply acc_ushadow; [exact H16 | clear - Q11; unfold SEGTOP_A in *; lia | lia | exact US].
    + intros mo (HM & HP). split; [|exact HP]. cbn [ARTM RTA] in *. unfold ARTM_A in *. destruct HM as (M1 & M2 & M3 & M4 & M5).
      split; [rewrite <- EM; exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [lia|].
      unfold artm_sys, confined0 in *. rewrite EL in M5. exact M5.
  - cbn [rt_live rt_frames rt_sp0 rt_credit RTA]. unfold rtA_live, rtA_frames, rtA_sp0, rtA_credit, mal_sec.
    cbn [live frames lay credit ann sec_new s_ubeg s_mb]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [clear - Q11; unfold SEGTOP_A in *; lia|]. split.
    + apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [apply Z.divide_add_r; [|exists 256; reflexivity] | exists 128; reflexivity].
      apply (Z.divide_trans 16 4096); [exists 256; reflexivity | apply Z.mod_divide; [lia | exact Q5]].
    + unfold USTACK_TOP in *. lia.
Qed.

Lemma sm_tail : forall Σ1, rtA_allow Σ1 = shw P n :: rtA_allow Σ -> rt_maps Σ1 = rt_maps Σf -> rt_eager Σ1 <= rt_eager Σf -> lay Σ1 = L ->
  aw Σ1 = shw P n :: aw Σ ->
  cps asegs (ASTA RTA Σ1 PMc (smid Σ mX B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A F fc n lo P tr tb j0))
            (core_post fc Σ PMc B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A n lo mX).
Proof using FDO MST Hn Hlive Hcr HA LOW LOR SPT SPA Htr Htrl HG.
  intros Σ1 EA EM EE EL EW.
  pose proof (ART_wf Σ mX HA) as HW. pose proof HW as (_ & _ & _ & _ & _ & _ & (B1 & B2 & B3 & B4 & B5) & _).
  pose proof (sec_eager_room Σ n HW ltac:(lia) Hcr) as (R1 & R2).
  pose proof (ms_window Σ mX P n HA HG Hn) as (AW1 & AW2).
  eapply (cps_conseq asegs); [| intros c' Hc'; exact Hc' | intros c' Hc'; exact (sm_fin Σ1 c' EA EM EE EL Hc')].
  exact (sm_small Σ1).
Qed.

Theorem sm_back : cps asegs (ASTA RTA (saΣ Σ P n) PMc (fA Σ PMc mX B gp F fc n lo P))
                            (core_post fc Σ PMc B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A n lo mX).
Proof using GN FN FDO MST Hn Hlive Hcr HA MI LOW LOR SPT SPA Htr Htrl TRC AFC HG.
  pose proof (ART_wf Σ mX HA) as HW. pose proof HW as (HL & _ & _ & (_ & HN & _) & _ & _ & (B1 & B2 & B3 & B4 & B5) & _).
  pose proof (sec_count Σ HW) as HSC.
  pose proof (sec_eager_room Σ n HW ltac:(lia) Hcr) as (R1 & R2).
  eapply (cps_conseq asegs); [| intros c Hc; eapply AST_conseq; [exact Hc | | intros mo Hmo; exact Hmo];
                                intros ms Hms; exact (bp_pre Σ PMc mX B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A F fc n lo P tr tb j0
                                                         Hn HA MI LOW LOR SPT Htrl TRC AFC HG ms Hms) | intros c Hc; exact Hc].
  destruct HN as [E0|E4].
  -
    eapply (cps_seq asegs).
    { apply (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rt_allow RTA (saΣ Σ P n)) _ _ (sb1_st Σ mX B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A F fc n lo P tr tb j0) (fl_ASTA_mat_stable (saΣ Σ P n) PMc MST)).
      intros ms Hms. exact (sb_first_A Σ mX B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A F fc n lo P tr tb j0 Hn HA LOW LOR SPT HG ms Hms E0). }
    eapply (cps_seq asegs).
    { apply (FN (saΣ Σ P n) (spΣ Σ P n) PMc (sb1_st Σ mX B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A F fc n lo P tr tb j0) (fun ms' => exists ms, sb1_st Σ mX B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A F fc n lo P tr tb j0 ms
                                                          /\ ms' = nretA ms (eff_pab Σ))
               (l_PAB L + 8 * 0) 0x20000 FDO MST eq_refl eq_refl eq_refl).
      - rewrite rt_eager_sa, rt_eager_sp, E0. lia.
      - rewrite rt_eager_sp. exact R2.
      - exact HL.
      - cbn [aw saΣ]. change (shw P n :: aw Σ) with ([shw P n] ++ aw Σ). rewrite A_bytes_app.
        pose proof (ms_window Σ mX P n HA HG Hn) as (_ & AW2). lia.
      - lia.
      - reflexivity.
      - pose proof (sb_geo Σ mX B n lo P Hn HA LOW LOR SPT HG) as (_ & _ & _ & _ & _ & Q6 & _). rewrite Z.mul_0_r, Z.add_0_r. exact Q6.
      - cbn [lay saΣ]. lia.
      - cbn [lay saΣ]. lia.
      - intros ms Hms. destruct (sb1_regs Σ mX B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A F fc n lo P tr tb j0 ms Hms)
          as (X1 & X2 & X3 & X4 & X5 & X6).
        split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|]. split; [exact X6|].
        exists ms. split; [exact Hms | reflexivity]. }
    eapply (cps_seq asegs).
    { apply (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rt_allow RTA (spΣ Σ P n)) _ _ (smid Σ mX B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A F fc n lo P tr tb j0) (fl_ASTA_mat_stable (spΣ Σ P n) PMc MST)).
      intros ms' (ms & Hms & ->). exact (sb_first_B Σ mX B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A F fc n lo P tr tb j0 Hn HA LOW LOR SPT HG ms Hms). }
    apply (sm_tail (spΣ Σ P n)); [reflexivity | rewrite rt_maps_sp, rt_maps_mal; reflexivity | rewrite rt_eager_mal; lia | reflexivity | reflexivity].
  -
    eapply (cps_seq asegs).
    { apply (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rt_allow RTA (saΣ Σ P n)) _ _ (smid Σ mX B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A F fc n lo P tr tb j0) (fl_ASTA_mat_stable (saΣ Σ P n) PMc MST)).
      intros ms Hms. exact (sb_notfirst Σ mX B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A F fc n lo P tr tb j0 Hn HA LOW LOR SPT HG ms Hms
                              ltac:(rewrite E4; lia)). }
    apply (sm_tail (saΣ Σ P n)); [reflexivity | rewrite rt_maps_sa, rt_maps_mal; reflexivity
                                  | rewrite rt_eager_mal, rt_eager_sp, rt_eager_sa, E4; lia | reflexivity | reflexivity].
Qed.
End Back.

Theorem mal_core_sec : core_stmt_sec.
Proof using GN FN.
  unfold core_stmt_sec, core_case.
  intros Σ PMc mX B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc n lo tr tb j0
    FDO MST Hn0 Hn Hlive Hcr HA MI ST LOW LOR SPT SPA Htr Htrl TRC AFC.
  assert (Hn' : 64512 < n <= 0x20001000) by lia.
  eapply (cps_seq asegs); [exact (fc_front Σ PMc mX B gp t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc n lo FDO MST Hn' Hcr HA MI ST LOW LOR
                                    ltac:(lia) GN)|].
  apply (cps_ex asegs). intros P T c (HGP & Hc) Hk.
  exact (sm_back Σ PMc mX B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A F fc n lo P tr tb j0 FDO MST Hn' Hlive Hcr HA MI LOW LOR SPT SPA
           Htr Htrl TRC AFC HGP T c Hc Hk).
Qed.
End Core.
