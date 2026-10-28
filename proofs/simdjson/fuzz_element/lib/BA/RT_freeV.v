(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_defs D_kit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs R_prim_defs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import R_thread R_m2s. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_quar_defs R_qput R_qenqueue R_asan_free R_prim_kit RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeA2 RT_freestmt RT_freeC RT_freeD RT_freeF RT_freeG RT_freeI RT_freeS RT_freeT RT_freeU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GW}.
Section AppG.
Variables (Σ1 : rtsA) (M n : Z) (m : mem) (pre : list batch) (j0 : nat) (ents : list (Z * Z)) (usp : Z).
Hypothesis HW1 : rt_wf0 Σ1.
Hypothesis HP : pend_e Σ1 M n.
Hypothesis HQL : ql Σ1 = pre ++ [(p_abeg (l_SB (lay Σ1)) 24 j0, ents)].
Hypothesis Hj0 : nth_error (r_st (pr Σ1 24)) j0 = Some CkBatch.
Hypothesis HL : (length ents < 1021)%nat.
Hypothesis Hsp : l_ACEIL (lay Σ1) + 0x10000 <= usp.
#[local] Notation L := (lay Σ1).
#[local] Notation T := (l_T (lay Σ1)).
#[local] Notation SB := (l_SB (lay Σ1)).
#[local] Notation b0 := (p_abeg (l_SB (lay Σ1)) 24 j0).
#[local] Notation W := (W_E (l_T (lay Σ1)) (p_abeg (l_SB (lay Σ1)) 24 j0) (p_abeg (l_SB (lay Σ1)) 24 j0) usp).
#[local] Notation Wa := [(l_T (lay Σ1) + 80, l_T (lay Σ1) + 112); (p_abeg (l_SB (lay Σ1)) 24 j0, p_abeg (l_SB (lay Σ1)) 24 j0 + 8192); (usp - 2400, usp)].
#[local] Notation Σ2 := (set_ql Σ1 (pre ++ [(p_abeg (l_SB (lay Σ1)) 24 j0, ents ++ [(M, n)])])).

Theorem app_ART_g : forall (m4 m' : mem) (ql' : list batch), ARTc Σ1 m4 -> munch Wa m4 m' -> wmono asegs m4 m' ->
  qcache_rep m' (qcacheT T) ql' -> ARTc (set_ql Σ1 ql') m'.
Proof using HW1 HQL Hj0 HL Hsp.
  intros m4 m' ql' ART4 MU WM QT. pose proof (geo_of_wf0 Σ1 HW1) as HG. pose proof HW1 as (_ & _ & _ & _ & _ & _ & _ & Dok & _).
  assert (MW : munch W m4 m') by (apply (munch_weaken Wa _ m4 m'); [unfold W_E; clear; solve_sub_fp | exact MU]).
  pose proof (se_img Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWi. pose proof (se_Tz Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWt.
  pose proof (se_grant Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWg. pose proof (se_ris Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWr.
  pose proof (se_fa Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWf. pose proof (se_slot Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWs.
  pose proof (se_shad_slot Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWss. pose proof (se_shad_reg Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWsr.
  pose proof (se_shad_app Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWsa. pose proof (se_secmap Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWm.
  destruct ART4 as (CR & PR & CA & CH & SR & QR & DR & FR & IR & SHR & VIS).
  pose proof (g_grant Σ1 HG (l_T L) 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (GT1 & _ & GT3 & _).
  apply ARTc_intro; cbn [set_ql lay pr ca ca_init sec sec_nres aw ql qg dep fs0 fsc0 fs4 fs1 ia_init credit live frames ann] in *.
  -
    apply (consts_rep_frame L m4 m' CR); [|exact WM]. intros a Ha. apply MW.
    destruct (Z.eq_dec (bv_unsigned a) (T + 0xc60)) as [E|NE].
    + rewrite E. unfold W_E. cbn [outside]. pose proof (se_geo Σ1 j0 j0 CkBatch CkBatch HG Hj0 Hj0) as (_ & _ & _ & K4 & K5 & K6 & K7 & K8 & _ & _ & K11 & K12 & _ & K14 & _).
      pose proof (se_disj Σ1 HG) as (_ & _ & ATP). clear - K4 K5 K6 K7 K8 K11 K12 K14 ATP Hsp. unfold rb, kUserCap in *.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
    + apply (kv_consts Σ1 W (TZ_E T) [] HWi HWt HWg); [apply Forall_forall; intros; exact I | unfold TZ_E; cbn; repeat split; try exact I; lia | exact Ha | exact NE].
  -
    intros c' Hc'. pose proof (PR c' Hc') as X. cbn [pr lay set_ql] in X |- *.
    exact (reg_rep_transport W _ c' _ m4 m' X MW WM (kv_reg Σ1 W [] HG (ris_of_whole _ W [] HWr) (fun c0 a k Hc0 _ => HWf c0 a k Hc0) (fun c0 a k Hc0 _ => HWsr c0 a k Hc0) c' Hc' ltac:(intros []))).
  -
    intros c' Hc'. pose proof (CA c' Hc') as X. cbn [lay pr ca ca_init set_ql] in X |- *. destruct (Z.eq_dec c' 24) as [->|Hcc].
    + apply (pclass_rep_transport Wa _ 24 _ _ m4 m' X MU WM). unfold pclass_avoid, pc_addr, cacheT. cbn [disjoint_from].
      pose proof (se_geo Σ1 j0 j0 CkBatch CkBatch HG Hj0 Hj0) as (_ & _ & _ & K4 & K5 & K6 & K7 & K8 & _ & _ & K11 & K12 & _ & K14 & _).
      pose proof (se_disj Σ1 HG) as (_ & _ & ATP). clear - K4 K5 K6 K7 K8 K11 K12 K14 ATP Hsp. unfold rb, kUserCap in *.
      split; [lia|]. split; [lia|]. split; [lia | exact I].
    + apply (pclass_rep_transport W _ c' _ _ m4 m' X MW WM). apply (kv_pclass Σ1 W (TZ_E T) HWt c' Hc').
      unfold TZ_E, pc_addr, cacheT. cbn [disjoint_from]. clear - Hc' Hcc. repeat split; try exact I; lia.
  -
    destruct CH as [P Sc]. split.
    + intros c' i' st Hc' Hn'. pose proof (P c' i' st Hc' Hn') as X. cbn [lay pr set_ql] in X, Hn' |- *. pose proof Hn' as Hn0.
      { assert (HD : (c' = 24 /\ i' = j0) \/ ~ In (c', i') [(24, j0); (24, j0)]).
        { destruct (Z.eq_dec c' 24) as [->|X1]; [destruct (Nat.eq_dec i' j0) as [->|X2]; [left; split; reflexivity|]|].
          - right. intros Hin. apply X2. destruct Hin as [E|[E|[]]]; injection E; auto.
          - right. intros Hin. apply X1. destruct Hin as [E|[E|[]]]; injection E; auto. }
        destruct HD as [(-> & ->)|Hnin].
        --
           rewrite Hj0 in Hn0. injection Hn0 as <-. apply (pchunk_transport W _ 24 j0 _ m4 m' X MW WM). unfold pchunk_avoid. change (ClassSize 24) with 8192.
           change (Z.max 0 (8192 / 8)) with 1024. exact (se_shad_des Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp j0 CkBatch Hj0).
        -- apply (pchunk_transport W _ c' i' _ m4 m' X MW WM). exact (kv_pchunk Σ1 W _ HG HWs HWss c' i' st Hc' Hn0 Hnin). }
    + intros k s Hk. apply (schunk_transport W k s m4 m' (Sc k s Hk) MW WM). exact (kv_schunk Σ1 W [] HG HWsa HWm k s Hk ltac:(intros [])).
  -
    exact (sec_rep_transport W _ m4 m' SR MW WM (kv_sec Σ1 W [] HG HWi HWg ltac:(apply Forall_forall; intros; exact I))).
  -
    destruct QR as (_ & (QG & CG) & MX). split; [exact QT|]. split.
    + split; [apply (rw_cells_transport asegs W m4 m' _ _ QG MW WM); cbn [cells_size csize Nat.add]; apply HWi; [unfold i_q_global, INST, g_instance; lia | unfold i_q_global, INST, g_instance, SEGTOP_A; lia | exact I]|].
      apply (qchain_transport W m4 m' _ CG MW WM). pose proof HW1 as (_ & _ & _ & _ & (_ & _ & QB & QN & _) & _).
      apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) QB b ltac:(apply in_or_app; right; exact Hb)) as (j & Hj & Eb). rewrite Eb.
      assert (Hjne : j <> j0).
      { intros ->. rewrite HQL in QN. rewrite <- app_assoc, map_app in QN. cbn [app map fst] in QN. apply NoDup_ListNoDup in QN.
        apply (NoDup_remove_2 (map fst pre) (map fst (qg Σ1)) b0 QN). apply in_or_app. right. rewrite <- Eb. apply in_map. exact Hb. }
      apply (HWs 24 j CkBatch); [lia | exact Hj | intros [E|[E|[]]]; injection E as E; exact (Hjne (eq_sym E)) | lia | change (ClassSize 24) with 8192; lia].
    + apply (rw_cells_transport asegs W m4 m' _ _ MX MW WM). cbn [cells_size csize Nat.add].
      apply HWi; [unfold i_q_cmutex, INST, g_instance; lia | unfold i_q_cmutex, INST, g_instance, SEGTOP_A; lia | exact I].
  -
    exact (dep_rep_transport W L (dep Σ1) m4 m' DR Dok MW WM (kv_dep Σ1 W [] HWi ltac:(apply Forall_forall; intros; exact I)
             (se_grant67 Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp))).
  -
    exact (fs_rep_transport W _ m4 m' FR MW WM (kv_fs Σ1 W [] (TZ_E T) [] HG HWi HWt HWg HWsa ltac:(apply Forall_forall; intros; exact I)
             ltac:(unfold TZ_E; cbn; repeat split; try exact I; lia))).
  - exact (ia_rep_transport W _ m4 m' IR MW WM (kv_ia W [] HWi ltac:(apply Forall_forall; intros; exact I))).
  - exact (shadow_rep_transport W _ m4 m' SHR MW WM (kv_shadow Σ1 W [] HG HWsa)).
  - exact (vis_rep_wmono _ m4 m' VIS WM).
Qed.

Lemma app_enq_g : forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' : word)
    (F : bvmap 5 word) (fc : bv 32) (m4 : mem) (lo : Z),
  bv_unsigned sp = usp -> ARTc Σ1 m4 -> mem_inv asegs m4 -> wmono asegs m m4 ->
  stk asegs m4 lo (usp + -2208) -> l_ACEIL L <= lo -> lo + 0x10000 <= usp -> usp + 16 <= USTACK_TOP ->
  rt_pres (live Σ1) (frames Σ1) usp m m4 ->
  icpt_frame m4 usp ra s0 s1 s2 s3 s4 s5 ->
  qput_frame m4 (usp + -2208) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 0x83030) (Z_to_bv 64 usp)
    (Z_to_bv 64 (M + 16)) (Z_to_bv 64 0x82fc0) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (usp + -81)) s6 ->
  evt asegs (enq_post Σ2 (live Σ1) (frames Σ1) ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR (Z_to_bv 64 0x5fbd0) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 QUAR)
             (Z_to_bv 64 (T + 80)) (Z_to_bv 64 (T + 80)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2128))
             (Z_to_bv 64 M) (Z_to_bv 64 n) a5' a6' a7' (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (T + 208))
             (Z_to_bv 64 M) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 qenq_entry) fc None m4 (seg_rom asegs)).
Proof using HW1 HP HQL Hj0 HL Hsp.
  intros ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' F fc m4 lo
    Esp ART4 MI4 WM4 ST4 HLO HLO2 Husp RP4 ICF FR4.
  pose proof (geo_of_wf0 Σ1 HW1) as HG.
  pose proof (se_geo Σ1 j0 j0 CkBatch CkBatch HG Hj0 Hj0) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16).
  pose proof (se_disj Σ1 HG) as (T5 & T4 & ATP).
  assert (Hn1 : 1 <= n <= 2 ^ 28) by (pose proof HP as (QE & _); exact (pe_n Σ1 M n HW1 QE)).
  assert (RSP : 0 <= usp + -2208 < 2 ^ 64) by (clear - Hsp Husp K15; unfold USTACK_TOP, SHB in *; lia).
  pose proof (qwf_ql Σ1 HW1) as QWF. rewrite HQL in QWF.
  pose proof HW1 as (_ & _ & _ & _ & (Q1 & _) & _).
  pose proof ART4 as (CR & PR & CA & CH & SR & QR & DR & FR & IR & SHR & VIS).
  pose proof QR as (QT & _). cbn [ql lay] in QT. rewrite HQL in QT.
  rewrite HQL, <- qbytes_eq in Q1.
  eapply evt_mono.
  { apply (qenq_app_spec (Z_to_bv 64 0x5fbd0) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80))
             a5' a6' a7' (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 M)
             (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m4
             (T + 80) (T + 208) (usp + -2128) M n SB lo pre b0 ents);
      try assumption; rewrite ?(unsigned_lit (usp + -2208)) by exact RSP.
    all: try (clear - Hn1; lia).
    all: try exact ST4.
    all: try (clear - ATP K5 K6 K11; unfold r24, rb, kUserCap in *; lia).
    all: try (clear - K13; lia). all: try (clear - K1 K5; lia). all: try (clear - HLO2; lia).
    all: try (clear - K14 HLO; lia). all: try (clear - K4 K6 HLO; unfold r24; lia).
    all: try (clear - Q1 Hn1; unfold QMAX_L in *; lia).
    eapply Z.le_lt_trans; [apply Z.add_le_mono; [exact Q1 | exact (proj2 Hn1)] | reflexivity]. }
  intros ms5 P5. destruct P5 as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m5 & -> & MU5 & WM5 & MI5 & QR5 & _ & ST5).
  rewrite (unsigned_lit (usp + -2208)) in MU5, ST5 by exact RSP. rewrite (ret_pc_even 0x5fbd0) by (first [reflexivity | lia]).
  assert (MWa : munch [(T + 80, T + 112); (b0, b0 + 8192); (usp - 2400, usp)] m4 m5).
  { lazymatch type of MU5 with munch ?W5 _ _ => apply (munch_weaken W5 _ m4 m5); [clear - Hsp; solve_sub_fp | exact MU5] end. }
  unfold enq_post. exists (Z_to_bv 64 0x5fbd0), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, (Z_to_bv 64 n), (Z_to_bv 64 (usp + -2128)),
    (Z_to_bv 64 (T + 208)), (Z_to_bv 64 M), x11, x12, x13, x14, (Z_to_bv 64 usp), (Z_to_bv 64 (M + 16)), (Z_to_bv 64 0x82fc0), (Z_to_bv 64 1),
    (Z_to_bv 64 (usp + -2128)), (Z_to_bv 64 (usp + -81)), m5.
  split; [unfold enq_ret_st; rewrite Esp; reflexivity|].
  split; [exact (app_ART_g m4 m5 _ ART4 MWa WM5 QR5)|].
  destruct (app_wfx_e Σ1 M n pre j0 ents HW1 HP HQL HL) as (WX & WC).
  split; [exact WX|]. split; [exact WC|]. split; [exact MI5|]. split; [exact (wmono_trans asegs _ _ _ WM4 WM5)|].
  split; [rewrite Esp; exact ST5|].
  split.
  { rewrite Esp. intros a Ha. rewrite (MWa a); [exact (RP4 a Ha)|].
    assert (HO : outside (W_E (l_T (lay Σ1)) b0 b0 usp) (bv_unsigned a)).
    { apply (kv_client Σ1 _ [(24, j0); (24, j0)] [] [] usp HG
               (se_img Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) (se_grant Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp)
               (se_slot Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) (se_shad_app Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp)
               (se_secmap Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) (se_stack Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp)
               ltac:(apply Forall_forall; intros; exact I) (live Σ1)); [|exact Ha].
      intros p' n' Hin.
      pose proof HW1 as (_ & _ & HV & _). destruct HV as (_ & _ & V3 & _).
      destruct (V3 p' n' Hin) as [(c' & i' & Hc' & Hn' & ->)|(s & Hs & Hq & Hsn & ->)].
      + left. exists c', i'. split; [exact Hc'|]. split; [exact Hn'|]. split; [reflexivity|].
        intros [E|[E|[]]]; injection E as <- <-; rewrite Hj0 in Hn'; discriminate.
      + right. destruct (In_nth_error _ _ Hs) as (k & Hk'). exists k, s. split; [exact Hk'|]. split; [exact Hq|]. split; [exact Hsn|].
        split; [reflexivity | intros []]. }
    revert HO. apply sub_fp_covered. unfold W_E. cbn [all_covered covered]. clear - Hsp.
    split; [left; split; lia|]. split; [right; right; right; left; split; lia|]. split; [right; right; right; right; right; left; split; lia | exact I]. }
  split.
  { rewrite Esp. apply (icpt_frame_transport _ m4 m5 usp ra s0 s1 s2 s3 s4 s5 ICF MU5 WM5). cbn [disjoint_from].
    clear - K4 K5 K6 K7 K8 K11 K12 K14 Hsp. unfold rb, kUserCap in *. repeat split; try exact I; lia. }
  rewrite Esp. unfold qput_frame in FR4 |- *. apply (rw_cells_transport asegs _ m4 m5 _ _ FR4 MU5 WM5).
  cbn [disjoint_from cells_size csize Nat.add]. clear - K4 K5 K6 K7 K8 K11 K12 K14 Hsp. unfold rb, kUserCap in *. repeat split; try exact I; lia.
Qed.

End AppG.

End GWIN.
