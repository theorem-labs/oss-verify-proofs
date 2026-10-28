(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface D_defs D_kit R_sizeclass R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_quar_defs R_qput R_qenqueue R_qenqueue_N R_qenqueue_F R_asan_free R_prim_kit RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeA2 RT_freestmt RT_freeC RT_freeD RT_freeF RT_freeG RT_freeI RT_freeJ RT_freeL RT_refreekA RT_refreekC RT_refreekD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section NewG.
Variables (Σ : rtsA) (c : Z) (i : nat) (n : Z) (cal : list Z) (jB j0 : nat) (st0 : ckst) (usp : Z).
Hypothesis HW0 : rt_wf0 Σ.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hn : nth_error (r_st (pr Σ c)) i = Some (CkQuar n).
Hypothesis HCA : ca Σ 24 = cal ++ [Z.of_nat jB].
Hypothesis Hj0 : nth_error (r_st (pr Σ 24)) j0 = Some st0.
Hypothesis Hvar : (j0 = jB /\ st0 = CkIdle) \/ (st0 = CkBatch /\ In (p_abeg (l_SB (lay Σ)) 24 j0) (map fst (ql Σ))).
Hypothesis Hsp : l_ACEIL (lay Σ) + 0xFFB0 <= usp.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation b0 := (p_abeg (l_SB (lay Σ)) 24 j0).
#[local] Notation bB := (p_abeg (l_SB (lay Σ)) 24 jB).
#[local] Notation M := (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16).
#[local] Notation W := (W_E (l_T (lay Σ)) (p_abeg (l_SB (lay Σ)) 24 j0) (p_abeg (l_SB (lay Σ)) 24 jB) usp).

Lemma ng_geo_r : geo_ok Σ.
Proof using HW0. exact (geo_of_wf0 Σ HW0). Qed.

(* [comment removed for export] *)
Lemma ng_jB_r : nth_error (r_st (pr Σ 24)) jB = Some CkIdle.
Proof using HW0 HCA.
  clear - HW0 HCA. pose proof HW0 as (_ & HR & _). destruct HR as (_ & _ & R3 & _). destruct (R3 24 ltac:(lia)) as (_ & _ & C3).
  rewrite HCA in C3. pose proof (proj1 (Forall_forall _ _) C3 (Z.of_nat jB) ltac:(apply in_or_app; right; left; reflexivity)) as (_ & X).
  rewrite Nat2Z.id in X. exact X.
Qed.

Lemma ng_notD_r : ~ In (c, i) [(24, j0); (24, jB)].
Proof using HW0 HCA Hn Hj0 Hvar.
  pose proof ng_jB_r as HjB. clear - Hn Hj0 Hvar HjB. intros [E|[E|[]]]; injection E as <- <-.
  - rewrite Hn in Hj0. injection Hj0 as <-. destruct Hvar as [(_ & X)|(X & _)]; discriminate X.
  - rewrite HjB in Hn. discriminate Hn.
Qed.

(* [comment removed for export] *)
Theorem new_ART_gen_r : forall (m4 m' : mem), ARTc Σ m4 -> munch W m4 m' -> wmono bsegs m4 m' ->
  qcache_rep m' (qcacheT T) (ql Σ ++ [(bB, [(M, n)])]) -> pclass_rep T 24 (ca_init Σ) cal m' -> ARTc (enq_new Σ cal jB M n) m'.
Proof using HW0 Hc Hn HCA Hj0 Hvar Hsp.
  intros m4 m' ART4 MW WM QT PC24.
  pose proof ng_geo_r as HG. pose proof ng_jB_r as HjB. pose proof ng_notD_r as ND.
  pose proof (se_img_r Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWi. pose proof (se_Tz_r Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWt.
  pose proof (se_grant_r Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWg. pose proof (se_ris_r Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWr.
  pose proof (se_fa_r Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWf. pose proof (se_slot_r Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWs.
  pose proof (se_shad_slot_r Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWss. pose proof (se_shad_reg_r Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWsr.
  pose proof (se_shad_app_r Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWsa. pose proof (se_secmap_r Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWm.
  pose proof (se_geo_r Σ j0 jB st0 CkIdle HG Hj0 HjB) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16).
  pose proof (se_disj_r Σ HG) as (T5 & T4 & ATP).
  assert (RA : forall c', 1 <= c' <= 31 -> reg_avoid W SB c' (pr Σ c')).
  { intros c' Hc'. exact (kv_reg Σ W [] HG (ris_of_whole _ W [] HWr) (fun c0 a k Hc0 _ => HWf c0 a k Hc0)
                                 (fun c0 a k Hc0 _ => HWsr c0 a k Hc0) c' Hc' ltac:(intros [])). }
  destruct ART4 as (CR & PR & CA & CH & SR & QR & DR & FR & IR & SHR & VIS).
  apply ARTc_intro.
  - (* [comment removed for export] *)
    cbn [enq_new pop24 set_ql lay] in *.
    apply (consts_rep_frame L m4 m' CR); [|exact WM]. intros a Ha. apply MW.
    destruct (Z.eq_dec (bv_unsigned a) (T + 0xc60)) as [E|NE].
    + rewrite E. unfold W_E. cbn [outside]. clear - K4 K5 K6 K7 K8 K9 K10 K11 K12 K14 ATP Hsp. unfold rb, kUserCap in *.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
    + apply (kv_consts Σ W (TZ_E T) [] HWi HWt HWg); [apply Forall_forall; intros; exact I | unfold TZ_E; cbn; repeat split; try exact I; lia | exact Ha | exact NE].
  - (* [comment removed for export] *)
    intros c' Hc'. pose proof (PR c' Hc') as X. cbn [enq_new pop24 set_ql lay pr] in X |- *.
    destruct (Z.eqb_spec c' 24) as [->|Hcc].
    + exact (reg_rep_transport W _ 24 _ m4 m' (reg_rep_upd_r _ _ _ jB CkBatch m4 X) MW WM (reg_avoid_upd _ _ _ _ _ _ (RA 24 ltac:(lia)))).
    + exact (reg_rep_transport W _ c' _ m4 m' X MW WM (RA c' Hc')).
  - (* [comment removed for export] *)
    intros c' Hc'. pose proof (CA c' Hc') as X. cbn [enq_new pop24 set_ql lay pr ca ca_init] in X |- *.
    destruct (Z.eqb_spec c' 24) as [->|Hcc]; [exact PC24|].
    apply (pclass_rep_transport W _ c' _ _ m4 m' X MW WM). apply (kv_pclass Σ W (TZ_E T) HWt c' Hc').
    unfold TZ_E, pc_addr, cacheT. cbn [disjoint_from]. clear - Hc' Hcc. repeat split; try exact I; lia.
  - (* [comment removed for export] *)
    destruct CH as [P Sc]. split.
    + intros c' i' st Hc' Hn'. cbn [enq_new set_ql lay] in Hn' |- *.
      destruct (pop24_st Σ cal jB c' i' st Hn') as [(-> & -> & ->)|(Hne & Hn1)].
      * (* [comment removed for export] *)
        pose proof (P 24 jB CkIdle ltac:(lia) HjB) as X.
        cbn [lay pchunk] in X |- *. destruct X as (_ & X).
        apply (pchunk_transport W _ 24 jB CkBatch m4 m' X MW WM). unfold pchunk_avoid. change (ClassSize 24) with 8192.
        change (Z.max 0 (8192 / 8)) with 1024. exact (se_shad_des_r Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp jB CkIdle HjB).
      * pose proof (P c' i' st Hc' Hn1) as X. cbn [lay] in X, Hn1 |- *.
        assert (HD : (c' = 24 /\ i' = j0) \/ ~ In (c', i') [(24, j0); (24, jB)]).
        { destruct (Z.eq_dec c' 24) as [->|X1]; [destruct (Nat.eq_dec i' j0) as [->|X2]; [left; split; reflexivity|]|].
          - right. intros Hin. destruct Hin as [E|[E|[]]]; injection E as E; [exact (X2 (eq_sym E))|].
            destruct Hne as [Y|Y]; [exact (Y eq_refl) | exact (Y (eq_sym E))].
          - right. intros Hin. apply X1. destruct Hin as [E|[E|[]]]; injection E; auto. }
        destruct HD as [(-> & ->)|Hnin].
        -- (* [comment removed for export] *)
           rewrite Hj0 in Hn1. injection Hn1 as Est. destruct Hvar as [(E & _)|(E0 & _)]; [destruct Hne as [Y|Y]; [exfalso; exact (Y eq_refl) | exfalso; exact (Y E)]|].
           rewrite <- Est, E0 in X |- *.
           apply (pchunk_transport W _ 24 j0 _ m4 m' X MW WM). unfold pchunk_avoid. change (ClassSize 24) with 8192.
           change (Z.max 0 (8192 / 8)) with 1024. exact (se_shad_des_r Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp j0 st0 Hj0).
        -- apply (pchunk_transport W _ c' i' _ m4 m' X MW WM). exact (kv_pchunk Σ W _ HG HWs HWss c' i' st Hc' Hn1 Hnin).
    + intros k s Hk. cbn [enq_new pop24 set_ql sec] in Hk |- *.
      apply (schunk_transport W k s m4 m' (Sc k s Hk) MW WM). exact (kv_schunk Σ W [] HG HWsa HWm k s Hk ltac:(intros [])).
  - (* [comment removed for export] *)
    cbn [enq_new pop24 set_ql] in *.
    exact (sec_rep_transport W _ m4 m' SR MW WM (kv_sec Σ W [] HG HWi HWg ltac:(apply Forall_forall; intros; exact I))).
  - (* [comment removed for export] *)
    cbn [enq_new pop24 set_ql ql qg lay] in *.
    destruct QR as (_ & (QG & CG) & MX). split; [exact QT|]. split.
    + split; [apply (rw_cells_transport bsegs W m4 m' _ _ QG MW WM); cbn [cells_size csize Nat.add]; apply HWi; [unfold i_q_global, INST, g_instance; lia | unfold i_q_global, INST, g_instance, SEGTOP_A; lia | exact I]|].
      apply (qchain_transport W m4 m' _ CG MW WM). pose proof HW0 as (_ & _ & _ & _ & (_ & _ & QB & QN & _) & _).
      apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) QB b ltac:(apply in_or_app; right; exact Hb)) as (j & Hj & Eb). rewrite Eb.
      assert (HjjB : j <> jB) by (intros ->; rewrite HjB in Hj; discriminate Hj).
      assert (Hjj0 : j <> j0).
      { intros ->. destruct Hvar as [(E & _)|(_ & Hin)]; [exact (HjjB E)|].
        rewrite map_app in QN. apply NoDup_ListNoDup in QN. apply (fl_nodup_app_not_in _ _ _ QN Hin). rewrite <- Eb. apply in_map. exact Hb. }
      apply (HWs 24 j CkBatch); [lia | exact Hj | | lia | change (ClassSize 24) with 8192; lia].
      intros [E|[E|[]]]; injection E as E; [exact (Hjj0 (eq_sym E)) | exact (HjjB (eq_sym E))].
    + apply (rw_cells_transport bsegs W m4 m' _ _ MX MW WM). cbn [cells_size csize Nat.add].
      apply HWi; [unfold i_q_cmutex, INST, g_instance; lia | unfold i_q_cmutex, INST, g_instance, SEGTOP_A; lia | exact I].
  - (* [comment removed for export] *)
    cbn [enq_new pop24 set_ql lay dep] in *. pose proof HW0 as (_ & _ & _ & _ & _ & _ & _ & Dok & _).
    exact (dep_rep_transport W L (dep Σ) m4 m' DR Dok MW WM (kv_dep Σ W [] HWi ltac:(apply Forall_forall; intros; exact I)
             (se_grant67_r Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp))).
  - (* [comment removed for export] *)
    cbn [enq_new pop24 set_ql] in *.
    exact (fs_rep_transport W _ m4 m' FR MW WM (kv_fs Σ W [] (TZ_E T) [] HG HWi HWt HWg HWsa ltac:(apply Forall_forall; intros; exact I)
             ltac:(unfold TZ_E; cbn; repeat split; try exact I; lia))).
  - cbn [enq_new pop24 set_ql] in *. exact (ia_rep_transport W _ m4 m' IR MW WM (kv_ia W [] HWi ltac:(apply Forall_forall; intros; exact I))).
  - cbn [enq_new pop24 set_ql lay] in *. exact (shadow_rep_transport W _ m4 m' SHR MW WM (kv_shadow Σ W [] HG HWsa)).
  - exact (vis_rep_wmono _ m4 m' VIS WM).
Qed.

End NewG.
