(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Mem Frame Cells Step Arr Exec RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_quar_defs R_qput R_qenqueue R_asan_free R_prim_kit RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeA2 RT_freeC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition set_ql (Σ : rtsA) (l : list batch) : rtsA :=
  mkRtsA (lay Σ) (pr Σ) (ca Σ) (ca_init Σ) (sec Σ) (sec_nres Σ) (aw Σ) l (qg Σ) (dep Σ) (fs0 Σ) (fs2 Σ) (fs4 Σ) (fs1 Σ) (fs3 Σ) (ia_init Σ)
    (credit Σ) (live Σ) (frames Σ).

Lemma reg_avoid_upd : forall W SB c r i st, reg_avoid W SB c r -> reg_avoid W SB c (upd_reg r i st).
Proof. intros W SB c r i st H. unfold reg_avoid, upd_reg in *. cbn [r_muser r_mfa r_st r_fl]. rewrite upd_length. exact H. Qed.

(* [comment removed for export] *)
Lemma se_shad_des : forall (Σ : rtsA) j0 jB st0 stB usp, geo_ok Σ -> nth_error (r_st (pr Σ 24)) j0 = Some st0 ->
  nth_error (r_st (pr Σ 24)) jB = Some stB -> l_ACEIL (lay Σ) + 0x10000 <= usp ->
  forall j st, nth_error (r_st (pr Σ 24)) j = Some st ->
  disjoint_from (W_E (l_T (lay Σ)) (p_abeg (l_SB (lay Σ)) 24 j0) (p_abeg (l_SB (lay Σ)) 24 jB) usp) (shad (p_abeg (l_SB (lay Σ)) 24 j)) 1024.
Proof.
  intros Σ j0 jB st0 stB usp HG Hj0 HjB Hsp j st Hj.
  pose proof (se_geo Σ j0 jB st0 stB HG Hj0 HjB) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16).
  pose proof (se_disj Σ HG) as (T5 & T4 & ATP).
  pose proof (fk_slot Σ HG 24 j st ltac:(lia) Hj) as (Z1 & Z2 & Z3 & Z4). change (ClassSize 24) with 8192 in *.
  pose proof (shad_lo (p_abeg (l_SB (lay Σ)) 24 j) ltac:(clear - Z1 K1 K5; unfold rb in *; lia)) as Q1.
  pose proof (fk_shad_le2 (p_abeg (l_SB (lay Σ)) 24 j) 8192 ltac:(clear - Z1 K1 K5; unfold rb in *; lia) ltac:(lia)) as E1. change (8192 / 8) with 1024 in E1.
  pose proof (shad_hi (p_abeg (l_SB (lay Σ)) 24 j + 8192) ltac:(clear - Z1 Z2 Z3 K4 K5 K6 K16; unfold rb, kUserCap in *; lia)) as Q2.
  unfold W_E. cbn [disjoint_from].
  split; [clear - T4 Q1 Q2 E1; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia|].
  split; [clear - T4 Q1 Q2 E1; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia|].
  split; [clear - T4 Q1 Q2 E1; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia|].
  split; [clear - K3 K5 K7 Q2 E1; unfold K_HIGH_SHADOW_hi, SHB, rb in *; lia|].
  split; [clear - K3 K5 K9 Q2 E1; unfold K_HIGH_SHADOW_hi, SHB, rb in *; lia|].
  split; [clear - Q2 E1 K15 Hsp; unfold SHB in *; lia | exact I].
Qed.

(* [comment removed for export] *)
Lemma se_grant67 : forall (Σ : rtsA) j0 jB st0 stB usp, geo_ok Σ -> nth_error (r_st (pr Σ 24)) j0 = Some st0 ->
  nth_error (r_st (pr Σ 24)) jB = Some stB -> l_ACEIL (lay Σ) + 0x10000 <= usp ->
  forall j b gn a k, nth_error (startup_grants (lay Σ)) j = Some (b, gn) -> (j = 6 \/ j = 7)%nat -> b <= a -> a + k <= b + gn ->
  disjoint_from (W_E (l_T (lay Σ)) (p_abeg (l_SB (lay Σ)) 24 j0) (p_abeg (l_SB (lay Σ)) 24 jB) usp) a k.
Proof.
  intros Σ j0 jB st0 stB usp HG Hj0 HjB Hsp j b gn a k Hj Hjr H1 H2.
  pose proof (se_geo Σ j0 jB st0 stB HG Hj0 HjB) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16).
  pose proof (g_grant Σ HG b gn (nth_error_In _ _ Hj)) as (B1 & B2 & B3 & B4 & B5).
  assert (HT1 : apart b gn (l_T (lay Σ)) 4096).
  { pose proof (g_apart Σ HG 2 j (l_T (lay Σ), 4096) (b, gn) ltac:(lia) eq_refl Hj) as X. cbn [fst snd] in X. unfold apart in *. lia. }
  assert (HT2 : apart b gn (l_PRB (lay Σ)) 0x2000011000).
  { pose proof (g_apart Σ HG 0 j (l_PRB (lay Σ), 0x2000011000) (b, gn) ltac:(lia) eq_refl Hj) as X. cbn [fst snd] in X. unfold apart in *. lia. }
  unfold W_E. cbn [disjoint_from]. unfold apart in *.
  split; [clear - H1 H2 HT1; lia|]. split; [clear - H1 H2 HT1; lia|]. split; [clear - H1 H2 HT1; lia|].
  split; [clear - H1 H2 HT2 K5 K6 K7 K8 K11 K12; unfold rb, kUserCap in *; lia|].
  split; [clear - H1 H2 HT2 K5 K6 K9 K10 K11 K12; unfold rb, kUserCap in *; lia|].
  split; [clear - H2 B3 Hsp; lia | exact I].
Qed.

(* [comment removed for export] *)
Lemma qbytes_eq : forall bs, R_quar_defs.qbytes bs = RT_state.qbytes bs.
Proof.
  induction bs as [|[b ents] bs IH]; [reflexivity|]. unfold R_quar_defs.qbytes, RT_state.qbytes, qsum, qn, bsum in *. cbn [fold_right length snd] in *.
  rewrite IH. lia.
Qed.

(* [comment removed for export] *)
Lemma qwf_ql : forall Σ, rt_wf0 Σ -> qwf (l_SB (lay Σ)) (ql Σ).
Proof.
  intros Σ HW. pose proof (geo_of_wf0 Σ HW) as HG. destruct HW as (_ & HR & _ & HS & HQ & _).
  destruct HQ as (_ & _ & QB & QN & QL & QE & _ & _). pose proof (g_prb Σ HG) as (P1 & P2 & P3).
  split.
  - rewrite map_app in QN. apply NoDup_ListNoDup in QN. exact (NoDup_app_remove_r _ _ QN).
  - apply Forall_forall. intros b Hb. assert (Hb' : In b (ql Σ ++ qg Σ)) by (apply in_or_app; left; exact Hb).
    destruct (proj1 (Forall_forall _ _) QB b Hb') as (i & Hi & Eb).
    pose proof (g_slot_geo Σ HG 24 i CkBatch ltac:(lia) Hi) as (S1 & S2 & S3 & _). change (ClassSize 24) with 8192 in *.
    split; [|split; [|split; [|split]]].
    + rewrite Eb. unfold p_abeg. apply Z.mod_divide in P3; [|lia]. destruct P3 as [q Hq]. rewrite Hq.
      replace (q * 2 ^ 16 + 24 * 2 ^ 32 + Z.of_nat i * 8192) with ((q * 8 + 24 * 2 ^ 19 + Z.of_nat i) * 8192) by ring. apply Z.mod_mul. lia.
    + rewrite Eb. unfold r24, rb in *. lia.
    + rewrite Eb. unfold r24, rb, kUserCap in *. lia.
    + exact (proj1 (Forall_forall _ _) QL b Hb').
    + apply Forall_forall. intros e He. assert (Hq : In e (qents Σ)).
      { unfold qents. apply in_flat_map. exists b. split; [exact Hb' | exact He]. }
      destruct (proj1 (Forall_forall _ _) QE e Hq) as [(c & j & Hc & Hj & _)|(s & Hs & _ & Hn & _)].
      * destruct HR as (HR & _). pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
        pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hj)) as X. cbv beta iota in X. lia.
      * destruct HS as (_ & _ & _ & HSF & _). pose proof (proj1 (Forall_forall _ _) HSF s Hs) as (X & _). lia.
Qed.

(* [comment removed for export] *)
Lemma qcache_transport : forall W (m m' : mem) Q bs, qcache_rep m Q bs -> munch W m m' -> wmono ctasegs m m' ->
  disjoint_from W Q 32 -> Forall (fun b => disjoint_from W (fst b) 8192) bs -> qcache_rep m' Q bs.
Proof.
  intros W m m' Q bs (H1 & H2) MU WM D1 D2. split; [|exact (qchain_transport W m m' bs H2 MU WM D2)].
  apply (rw_cells_transport ctasegs W m m' _ _ H1 MU WM). cbn [cells_size csize Nat.add]. exact D1.
Qed.

Section App.
Variables (Σ : rtsA) (c : Z) (i : nat) (n : Z) (D' : depot) (pre : list batch) (j0 : nat) (ents : list (Z * Z)) (usp : Z).
Hypothesis HW0 : rt_wf Σ.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hn : nth_error (r_st (pr Σ c)) i = Some (CkAlloc n).
Hypothesis HQL : ql Σ = pre ++ [(p_abeg (l_SB (lay Σ)) 24 j0, ents)].
Hypothesis Hj0 : nth_error (r_st (pr Σ 24)) j0 = Some CkBatch.
Hypothesis Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation b0 := (p_abeg (l_SB (lay Σ)) 24 j0).
#[local] Notation Σ1 := (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) D').
#[local] Notation W := (W_E (l_T (lay Σ)) (p_abeg (l_SB (lay Σ)) 24 j0) (p_abeg (l_SB (lay Σ)) 24 j0) usp).
#[local] Notation Wa := [(l_T (lay Σ) + 80, l_T (lay Σ) + 112); (p_abeg (l_SB (lay Σ)) 24 j0, p_abeg (l_SB (lay Σ)) 24 j0 + 8192); (usp - 2400, usp)].

Let HG : geo_ok Σ := geo_of_wf Σ HW0.

Lemma ap_notD : ~ In (c, i) [(24, j0); (24, j0)].
Proof using Hn Hj0. clear - Hn Hj0. intros [E|[E|[]]]; injection E as <- <-; rewrite Hn in Hj0; discriminate. Qed.

(* [comment removed for export] *)
Theorem app_ART : forall (m4 m' : mem) (ql' : list batch), ARTc Σ1 m4 -> munch Wa m4 m' -> wmono ctasegs m4 m' ->
  qcache_rep m' (qcacheT T) ql' -> depot_ok D' (l_DNB L) (l_SSB L) (l_ACEIL L) -> ARTc (set_ql Σ1 ql') m'.
Proof.
  intros m4 m' ql' ART4 MU WM QT Dok.
  assert (MW : munch W m4 m') by (apply (munch_weaken Wa _ m4 m'); [unfold W_E; clear; solve_sub_fp | exact MU]).
  pose proof (se_img Σ j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWi. pose proof (se_Tz Σ j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWt.
  pose proof (se_grant Σ j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWg. pose proof (se_ris Σ j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWr.
  pose proof (se_fa Σ j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWf. pose proof (se_slot Σ j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWs.
  pose proof (se_shad_slot Σ j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWss. pose proof (se_shad_reg Σ j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWsr.
  pose proof (se_shad_app Σ j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWsa. pose proof (se_secmap Σ j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWm.
  destruct ART4 as (CR & PR & CA & CH & SR & QR & DR & FR & IR & SHR & VIS).
  pose proof (g_grant Σ HG (l_T L) 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (GT1 & _ & GT3 & _).
  apply ARTc_intro; cbn [set_ql lay pr ca ca_init sec sec_nres aw ql qg dep fs0 fs2 fs4 fs1 fs3 ia_init credit live frames free_p] in *.
  - (* [comment removed for export] *)
    apply (consts_rep_frame L m4 m' CR); [|exact WM]. intros a Ha. apply MW.
    destruct (Z.eq_dec (bv_unsigned a) (T + 0xc60)) as [E|NE].
    + rewrite E. unfold W_E. cbn [outside]. pose proof (se_geo Σ j0 j0 CkBatch CkBatch HG Hj0 Hj0) as (_ & _ & _ & K4 & K5 & K6 & K7 & K8 & _ & _ & K11 & K12 & _ & K14 & _).
      pose proof (se_disj Σ HG) as (_ & _ & ATP). clear - K4 K5 K6 K7 K8 K11 K12 K14 ATP Hsp. unfold rb, kUserCap in *.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
    + apply (kv_consts Σ W (TZ_E T) [] HWi HWt HWg); [apply Forall_forall; intros; exact I | unfold TZ_E; cbn; repeat split; try exact I; lia | exact Ha | exact NE].
  - (* [comment removed for export] *)
    intros c' Hc'. pose proof (PR c' Hc') as X. destruct (Z.eqb_spec c' c) as [->|Hcc].
    + cbn [pr lay set_ql free_p] in X |- *. rewrite Z.eqb_refl in X |- *. exact (reg_rep_transport W _ c _ m4 m' X MW WM (reg_avoid_upd _ _ _ _ _ _ (kv_reg Σ W [] HG (ris_of_whole _ W [] HWr) (fun c0 a k Hc0 _ => HWf c0 a k Hc0) (fun c0 a k Hc0 _ => HWsr c0 a k Hc0) c Hc ltac:(intros [])))).
    + cbn [pr lay set_ql free_p] in X |- *. rewrite (proj2 (Z.eqb_neq c' c) Hcc) in X |- *. exact (reg_rep_transport W _ c' _ m4 m' X MW WM (kv_reg Σ W [] HG (ris_of_whole _ W [] HWr) (fun c0 a k Hc0 _ => HWf c0 a k Hc0) (fun c0 a k Hc0 _ => HWsr c0 a k Hc0) c' Hc' ltac:(intros []))).
  - (* [comment removed for export] *)
    intros c' Hc'. pose proof (CA c' Hc') as X. cbn [lay pr ca ca_init free_p set_ql] in X |- *. destruct (Z.eq_dec c' 24) as [->|Hcc].
    + apply (pclass_rep_transport Wa _ 24 _ _ m4 m' X MU WM). unfold pclass_avoid, pc_addr, cacheT. cbn [disjoint_from].
      pose proof (se_geo Σ j0 j0 CkBatch CkBatch HG Hj0 Hj0) as (_ & _ & _ & K4 & K5 & K6 & K7 & K8 & _ & _ & K11 & K12 & _ & K14 & _).
      pose proof (se_disj Σ HG) as (_ & _ & ATP). clear - K4 K5 K6 K7 K8 K11 K12 K14 ATP Hsp. unfold rb, kUserCap in *.
      split; [lia|]. split; [lia|]. split; [lia | exact I].
    + apply (pclass_rep_transport W _ c' _ _ m4 m' X MW WM). apply (kv_pclass Σ W (TZ_E T) HWt c' Hc').
      unfold TZ_E, pc_addr, cacheT. cbn [disjoint_from]. clear - Hc' Hcc. repeat split; try exact I; lia.
  - (* [comment removed for export] *)
    destruct CH as [P Sc]. split.
    + intros c' i' st Hc' Hn'. pose proof (P c' i' st Hc' Hn') as X. cbn [lay pr free_p set_ql] in X, Hn' |- *. destruct (fp_st Σ c i n Hc c' i' st Hn') as [(-> & -> & ->)|(Hne & Hn0)].
      * apply (pchunk_transport W _ c i _ m4 m' X MW WM). apply (kv_pchunk_gen Σ W [(24, j0); (24, j0)] HG HWs HWss c i (CkAlloc n) (CkQuar n) Hc Hn ap_notD).
        intros n' [E|E]; [discriminate E|]. injection E as <-. pose proof HG as (_ & HR & _). destruct HR as (HR & _).
        pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
        pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hn)) as Y. cbv beta iota in Y. clear - Y; lia.
      * assert (HD : (c' = 24 /\ i' = j0) \/ ~ In (c', i') [(24, j0); (24, j0)]).
        { destruct (Z.eq_dec c' 24) as [->|X1]; [destruct (Nat.eq_dec i' j0) as [->|X2]; [left; split; reflexivity|]|].
          - right. intros Hin. apply X2. destruct Hin as [E|[E|[]]]; injection E; auto.
          - right. intros Hin. apply X1. destruct Hin as [E|[E|[]]]; injection E; auto. }
        destruct HD as [(-> & ->)|Hnin].
        --
           rewrite Hj0 in Hn0. injection Hn0 as <-. apply (pchunk_transport W _ 24 j0 _ m4 m' X MW WM). unfold pchunk_avoid. change (ClassSize 24) with 8192.
           change (Z.max 0 (8192 / 8)) with 1024. exact (se_shad_des Σ j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp j0 CkBatch Hj0).
        -- apply (pchunk_transport W _ c' i' _ m4 m' X MW WM). exact (kv_pchunk Σ W _ HG HWs HWss c' i' st Hc' Hn0 Hnin).
    + intros k s Hk. apply (schunk_transport W k s m4 m' (Sc k s Hk) MW WM). exact (kv_schunk Σ W [] HG HWsa HWm k s Hk ltac:(intros [])).
  - (* [comment removed for export] *)
    exact (sec_rep_transport W _ m4 m' SR MW WM (kv_sec Σ W [] HG HWi HWg ltac:(apply Forall_forall; intros; exact I))).
  - (* [comment removed for export] *)
    destruct QR as (_ & (QG & CG) & MX). split; [exact QT|]. split.
    + split; [apply (rw_cells_transport ctasegs W m4 m' _ _ QG MW WM); cbn [cells_size csize Nat.add]; apply HWi; [unfold i_q_global, INST, g_instance; lia | unfold i_q_global, INST, g_instance, SEGTOP_A; lia | exact I]|].
      apply (qchain_transport W m4 m' _ CG MW WM). pose proof HW0 as (_ & _ & _ & _ & (_ & _ & QB & QN & _) & _).
      apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) QB b ltac:(apply in_or_app; right; exact Hb)) as (j & Hj & Eb). rewrite Eb.
      assert (Hjne : j <> j0).
      { intros ->. rewrite HQL in QN. rewrite <- app_assoc, map_app in QN. cbn [app map fst] in QN. apply NoDup_ListNoDup in QN.
        apply (NoDup_remove_2 (map fst pre) (map fst (qg Σ)) b0 QN). apply in_or_app. right. rewrite <- Eb. apply in_map. exact Hb. }
      apply (HWs 24 j CkBatch); [lia | exact Hj | intros [E|[E|[]]]; injection E as E; exact (Hjne (eq_sym E)) | lia | change (ClassSize 24) with 8192; lia].
    + apply (rw_cells_transport ctasegs W m4 m' _ _ MX MW WM). cbn [cells_size csize Nat.add].
      apply HWi; [unfold i_q_cmutex, INST, g_instance; lia | unfold i_q_cmutex, INST, g_instance, SEGTOP_A; lia | exact I].
  - (* [comment removed for export] *)
    exact (dep_rep_transport W L D' m4 m' DR Dok MW WM (kv_dep Σ W [] HWi ltac:(apply Forall_forall; intros; exact I)
             (se_grant67 Σ j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp))).
  - (* [comment removed for export] *)
    exact (fs_rep_transport W _ m4 m' FR MW WM (kv_fs Σ W [] (TZ_E T) [] HG HWi HWt HWg HWsa ltac:(apply Forall_forall; intros; exact I)
             ltac:(unfold TZ_E; cbn; repeat split; try exact I; lia))).
  - exact (ia_rep_transport W _ m4 m' IR MW WM (kv_ia W [] HWi ltac:(apply Forall_forall; intros; exact I))).
  - exact (shadow_rep_transport W _ m4 m' SHR MW WM (kv_shadow Σ W [] HG HWsa)).
  - exact (vis_rep_wmono _ m4 m' VIS WM).
Qed.

(* [comment removed for export] *)
Definition app_post (Σ2 : rtsA) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m4 : mem) : machine_state -> Prop :=
  fun ms => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms = MS (mkR ra sp gp (Z_to_bv 64 tpA) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom ctasegs)
    /\ ARTc Σ2 m' /\ mem_inv ctasegs m' /\ wmono ctasegs m4 m' /\ stk ctasegs m' lo (bv_unsigned sp) /\ munch Wa m4 m'.

Lemma app_run : forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' : word)
    (F : bvmap 5 word) (fc : bv 32) (m4 : mem) (lo : Z),
  bv_unsigned sp = usp -> ARTc Σ1 m4 -> depot_ok D' (l_DNB L) (l_SSB L) (l_ACEIL L) -> mem_inv ctasegs m4 ->
  stk ctasegs m4 lo (usp + -2208) -> l_ACEIL L <= lo -> lo + 0x10000 <= usp -> usp + 16 <= USTACK_TOP ->
  icpt_frame m4 usp ra s0 s1 s2 s3 s4 s5 ->
  qput_frame m4 (usp + -2208) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 0x1c424c) (Z_to_bv 64 usp)
    (Z_to_bv 64 (p_abeg SB c i + rz_size n - 16 + 16)) (Z_to_bv 64 0x1c41dc) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2128))
    (Z_to_bv 64 (usp + -81)) s6 ->
  (length ents < 1021)%nat -> RT_state.qbytes (ql Σ) + n <= 0x100000 ->
  evt ctasegs (app_post (set_ql Σ1 (pre ++ [(b0, ents ++ [(p_abeg SB c i + rz_size n - 16, n)])])) ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               F fc lo m4)
    (MS (mkR (Z_to_bv 64 0x1a038c) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 QUAR)
             (Z_to_bv 64 (T + 80)) (Z_to_bv 64 (T + 80)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2128))
             (Z_to_bv 64 (p_abeg SB c i + rz_size n - 16)) (Z_to_bv 64 n) a5' a6' a7'
             (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (T + 208))
             (Z_to_bv 64 (p_abeg SB c i + rz_size n - 16)) (Z_to_bv 64 0x100000)
             s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 qenq_entry) fc None m4 (seg_rom ctasegs)).
Proof.
  intros ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' F fc m4 lo
    Esp ART4 Dok MI4 ST4 HLO HLO2 Husp ICF FR4 HL HBY.
  pose proof (se_geo Σ j0 j0 CkBatch CkBatch HG Hj0 Hj0) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16).
  pose proof (se_disj Σ HG) as (T5 & T4 & ATP).
  assert (Hn1 : 1 <= n <= 2 ^ 16).
  { pose proof HG as (_ & HR & _). destruct HR as (HR & _). pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
    pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hn)) as X. cbv beta iota in X. pose proof (ClassSize_range c Hc) as X2.
    pose proof (rz_facts n) as (_ & X3). clear - X X2 X3; lia. }
  assert (RSP : 0 <= usp + -2208 < 2 ^ 64) by (clear - Hsp Husp K15; unfold USTACK_TOP, SHB in *; lia).
  assert (RSP2 : 0 <= usp + -2128 < 2 ^ 64) by (clear - Hsp Husp K15; unfold USTACK_TOP, SHB in *; lia).
  pose proof (qwf_ql Σ (proj1 (proj1 (rt_wf_split Σ) HW0))) as QWF. rewrite HQL in QWF.
  pose proof ART4 as (CR & PR & CA & CH & SR & QR & DR & FR & IR & SHR & VIS).
  pose proof QR as (QT & _). cbn [ql lay free_p] in QT. rewrite HQL in QT.
  rewrite <- qbytes_eq in HBY. rewrite HQL in HBY.
  (* [comment removed for export] *)
  eapply evt_cut.
  { apply (qenq_app_spec (Z_to_bv 64 0x1a038c) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80))
             a5' a6' a7' (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (p_abeg SB c i + rz_size n - 16))
             (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m4
             (T + 80) (T + 208) (usp + -2128) (p_abeg SB c i + rz_size n - 16) n SB lo pre b0 ents);
      try assumption; rewrite ?(unsigned_lit (usp + -2208)) by exact RSP.
    all: try (clear - Hn1; lia).
    all: try exact ST4. all: try (clear - HBY; lia).
    all: try (clear - ATP K5 K6 K11; unfold r24, rb, kUserCap in *; lia).
    all: try (clear - K13; lia). all: try (clear - K1 K5; lia). all: try (clear - HLO2; lia).
    all: try (clear - K14 HLO; lia). all: try (clear - K4 K6 HLO; unfold r24; lia).
    all: apply (Z.le_lt_trans _ 1048576); [exact HBY | reflexivity].
  }
  intros ms5 P5. destruct P5 as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m5 & -> & MU5 & WM5 & MI5 & QR5 & _ & ST5).
  rewrite (unsigned_lit (usp + -2208)) in MU5, ST5 by exact RSP. rewrite (ret_pc_even 0x1a038c) by (first [reflexivity | lia]).
  (* [comment removed for export] *)
  unfold qput_frame in FR4. pose proof (rw_cells_transport ctasegs _ m4 m5 _ _ FR4 MU5 WM5) as FR5.
  specialize (FR5 ltac:(cbn [disjoint_from cells_size csize Nat.add]; clear - K4 K5 K6 K7 K8 K11 K12 K14 Hsp; unfold rb, kUserCap in *; repeat split; try exact I; lia)).
  clear FR4.
  (* [comment removed for export] *)
  pose proof QR5 as QR5'. apply (proj1 (qcache_rep_iff _ _ _)) in QR5'. destruct QR5' as (QH5 & _).
  rewrite qbytes_snoc, qlast_snoc in QH5.
  replace (usp + -2208) with (usp + -2128 - 80) in ST5, FR5 by lia.
  replace (Z_to_bv 64 (usp + -2208)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (usp + -2128)) + -80))
    by (rewrite (unsigned_lit (usp + -2128)) by exact RSP2; f_equal; lia).
  eapply evt_cut.
  { apply (qput_B_ret_spec (Z_to_bv 64 0x1c424c) (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) x0 x1 x2 (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2128))
             (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (p_abeg SB c i + rz_size n - 16)) x3 x4 x5 x6 x7 x8 x9 x10 s7 s8 s9 s10 s11 x11 x12 x13 x14
             (Z_to_bv 64 0x1a038c) (Z_to_bv 64 usp) (Z_to_bv 64 (p_abeg SB c i + rz_size n - 16 + 16)) (Z_to_bv 64 0x1c41dc) (Z_to_bv 64 1)
             (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (usp + -81)) s6 (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2128)) F fc m5
             (T + 80) (R_quar_defs.qbytes pre + 8192 + bsum (ents ++ [(p_abeg SB c i + rz_size n - 16, n)])) lo
             (Z_to_bv 64 (Z.of_nat (length (pre ++ [(b0, ents ++ [(p_abeg SB c i + rz_size n - 16, n)])]))))
             (Z_to_bv 64 (qfirst (pre ++ [(b0, ents ++ [(p_abeg SB c i + rz_size n - 16, n)])]))) (Z_to_bv 64 b0));
      try assumption; rewrite ?(unsigned_lit (usp + -2128)) by exact RSP2.
    all: try exact ST5. all: try exact FR5. all: try exact QH5. all: try (clear - HLO2; lia).
    all: try (clear - K15 HLO; unfold SHB in *; lia).
    rewrite bsum_app. cbn [bsum fold_right snd]. rewrite qbytes_snoc in HBY. pose proof (qbytes_nonneg _ _ (qwf_prefix _ _ _ QWF)) as Q0.
    pose proof (qwf_last _ _ _ _ QWF) as (_ & _ & _ & _ & EN). pose proof (bsum_nonneg _ EN) as B0. unfold bsum in *. clear - HBY Hn1 Q0 B0. lia. }
  intros ms6 P6. destruct P6 as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m6 & -> & MU6 & WM6 & MI6 & ST6).
  rewrite (unsigned_lit (usp + -2128)) in MU6, ST6 by exact RSP2. rewrite (ret_pc_even 0x1c424c) by (first [reflexivity | lia]).
  (* [comment removed for export] *)
  destruct ICF as (FRs & (jp & FRp) & FRt & (ws & TB & HTB) & (w & FRb)).
  lazymatch type of MU5 with munch ?W5 _ _ => lazymatch type of MU6 with munch ?W6 _ _ =>
    pose proof (munch_trans (W5 ++ W6) m4 m5 m6 (munch_weaken W5 (W5 ++ W6) m4 m5 ltac:(clear; cbn [app]; solve_sub_fp) MU5)
                  (munch_weaken W6 (W5 ++ W6) m5 m6 ltac:(clear; cbn [app]; solve_sub_fp) MU6)) as MU46; cbn [app] in MU46 end end.
  pose proof (wmono_trans ctasegs _ _ _ WM5 WM6) as WM46.
  assert (DSF : forall a k, usp - 2128 <= a -> a + k <= usp -> disjoint_from [(T + 80, T + 80 + 32); (b0, b0 + 8192); (usp + -2208 - 64, usp + -2208);
                                                                           (usp + -2128 - 80, usp + -2128)] a k).
  { intros a k H1 H2. cbn [disjoint_from]. clear - H1 H2 K4 K5 K6 K7 K8 K11 K12 K14 Hsp. unfold rb, kUserCap in *. repeat split; try exact I; lia. }
  pose proof (rw_cells_transport ctasegs _ m4 m6 _ _ FRs MU46 WM46 ltac:(apply DSF; cbn; lia)) as FRs6.
  pose proof (rw_cells_transport ctasegs _ m4 m6 _ _ FRp MU46 WM46 ltac:(apply DSF; cbn; lia)) as FRp6.
  pose proof (rw_cells_transport ctasegs _ m4 m6 _ _ FRt MU46 WM46 ltac:(apply DSF; cbn; lia)) as FRt6.
  pose proof (rw_cells_transport ctasegs _ m4 m6 _ _ FRb MU46 WM46 ltac:(apply DSF; cbn; lia)) as FRb6.
  pose proof (u64arr_transport ctasegs _ m4 m6 _ _ TB MU46 WM46 ltac:(rewrite HTB; apply DSF; cbn; lia)) as TB6.
  clear FRs FRp FRt FRb TB.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 (usp + -2128)) with (Z_to_bv 64 (bv_unsigned sp + -2128)) by (rewrite Esp; reflexivity).
  eapply evt_mono.
  { apply (free_B_spec ra sp gp (Z_to_bv 64 tpA) y0 y1 y2 (Z_to_bv 64 usp) (Z_to_bv 64 (p_abeg SB c i + rz_size n - 16 + 16)) y3 y4 y5 y6 y7 y8 y9 y10
             (Z_to_bv 64 0x1c41dc) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (usp + -81)) s6 s7 s8 s9 s10 s11 y11 y12 y13 y14
             (Z_to_bv 64 0x1c424c) s0 s1 s2 s3 s4 s5 F fc m6 lo ws w jp); rewrite ?Esp; try assumption.
    all: try (clear - HLO2; lia). all: try (clear - K15 HLO; unfold SHB in *; lia). }
  intros ms P7. destruct P7 as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m7 & -> & MU7 & WM7 & MI7 & ST7).
  rewrite Esp in MU7, ST7.
  pose proof (wmono_trans ctasegs _ _ _ WM46 WM7) as WM47.
  lazymatch type of MU7 with munch ?W7 _ _ => lazymatch type of MU46 with munch ?W46 _ _ =>
    pose proof (munch_trans Wa m4 m6 m7 (munch_weaken W46 Wa m4 m6 ltac:(clear - Hsp; solve_sub_fp) MU46)
                  (munch_weaken W7 Wa m6 m7 ltac:(clear - Hsp; solve_sub_fp) MU7)) as MWa end end.
  assert (QR7 : qcache_rep m7 (qcacheT T) (pre ++ [(b0, ents ++ [(p_abeg SB c i + rz_size n - 16, n)])])).
  { lazymatch type of MU7 with munch ?W7 _ _ => lazymatch type of MU6 with munch ?W6 _ _ =>
      pose proof (munch_trans (W6 ++ W7) m5 m6 m7 (munch_weaken W6 (W6 ++ W7) m5 m6 ltac:(clear; cbn [app]; solve_sub_fp) MU6)
                    (munch_weaken W7 (W6 ++ W7) m6 m7 ltac:(clear; cbn [app]; solve_sub_fp) MU7)) as MU57; cbn [app] in MU57 end end.
    apply (qcache_transport _ m5 m7 _ _ QR5 MU57 (wmono_trans ctasegs _ _ _ WM6 WM7)).
    - unfold qcacheT. cbn [disjoint_from]. clear - K14 Hsp. repeat split; try exact I; lia.
    - pose proof (qwf_region _ _ QWF) as RG. rewrite Forall_app in RG |- *. destruct RG as [RG1 RG2]. split.
      + apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) RG1 e He) as (E1 & E2). cbn [disjoint_from].
        clear - E1 E2 K4 K6 K11 Hsp. unfold r24, rb, kUserCap in *. repeat split; try exact I; lia.
      + apply Forall_cons; [|apply Forall_nil]. inversion RG2 as [|? ? (E1 & E2) _]; subst. cbn [disjoint_from fst] in *.
        clear - E1 E2 K4 K6 K11 Hsp. unfold r24, rb, kUserCap in *. repeat split; try exact I; lia. }
  unfold app_post. exists z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, m7. split; [reflexivity|].
  split; [exact (app_ART m4 m7 _ ART4 MWa WM47 QR7 Dok)|]. split; [exact MI7|]. split; [exact WM47|]. split; [rewrite Esp; exact ST7 | exact MWa].
Qed.

End App.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma qents_app_snoc : forall (pre : list (Z * list (Z * Z))) (b : Z) (ents : list (Z * Z)) (e : Z * Z) (qg : list (Z * list (Z * Z))), flat_map snd ((pre ++ [(b, ents ++ [e])]) ++ qg) = flat_map snd pre ++ ents ++ e :: flat_map snd qg.
Proof. intros. rewrite !flat_map_app. cbn [flat_map snd]. rewrite app_nil_r, <- !app_assoc. reflexivity. Qed.
Lemma qents_app : forall (pre : list (Z * list (Z * Z))) (b : Z) (ents : list (Z * Z)) (qg : list (Z * list (Z * Z))), flat_map snd ((pre ++ [(b, ents)]) ++ qg) = flat_map snd pre ++ ents ++ flat_map snd qg.
Proof. intros. rewrite !flat_map_app. cbn [flat_map snd]. rewrite app_nil_r, <- !app_assoc. reflexivity. Qed.

(* [comment removed for export] *)
Lemma new_ent_fresh : forall Σ m c i n, ART_A Σ m -> 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkAlloc n) ->
  ~ In (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) (map fst (qents Σ)).
Proof.
  intros Σ m c i n HA Hc Hn Hin. apply in_map_iff in Hin as (e & Ee & He).
  pose proof (ART_wf Σ m HA) as (_ & _ & _ & HS & (_ & _ & _ & _ & _ & QE & _) & _).
  pose proof (live_in_slot Σ m HA c i n Hc Hn) as (_ & R16 & F & F0).
  pose proof (slot_geo Σ m HA c i _ Hc Hn) as (S1 & S2 & S3 & S4 & _). pose proof (geo_prb Σ m HA) as (P1 & P2 & _).
  destruct (proj1 (Forall_forall _ _) QE e He) as [(c' & i' & Hc' & Hi' & E')|(s & Hs & _ & Hsn & E')].
  - destruct (Z.eq_dec c c') as [<-|Hcc]; [destruct (Nat.eq_dec i i') as [<-|Hii]|].
    + rewrite Hn in Hi'. discriminate.
    + pose proof (slot_apart Σ m HA c i c i' _ _ Hc Hc Hn Hi' (or_intror Hii)) as Y.
      pose proof (slot_geo Σ m HA c i' _ Hc Hi') as (Z1 & Z2 & _).
      pose proof (ART_wf Σ m HA) as (_ & HR & _). destruct HR as (HR & _). pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
      pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hi')) as X. cbv beta iota in X. pose proof (rz_facts (snd e)) as (_ & R').
      rewrite E' in Ee. lia.
    + pose proof (slot_apart Σ m HA c i c' i' _ _ Hc Hc' Hn Hi' (or_introl Hcc)) as Y.
      pose proof (ART_wf Σ m HA) as (_ & HR & _). destruct HR as (HR & _). pose proof (HR c' Hc') as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
      pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hi')) as X. cbv beta iota in X. pose proof (rz_facts (snd e)) as (_ & R').
      rewrite E' in Ee. lia.
  - destruct HS as (_ & _ & _ & HSF & _). pose proof (proj1 (Forall_forall _ _) HSF s Hs) as (Hsn' & _ & Ha & _).
    pose proof (smsz_room (s_n s) ltac:(lia)) as Hroom. rewrite E' in Ee.
    unfold apart, p_abeg, rb, kUserCap in *. assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
Qed.

Lemma nodup_insert : forall (l1 l2 : list Z) x, NoDup (l1 ++ l2) -> ~ In x (l1 ++ l2) -> NoDup (l1 ++ x :: l2).
Proof.
  intros l1 l2 x H Hx. apply NoDup_ListNoDup in H. apply NoDup_ListNoDup.
  apply (Permutation.Permutation_NoDup (Permutation.Permutation_middle l1 l2 x)). constructor; [exact Hx | exact H].
Qed.

Lemma qbytes_app_ent : forall pre b ents e, RT_state.qbytes (pre ++ [(b, ents ++ [e])]) = RT_state.qbytes (pre ++ [(b, ents)]) + snd e.
Proof. intros. rewrite <- !qbytes_eq, !qbytes_snoc, bsum_app. unfold bsum. cbn [fold_right]. lia. Qed.

Theorem app_wf : forall (Σ : rtsA) (m : mem) c i n D' (pre : list (Z * list (Z * Z))) j0 (ents : list (Z * Z)), ART_A Σ m -> 1 <= c <= 31 ->
  nth_error (r_st (pr Σ c)) i = Some (CkAlloc n) ->
  depot_ok D' (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ)) -> dep_inv D' ->
  ql Σ = pre ++ [(p_abeg (l_SB (lay Σ)) 24 j0, ents)] -> (length ents < 1021)%nat -> RT_state.qbytes (ql Σ) + n <= 0x100000 ->
  rt_wf (set_ql (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) D')
                (pre ++ [(p_abeg (l_SB (lay Σ)) 24 j0, ents ++ [(p_abeg (l_SB (lay Σ)) c i + rz_size n - 16, n)])])).
Proof.
  intros Σ m c i n D' pre j0 ents HA Hc Hn HDok HDinv HQL HL HBY.
  pose proof (free_p_wf Σ m c i n D' HA Hc Hn HDok HDinv) as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11).
  pose proof (ART_wf Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RC).
  pose proof (new_ent_fresh Σ m c i n HA Hc Hn) as FR.
  destruct W5 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8). cbn [ql qg pr lay sec free_p] in Q1, Q2, Q3, Q4, Q5, Q8.
  unfold qents in Q6, Q7, FR. cbn [ql qg free_p] in Q6, Q7. rewrite HQL in Q1, Q3, Q4, Q5, Q6, Q7, Q8, FR, HBY. rewrite qents_app in Q6, Q7, FR.
  split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. split.
  { unfold quar_wf. cbn [set_ql ql qg pr lay free_p]. split; [rewrite qbytes_app_ent; cbn [snd]; unfold QMAX_L; lia|].
    split; [exact Q2|].
    split; [rewrite Forall_app in Q3 |- *; destruct Q3 as [Q3a Q3b]; rewrite Forall_app in Q3a |- *; destruct Q3a as [Q3a Q3c]; split; [split; [exact Q3a|]|exact Q3b];
            inversion Q3c as [|? ? X _]; subst; constructor; [exact X | constructor]|].
    split; [rewrite !map_app in Q4 |- *; cbn [map fst] in Q4 |- *; exact Q4|].
    split; [rewrite Forall_app in Q5 |- *; destruct Q5 as [Q5a Q5b]; rewrite Forall_app in Q5a |- *; destruct Q5a as [Q5a Q5c]; split; [split; [exact Q5a|]|exact Q5b];
            constructor; [cbn [snd]; rewrite length_app; cbn [length]; lia | constructor]|].
    unfold qents. cbn [set_ql ql qg]. rewrite qents_app_snoc. split; [|split].
    - rewrite Forall_app in Q6 |- *. destruct Q6 as [Q6a Q6b]. rewrite Forall_app in Q6b. destruct Q6b as [Q6b Q6c].
      split; [exact Q6a|]. rewrite Forall_app. split; [exact Q6b|]. constructor; [|exact Q6c].
      left. exists c, i. split; [exact Hc|]. cbn [snd fst pr free_p set_ql]. destruct (Z.eqb_spec c c) as [_|X]; [|exfalso; apply X; reflexivity].
      unfold upd_reg. cbn [r_st]. rewrite nth_error_upd_ck, Nat.eqb_refl.
      rewrite (proj2 (Nat.ltb_lt _ _) (proj1 (nth_error_Some _ _) ltac:(rewrite Hn; discriminate))). split; reflexivity.
    - rewrite !map_app in Q7 |- *. cbn [map fst] in Q7 |- *. rewrite !map_app in FR. rewrite app_assoc in Q7, FR |- *. apply nodup_insert; [exact Q7 | exact FR].
    - intros c' i' Hc' Hi'. destruct (Q8 c' i' Hc' Hi') as (Ec & Hin). split; [exact Ec|]. rewrite !map_app in Hin |- *. cbn [map fst] in Hin |- *. exact Hin. }
  split; [exact W6|]. split; [exact W7|]. split; [exact W8|]. split; [exact W9|]. split; [exact W10|]. split; [exact W11|].
  (* [comment removed for export] *)
  destruct RC as (RC1 & RC2). unfold qents in RC1, RC2. rewrite HQL, qents_app in RC1, RC2. split.
  - intros c' i' n' Hc' Hi'. unfold qents. cbn [set_ql ql qg lay free_p] in *. rewrite qents_app_snoc.
    destruct (fp_st Σ c i n Hc c' i' _ Hi') as [(-> & -> & E)|(Hne & Hi0)].
    + injection E as ->. apply in_or_app. right. apply in_or_app. right. left. reflexivity.
    + pose proof (RC1 c' i' n' Hc' Hi0) as X. rewrite !in_app_iff in X |- *. cbn [In]. tauto.
  - intros s Hs Hq. unfold qents. cbn [set_ql ql qg sec free_p] in *. rewrite qents_app_snoc.
    pose proof (RC2 s Hs Hq) as X. rewrite !in_app_iff in X |- *. cbn [In]. tauto.
Qed.
