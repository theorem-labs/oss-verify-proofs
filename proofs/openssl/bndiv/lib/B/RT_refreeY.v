(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface D_defs D_kit R_sizeclass R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_quar_defs R_qput R_qenqueue R_qenqueue_N R_qenqueue_F R_qenqueue_M R_qenqueue_MF R_asan_free R_prim_kit R_refill RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeA2 RT_freestmt RT_freeC RT_freeD RT_freeF RT_freeG RT_freeE RT_freeH RT_freeI RT_freeJ RT_freeK RT_freeL RT_freeM RT_freeN RT_freeS RT_freeT RT_freeU RT_freeV RT_freeW RT_freeX RT_refillstmt RT_refillst RT_refillwf RT_rfkit RT_refillrun RT_count RT_refill RT_sys_stmt RT_refreekA RT_refreekC RT_refreekD RT_refreekL RT_refreekH RT_refreeG RT_refreeV RT_refreeW RT_refreeX RT_refreeH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition enq_entry_st_r (usp T M n : Z) (gp t0 t1 t2 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) : machine_state :=
  MS (mkR (Z_to_bv 64 0x19a298) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 QUAR)
          (Z_to_bv 64 (T + 80)) (Z_to_bv 64 (T + 80)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056))
          (Z_to_bv 64 M) (Z_to_bv 64 n) a5 a6 a7 (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 (T + 208))
          (Z_to_bv 64 M) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 qenq_entry) fc None m (seg_rom bsegs).

(* [comment removed for export] *)
Definition mfg_post_r (Σ1 : rtsA) (M n : Z) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m5 : mem) (jf : list byte),
    ms = refill_entry_st (Z_to_bv 64 qenq_refill_ret) (Z_to_bv 64 (bv_unsigned sp + -2208 + -64)) gp t0' t1' t2'
           (Z_to_bv 64 (pc_addr (l_T (lay Σ1)) 24)) (Z_to_bv 64 (cacheT (l_T (lay Σ1)))) a4' a5' a6' a7'
           (Z_to_bv 64 M) (Z_to_bv 64 (qcacheT (l_T (lay Σ1)))) (Z_to_bv 64 (bv_unsigned sp + -2056))
           (Z_to_bv 64 n) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc (l_T (lay Σ1)) 24 m5
    /\ ARTc Σ1 m5 /\ mem_inv bsegs m5 /\ wmono bsegs m m5 /\ stk bsegs m5 lo (bv_unsigned sp + -2208 + -64)
    /\ rt_pres (live Σ1) (frames Σ1) (bv_unsigned sp) m m5
    /\ ricpt_frame m5 (bv_unsigned sp) ra s0 s1 s2 s3 s4 s5
    /\ qput_frame m5 (bv_unsigned sp + -2208) (Z_to_bv 64 (l_T (lay Σ1) + 208)) (Z_to_bv 64 (bv_unsigned sp + -2056)) (Z_to_bv 64 0x19683c)
         s0 (Z_to_bv 64 (M + 16)) s2 s3
         s4 s5 s6
    /\ rw_cells bsegs m5 (bv_unsigned sp + -2208 + -64)
         [CB 8 jf; C8 (Z_to_bv 64 M); C8 (Z_to_bv 64 (l_T (lay Σ1) + 208));
          C8 (Z_to_bv 64 (bv_unsigned sp + -2056)); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (l_T (lay Σ1) + 80)); C8 (Z_to_bv 64 QUAR);
          C8 (Z_to_bv 64 0x19a298)].

(* [comment removed for export] *)
Lemma miss_front_g_r : forall (Σ1 : rtsA) (M n : Z) (m : mem) (j0 : nat)
    (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' : word) (F : bvmap 5 word) (fc : bv 32)
    (m4 : mem) (lo : Z),
  rt_wf0 Σ1 -> 1 <= n <= 2 ^ 27 -> l_ACEIL (lay Σ1) <= lo -> lo + 0xFFB0 <= bv_unsigned sp -> bv_unsigned sp + 16 <= USTACK_TOP ->
  ARTc Σ1 m4 -> mem_inv bsegs m4 -> wmono bsegs m m4 -> stk bsegs m4 lo (bv_unsigned sp + -2208) ->
  rt_pres (live Σ1) (frames Σ1) (bv_unsigned sp) m m4 -> ricpt_frame m4 (bv_unsigned sp) ra s0 s1 s2 s3 s4 s5 ->
  qput_frame m4 (bv_unsigned sp + -2208) (Z_to_bv 64 (l_T (lay Σ1) + 208)) (Z_to_bv 64 (bv_unsigned sp + -2056)) (Z_to_bv 64 0x19683c)
    s0 (Z_to_bv 64 (M + 16)) s2 s3
    s4 s5 s6 ->
  ca Σ1 24 = [] ->
  (ql Σ1 = [] \/ exists pre ents0, nth_error (r_st (pr Σ1 24)) j0 = Some CkBatch /\ ql Σ1 = pre ++ [(p_abeg (l_SB (lay Σ1)) 24 j0, ents0)]
                                   /\ length ents0 = 1021%nat) ->
  evt bsegs (mfg_post_r Σ1 M n ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (enq_entry_st_r (bv_unsigned sp) (l_T (lay Σ1)) M n gp t0' t1' t2' a5' a6' a7' s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m4).
Proof.
  intros Σ1 M n m j0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 F fc m4 lo
    HW1 Hn1 HLO HLO2 Husp ART4 MI4 WM4 ST4 RP4 ICF FR4 HCA0 Hvar0.
  set (usp := bv_unsigned sp) in *.
  pose proof (geo_of_wf0 Σ1 HW1) as HG1.
  pose proof (g_grant Σ1 HG1 (l_T (lay Σ1)) 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (GT1 & GT2 & GT3 & _).
  pose proof (se_disj_r Σ1 HG1) as (T5 & T4 & ATP). pose proof (fk_prb Σ1 HG1) as (FP1 & FP2 & FP3 & FP4 & FP5).
  pose proof (fk_aceil Σ1 HG1) as (AC1 & AC2).
  assert (Hsp : l_ACEIL (lay Σ1) + 0xFFB0 <= usp) by (clear - HLO HLO2; lia).
  assert (RSP : 0 <= usp + -2208 < 2 ^ 64) by (clear - Hsp Husp AC1; unfold USTACK_TOP, SHB in *; lia).
  pose proof ART4 as (CR4 & PR4 & CA4 & CH4 & SR4 & QR4 & DR4 & FS4 & IR4 & SH4 & VIS4).
  pose proof (CA4 24 ltac:(lia)) as (PC24 & _). rewrite HCA0 in PC24. cbn [length Z.of_nat] in PC24.
  pose proof QR4 as (QT4 & _).
  eapply evt_cut.
  { unfold enq_entry_st_r. destruct Hvar0 as [HQL|(pre & ents0 & Hj0 & HQL & HL0)].
    - rewrite HQL in QT4.
      apply (qenq_miss_A_empty_spec (Z_to_bv 64 0x19a298) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) y0 y1 y2 (Z_to_bv 64 QUAR)
               (Z_to_bv 64 (l_T (lay Σ1) + 80)) y3 y4 y5 (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 (l_T (lay Σ1) + 208))
               (Z_to_bv 64 M) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 y6 y7 y8 y9 F fc m4
               (l_T (lay Σ1)) (usp + -2056) M n lo _ _ QT4 PC24);
        rewrite ?(unsigned_lit (usp + -2208)) by exact RSP.
      + clear - GT1. lia.
      + clear - T5. unfold SEGTOP_A in *. lia.
      + clear - GT3 HLO. lia.
      + exact ST4.
      + clear - HLO2. lia.
      + clear - Hsp Husp. unfold USTACK_TOP in *. lia.
      + exact MI4.
    - rewrite HQL in QT4. pose proof (qwf_ql _ HW1) as QWF. rewrite HQL in QWF.
      pose proof HW1 as (_ & _ & _ & _ & (Q1 & _) & _). rewrite <- qbytes_eq, HQL in Q1.
      eapply (qenq_miss_A_full_spec (Z_to_bv 64 0x19a298) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) y0 y1 y2 (Z_to_bv 64 QUAR)
               (Z_to_bv 64 (l_T (lay Σ1) + 80)) y3 y4 y5 (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 (l_T (lay Σ1) + 208))
               (Z_to_bv 64 M) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 y6 y7 y8 y9 F fc m4
               (l_T (lay Σ1)) (usp + -2056) M n lo _ _ (l_SB (lay Σ1)) pre
               (p_abeg (l_SB (lay Σ1)) 24 j0) ents0 HL0 QT4 QWF);
        rewrite ?(unsigned_lit (usp + -2208)) by exact RSP.
      + eapply Z.le_lt_trans; [exact Q1 | reflexivity].
      + exact PC24.
      + clear - GT1. lia.
      + clear - T5. unfold SEGTOP_A in *. lia.
      + clear - GT3 HLO. lia.
      + clear - FP2 FP4 FP5 HLO. unfold r24. lia.
      + clear - FP4 FP5 ATP. unfold r24 in *. lia.
      + clear - FP1 FP4. lia.
      + exact ST4.
      + clear - HLO2. lia.
      + clear - Hsp Husp. unfold USTACK_TOP in *. lia.
      + exact MI4. }
  intros ms P. destruct P as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & m5 & -> & MU5 & WM5 & MI5 & (jf & EF5) & ST5).
  rewrite (unsigned_lit (usp + -2208)) in MU5, EF5, ST5 |- * by exact RSP.
  apply evt_done.
  pose proof HW1 as (_ & _ & _ & _ & (_ & _ & HBt & _) & _). pose proof HW1 as (_ & _ & _ & _ & _ & _ & _ & Dok1 & _).
  assert (Ha : l_ACEIL (lay Σ1) <= usp + -2208 - 64) by (clear - Hsp; lia).
  exists z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, m5, jf.
  split; [reflexivity|].
  split; [exact (ARTc_stack _ (usp + -2208 - 64) (usp + -2208) HG1 Ha m4 m5 ART4 MU5 WM5 HBt Dok1)|].
  split; [exact MI5|]. split; [exact (wmono_trans bsegs _ _ _ WM4 WM5)|].
  split; [replace (usp + -2208 + -64) with (usp + -2208 - 64) by ring; exact ST5|].
  split.
  { intros a Ha'. rewrite (MU5 a); [exact (RP4 a Ha')|].
    refine (kv_client Σ1 [(usp + -2208 - 64, usp + -2208)] [] [] [] usp HG1
             (sk_img _ _ _ HG1 Ha) (sk_grant _ _ _ HG1 Ha) (sk_slot _ _ _ HG1 Ha) (sk_shad_app _ _ _ HG1 Ha) (sk_secmap _ _ _ HG1 Ha) _
             ltac:(apply Forall_forall; intros; exact I) (live Σ1) _ _ Ha').
    - intros a' k' H1 H2. cbn [disjoint_from]. split; [clear - H1; lia | exact I].
    - intros p' n' Hin. pose proof HW1 as (_ & _ & HV & _). destruct HV as (_ & _ & V3 & _).
      destruct (V3 p' n' Hin) as [(c' & i' & Hc' & Hn' & ->)|(s & Hs & Hq & Hsn & ->)].
      + left. exists c', i'. split; [exact Hc'|]. split; [exact Hn'|]. split; [reflexivity | intros []].
      + right. destruct (In_nth_error _ _ Hs) as (k & Hk'). exists k, s. split; [exact Hk'|]. split; [exact Hq|]. split; [exact Hsn|].
        split; [reflexivity | intros []]. }
  split.
  { apply (ricpt_frame_transport _ m4 m5 usp ra s0 s1 s2 s3 s4 s5 ICF MU5 WM5). cbn [disjoint_from]. split; [clear; lia | exact I]. }
  split.
  { unfold qput_frame in FR4 |- *. apply (rw_cells_transport bsegs _ m4 m5 _ _ FR4 MU5 WM5). cbn [disjoint_from cells_size csize Nat.add].
    split; [clear; lia | exact I]. }
  replace (usp + -2208 + -64) with (usp + -2208 - 64) by ring. exact EF5.
Qed.

Lemma rt_eager_en_r : forall Σ cal jB M n, rt_eager (enq_new Σ cal jB M n) = rt_eager Σ.
Proof.
  intros Σ cal jB M n. apply rt_eager_ext; [|reflexivity | reflexivity]. intros k'.
  cbn [enq_new set_ql pop24 pr]. destruct (Z.eqb_spec k' 24) as [->|_]; [|split; reflexivity]. unfold upd_reg. cbn [r_muser r_mfa]. split; reflexivity.
Qed.

Section Stage.
Variables (Σ Σ1 : rtsA) (PMc : Model -> Prop) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' : word)
          (F : bvmap 5 word) (fc : bv 32) (m m4 : mem) (lo M n p : Z) (T : TSet).
Hypothesis DRAIN : drain_stmt_r.
Hypothesis FC : fixed_commit_node.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis HW1 : rt_wf0 Σ1.
Hypothesis HP : pend_e Σ1 M n.
Hypothesis EL : live Σ1 = live_remove p (live Σ).
Hypothesis EF : frames Σ1 = frames Σ.
Hypothesis ELY : lay Σ1 = lay Σ.
Hypothesis EC : credit Σ1 = credit Σ.
Hypothesis HLO : l_ACEIL (lay Σ) <= lo.
Hypothesis HLO2 : lo + 0xFFB0 <= bv_unsigned sp.
Hypothesis Husp : bv_unsigned sp + 16 <= USTACK_TOP.
Hypothesis ART4 : ARTc Σ1 m4.
Hypothesis MI4 : mem_inv bsegs m4.
Hypothesis WM4 : wmono bsegs m m4.
Hypothesis ST4 : stk bsegs m4 lo (bv_unsigned sp + -2208).
Hypothesis RP4 : rt_pres (live Σ1) (frames Σ1) (bv_unsigned sp) m m4.
Hypothesis ICF : ricpt_frame m4 (bv_unsigned sp) ra s0 s1 s2 s3 s4 s5.
Hypothesis FR4 : qput_frame m4 (bv_unsigned sp + -2208) (Z_to_bv 64 (l_T (lay Σ1) + 208)) (Z_to_bv 64 (bv_unsigned sp + -2056)) (Z_to_bv 64 0x19683c)
    s0 (Z_to_bv 64 (M + 16)) s2 s3
    s4 s5 s6.
Hypothesis Hk : forall c', refree_post Σ PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p lo m c' -> realizes bsegs c' T.
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation entry := (enq_entry_st_r (bv_unsigned sp) (l_T (lay Σ1)) M n gp t0' t1' t2' a5' a6' a7' s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m4).

Lemma es_n_r : 1 <= n <= 2 ^ 27.
Proof using HW1 HP. exact (pe_n Σ1 M n HW1 (proj1 HP)). Qed.

Lemma es_sp_r : l_ACEIL (lay Σ1) + 0xFFB0 <= usp.
Proof using ELY HLO HLO2. rewrite ELY. clear - HLO HLO2. lia. Qed.

(* [comment removed for export] *)
Lemma es_fin_r : forall Σ2 F' fc' c2, live Σ2 = live Σ1 -> frames Σ2 = frames Σ1 -> lay Σ2 = lay Σ1 -> credit Σ2 = credit Σ1 ->
  AST SEGTOP_A (rtA_allow Σ2) (renq_post Σ2 (live Σ1) (frames Σ1) ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F' fc' lo m)
    (fun mo => ARTM_A Σ2 mo /\ PMc mo) c2 -> realizes bsegs c2 T.
Proof using DRAIN FDO MST EL EF ELY EC HLO HLO2 Husp Hk.
  intros Σ2 F' fc' c2 E1 E2 E3 E4 Hc2.
  apply (fin_from_enq_r DRAIN Σ Σ2 PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F' fc' m lo p T c2 FDO MST
           ltac:(rewrite E1; exact EL) ltac:(rewrite E2; exact EF) ltac:(rewrite E3; exact ELY) ltac:(rewrite E4; exact EC)
           HLO HLO2 Husp); [|exact Hk].
  rewrite E1, <- EF. exact Hc2.
Qed.

(* [comment removed for export] *)
Lemma es_new_r : forall (j0 : nat) cf,
  (ql Σ1 = [] \/ exists pre ents0, nth_error (r_st (pr Σ1 24)) j0 = Some CkBatch /\ ql Σ1 = pre ++ [(p_abeg (l_SB (lay Σ1)) 24 j0, ents0)]
                                   /\ length ents0 = 1021%nat) ->
  AST SEGTOP_A (rtA_allow Σ1) (eq entry) (fun mo => ARTM_A Σ1 mo /\ PMc mo) cf -> realizes bsegs cf T.
Proof using DRAIN FC FDO MST HW1 HP EL EF ELY EC HLO HLO2 Husp ART4 MI4 WM4 ST4 RP4 ICF FR4 Hk.
  intros j0 cf Hvar0 Hc. pose proof es_n_r as Hn1. pose proof es_sp_r as Hsp. pose proof (geo_of_wf0 Σ1 HW1) as HG1.
  pose proof (fk_aceil Σ1 HG1) as (AC1 & AC2).
  assert (HLO1 : l_ACEIL (lay Σ1) <= lo) by (rewrite ELY; exact HLO).
  pose proof HW1 as (_ & (_ & _ & R3 & _) & _). destruct (R3 24 ltac:(lia)) as (_ & _ & CAF).
  destruct (ca Σ1 24) as [|x l] eqn:ECA.
  - (* [comment removed for export] *)
    assert (W1 : forall ms, eq entry ms -> evt bsegs (mfg_post_r Σ1 M n ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m) ms)
      by (intros ms <-; exact (miss_front_g_r Σ1 M n m j0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' F fc m4 lo
                                 HW1 Hn1 HLO1 HLO2 Husp ART4 MI4 WM4 ST4 RP4 ICF FR4 ECA Hvar0)).
    apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ1) _ _ _ (fl_ASTA_mat_stable Σ1 PMc MST) W1) Hc).
    intros c1 Hc1.
    apply AST_exI in Hc1 as [y0 Hc1]. apply AST_exI in Hc1 as [y1 Hc1]. apply AST_exI in Hc1 as [y2 Hc1]. apply AST_exI in Hc1 as [y3 Hc1].
    apply AST_exI in Hc1 as [y4 Hc1]. apply AST_exI in Hc1 as [y5 Hc1]. apply AST_exI in Hc1 as [y6 Hc1]. apply AST_exI in Hc1 as [y7 Hc1].
    apply AST_exI in Hc1 as [y8 Hc1]. apply AST_exI in Hc1 as [y9 Hc1]. apply AST_exI in Hc1 as [y10 Hc1].
    apply AST_exI in Hc1 as [m5 Hc1]. apply AST_exI in Hc1 as [jf Hc1].
    pose proof Hc1 as (_ & (_ & ART5 & MI5 & WM5 & ST5 & RP5 & ICF5 & FR5 & EF5) & _ & _).
    assert (RSP : 0 <= usp + -2208 + -64 < 2 ^ 64) by (clear - Hsp Husp AC1; unfold USTACK_TOP, SHB in *; lia).
    pose proof (pend_room_e Σ1 M n HW1 HP ECA) as HROOM.
    (* [comment removed for export] *)
    pose proof HW1 as (_ & (HR1 & _) & _).
    pose proof (refill_ca_len (pr Σ1 24) 24 ltac:(clear; lia) (HR1 24 ltac:(clear; lia))) as LCA.
    change (MaxCount 24 / 2) with 1 in LCA.
    pose proof (refill_wf0 Σ1 24 ltac:(clear; lia) HW1 ECA HROOM) as HWb.
    pose proof HWb as (_ & (_ & _ & HR3 & _) & _). destruct (HR3 24 ltac:(clear; lia)) as (_ & _ & CAFb).
    cbn [refillΣ ca] in CAFb. rewrite Z.eqb_refl in CAFb.
    destruct (refill_ca (pr Σ1 24) 24) as [|xb [|yb lb]] eqn:ECAb; [cbn in LCA; lia | | cbn in LCA; lia].
    pose proof (proj1 (Forall_forall _ _) CAFb xb (in_eq xb [])) as (Hxb & _).
    set (jB := Z.to_nat xb).
    assert (HjB : refill_ca (pr Σ1 24) 24 = [Z.of_nat jB]) by (rewrite ECAb; unfold jB; rewrite Z2Nat.id by (clear - Hxb; lia); reflexivity).
    assert (Hc1' : AST SEGTOP_A (rtA_allow Σ1)
                     (eq (refill_entry_st (Z_to_bv 64 qenq_refill_ret) (Z_to_bv 64 (usp + -2208 + -64)) gp y0 y1 y2
                            (Z_to_bv 64 (pc_addr (l_T (lay Σ1)) 24)) (Z_to_bv 64 (cacheT (l_T (lay Σ1)))) y3 y4 y5 y6
                            (Z_to_bv 64 M) (Z_to_bv 64 (qcacheT (l_T (lay Σ1)))) (Z_to_bv 64 (usp + -2056))
                            (Z_to_bv 64 n) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 y7 y8 y9 y10 F fc (l_T (lay Σ1)) 24 m5))
                     (fun mo => ARTM_A Σ1 mo /\ PMc mo) c1).
    { eapply AST_conseq; [exact Hc1 | intros ms (E & _); symmetry; exact E | intros mo X; exact X]. }
    apply (refill_core Σ1 PMc m5 24 lo (Z_to_bv 64 qenq_refill_ret) (Z_to_bv 64 (usp + -2208 + -64)) gp
             (Z_to_bv 64 (pc_addr (l_T (lay Σ1)) 24)) (Z_to_bv 64 (cacheT (l_T (lay Σ1)))) (Z_to_bv 64 M)
             (Z_to_bv 64 (qcacheT (l_T (lay Σ1)))) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 n) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 F fc
             y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 FDO MST HW1 ART5 ltac:(clear; lia) ECA HROOM MI5
             ltac:(rewrite (unsigned_lit (usp + -2208 + -64)) by exact RSP; exact ST5) HLO1
             ltac:(rewrite (unsigned_lit (usp + -2208 + -64)) by exact RSP; clear - HLO2; lia)
             ltac:(rewrite (unsigned_lit (usp + -2208 + -64)) by exact RSP; clear - Husp; unfold USTACK_TOP in *; lia) FC T c1 Hc1').
    intros c2 Hc2.
    assert (VAR : exists (jX : nat) (stX : ckst), nth_error (r_st (pr (refillΣ Σ1 24) 24)) jX = Some stX
              /\ ((jX = jB /\ stX = CkIdle /\ ql Σ1 = [])
                  \/ (stX = CkBatch /\ exists pre ents0, ql Σ1 = pre ++ [(p_abeg (l_SB (lay Σ1)) 24 jX, ents0)] /\ length ents0 = 1021%nat))).
    { destruct Hvar0 as [HQL|(pre & ents0 & Hj0 & HQL & HL0)].
      - exists jB, CkIdle. split; [|left; split; [reflexivity|]; split; [reflexivity | exact HQL]].
        exact (ng_jB_r _ [] jB HWb ltac:(cbn [refillΣ ca]; rewrite Z.eqb_refl; exact HjB)).
      - exists j0, CkBatch. split; [|right; split; [reflexivity|]; exists pre, ents0; split; [exact HQL | exact HL0]].
        exact (rfs_keep Σ1 24 ltac:(clear; lia) HW1 24 j0 _ Hj0). }
    destruct VAR as (jX & stX & HjX & HvarX).
    assert (W2 : forall ms, rf_post Σ1 24 lo (Z_to_bv 64 qenq_refill_ret) (Z_to_bv 64 (usp + -2208 + -64)) gp
                            (Z_to_bv 64 (pc_addr (l_T (lay Σ1)) 24)) (Z_to_bv 64 (cacheT (l_T (lay Σ1)))) (Z_to_bv 64 M)
                            (Z_to_bv 64 (qcacheT (l_T (lay Σ1)))) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 n) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 m5 ms ->
                   evt bsegs (fun ms' => exists (F' : bvmap 5 word) (fc' : bv 32),
                                renq_post (enq_new (refillΣ Σ1 24) [] jB M n) (live Σ1) (frames Σ1)
                                         ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F' fc' lo m ms') ms).
    { intros ms (m6 & RET & ART6 & MI6 & WM6 & ST6 & MU6).
      destruct RET as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & F' & fc' & ->).
      rewrite (ret_pc_even qenq_refill_ret) by (unfold qenq_refill_ret; first [reflexivity | lia]).
      rewrite (unsigned_lit (usp + -2208 + -64)) in ST6, MU6 by exact RSP.
      eapply evt_mono; [apply (miss_enq_g_r Σ1 M n m jB jX stX usp HW1 HP ECA Hsp HjB HjX HvarX
                                 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F' fc' m5 m6 lo jf (Z_to_bv 64 qenq_refill_ret)
                                 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 eq_refl HLO1 HLO2 Husp WM5 RP5 ICF5 FR5 EF5 ART6 MI6 WM6 ST6 MU6)|].
      intros ms' P. exists F', fc'. exact P. }
    apply (cps_realizes bsegs _ _ _ c2 (ast_evt bsegs SEGTOP_A asegs_wx asegs_below _ _ _ _ (fl_ASTA_mat_stable _ PMc MST) W2) Hc2).
    intros c3 Hc3. apply AST_exI in Hc3 as [F' Hc3]. apply AST_exI in Hc3 as [fc' Hc3].
    apply (es_fin_r (enq_new (refillΣ Σ1 24) [] jB M n) F' fc' c3 eq_refl eq_refl eq_refl eq_refl).
    eapply AST_conseq; [exact Hc3 | intros ms H; exact H|]. intros mo (HM & HP'). split; [|exact HP'].
    apply (artm_eq (refillΣ Σ1 24)); [reflexivity | reflexivity | exact (rt_eager_en_r _ [] jB M n) | exact HM].
  - (* [comment removed for export] *)
    destruct (exists_last (l := x :: l) ltac:(discriminate)) as (cal & xj & Ecal).
    pose proof (proj1 (Forall_forall _ _) CAF xj ltac:(rewrite Ecal; apply in_or_app; right; left; reflexivity)) as (Hxj & _).
    set (jB := Z.to_nat xj).
    assert (HCA : ca Σ1 24 = cal ++ [Z.of_nat jB]) by (rewrite ECA, Ecal; unfold jB; rewrite Z2Nat.id by (clear - Hxj; lia); reflexivity).
    assert (VAR : exists (jX : nat) (stX : ckst), nth_error (r_st (pr Σ1 24)) jX = Some stX
              /\ ((jX = jB /\ stX = CkIdle /\ ql Σ1 = [])
                  \/ (stX = CkBatch /\ exists pre ents0, ql Σ1 = pre ++ [(p_abeg (l_SB (lay Σ1)) 24 jX, ents0)] /\ length ents0 = 1021%nat))).
    { destruct Hvar0 as [HQL|(pre & ents0 & Hj0 & HQL & HL0)].
      - exists jB, CkIdle. split; [exact (ng_jB_r Σ1 cal jB HW1 HCA)|]. left. split; [reflexivity|]. split; [reflexivity | exact HQL].
      - exists j0, CkBatch. split; [exact Hj0|]. right. split; [reflexivity|]. exists pre, ents0. split; [exact HQL | exact HL0]. }
    destruct VAR as (jX & stX & HjX & HvarX).
    assert (W1 : forall ms, eq entry ms ->
                   evt bsegs (renq_post (enq_new Σ1 cal jB M n) (live Σ1) (frames Σ1) ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m) ms)
      by (intros ms <-; exact (new_enq_g_r Σ1 M n m cal jB jX stX usp HW1 HP HCA HjX HvarX Hsp
                                 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' F fc m4 lo
                                 eq_refl ART4 MI4 WM4 ST4 HLO1 HLO2 Husp RP4 ICF FR4)).
    apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ1) _ _ _ (fl_ASTA_mat_stable Σ1 PMc MST) W1) Hc).
    intros c1 Hc1. apply (es_fin_r (enq_new Σ1 cal jB M n) F fc c1 eq_refl eq_refl eq_refl eq_refl).
    eapply AST_conseq; [exact Hc1 | intros ms H; exact H|]. intros mo (HM & HP'). split; [|exact HP'].
    apply (artm_eq Σ1); [reflexivity | reflexivity | exact (rt_eager_en_r Σ1 cal jB M n) | exact HM].
Qed.

(* [comment removed for export] *)
Theorem enq_stage_r : forall cf, AST SEGTOP_A (rtA_allow Σ1) (eq entry) (fun mo => ARTM_A Σ1 mo /\ PMc mo) cf -> realizes bsegs cf T.
Proof using DRAIN FC FDO MST HW1 HP EL EF ELY EC HLO HLO2 Husp ART4 MI4 WM4 ST4 RP4 ICF FR4 Hk.
  intros cf Hc. pose proof es_n_r as Hn1. pose proof es_sp_r as Hsp.
  pose proof HW1 as (_ & _ & _ & _ & (_ & _ & QB & _ & Q5 & _) & _).
  destruct (ql Σ1) as [|b l] eqn:EQL; [exact (es_new_r 0 cf (or_introl EQL) Hc)|].
  destruct (exists_last (l := b :: l) ltac:(discriminate)) as (pre & (b0 & ents) & Eql).
  destruct (proj1 (Forall_forall _ _) QB (b0, ents) ltac:(rewrite Eql; apply in_or_app; left; apply in_or_app; right; left; reflexivity))
    as (j0 & Hj0 & Eb0). cbn [fst] in Eb0.
  assert (HQL : ql Σ1 = pre ++ [(p_abeg (l_SB (lay Σ1)) 24 j0, ents)]) by (rewrite EQL, Eql, Eb0; reflexivity).
  pose proof (proj1 (Forall_forall _ _) Q5 (b0, ents) ltac:(rewrite Eql; apply in_or_app; left; apply in_or_app; right; left; reflexivity)) as HL5.
  cbn [snd] in HL5.
  destruct (Nat.lt_ge_cases (length ents) 1021) as [HL|HL].
  - (* [comment removed for export] *)
    assert (W1 : forall ms, eq entry ms ->
                   evt bsegs (renq_post (set_ql Σ1 (pre ++ [(p_abeg (l_SB (lay Σ1)) 24 j0, ents ++ [(M, n)])])) (live Σ1) (frames Σ1)
                                       ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m) ms)
      by (intros ms <-; exact (app_enq_g_r Σ1 M n m pre j0 ents usp HW1 HP HQL Hj0 HL Hsp
                                 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' F fc m4 lo
                                 eq_refl ART4 MI4 WM4 ST4 ltac:(rewrite ELY; exact HLO) HLO2 Husp RP4 ICF FR4)).
    apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ1) _ _ _ (fl_ASTA_mat_stable Σ1 PMc MST) W1) Hc).
    intros c1 Hc1. apply (es_fin_r (set_ql Σ1 (pre ++ [(p_abeg (l_SB (lay Σ1)) 24 j0, ents ++ [(M, n)])])) F fc c1 eq_refl eq_refl eq_refl eq_refl).
    eapply AST_conseq; [exact Hc1 | intros ms H; exact H|]. intros mo (HM & HP'). split; [|exact HP'].
    apply (artm_eq Σ1); [reflexivity | reflexivity | reflexivity | exact HM].
  - (* [comment removed for export] *)
    apply (es_new_r j0 cf); [|exact Hc]. right. exists pre, ents. split; [exact Hj0|]. split; [exact HQL | clear - HL HL5; lia].
Qed.

End Stage.
