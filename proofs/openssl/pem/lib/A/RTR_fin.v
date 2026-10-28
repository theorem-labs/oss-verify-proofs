(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_quar_defs R_qput R_qenqueue R_asan_free R_prim_kit RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeA2 RT_freestmt RT_freeC RT_freeD RT_freeF RT_freeG RT_freeH RTR_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition putret_st (retw : word) (usp : Z) (gp w0 w1 w2 w3 w4 w5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m5 : mem) :
  machine_state -> Prop :=
  fun ms => exists (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word) (m6 : mem),
    ms = MS (mkR retw (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) y0 y1 y2 w0 w1 y3 y4 y5 y6 y7 y8 y9 y10 w2 w3 w4 w5 s6 s7 s8 s9 s10 s11
                 y11 y12 y13 y14) F retw fc None m6 (seg_rom asegs)
    /\ munch [(usp - 2208, usp - 2128)] m5 m6 /\ wmono asegs m5 m6 /\ mem_inv asegs m6 /\ stk asegs m6 lo (usp + -2128).

Lemma ret_tail_r : forall (retw : word) (Σ2 : rtsA) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5'
    t3 t4 t5 t6 w0 w1 w2 w3 w4 w5 wc ws : word) (F : bvmap 5 word) (fc : bv 32) (m5 : mem) (lo : Z),
  geo_ok Σ2 -> ARTc Σ2 m5 -> rt_wfx Σ2 -> rt_count Σ2 -> RT_state.qbytes (ql Σ2) <= 0x100000 ->
  mem_inv asegs m5 -> stk asegs m5 lo (bv_unsigned sp + -2208) -> l_ACEIL (lay Σ2) <= lo -> lo + 0x10000 <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP ->
  ret_pc retw = retw ->
  qput_frame m5 (bv_unsigned sp + -2208) wc ws retw w0 w1 w2 w3 w4 w5 s6 ->
  evt asegs (putret_st retw (bv_unsigned sp) gp w0 w1 w2 w3 w4 w5 s6 s7 s8 s9 s10 s11 F fc lo m5)
    (enq_ret_st (bv_unsigned sp) (l_T (lay Σ2)) gp ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m5).
Proof.
  intros retw Σ2 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' t3 t4 t5 t6 w0 w1 w2 w3 w4 w5 wc ws F fc m5 lo
    HG ART5 HWX HC HBY MI5 ST5 HLO HLO2 Husp RETW FR5.
  set (usp := bv_unsigned sp) in *.
  pose proof (fk_aceil Σ2 HG) as (X1 & X2).
  assert (RSP2 : 0 <= usp + -2128 < 2 ^ 64) by (clear - HLO HLO2 Husp X1; unfold USTACK_TOP, SHB in *; lia).
  pose proof ART5 as (_ & _ & _ & _ & _ & QR & _). destruct QR as (QT & _).
  pose proof QT as QT'. apply (proj1 (qcache_rep_iff _ _ _)) in QT'. destruct QT' as (QH & _).
  unfold enq_ret_st.
  replace (Z_to_bv 64 (usp + -2208)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (usp + -2128)) + -80))
    by (rewrite (unsigned_lit (usp + -2128)) by exact RSP2; f_equal; lia).
  replace (usp + -2208) with (usp + -2128 - 80) in ST5, FR5 by lia.
  pose proof (qbytes_nonneg _ _ (qwf_ql_x Σ2 HWX)) as QB0.
  eapply evt_cut.
  { apply (qput_B_ret_spec retw (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) t0 t1 t2 s2' s3' s4' s5' a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11
             t3 t4 t5 t6 ra0 w0 w1 w2 w3 w4 w5 s6 wc ws F fc m5 (l_T (lay Σ2) + 80) (R_quar_defs.qbytes (ql Σ2)) lo
             (Z_to_bv 64 (Z.of_nat (length (ql Σ2)))) (Z_to_bv 64 (qfirst (ql Σ2))) (Z_to_bv 64 (qlast (ql Σ2))));
      try assumption; rewrite ?(unsigned_lit (usp + -2128)) by exact RSP2.
    all: try exact ST5. all: try exact FR5. all: try (clear - HLO2; lia). all: try (clear - X1 HLO; unfold SHB in *; lia).
    rewrite qbytes_eq. clear - QB0 HBY. rewrite qbytes_eq in QB0. lia. }
  intros ms6 P6. destruct P6 as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m6 & -> & MU6 & WM6 & MI6 & ST6).
  rewrite (unsigned_lit (usp + -2128)) in MU6, ST6 by exact RSP2. rewrite RETW.
  apply evt_done. unfold putret_st. exists y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, m6.
  split; [reflexivity|]. split; [|split; [exact WM6 | split; [exact MI6 | exact ST6]]].
  lazymatch type of MU6 with munch ?W6 _ _ => exact (munch_weaken W6 [(usp - 2208, usp - 2128)] m5 m6 ltac:(clear - HLO2; solve_sub_fp) MU6) end.
Qed.

(* [comment removed for export] *)
Definition cf_ok (CF : mem -> Prop) (usp : Z) : Prop :=
  forall ma mb : mem, CF ma -> (forall a : word, usp - 2128 <= bv_unsigned a < usp -> mb a = ma a) -> CF mb.

(* [comment removed for export] *)
Definition putret_post (CF : mem -> Prop) (retw q0 q1 q2 q3 q4 q5 : word) (Σ2 : rtsA) (PMc : Model -> Prop) (frames0 : list (Z * nat))
    (sp gp s6 s7 s8 s9 s10 s11 : word) (lo : Z) (m : mem) : config -> Prop :=
  fun cf => exists Σ' : rtsA,
    ASTA RTA Σ' PMc (fun ms => exists (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
        ms = MS (mkR retw (Z_to_bv 64 (bv_unsigned sp + -2128)) gp (Z_to_bv 64 tpA) y0 y1 y2 q0 q1 y3 y4 y5 y6 y7 y8 y9 y10 q2 q3 q4 q5 s6
                     s7 s8 s9 s10 s11 y11 y12 y13 y14) F' retw fc' None m' (seg_rom asegs)
        /\ ART_A Σ' m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + -2128)
        /\ rt_pres (live Σ2) frames0 (bv_unsigned sp) m m' /\ CF m') cf
    /\ live Σ' = live Σ2 /\ frames Σ' = frames Σ2 /\ lay Σ' = lay Σ2 /\ credit Σ' = credit Σ2.

Section FinR.
Hypothesis DRAIN : drain_stmt.

Theorem fin_from_enq_r : forall (CF : mem -> Prop) (retw q0 q1 q2 q3 q4 q5 : word) (Bt : Z) (Σ Σ2 : rtsA) PMc
    (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) T cf,
  ret_pc retw = retw -> 0 <= Bt < 2 ^ 64 -> cf_ok CF (bv_unsigned sp) ->
  fdfs_only PMc -> mat_stable PMc -> frames Σ2 = frames Σ -> lay Σ2 = lay Σ ->
  l_ACEIL (lay Σ) <= lo -> lo + 0x10000 <= bv_unsigned sp -> bv_unsigned sp + 16 <= USTACK_TOP ->
  AST SEGTOP_A (rtA_allow Σ2) (enq_post_g CF retw q0 q1 q2 q3 q4 q5 Bt Σ2 (live Σ2) (frames Σ) ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (fun mo => ARTM_A Σ2 mo /\ PMc mo) cf ->
  (forall c', putret_post CF retw q0 q1 q2 q3 q4 q5 Σ2 PMc (frames Σ) sp gp s6 s7 s8 s9 s10 s11 lo m c' -> realizes asegs c' T) ->
  realizes asegs cf T.
Proof.
  intros CF retw q0 q1 q2 q3 q4 q5 Bt Σ Σ2 PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo T cf RETW HBT CFA FDO MST EF ELY HLO HLO2 Husp Hc Hk.
  set (usp := bv_unsigned sp) in *.
  assert (Hsp : l_ACEIL (lay Σ2) + 0x10000 <= usp) by (rewrite ELY; clear - HLO HLO2; lia).
  destruct (Z_le_gt_dec (RT_state.qbytes (ql Σ2)) 0x100000) as [HBY|HBY].
  - (* [comment removed for export] *)
    assert (W1 : forall ms, enq_post_g CF retw q0 q1 q2 q3 q4 q5 Bt Σ2 (live Σ2) (frames Σ) ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m ms ->
      evt asegs (fun ms' => exists (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word) (m' : mem),
                   ms' = MS (mkR retw (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) y0 y1 y2 q0 q1 y3 y4 y5 y6 y7 y8 y9 y10 q2 q3 q4 q5 s6
                                 s7 s8 s9 s10 s11 y11 y12 y13 y14) F retw fc None m' (seg_rom asegs)
                   /\ ART_A Σ2 m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -2128)
                   /\ rt_pres (live Σ2) (frames Σ) usp m m' /\ CF m') ms).
    { intros ms P. destruct P as (ra0 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2' & s3' & s4' & s5' & t3 & t4 & t5 & t6
                                  & m5 & -> & ART5 & WX5 & WC5 & MI5 & WM5 & ST5 & RP5 & CF5 & FR5).
      pose proof (geo_of_wfx Σ2 WX5) as HG2.
      eapply evt_mono; [apply (ret_tail_r retw Σ2 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5'
                                  t3 t4 t5 t6 q0 q1 q2 q3 q4 q5 _ _ F fc m5 lo HG2 ART5 WX5 WC5 HBY MI5 ST5 ltac:(rewrite ELY; exact HLO)
                                  HLO2 Husp RETW FR5)|].
      intros ms' P'. destruct P' as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m6 & -> & MU6 & WM6 & MI6 & ST6).
      fold usp in MU6, ST6.
      exists y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, m6. split; [reflexivity|].
      assert (ART6 : ART_A Σ2 m6).
      { apply c_ART; [exact (rt_wf_of_x Σ2 WX5 WC5 ltac:(clear - HBY; unfold QMAX_L; lia))|].
        apply (ARTc_stack Σ2 (usp - 2208) (usp - 2128) HG2 ltac:(rewrite ELY; clear - HLO HLO2; lia) m5 m6 ART5 MU6 WM6).
        - destruct WX5 as (_ & _ & _ & _ & (_ & _ & QB & _) & _). exact QB.
        - destruct WX5 as (_ & _ & _ & _ & _ & _ & _ & DOK & _). exact DOK. }
      split; [exact ART6|]. split; [exact MI6|]. split; [exact ST6|]. split.
      + intros a Ha. rewrite (MU6 a); [exact (RP5 a Ha)|].
        pose proof (ART_wf Σ2 m6 ART6) as HW2. pose proof HW2 as (_ & _ & HV & _). destruct HV as (_ & _ & V3 & _).
        pose proof (aclient_split Σ2 (live Σ2) usp (bv_unsigned a) HG2 Hsp
                      ltac:(intros p0 n0 Hin; destruct (V3 p0 n0 Hin) as [X|(s & Hs & Hq & Hsn & ->)]; [left; exact X|];
                            right; destruct (In_nth_error _ _ Hs) as (k & Hk'); exists k, s; split; [exact Hk' | split; [exact Hq | split; [exact Hsn | reflexivity]]])
                      ltac:(rewrite EF; exact Ha)) as HO.
        cbn [outside] in HO |- *. clear - HO Hsp. split; [lia | exact I].
      + apply (CFA m5 m6 CF5). intros a Ha. apply MU6. cbn [outside]. clear - Ha. split; [lia | exact I]. }
    apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ2) _ _ _ (fl_ASTA_mat_stable Σ2 PMc MST) W1) Hc).
    intros c1 Hc1. apply Hk. exists Σ2. split; [|split; [reflexivity | split; [reflexivity | split; reflexivity]]].
    unfold ASTA. eapply AST_conseq; [exact Hc1| |intros mo H; exact H].
    intros ms (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & -> & X).
    exists y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, F, fc, m'. split; [reflexivity | exact X].
  - (* [comment removed for export] *)
    destruct Hc as (Hmc & HP & HPM & HZ).
    destruct HP as (ra0 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2' & s3' & s4' & s5' & t3 & t4 & t5 & t6
                    & m5 & E5 & ART5 & WX5 & WC5 & MI5 & WM5 & ST5 & RP5 & CF5 & FR5).
    assert (Hc' : ASTA RTA Σ2 PMc (eq (MS (mkR ra0 (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 QUAR)
                                             (Z_to_bv 64 (l_T (lay Σ2) + 80)) a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' (Z_to_bv 64 0x100000)
                                             s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x19f2dc) fc None m5 (seg_rom asegs))) cf).
    { split; [exact Hmc|]. split; [unfold enq_ret_st in E5; exact (eq_sym E5)|]. split; [exact HPM | exact HZ]. }
    apply (DRAIN Σ2 PMc ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m5 lo usp
             q0 q1 q2 q3 q4 q5 s6 retw Bt FDO MST ART5 WX5 WC5 ltac:(clear - HBY; lia) RETW HBT FR5 ST5 ltac:(rewrite ELY; exact HLO) ltac:(clear - HLO2; lia)
             ltac:(clear - Husp; unfold USTACK_TOP in *; lia) MI5 T cf Hc').
    intros c2 (Σ' & Hc2 & EL' & EF' & ELY' & EC'). apply Hk. exists Σ'. split; [|split; [exact EL' | split; [exact EF' | split; [exact ELY' | exact EC']]]].
    unfold ASTA in *. eapply AST_conseq; [exact Hc2| |intros mo H; exact H].
    intros ms (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F' & fc' & m6 & -> & ART6 & MI6 & ST6 & RP6).
    exists y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, F', fc', m6. split; [reflexivity|].
    split; [exact ART6|]. split; [exact MI6|]. split; [exact ST6|]. split.
    + intros a Ha. rewrite (RP6 a); [exact (RP5 a Ha)|]. rewrite EF. destruct Ha as [Ha|Ha]; [left; clear - Ha; lia | right; exact Ha].
    + apply (CFA m5 m6 CF5). intros a Ha. apply RP6. left. clear - Ha Husp. unfold USTACK_TOP in *. lia.
Qed.
End FinR.

(* [comment removed for export] *)
Lemma cft_of_cf_ok : forall (CF : mem -> Prop) (usp : Z), cf_ok CF usp ->
  forall W (ma mb : mem), CF ma -> munch W ma mb -> wmono asegs ma mb -> disjoint_from W (usp - 2128) 2128 -> CF mb.
Proof.
  intros CF usp H W ma mb Ha MU _ D. apply (H ma mb Ha). intros a Hr. apply MU.
  apply (disjoint_outside W (usp - 2128) 2128 (bv_unsigned a) D). lia.
Qed.
