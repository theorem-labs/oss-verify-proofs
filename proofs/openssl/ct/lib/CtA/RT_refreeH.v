(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Mem Frame Cells Step Arr Exec RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_quar_defs R_qput R_qenqueue R_asan_free R_prim_kit RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeA2 RT_freestmt RT_freeC RT_freeD RT_freeF RT_freeG RT_freeE RT_freeH RT_refreekH RT_refreeG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition refree_post (Σ : rtsA) (PMc : Model -> Prop) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (p lo : Z) (m : mem) : config -> Prop :=
  fun c => exists (Σ' : rtsA),
    ASTA RTA Σ' PMc (fun ms => exists (w0 w1 w2 w3 w5 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
         ms = MS (mkR (Z_to_bv 64 0x19c930) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp (Z_to_bv 64 tpA) t0' t1' t2' w0 w1 a0' a1' a2' a3' a4' a5' a6' a7'
                      w2 w3 s4 w5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (Z_to_bv 64 0x19c930) fc' None m' (seg_rom ctasegs)
         /\ ART_A Σ' m' /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp + -2128)
         /\ rt_pres (live Σ') (frames Σ) (bv_unsigned sp) m m'
         /\ ricpt_frame m' (bv_unsigned sp) ra s0 s1 s2 s3 s4 s5) c
    /\ live Σ' = live_remove p (live Σ) /\ frames Σ' = frames Σ /\ rtA_sp0 Σ' = rtA_sp0 Σ /\ credit Σ' = credit Σ.

Section FinR.
Hypothesis DRAIN : drain_stmt_r.

(* [comment removed for export] *)
Theorem fin_from_enq_r : forall (Σ Σ2 : rtsA) PMc (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo p : Z) T cf,
  fdfs_only PMc -> mat_stable PMc ->
  live Σ2 = live_remove p (live Σ) -> frames Σ2 = frames Σ -> lay Σ2 = lay Σ -> credit Σ2 = credit Σ ->
  l_ACEIL (lay Σ) <= lo -> lo + 0xFFB0 <= bv_unsigned sp -> bv_unsigned sp + 16 <= USTACK_TOP ->
  AST SEGTOP_A (rtA_allow Σ2) (renq_post Σ2 (live Σ2) (frames Σ) ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (fun mo => ARTM_A Σ2 mo /\ PMc mo) cf ->
  (forall c', refree_post Σ PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p lo m c' -> realizes ctasegs c' T) ->
  realizes ctasegs cf T.
Proof.
  intros Σ Σ2 PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo p T cf FDO MST EL EF ELY EC HLO HLO2 Husp Hc Hk.
  set (usp := bv_unsigned sp) in *.
  assert (Hsp : l_ACEIL (lay Σ2) + 0xFFB0 <= usp) by (rewrite ELY; clear - HLO HLO2; lia).
  destruct (Z_le_gt_dec (RT_state.qbytes (ql Σ2)) 0x100000) as [HBY|HBY].
  - (* [comment removed for export] *)
    assert (W1 : forall ms, renq_post Σ2 (live Σ2) (frames Σ) ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m ms ->
      evt ctasegs (fun ms' => exists (w0 w1 w2 w3 w5 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
                   ms' = MS (mkR (Z_to_bv 64 0x19c930) (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) t0' t1' t2' w0 w1 a0' a1' a2' a3' a4' a5' a6' a7'
                                 w2 w3 s4 w5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x19c930) fc None m' (seg_rom ctasegs)
                   /\ ART_A Σ2 m' /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (usp + -2128)
                   /\ rt_pres (live Σ2) (frames Σ) usp m m'
                   /\ ricpt_frame m' usp ra s0 s1 s2 s3 s4 s5) ms).
    { intros ms P. destruct P as (ra0 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2' & s3' & s4' & s5' & t3 & t4 & t5 & t6
                                  & w0 & w1 & w2 & w3 & w4 & w5 & m5 & (-> & Ew4) & ART5 & WX5 & WC5 & MI5 & WM5 & ST5 & RP5 & ICF5 & FR5).
      subst w4.
      pose proof (geo_of_wfx Σ2 WX5) as HG2.
      eapply evt_mono; [apply (ret_tail_r Σ2 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5'
                                  t3 t4 t5 t6 w0 w1 w2 w3 w5 _ _ F fc m5 lo HG2 ART5 WX5 WC5 HBY MI5 ST5 ltac:(rewrite ELY; exact HLO)
                                  HLO2 Husp ICF5 FR5)|].
      intros ms' P'. destruct P' as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m' & -> & ART' & MI' & WM' & ST' & MU' & ICF').
      exists w0, w1, w2, w3, w5, z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, m'. split; [reflexivity|].
      split; [exact ART'|]. split; [exact MI'|]. split; [exact ST'|]. split; [|exact ICF'].
      intros a Ha. rewrite (MU' a); [exact (RP5 a Ha)|].
      pose proof (ART_wf Σ2 m' ART') as HW2. pose proof HW2 as (_ & _ & HV & _). destruct HV as (_ & _ & V3 & _).
      pose proof (aclient_split_r Σ2 (live Σ2) usp (bv_unsigned a) HG2 Hsp
                    ltac:(intros p0 n0 Hin; destruct (V3 p0 n0 Hin) as [X|(s & Hs & Hq & Hsn & ->)]; [left; exact X|];
                          right; destruct (In_nth_error _ _ Hs) as (k & Hk'); exists k, s; split; [exact Hk' | split; [exact Hq | split; [exact Hsn | reflexivity]]])
                    ltac:(rewrite EF; exact Ha)) as HO.
      cbn [outside] in HO |- *. clear - HO Hsp. split; [lia | exact I]. }
    apply (cps_realizes ctasegs _ _ _ cf (ast_evt ctasegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ2) _ _ _ (fl_ASTA_mat_stable Σ2 PMc MST) W1) Hc).
    intros c1 Hc1. apply Hk.
    exists Σ2. split; [|split; [exact EL | split; [exact EF | split; [unfold rtA_sp0; rewrite ELY; reflexivity | exact EC]]]].
    unfold ASTA. eapply AST_conseq; [exact Hc1| |intros mo H; exact H].
    intros ms (w0 & w1 & w2 & w3 & w5 & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & ART' & MI' & ST' & RP' & ICF').
    exists w0, w1, w2, w3, w5, t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F, fc, m'. split; [reflexivity|].
    split; [exact ART'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact RP' | exact ICF'].
  - (* [comment removed for export] *)
    destruct Hc as (Hmc & HP & HPM & HZ).
    destruct HP as (ra0 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2' & s3' & s4' & s5' & t3 & t4 & t5 & t6
                    & w0 & w1 & w2 & w3 & w4 & w5 & m5 & (E5 & Ew4) & ART5 & WX5 & WC5 & MI5 & WM5 & ST5 & RP5 & ICF5 & FR5).
    subst w4.
    assert (Hc' : ASTA RTA Σ2 PMc (eq (MS (mkR ra0 (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 QUAR)
                                             (Z_to_bv 64 (l_T (lay Σ2) + 80)) a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' (Z_to_bv 64 0x100000)
                                             s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1a038c) fc None m5 (seg_rom ctasegs))) cf).
    { split; [exact Hmc|]. split; [unfold enq_ret_st in E5; exact (eq_sym E5)|]. split; [exact HPM | exact HZ]. }
    apply (DRAIN Σ2 PMc ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m5 lo usp
             w0 w1 w2 w3 s4 w5 s6 FDO MST ART5 WX5 WC5 ltac:(clear - HBY; lia) FR5 ST5 ltac:(rewrite ELY; exact HLO) ltac:(clear - HLO2; lia)
             ltac:(clear - Husp; unfold USTACK_TOP in *; lia) MI5 T cf Hc').
    intros c2 (Σ' & Hc2 & EL' & EF' & ELY' & EC').
    apply Hk.
    exists Σ'. split; [|split; [exact (eq_trans EL' EL) | split; [exact (eq_trans EF' EF) | split; [unfold rtA_sp0; rewrite ELY', ELY; reflexivity | exact (eq_trans EC' EC)]]]].
    unfold ASTA in Hc2 |- *. eapply AST_conseq; [exact Hc2| |intros mo H; exact H].
    intros ms (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F' & fc' & m6 & -> & ART6 & MI6 & ST6 & RP6).
    exists w0, w1, w2, w3, w5, y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, F', fc', m6. split; [reflexivity|].
    split; [exact ART6|]. split; [exact MI6|]. split; [exact ST6|].
    assert (AG : forall a : word, usp - 2128 <= bv_unsigned a < usp -> m6 a = m5 a).
    { intros a Ha. apply RP6. left. clear - Ha Husp. unfold USTACK_TOP in *. lia. }
    split; [|exact (ricpt_frame_agree m5 m6 usp ra s0 s1 s2 s3 s4 s5 ICF5 AG)].
    intros a Ha.
    rewrite (RP6 a) by (rewrite EL' in Ha; destruct Ha as [Ha|Ha]; [left; unfold USTACK_TOP in *; lia | right; rewrite EF; exact Ha]).
    exact (RP5 a ltac:(rewrite EL' in Ha; exact Ha)).
Qed.

End FinR.
