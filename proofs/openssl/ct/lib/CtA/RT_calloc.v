(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Mem Frame Cells Step Arr Exec RzCPS MState. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_glue_defs R_thread R_m2s R_poison R_leaves R_setshadow R_depot_defs R_unwind_defs R_asan_defs R_allocate1 R_asan_malloc R_asan_calloc R_intalloc I_lkit RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_facts RT_artfacts RT_malpre RT_maltail RT_freelift RT_malloc RT_refillstmt RT_caltail RT_calcore_stmt RT_calcore_m RT_calfront R_unwind_chain RT_sites.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Back.
Variables (Σ : rtsA) (PMc : Model -> Prop) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m m1 : mem) (k sz lo : Z)
          (tb : list word) (w : word) (jp jq jr : list byte).
Hypothesis MST : mat_stable PMc.
Hypothesis Hn : 1 <= k * sz <= 64512.
Hypothesis HA : ART_A Σ m.
Hypothesis LOW : l_ACEIL (lay Σ) <= lo.
Hypothesis LOR : lo + 0xF000 <= bv_unsigned sp.
Hypothesis SPT : bv_unsigned sp + 16 <= USTACK_TOP.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis MU1 : munch [(l_T (lay Σ) + 3168, l_T (lay Σ) + 3169); (bv_unsigned sp - 2336, bv_unsigned sp)] m m1.
Hypothesis WM1 : wmono ctasegs m m1.
Hypothesis IC1 : rw_cells ctasegs m1 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Hypothesis IC2 : rw_cells ctasegs m1 (bv_unsigned sp + -72) [CB 8 jp].
Hypothesis IC3 : rw_cells ctasegs m1 (bv_unsigned sp + -80) [C8 (Z_to_bv 64 (bv_unsigned sp))].
Hypothesis TB1 : u64arr ctasegs m1 (bv_unsigned sp + -2120) tb.
Hypothesis HTB : length tb = 255%nat.
Hypothesis IC4 : rw_cells ctasegs m1 (bv_unsigned sp + -2136) [C8 (Z_to_bv 64 (bv_unsigned sp + -2120)); C8 w].
Hypothesis IC5 : rw_cells ctasegs m1 (bv_unsigned sp + -2144) [CB 8 jq].
Hypothesis IC6 : rw_cells ctasegs m1 (bv_unsigned sp + -2184)
                   [C8 (Z_to_bv 64 calloc_pc); C8 (Z_to_bv 64 k); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 (bv_unsigned sp)); C8 (Z_to_bv 64 0x1c45e0)].
Hypothesis IC7 : rw_cells ctasegs m1 (bv_unsigned sp + -2192) [CB 8 jr].
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation n := (k * sz).

Lemma cbk_agree : forall (m' : mem) a j, rt_pres (live Σ) (frames Σ) (usp + -2192) m1 m' -> usp + -2192 <= a -> a + j <= USTACK_TOP ->
  agree_on (fun x => a <= x < a + j) m1 m'.
Proof. intros m' a j P H1 H2 x Hx. apply P. left. lia. Qed.

Theorem cback_cps : cps ctasegs (ccore_post Σ PMc (usp + -2136) gp (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 INST) (Z_to_bv 64 1)
                                          (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 n lo m1)
                              (calloc_post RTA Σ PMc ra sp gp (Z_to_bv 64 0xba93f0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 n lo m).
Proof using MST Hn HA LOW LOR SPT SPA MU1 WM1 IC1 IC2 IC3 TB1 HTB IC4 IC5 IC6 IC7.
  intros TT c2 Hc2 Hk. destruct Hc2 as (Σ' & p & HAST & HL & HF & HS & HCR & Hp0 & Hp16 & HpU).
  assert (Hsp0 : l_ACEIL (lay Σ) + 0xF000 <= usp) by lia.
  assert (W2 : forall ms, (exists m', ret_st (Z_to_bv 64 0x19c6f8) (Z_to_bv 64 (usp + -2136 + -56)) gp (Z_to_bv 64 tpA) (Z_to_bv 64 n)
                                      (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 INST) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2136))
                                      (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
                            /\ ART_A Σ' m' /\ mem_inv ctasegs m' /\ wmono ctasegs m1 m' /\ stk ctasegs m' lo (usp + -2136 + -56)
                            /\ rt_pres (live Σ) (frames Σ) (usp + -2136 + -56) m1 m' /\ wr_at ctasegs m' p n /\ acc ctasegs m' p n) ->
             evt ctasegs (fun ms => exists m'', ret_st ra sp gp (Z_to_bv 64 0xba93f0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m'' ms
                  /\ rt_after RTA Σ' usp lo m m'' /\ rt_pres (rt_live RTA Σ) (rt_frames RTA Σ) usp m m''
                  /\ wr_at ctasegs m'' p n /\ acc ctasegs m'' p n /\ bytes_at ctasegs m'' p (repeat (Z_to_bv 8 0) (Z.to_nat n))) ms).
  { intros ms (m' & (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F' & fc' & ->) & ART' & MI' & WM' & ST' & PR' & WR' & AC').
    replace (usp + -2136 + -56) with (usp + -2192) in * by lia.
    rewrite (ret_pc_even 0x19c6f8) by (lia || reflexivity).
    assert (AG : forall a j, usp + -2192 <= a -> a + j <= USTACK_TOP -> agree_on (fun x => a <= x < a + j) m1 m')
      by (intros a j H1 H2; exact (cbk_agree m' a j PR' H1 H2)).
    assert (TB' : u64arr ctasegs m' (usp + -2120) (ma_dec64 255 (u64s tb))).
    { pose proof (u64arr_rw_ma m1 _ _ TB1) as X. rewrite HTB in X.
      apply ma_rw_cells_u64arr. apply (rw_cells_agree ctasegs m1 m' _ _ X); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM']. }
    (* [comment removed for export] *)
    assert (Hin' : In (p, n) (live Σ')) by (rewrite HL; left; reflexivity).
    pose proof (geo_prb Σ' m' ART') as (P1 & P2 & P3).
    pose proof (geo_grant Σ' m' ART' (l_PRB (lay Σ')) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (G1 & G2 & G3 & G4 & G5).
    pose proof (rta_sp0_win Σ' m' ART') as Hw'.
    assert (HSBp : l_SB (lay Σ') <= p /\ p + n <= l_SB (lay Σ') + 2 ^ 37).
    { destruct (geo_live Σ' m' ART' p n Hin') as [(c & i & Hc & Hni & -> & Y1 & Y2 & Y3 & Y4 & Y5)|(s & Hs & _ & Hn' & _)].
      - unfold rb, kUserCap in *. lia.
      - exfalso. pose proof (ART_wf Σ' m' ART') as (_ & _ & _ & HSW & _). destruct HSW as (_ & _ & _ & SW4 & _).
        pose proof (proj1 (Forall_forall _ _) SW4 s Hs) as ((Tn1 & _) & _). lia. }
    assert (HACE : l_ACEIL (lay Σ') = l_ACEIL (lay Σ)) by (unfold l_ACEIL; unfold rtA_sp0 in HS; rewrite HS; reflexivity).
    assert (HPlo : p + n <= lo /\ 0xbcb000 <= l_SB (lay Σ') /\ l_SB (lay Σ') + 2 ^ 37 <= 2 ^ 47 /\ 0x10007fff8000 <= p).
    { unfold l_ACEIL, rtA_sp0, STACK_WIN, SEGTOP_A, K_HIGH_SHADOW_hi, K_LOW_SHADOW_lo, USTACK_TOP in *. destruct G4 as [G4|G4]; lia. }
    destruct HPlo as (HPlo & HSB0 & HSBt & HPhi).
    pose proof (ART_consts Σ' m' ART') as ((SBC0 & _) & _ & _ & _ & (_ & _ & SS' & _) & _).
    assert (SBC : rw_cells ctasegs m' i_spacebeg [C8 (Z_to_bv 64 (l_SB (lay Σ')))]) by exact (rw_cells_app_l m' _ [C8 (Z_to_bv 64 (l_SB (lay Σ')))] _ SBC0).
    destruct (wr_at_rw_CB m' p n WR' ltac:(lia)) as (uj & UJ).
    eapply evt_mono.
    { apply (calloc_B_spec ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 (usp + -2136)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2136))
               (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 t3 t4 t5 t6 (Z_to_bv 64 0x19c6f8) s0 s1 s2 s3 s4 s5 s6
               (Z_to_bv 64 usp) (Z_to_bv 64 sz) (Z_to_bv 64 k) (Z_to_bv 64 calloc_pc) F' fc' m' p n (l_SB (lay Σ')) lo (ma_dec64 255 (u64s tb)) w jp jq jr uj).
      - lia.
      - exact HSB0.
      - exact (proj1 HSBp).
      - exact (proj2 HSBp).
      - exact HSBt.
      - exact HPlo.
      - exact ST'.
      - lia.
      - unfold l_ACEIL, rtA_sp0, STACK_WIN, SEGTOP_A in *. pose proof (rta_sp0_win Σ m HA). unfold rtA_sp0 in *. lia.
      - apply (rw_cells_agree ctasegs m1 m' _ _ IC1); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM'].
      - apply (rw_cells_agree ctasegs m1 m' _ _ IC2); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM'].
      - apply (rw_cells_agree ctasegs m1 m' _ _ IC3); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM'].
      - exact TB'.
      - apply ma_dec64_length.
      - apply (rw_cells_agree ctasegs m1 m' _ _ IC4); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM'].
      - apply (rw_cells_agree ctasegs m1 m' _ _ IC5); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM'].
      - apply (rw_cells_agree ctasegs m1 m' _ _ IC6); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM'].
      - apply (rw_cells_agree ctasegs m1 m' _ _ IC7); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM'].
      - exact SBC.
      - exact SS'.
      - exact UJ.
      - exact MI'. }
    intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'' & -> & MU'' & WM'' & MI'' & ZB'' & ST'').
    exists m''. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F', fc'; reflexivity|].
    (* [comment removed for export] *)
    assert (MUC : munch (W_client Σ' (usp + -2192)) m' m'').
    { eapply (munch_weaken _ _ m' m''); [|exact MU'']. intros x Hx. unfold W_client in Hx. cbn [app outside] in Hx |- *.
      destruct Hx as (X1 & X2). split; [|split; [lia | exact I]].
      intros Hpx. destruct (outside_app_inv _ _ _ X2) as (_ & X3). destruct (outside_app_inv _ _ _ X3) as (X4 & _).
      refine (not_outside _ p (p + n) x _ Hpx X4). rewrite HL. left. reflexivity. }
    assert (Hsp' : rtA_sp0 Σ' - STACK_WIN <= usp + -2192) by (rewrite HS; unfold l_ACEIL, rtA_sp0 in *; lia).
    split.
    { split; [exact (ART_transport _ Σ' m' m'' ART' MUC WM'' (art_avoid_client Σ' m' (usp + -2192) ART' Hsp'))|].
      split; [exact MI''|]. split; [exact (wmono_trans ctasegs _ _ _ WM1 (wmono_trans ctasegs _ _ _ WM' WM''))|]. exact ST''. }
    split.
    { (* [comment removed for export] *)
      intros a Ha. cbn [rt_live rt_frames RTA] in Ha. unfold rtA_live, rtA_frames in Ha.
      pose proof (fc_client Σ m usp HA Hsp0 (bv_unsigned a) Ha) as Ho. unfold W_fc in Ho. cbn [outside] in Ho.
      destruct Ho as (O1 & _ & _ & O4 & _).
      assert (NP : ~ (p <= bv_unsigned a < p + n)).
      { intros Hpa. destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
        - lia.
        - destruct Ha as ((lo0 & hi0 & Hin0 & Hlh0) & _). unfold CLIENT_STATIC in Hin0.
          repeat (destruct Hin0 as [E|Hin0]; [injection E as <- <-; lia|]). destruct Hin0.
        - destruct Ha as (p2 & n2 & Hin2 & Hp2).
          pose proof (af_live_disj RTA rta_art_facts Σ' m' p n p2 n2 [] (live Σ) ART' HL Hin2) as D. lia.
        - destruct Ha as (f & kf & Hinf & Hf). rewrite <- HF in Hinf.
          pose proof (af_frames_range RTA rta_art_facts Σ' m' f kf ART' Hinf) as (_ & _ & _ & D). specialize (D p n Hin'). lia.
        - destruct Ha as (f & kf & Hinf & Hf). rewrite <- HF in Hinf.
          pose proof (af_fshadow_apart RTA rta_art_facts Σ' m' f kf ART' Hinf) as (D & _). specialize (D p n Hin'). lia. }
      rewrite (MU'' a ltac:(cbn [outside]; split; [exact NP|]; split; [lia | exact I])).
      rewrite (PR' a ltac:(destruct Ha as [Ha|Ha]; [left; lia | right; exact Ha])).
      exact (MU1 a ltac:(cbn [outside]; split; [exact O1|]; split; [exact O4 | exact I])). }
    split; [exact (wr_at_wmono m' m'' _ _ WR' WM'')|].
    split.
    { apply (acc_transport _ m' m'' _ _ AC' MU''); [lia|].
      assert (Hsh : shad (p + n - 1) + 1 <= 2 ^ 44 + SHB) by (unfold shad; assert ((p + n - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; unfold USTACK_TOP in HpU; lia); lia).
      cbn [disjoint_from]. unfold SHB in *. split; [left; lia|]. split; [left; lia | exact I]. }
    destruct ZB'' as [[_ DB] _]. cbn [cells_bytes cbytes] in DB. rewrite app_nil_r in DB. exact DB. }
  apply (cps_realizes ctasegs _ _ _ c2 (ast_evt ctasegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ') _ _ _ (fl_ASTA_mat_stable Σ' PMc MST) W2) HAST).
  intros c3 Hc3. apply Hk. exists Σ', p. split; [exact Hc3|].
  cbn [rt_live rt_frames rt_sp0 rt_credit RTA]. unfold rtA_live, rtA_frames, rtA_sp0, rtA_credit.
  split; [exact HL|]. split; [exact HF|]. split; [exact HS|]. split; [exact HCR|]. split; [exact Hp0|]. split; [exact Hp16 | exact HpU].
Qed.

End Back.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem rta_calloc_of : core_stmt_calloc -> calloc_contract RTA.
Proof.
  intros CP Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m k sz lo
    FDO MST Hk Hsz Hn Ha0 Ha1 Htp Hlen Hcr ART0 MI0 CALL UWOK. subst a0 a1 tp.
  intros TT cf Hc Hkk. cbn [ART rt_live rt_frames rt_sp0 rt_credit RTA] in Hlen, Hcr, ART0.
  unfold rtA_live, rtA_credit in Hlen, Hcr.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA). cbn [rt_sp0 RTA] in LOW. unfold rtA_sp0 in LOW.
  pose proof (mp_cells Σ m ART0) as (G60 & GCF & MX & RZ & AI & MCS & RSS & PSC & FUM & TC & SC & UB).
  pose proof (mp_layout Σ m sp lo ART0 CALL) as (HTCX & HTCXl & HTl & HTT & HLOH & Hbt & Htop & HT).
  pose proof (geo_grant Σ m ART0 (l_T (lay Σ)) 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (GT1 & _).
  assert (LOW' : l_ACEIL (lay Σ) <= lo) by (unfold l_ACEIL; lia).
  destruct (site_trace_main m calloc_pc (l_top (lay Σ) - 0x800000) (l_top (lay Σ)) ra s0 sp ltac:(right; right; left; reflexivity) UWOK ltac:(lia))
    as (ch & tr & CHC & HTR & Htr & Htrl).
  assert (W1 : evt ctasegs (calloc_A_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc k sz (l_T (lay Σ)) lo tr m)
                 (entry_st ra sp gp (Z_to_bv 64 0xba93f0) t0 t1 t2 s0 s1 (Z_to_bv 64 k) (Z_to_bv 64 sz) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                    t3 t4 t5 t6 F fc e_calloc m)).
  { unfold entry_st, e_calloc.
    exact (calloc_A_spec ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m k sz
             (l_TCX (lay Σ)) (l_T (lay Σ)) (l_top (lay Σ)) (l_top (lay Σ) - 0x800000) lo ch tr
             Hk Hsz ltac:(lia) ST ltac:(unfold RT_STACK in LOR; lia) HLOH ltac:(unfold USTACK_TOP in SPT; lia) ltac:(lia) ltac:(lia) CHC HTR
             G60 GCF MX RZ AI MCS RSS PSC FUM TC HTCX HTCXl GT1 HT HTl HTT SC UB MI0). }
  assert (W1' : forall ms, eq (entry_st ra sp gp (Z_to_bv 64 0xba93f0) t0 t1 t2 s0 s1 (Z_to_bv 64 k) (Z_to_bv 64 sz) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
                                   s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_calloc m) ms ->
                  evt ctasegs (calloc_A_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc k sz (l_T (lay Σ)) lo tr m) ms)
    by (intros ms <-; exact W1).
  clear W1.
  apply (cps_realizes ctasegs _ _ _ cf (ast_evt ctasegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1') Hc).
  intros c1 Hc1. unfold calloc_A_post in Hc1.
  apply AST_exI in Hc1 as (t0' & Hc1). apply AST_exI in Hc1 as (t1' & Hc1). apply AST_exI in Hc1 as (t2' & Hc1).
  apply AST_exI in Hc1 as (a4' & Hc1). apply AST_exI in Hc1 as (a5' & Hc1). apply AST_exI in Hc1 as (a6' & Hc1).
  apply AST_exI in Hc1 as (a7' & Hc1). apply AST_exI in Hc1 as (t3' & Hc1). apply AST_exI in Hc1 as (t4' & Hc1).
  apply AST_exI in Hc1 as (t5' & Hc1). apply AST_exI in Hc1 as (t6' & Hc1). apply AST_exI in Hc1 as (tb & Hc1).
  apply AST_exI in Hc1 as (jp & Hc1). apply AST_exI in Hc1 as (jq & Hc1). apply AST_exI in Hc1 as (jr & Hc1).
  apply AST_exI in Hc1 as (j0 & Hc1). apply AST_exI in Hc1 as (m1 & Hc1).
  destruct Hc1 as (HM & HPm & HPM & HZ).
  destruct HPm as (Hms & MU1 & WM1 & MI1 & IC1 & IC2 & IC3 & TB1 & HTB & IC4 & IC5 & IC6 & IC7 & AFr & J0 & UB1 & ST1).
  assert (Hsp0 : l_ACEIL (lay Σ) + 0xF000 <= bv_unsigned sp) by (unfold RT_STACK in LOR; lia).
  pose proof (cfront_ART Σ m (bv_unsigned sp) ART0 Hsp0 m1 MU1 WM1 UB1) as ART1.
  set (usp := bv_unsigned sp) in *.
  assert (Hc2 : ASTA RTA Σ PMc (eq (ccore_entry Σ (usp + -2136) gp t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' F fc (k * sz) m1)) c1).
  { split; [exact HM|]. split; [|split; [exact HPM | exact HZ]]. rewrite Hms. unfold ccore_entry.
    replace (usp + -2136 + -184) with (usp + -2320) by lia. reflexivity. }
  assert (ST1' : stk ctasegs m1 lo (usp + -2136 + -184)) by (replace (usp + -2136 + -184) with (usp + -2320) by lia; exact ST1).
  assert (TRC : trc_cells (usp + -2136) tr m1 tb).
  { split; [replace (usp + -2136 + 16) with (usp + -2120) by lia; exact IC4|]. split; [replace (usp + -2136 + 16) with (usp + -2120) by lia; exact TB1 | exact HTB]. }
  assert (AFC : caf_cells (usp + -2136) (Z_to_bv 64 (k * sz)) (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 INST) (Z_to_bv 64 1) (Z_to_bv 64 1)
                  (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 m1 j0).
  { split; replace (usp + -2136 + -184) with (usp + -2320) by lia; [exact AFr | exact J0]. }
  assert (LOR' : lo + 0x1000 <= usp + -2136 + -184) by (unfold RT_STACK in LOR; lia).
  assert (SPT' : usp + -2136 + 2144 <= USTACK_TOP) by lia.
  assert (SPA' : (usp + -2136) mod 16 = 8).
  { pose proof SPA as SPA0. apply Z.mod_divide in SPA0; [|lia]. destruct SPA0 as [q Hq].
    replace (usp + -2136) with (8 + (q - 134) * 16) by lia. rewrite Z_mod_plus_full. reflexivity. }
  assert (K : forall c2, ccore_post Σ PMc (usp + -2136) gp (Z_to_bv 64 (k * sz)) (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 INST) (Z_to_bv 64 1)
                           (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 (k * sz) lo m1 c2 -> realizes ctasegs c2 TT).
  { intros c2 Hc2'. exact (cback_cps Σ PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m m1 k sz lo (wr_trace tr tb) (Z_to_bv 64 (Z.of_nat (length tr))) jp jq jr
                             MST Hn ART0 LOW' ltac:(unfold RT_STACK in LOR; lia) SPT SPA MU1 WM1 IC1 IC2 IC3 TB1 ltac:(rewrite wr_trace_length by lia; exact HTB)
                             IC4 IC5 IC6 IC7 TT c2 Hc2' Hkk). }
  exact (CP Σ PMc m1 (usp + -2136) gp (Z_to_bv 64 (k * sz)) (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 INST) (Z_to_bv 64 1) (Z_to_bv 64 1)
           (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' F fc (k * sz) lo tr tb j0
           FDO MST Hn Hlen Hcr ART1 MI1 ST1' LOW' LOR' SPT' SPA' Htr Htrl TRC AFC TT c1 Hc2 K).
Qed.

(* [comment removed for export] *)
Theorem rta_calloc : refill_stmt -> calloc_contract RTA.
Proof. intros RF. exact (rta_calloc_of (ccore_prim RF)). Qed.
