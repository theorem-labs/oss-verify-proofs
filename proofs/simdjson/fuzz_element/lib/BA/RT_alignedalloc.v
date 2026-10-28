(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_defs D_kit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs R_prim_defs R_glue_defs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import R_thread R_m2s. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_poison R_leaves R_setshadow R_depot_defs R_unwind_defs R_asan_defs R_allocate1 R_asan_malloc R_intalloc RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_facts RT_malpre RT_maltail RT_freelift RT_malcore_stmt R_unwind_gen RT_gentrace RT_iface5 RT_refillstmt RT_malloc R_alalloc1 R_alasan RT_almaltail RT_almalcore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GWf.

Section Back.
Variables (Σ : rtsA) (PMc : Model -> Prop) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (fc : bv 32) (m mp m1 : mem) (n lo : Z)
          (tb : list word) (w : word) (jp jq : list byte).
Hypothesis MST : mat_stable PMc.
Hypothesis Hn1 : 1 <= n.
Hypothesis HA : ART_A Σ m.
Hypothesis LOW : l_ACEIL (lay Σ) <= lo.
Hypothesis LOR : lo + 0x10000 <= bv_unsigned sp.
Hypothesis SPT : bv_unsigned sp + 16 <= USTACK_TOP.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis MU0 : munch [(bv_unsigned sp - 64, bv_unsigned sp)] m mp.
Hypothesis WM0 : wmono asegs m mp.
Hypothesis MU1 : munch [(l_T (lay Σ) + 3168, l_T (lay Σ) + 3169); (bv_unsigned sp - 2320, bv_unsigned sp - 64)] mp m1.
Hypothesis WM1 : wmono asegs mp m1.
Hypothesis IC1 : rw_cells asegs m1 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Hypothesis IC2 : rw_cells asegs m1 (bv_unsigned sp + -72) [CB 8 jp].
Hypothesis IC3 : rw_cells asegs m1 (bv_unsigned sp + -80) [C8 (Z_to_bv 64 (bv_unsigned sp))].
Hypothesis TB1 : u64arr asegs m1 (bv_unsigned sp + -2120) tb.
Hypothesis HTB : length tb = 255%nat.
Hypothesis IC4 : rw_cells asegs m1 (bv_unsigned sp + -2136) [C8 (Z_to_bv 64 (bv_unsigned sp + -2120)); C8 w].
Hypothesis IC5 : rw_cells asegs m1 (bv_unsigned sp + -2144) [CB 8 jq].
Hypothesis IC6 : rw_cells asegs m1 (bv_unsigned sp + -2176) [C8 (Z_to_bv 64 16); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (bv_unsigned sp)); C8 (Z_to_bv 64 0x836cc)].
#[local] Notation usp := (bv_unsigned sp).

Lemma bka_agree : forall (m' : mem) a k, rt_pres (live Σ) (frames Σ) (usp + -2176) m1 m' -> usp + -2176 <= a -> a + k <= USTACK_TOP ->
  agree_on (fun x => a <= x < a + k) m1 m'.
Proof. intros m' a k P H1 H2 x Hx. apply P. left. lia. Qed.

Theorem back_cps_al : cps asegs (core_post_al fc Σ PMc (usp + -2160) gp (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 16) (Z_to_bv 64 16) (Z_to_bv 64 aligned_pc)
                                            (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 n lo m1)
                                (malloc_postF RTA fc Σ PMc ra sp gp (Z_to_bv 64 0x6a7e68) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 n lo m).
Proof using MST Hn1 HA LOW LOR SPT SPA MU0 WM0 MU1 WM1 IC1 IC2 IC3 TB1 HTB IC4 IC5 IC6.
  intros TT c2 Hc2 Hk. destruct Hc2 as (Σ' & p & HAST & HL & HAN & HF & HS & HCR & Hp0 & Hp16 & HpU).
  assert (Hsp0 : l_ACEIL (lay Σ) + 0xF000 <= usp) by lia.
  assert (Hsp32 : l_ACEIL (lay Σ) + 0xF000 <= usp - 32) by lia.
  assert (LO8 : 0x7fff7f800000 <= lo) by (pose proof (rta_sp0_win Σ m HA); unfold l_ACEIL, rtA_sp0, STACK_WIN in *; lia).
  assert (W2 : forall ms, (exists m', ret_stF fc (Z_to_bv 64 0x5c248) (Z_to_bv 64 (usp + -2160 + -16)) gp (Z_to_bv 64 tpA) (Z_to_bv 64 (usp + -2136))
                                      (Z_to_bv 64 16) (Z_to_bv 64 16) (Z_to_bv 64 aligned_pc) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89))
                                      s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
                            /\ ART_A Σ' m' /\ mem_inv asegs m' /\ wmono asegs m1 m' /\ stk asegs m' lo (usp + -2160 + -16)
                            /\ rt_pres (live Σ) (frames Σ) (usp + -2160 + -16) m1 m' /\ wr_at asegs m' p n /\ acc asegs m' p n) ->
             evt asegs (fun ms => exists m'', ret_stF fc ra sp gp (Z_to_bv 64 0x6a7e68) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m'' ms
                  /\ rt_after RTA Σ' usp lo m m'' /\ rt_pres (rt_live RTA Σ) (rt_frames RTA Σ) usp m m''
                  /\ wr_at asegs m'' p n /\ acc asegs m'' p n) ms).
  { intros ms (m' & (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F' & ->) & ART' & MI' & WM' & ST' & PR' & WR' & AC').
    replace (usp + -2160 + -16) with (usp + -2176) in * by lia.
    rewrite (ret_pc_even 0x5c248) by (lia || reflexivity).
    assert (AG : forall a k, usp + -2176 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m1 m')
      by (intros a k H1 H2; exact (bka_agree m' a k PR' H1 H2)).
    assert (TB' : u64arr asegs m' (usp + -2120) (ma_dec64 255 (u64s tb))).
    { pose proof (u64arr_rw_ma m1 _ _ TB1) as X. rewrite HTB in X.
      apply ma_rw_cells_u64arr. apply (rw_cells_agree asegs m1 m' _ _ X); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM']. }
    eapply evt_mono.
    { apply (aligned_B_spec ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 16) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 16)
               (Z_to_bv 64 aligned_pc) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 t3 t4 t5 t6
               (Z_to_bv 64 0x5c248) s0 s1 s2 s3 s4 s5 s6 F' fc m' p lo (ma_dec64 255 (u64s tb)) w (Z_to_bv 64 16) (Z_to_bv 64 n) jp jq).
      - unfold USTACK_TOP in HpU. lia.
      - exact ST'.
      - lia.
      - lia.
      - apply (rw_cells_agree asegs m1 m' _ _ IC1); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM'].
      - apply (rw_cells_agree asegs m1 m' _ _ IC2); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM'].
      - apply (rw_cells_agree asegs m1 m' _ _ IC3); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM'].
      - exact TB'.
      - apply ma_dec64_length.
      - apply (rw_cells_agree asegs m1 m' _ _ IC4); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM'].
      - apply (rw_cells_agree asegs m1 m' _ _ IC5); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM'].
      - apply (rw_cells_agree asegs m1 m' _ _ IC6); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM'].
      - exact MI'. }
    intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'' & -> & MU'' & WM'' & MI'' & ST'').
    exists m''. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F'; reflexivity|].
    assert (MUC : munch (W_client Σ' (usp + -2176)) m' m'').
    { eapply (munch_weaken _ _ m' m''); [|exact MU'']. intros x Hx. unfold W_client in Hx. cbn [app outside] in Hx |- *.
      destruct Hx as (X1 & _). split; [lia | exact I]. }
    assert (Hsp' : rtA_sp0 Σ' - STACK_WIN <= usp + -2176) by (rewrite HS; unfold l_ACEIL, rtA_sp0 in *; lia).
    split.
    { split; [exact (ART_transport _ Σ' m' m'' ART' MUC WM'' (art_avoid_client Σ' m' (usp + -2176) ART' Hsp'))|].
      split; [exact MI''|]. split; [exact (wmono_trans asegs _ _ _ WM0 (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM' WM'')))|]. exact ST''. }
    split.
    { intros a Ha. cbn [rt_live rt_frames RTA] in Ha. unfold rtA_live, rtA_frames in Ha. apply aclient_vis in Ha.
      pose proof (fn_client Σ m usp HA Hsp0 (bv_unsigned a) Ha) as Ho. unfold W_fn in Ho. cbn [outside] in Ho.
      destruct Ho as (O1 & _ & _ & O4 & _).
      pose proof (fn_client Σ m (usp - 32) HA Hsp32 (bv_unsigned a) ltac:(destruct Ha as [Ha|Ha]; [left; lia | right; exact Ha])) as Ho'.
      unfold W_fn in Ho'. cbn [outside] in Ho'. destruct Ho' as (_ & _ & _ & O4' & _).
      rewrite (MU'' a ltac:(cbn [outside]; split; [lia | exact I])).
      rewrite (PR' a ltac:(destruct Ha as [Ha|Ha]; [left; lia | right; exact Ha])).
      rewrite (MU1 a ltac:(cbn [outside]; split; [exact O1|]; split; [lia | exact I])).
      exact (MU0 a ltac:(cbn [outside]; split; [lia | exact I])). }
    split; [exact (wr_at_wmono m' m'' _ _ WR' WM'')|].
    apply (acc_transport _ m' m'' _ _ AC' MU''); [lia|].
    assert (Hsh : shad (p + n - 1) + 1 <= 2 ^ 44 + SHB + 1) by (unfold shad; assert ((p + n - 1) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; unfold USTACK_TOP in HpU; lia); lia).
    cbn [disjoint_from]. unfold SHB in *. split; [left; lia | exact I]. }
  apply (cps_realizes asegs _ _ _ c2 (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ') _ _ _ (fl_ASTA_mat_stable Σ' PMc MST) W2) HAST).
  intros c3 Hc3. apply Hk. exists Σ', p. split; [exact Hc3|].
  cbn [rt_live rt_frames rt_sp0 rt_credit RTA]. unfold rtA_live, rtA_frames, rtA_sp0, rtA_credit.
  split.
  { destruct c3 as [ms3 mo3]. destruct Hc3 as (_ & (m3 & _ & (ART3 & _) & _) & _).
    destruct ART3 as ((_ & _ & (_ & ND3 & _) & _) & _).
    rewrite HL, HAN. apply vis_live_fresh_cons. rewrite <- HL. exact (proj1 (stdpp.base.NoDup_ListNoDup _) ND3). }
  split; [exact HF|]. split; [exact HS|]. split; [exact HCR|]. split; [exact Hp0|]. split; [exact Hp16 | exact HpU].
Qed.

End Back.

Theorem rta_aligned_alloc : refill_stmt -> aligned_alloc_contract RTA.
Proof.
  intros RF Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    FDO MST Ha0 Ha1 Htp Hlen Hcr ART0 MI0 CALL UWOK. subst a0 a1 tp. unfold EXC_SIZE in *.
  intros TT cf Hc Hk. cbn [ART rt_live rt_frames rt_sp0 rt_credit RTA] in Hlen, Hcr, ART0.
  unfold rtA_live, rtA_credit in Hlen, Hcr.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA). cbn [rt_sp0 RTA] in LOW. unfold rtA_sp0 in LOW.
  pose proof (mp_cells Σ m ART0) as (G60 & GCF & MX & RZ & AI & MCS & RSS & PSC & FUM & TC & SC & UB).
  pose proof (mp_layout Σ m sp lo ART0 CALL) as (HTCX & HTCXl & HTl & HTT & HLOH & Hbt & Htop & HT).
  pose proof (geo_grant Σ m ART0 (l_T (lay Σ)) 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (GT1 & _).
  assert (LOW' : l_ACEIL (lay Σ) <= lo) by (unfold l_ACEIL; lia).
  destruct (art_trace_main Σ m aligned_pc ra s0 sp ART0 ltac:(unfold l_ACEIL, RT_STACK in *; lia) UWOK ltac:(unfold aligned_pc; lia))
    as (ch & tr & CHC & HTR & Htr & Htrl).
  assert (W1 : evt asegs (aligned_A_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 144 (l_T (lay Σ)) lo tr m)
                 (entry_st ra sp gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s0 s1 (Z_to_bv 64 16) (Z_to_bv 64 144) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                    t3 t4 t5 t6 F fc e_aligned_alloc m)).
  { unfold entry_st, e_aligned_alloc.
    exact (aligned_A_spec ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m 144
             (l_TCX (lay Σ)) (l_T (lay Σ)) (l_top (lay Σ)) (l_top (lay Σ) - 0x800000) lo ch tr
             ltac:(lia) eq_refl eq_refl ltac:(vm_compute; discriminate) ST ltac:(unfold RT_STACK in LOR; lia) HLOH ltac:(unfold USTACK_TOP in SPT; lia) ltac:(lia) ltac:(lia) CHC HTR
             G60 GCF MX RZ AI MCS RSS PSC FUM TC HTCX HTCXl GT1 HT HTl HTT SC UB MI0). }
  assert (W1' : forall ms, eq (entry_st ra sp gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s0 s1 (Z_to_bv 64 16) (Z_to_bv 64 144) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
                                   s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_aligned_alloc m) ms ->
                  evt asegs (aligned_A_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 144 (l_T (lay Σ)) lo tr m) ms)
    by (intros ms <-; exact W1).
  clear W1.
  apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1') Hc).
  intros c1 Hc1. unfold aligned_A_post in Hc1.
  apply AST_exI in Hc1 as (t0' & Hc1). apply AST_exI in Hc1 as (t1' & Hc1). apply AST_exI in Hc1 as (t2' & Hc1).
  apply AST_exI in Hc1 as (a4' & Hc1). apply AST_exI in Hc1 as (a5' & Hc1). apply AST_exI in Hc1 as (a6' & Hc1).
  apply AST_exI in Hc1 as (a7' & Hc1). apply AST_exI in Hc1 as (t3' & Hc1). apply AST_exI in Hc1 as (t4' & Hc1).
  apply AST_exI in Hc1 as (t5' & Hc1). apply AST_exI in Hc1 as (t6' & Hc1). apply AST_exI in Hc1 as (tb & Hc1).
  apply AST_exI in Hc1 as (jp & Hc1). apply AST_exI in Hc1 as (jq & Hc1). apply AST_exI in Hc1 as (j0 & Hc1).
  apply AST_exI in Hc1 as (mp & Hc1). apply AST_exI in Hc1 as (m1 & Hc1).
  destruct Hc1 as (HM & HPm & HPM & HZ).
  destruct HPm as (Hms & MU0 & WM0 & MU1 & WM1 & MI1 & IC1 & IC2 & IC3 & TB1 & HTB & IC4 & IC5 & IC6 & AFr & J0 & UB1 & ST1).
  set (usp := bv_unsigned sp) in *.
  assert (Hsp64 : rtA_sp0 Σ - STACK_WIN <= usp - 64) by (unfold rtA_sp0, l_ACEIL, RT_STACK in *; lia).
  assert (MUC0 : munch (W_client Σ (usp - 64)) m mp).
  { eapply (munch_weaken _ _ m mp); [|exact MU0]. intros x Hx. unfold W_client in Hx. cbn [app outside] in Hx |- *.
    destruct Hx as (X1 & _). split; [lia | exact I]. }
  pose proof (ART_transport _ Σ m mp ART0 MUC0 WM0 (art_avoid_client Σ m (usp - 64) ART0 Hsp64)) as ARTp.
  assert (Hsp32 : l_ACEIL (lay Σ) + 0xF000 <= usp - 32) by (unfold RT_STACK in LOR; lia).
  assert (MU1w : munch [(l_T (lay Σ) + 3168, l_T (lay Σ) + 3169); (usp - 32 - 2288, usp - 32)] mp m1).
  { eapply (munch_weaken _ _ mp m1); [|exact MU1]. intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (X1 & X2 & _).
    split; [exact X1|]. split; [lia | exact I]. }
  pose proof (front_ART Σ mp (usp - 32) ARTp Hsp32 m1 MU1w WM1 UB1) as ART1.
  assert (Hc2 : ASTA RTA Σ PMc (eq (core_entry_al Σ (usp + -2160) gp t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' F fc 144 m1)) c1).
  { split; [exact HM|]. split; [|split; [exact HPM | exact HZ]]. rewrite Hms. unfold core_entry_al.
    replace (usp + -2160 + -144) with (usp + -2304) by lia. replace (usp + -2160 + 24) with (usp + -2136) by lia. reflexivity. }
  assert (ST1' : stk asegs m1 lo (usp + -2160 + -144)) by (replace (usp + -2160 + -144) with (usp + -2304) by lia; exact ST1).
  assert (TRC : trc_cells (usp + -2160 + 24) tr m1 tb).
  { replace (usp + -2160 + 24) with (usp + -2136) by lia.
    split; [replace (usp + -2136 + 16) with (usp + -2120) by lia; exact IC4|]. split; [replace (usp + -2136 + 16) with (usp + -2120) by lia; exact TB1 | exact HTB]. }
  assert (AFC : af32_cells (usp + -2160) (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 16) (Z_to_bv 64 16) (Z_to_bv 64 aligned_pc) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2136))
                  (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 m1 j0).
  { split; replace (usp + -2160 + -144) with (usp + -2304) by lia; [exact AFr | exact J0]. }
  assert (LOR' : lo + 0x1000 <= usp + -2160 + -144) by (unfold RT_STACK in LOR; lia).
  assert (SPT' : usp + -2160 + 2144 <= USTACK_TOP) by lia.
  assert (SPA' : (usp + -2160) mod 16 = 0).
  { pose proof SPA as SPA0. apply Z.mod_divide in SPA0; [|lia]. destruct SPA0 as [q Hq]. apply Z.mod_divide; [lia|]. exists (q - 135). lia. }
  assert (SPT3 : usp + -2160 + 24 + 2064 <= 2 ^ 63) by (unfold USTACK_TOP in SPT; lia).
  assert (K : forall c2, core_post_al fc Σ PMc (usp + -2160) gp (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 16) (Z_to_bv 64 16) (Z_to_bv 64 aligned_pc) (Z_to_bv 64 1)
                           (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 144 lo m1 c2 -> realizes asegs c2 TT).
  { intros c2 Hc2'. exact (back_cps_al Σ PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fc m mp m1 144 lo (wr_trace tr tb) (Z_to_bv 64 (Z.of_nat (length tr))) jp jq
                             MST ltac:(lia) ART0 LOW' ltac:(unfold RT_STACK in LOR; lia) SPT SPA MU0 WM0 MU1 WM1 IC1 IC2 IC3 TB1 ltac:(rewrite wr_trace_length by lia; exact HTB) IC4 IC5 IC6 TT c2 Hc2' Hk). }
  exact (core_prim_al RF Σ PMc m1 (usp + -2160) gp (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 16) (Z_to_bv 64 16) (Z_to_bv 64 aligned_pc) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2136))
           (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' F fc 144 lo tr tb j0
           FDO MST ltac:(cbv beta; lia) ltac:(lia) ltac:(pose proof (vis_live_length (ann Σ) (live Σ)); lia) Hcr ART1 MI1 ST1' LOW' LOR' SPT' SPA' Htr Htrl TRC AFC
           ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity) SPT3 TT c1 Hc2 K).
Qed.
