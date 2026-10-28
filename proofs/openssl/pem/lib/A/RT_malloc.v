(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_glue_defs R_thread R_m2s R_poison R_leaves R_setshadow R_depot_defs R_unwind_defs R_asan_defs R_allocate1 R_asan_malloc R_intalloc RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_facts RT_malpre RT_maltail RT_freelift RT_malcore_stmt R_asan_front_k.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Front.
Variables (Σ : rtsA) (m : mem) (usp : Z).
Hypothesis HA : ART_A Σ m.
Hypothesis Hsp : l_ACEIL (lay Σ) + 0xF000 <= usp.   (* [comment removed for export] *)
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation W := (W_fn (l_T (lay Σ)) usp).

(* [comment removed for export] *)
Theorem front_ART : forall m', munch [(T + 3168, T + 3169); (usp - 2288, usp)] m m' -> wmono asegs m m' ->
  rw_cells asegs m' (T + 3168) [C1 (Z_to_bv 8 0)] -> ART_A Σ m'.
Proof using HA Hsp.
  intros m' MU0 WM TB. pose proof (ART_wf Σ m HA) as Hwf.
  assert (MU : munch W m m').
  { eapply (munch_weaken _ _ m m'); [|exact MU0]. intros x Hx. unfold W_fn in Hx. cbn [outside] in Hx |- *.
    destruct Hx as (X1 & _ & _ & X4 & _). split; [exact X1|]. split; [exact X4 | exact I]. }
  apply ART_intro; [exact Hwf | | | | | | | | | | |].
  - apply (consts_rep_frame (lay Σ) m m' (ART_consts Σ m HA)); [|exact WM].
    pose proof (mp_cells Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & UB).
    pose proof (fn_Tgrant Σ m HA) as (G1 & G2 & G3 & G4 & G5). pose proof (fn_aceil Σ m HA) as (_ & X).
    intros a Ha. destruct (Z.eq_dec (bv_unsigned a) (T + 3168)) as [E|NE].
    + assert (Ea : a = wa (T + 3168)) by (rewrite <- E; unfold wa; symmetry; apply Z_to_bv_bv_unsigned). subst a.
      assert (Hx : T + 3168 + 1 <= img_hull_lo \/ img_hull_hi <= T + 3168) by (unfold img_hull_lo, img_hull_hi, SEGTOP_A in *; lia).
      rewrite (fn_byte m' _ _ TB Hx ltac:(lia)), (fn_byte m _ _ UB Hx ltac:(lia)). reflexivity.
    + apply MU. exact (fn_consts Σ m usp HA Hsp _ Ha NE).
  - intros c Hc. exact (reg_rep_transport W _ c _ m m' (ART_prim Σ m HA c Hc) MU WM (proj1 (fn_reg Σ m usp HA Hsp c Hc))).
  - intros c Hc. exact (pclass_rep_transport W _ c _ _ m m' (ART_cache Σ m HA c Hc) MU WM (proj2 (fn_reg Σ m usp HA Hsp c Hc))).
  - destruct (ART_chunk Σ m HA) as [P S]. split.
    + intros c i st Hc Hn. exact (pchunk_transport W _ c i st m m' (P c i st Hc Hn) MU WM (fn_pchunk Σ m usp HA Hsp c i st Hc Hn)).
    + intros k s Hk. exact (schunk_transport W k s m m' (S k s Hk) MU WM (fn_schunk Σ m usp HA Hsp k s Hk)).
  - exact (sec_rep_transport W Σ m m' (ART_sec Σ m HA) MU WM (fn_sec Σ m usp HA Hsp)).
  - exact (quar_rep_transport W Σ m m' (ART_quar Σ m HA) MU WM (fn_quar Σ m usp HA Hsp)).
  - destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & Hdok & _).
    exact (dep_rep_transport W _ _ m m' (ART_dep Σ m HA) Hdok MU WM (fn_dep Σ m usp HA Hsp)).
  - exact (fs_rep_transport W Σ m m' (ART_fs Σ m HA) MU WM (fn_fs Σ m usp HA Hsp)).
  - (* [comment removed for export] *)
    pose proof (fn_Tgrant Σ m HA) as (G1 & G2 & G3 & G4 & G5). pose proof (fn_aceil Σ m HA) as (X0 & X). unfold SHB in X0.
    apply (ia_rep_transport _ Σ m m' (ART_ia Σ m HA) MU0 WM). unfold dsjl, ia_lits.
    repeat (apply Forall_cons; [cbn [fst snd disjoint_from]; unfold g_ia_word, IAP, SEGTOP_A in *;
                                split; [destruct G5; lia|]; split; [lia | exact I]|]). apply Forall_nil.
  - exact (shadow_rep_transport W _ m m' (ART_shadow Σ m HA) MU WM (fn_shadow Σ m usp HA Hsp)).
  - exact (vis_rep_wmono _ m m' (ART_vis Σ m HA) WM).
Qed.

End Front.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Back.
Variables (Σ : rtsA) (PMc : Model -> Prop) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m m1 : mem) (n lo : Z)
          (tb : list word) (w : word) (jp : list byte).
Hypothesis MST : mat_stable PMc.
Hypothesis Hn1 : 1 <= n.
Hypothesis HA : ART_A Σ m.
Hypothesis LOW : l_ACEIL (lay Σ) <= lo.
Hypothesis LOR : lo + 0xF000 <= bv_unsigned sp.   (* [comment removed for export] *)
Hypothesis SPT : bv_unsigned sp + 16 <= USTACK_TOP.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis MU1 : munch [(l_T (lay Σ) + 3168, l_T (lay Σ) + 3169); (bv_unsigned sp - 2288, bv_unsigned sp)] m m1.
Hypothesis WM1 : wmono asegs m m1.
Hypothesis IC1 : rw_cells asegs m1 (bv_unsigned sp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Hypothesis IC2 : rw_cells asegs m1 (bv_unsigned sp + -64) [CB 8 jp].
Hypothesis IC3 : rw_cells asegs m1 (bv_unsigned sp + -72) [C8 (Z_to_bv 64 (bv_unsigned sp))].
Hypothesis TB1 : u64arr asegs m1 (bv_unsigned sp + -2112) tb.
Hypothesis HTB : length tb = 255%nat.
Hypothesis IC4 : rw_cells asegs m1 (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2112)); C8 w].
Hypothesis IC5 : rw_cells asegs m1 (bv_unsigned sp + -2144) [C8 (Z_to_bv 64 (bv_unsigned sp)); C8 (Z_to_bv 64 0x1c32f8)].
#[local] Notation usp := (bv_unsigned sp).

Lemma bk_agree : forall (m' : mem) a k, rt_pres (live Σ) (frames Σ) (usp + -2144) m1 m' -> usp + -2144 <= a -> a + k <= USTACK_TOP ->
  agree_on (fun x => a <= x < a + k) m1 m'.
Proof. intros m' a k P H1 H2 x Hx. apply P. left. lia. Qed.

Theorem back_cps : cps asegs (core_post Σ PMc (usp + -2128) gp (Z_to_bv 64 usp) (Z_to_bv 64 n) (Z_to_bv 64 0x1c328c) (Z_to_bv 64 1)
                                         (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (usp + -81)) s6 s7 s8 s9 s10 s11 n lo m1)
                             (malloc_post RTA Σ PMc ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 n lo m).
Proof using MST Hn1 HA LOW LOR SPT SPA MU1 WM1 IC1 IC2 IC3 TB1 HTB IC4 IC5.
  intros TT c2 Hc2 Hk. destruct Hc2 as (Σ' & p & HAST & HL & HF & HS & HCR & Hp0 & Hp16 & HpU & HLAY).
  assert (Hsp0 : l_ACEIL (lay Σ) + 0xF000 <= usp) by (unfold RT_STACK in LOR; lia).
  assert (LO8 : 0x7fff7f800000 <= lo) by (pose proof (rta_sp0_win Σ m HA); unfold l_ACEIL, rtA_sp0, STACK_WIN in *; lia).
  assert (W2 : forall ms, (exists m', ret_st (Z_to_bv 64 0x19ac3c) (Z_to_bv 64 (usp + -2128 + -16)) gp (Z_to_bv 64 tpA) (Z_to_bv 64 usp)
                                      (Z_to_bv 64 n) (Z_to_bv 64 0x1c328c) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (usp + -81))
                                      s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
                            /\ ART_A Σ' m' /\ mem_inv asegs m' /\ wmono asegs m1 m' /\ stk asegs m' lo (usp + -2128 + -16)
                            /\ rt_pres (live Σ) (frames Σ) (usp + -2128 + -16) m1 m' /\ wr_at asegs m' p n /\ acc asegs m' p n) ->
             evt asegs (fun ms => exists m'', ret_st ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m'' ms
                  /\ rt_after RTA Σ' usp lo m m'' /\ rt_pres (rt_live RTA Σ) (rt_frames RTA Σ) usp m m''
                  /\ wr_at asegs m'' p n /\ acc asegs m'' p n) ms).
  { intros ms (m' & (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F' & fc' & ->) & ART' & MI' & WM' & ST' & PR' & WR' & AC').
    replace (usp + -2128 + -16) with (usp + -2144) in * by lia.
    rewrite (ret_pc_even 0x19ac3c) by (lia || reflexivity).
    assert (AG : forall a k, usp + -2144 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m1 m')
      by (intros a k H1 H2; exact (bk_agree m' a k PR' H1 H2)).
    assert (TB' : u64arr asegs m' (usp + -2112) (ma_dec64 255 (u64s tb))).
    { pose proof (u64arr_rw_ma m1 _ _ TB1) as X. rewrite HTB in X.
      apply ma_rw_cells_u64arr. apply (rw_cells_agree asegs m1 m' _ _ X); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM']. }
    eapply evt_mono.
    { apply (malloc_B_spec ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0x1c328c)
               (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (usp + -81)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               (Z_to_bv 64 0x19ac3c) s0 s1 s2 s3 s4 s5 F' fc' m' p lo (ma_dec64 255 (u64s tb)) w jp).
      - unfold USTACK_TOP in HpU. lia.
      - exact ST'.
      - unfold RT_STACK in LOR. lia.
      - lia.
      - apply (rw_cells_agree asegs m1 m' _ _ IC1); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM'].
      - apply (rw_cells_agree asegs m1 m' _ _ IC2); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM'].
      - apply (rw_cells_agree asegs m1 m' _ _ IC3); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM'].
      - exact TB'.
      - apply ma_dec64_length.
      - apply (rw_cells_agree asegs m1 m' _ _ IC4); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM'].
      - apply (rw_cells_agree asegs m1 m' _ _ IC5); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM'].
      - exact MI'. }
    intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'' & -> & MU'' & WM'' & MI'' & ST'').
    exists m''. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F', fc'; reflexivity|].
    assert (MUC : munch (W_client Σ' (usp + -2144)) m' m'').
    { eapply (munch_weaken _ _ m' m''); [|exact MU'']. intros x Hx. unfold W_client in Hx. cbn [app outside] in Hx |- *.
      destruct Hx as (X1 & _). split; [lia | exact I]. }
    assert (Hsp' : rtA_sp0 Σ' - STACK_WIN <= usp + -2144) by (rewrite HS; unfold l_ACEIL, rtA_sp0 in *; lia).
    split.
    { split; [exact (ART_transport _ Σ' m' m'' ART' MUC WM'' (art_avoid_client Σ' m' (usp + -2144) ART' Hsp'))|].
      split; [exact MI''|]. split; [exact (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM' WM''))|]. exact ST''. }
    split.
    { intros a Ha. cbn [rt_live rt_frames RTA] in Ha. unfold rtA_live, rtA_frames in Ha.
      pose proof (fn_client Σ m usp HA Hsp0 (bv_unsigned a) Ha) as Ho. unfold W_fn in Ho. cbn [outside] in Ho.
      destruct Ho as (O1 & _ & _ & O4 & _).
      rewrite (MU'' a ltac:(cbn [outside]; split; [lia | exact I])).
      rewrite (PR' a ltac:(destruct Ha as [Ha|Ha]; [left; lia | right; exact Ha])).
      exact (MU1 a ltac:(cbn [outside]; split; [exact O1|]; split; [exact O4 | exact I])). }
    split; [exact (wr_at_wmono m' m'' _ _ WR' WM'')|].
    apply (acc_transport _ m' m'' _ _ AC' MU''); [lia|].
    assert (Hsh : shad (p + n - 1) + 1 <= 2 ^ 44 + SHB + 1) by (unfold shad; assert ((p + n - 1) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; unfold USTACK_TOP in HpU; lia); lia).
    cbn [disjoint_from]. unfold SHB in *. split; [left; unfold RT_STACK in LOR; lia | exact I]. }
  apply (cps_realizes asegs _ _ _ c2 (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ') _ _ _ (fl_ASTA_mat_stable Σ' PMc MST) W2) HAST).
  intros c3 Hc3. apply Hk. exists Σ', p. split; [exact Hc3|].
  cbn [rt_live rt_frames rt_sp0 rt_credit RTA]. unfold rtA_live, rtA_frames, rtA_sp0, rtA_credit.
  split; [exact HL|]. split; [exact HF|]. split; [exact HS|]. split; [exact HCR|]. split; [exact Hp0|]. split; [exact Hp16|]. split; [exact HpU|]. unfold rt_cg, RTA, rtA_cg. rewrite HLAY. reflexivity.
Qed.

End Back.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_alloc_ras_range : forall x, In x ALLOC_RAS -> 4096 <= x < 2 ^ 64.
Proof. intros x H. unfold ALLOC_RAS in H. repeat (destruct H as [<-|H]; [lia|]). destruct H. Qed.

Theorem rta_malloc : core_stmt_prim -> core_stmt_sec -> malloc_contract RTA.
Proof.
  intros CP CS Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n lo
    FDO MST Hn Ha0 Htp Hlen Hcr ART0 MI0 CALL UWOK. subst a0 tp.
  intros TT cf Hc Hk. cbn [ART rt_live rt_frames rt_sp0 rt_credit RTA] in Hlen, Hcr, ART0.
  unfold rtA_live, rtA_credit in Hlen, Hcr.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA). cbn [rt_sp0 RTA] in LOW. unfold rtA_sp0 in LOW.
  pose proof (mp_cells Σ m ART0) as (G60 & GCF & MX & RZ & AI & MCS & RSS & PSC & FUM & TC & SC & UB).
  pose proof (mp_layout Σ m sp lo ART0 CALL) as (HTCX & HTCXl & HTl & HTT & HLOH & Hbt & Htop & HT).
  pose proof (geo_grant Σ m ART0 (l_T (lay Σ)) 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (GT1 & _).
  assert (LOW' : l_ACEIL (lay Σ) <= lo) by (unfold l_ACEIL; lia).
  (* [comment removed for export] *)
  assert (HW : exists tr, (1 <= length tr <= 30)%nat /\ In tr (T_MAIN (l_cg (lay Σ)))
             /\ evt asegs (malloc_A_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n (l_T (lay Σ)) lo tr m)
                  (entry_st ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                     t3 t4 t5 t6 F fc e_malloc m)).
  { unfold entry_st, e_malloc.
    exact (malloc_front_spec ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n
             (l_TCX (lay Σ)) (l_T (lay Σ)) (l_top (lay Σ)) (l_top (lay Σ) - 0x800000) lo (l_cg (lay Σ)) (ART_cg_wf Σ m ART0)
             ltac:(lia) ST ltac:(unfold RT_STACK in LOR; lia) HLOH ltac:(unfold USTACK_TOP in SPT; lia) ltac:(lia) ltac:(lia) UWOK
             ltac:(lia) ltac:(lia)
             G60 GCF MX RZ AI MCS RSS PSC FUM TC HTCX HTCXl GT1 HT HTl HTT SC UB MI0). }
  destruct HW as (tr & Htrl & Htr & W1).
  assert (W1' : forall ms, eq (entry_st ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
                                   s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_malloc m) ms ->
                  evt asegs (malloc_A_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n (l_T (lay Σ)) lo tr m) ms)
    by (intros ms <-; exact W1).
  clear W1.
  apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1') Hc).
  intros c1 Hc1. unfold malloc_A_post in Hc1.
  apply AST_exI in Hc1 as (t0' & Hc1). apply AST_exI in Hc1 as (t1' & Hc1). apply AST_exI in Hc1 as (t2' & Hc1).
  apply AST_exI in Hc1 as (a4' & Hc1). apply AST_exI in Hc1 as (a5' & Hc1). apply AST_exI in Hc1 as (a6' & Hc1).
  apply AST_exI in Hc1 as (a7' & Hc1). apply AST_exI in Hc1 as (t3' & Hc1). apply AST_exI in Hc1 as (t4' & Hc1).
  apply AST_exI in Hc1 as (t5' & Hc1). apply AST_exI in Hc1 as (t6' & Hc1). apply AST_exI in Hc1 as (tb & Hc1).
  apply AST_exI in Hc1 as (jp & Hc1). apply AST_exI in Hc1 as (j0 & Hc1). apply AST_exI in Hc1 as (m1 & Hc1).
  destruct Hc1 as (HM & HPm & HPM & HZ).
  destruct HPm as (Hms & MU1 & WM1 & MI1 & IC1 & IC2 & IC3 & TB1 & HTB & IC4 & IC5 & AFr & J0 & UB1 & ST1).
  assert (Hsp0 : l_ACEIL (lay Σ) + 0xF000 <= bv_unsigned sp) by (unfold RT_STACK in LOR; lia).
  pose proof (front_ART Σ m (bv_unsigned sp) ART0 Hsp0 m1 MU1 WM1 UB1) as ART1.
  set (usp := bv_unsigned sp) in *.
  assert (Hc2 : ASTA RTA Σ PMc (eq (core_entry Σ (usp + -2128) gp t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' F fc n m1)) c1).
  { split; [exact HM|]. split; [|split; [exact HPM | exact HZ]]. rewrite Hms. unfold core_entry.
    replace (usp + -2128 + -144) with (usp + -2272) by lia. reflexivity. }
  assert (ST1' : stk asegs m1 lo (usp + -2128 + -144)) by (replace (usp + -2128 + -144) with (usp + -2272) by lia; exact ST1).
  assert (TRC : trc_cells (usp + -2128) tr m1 tb).
  { split; [replace (usp + -2128 + 16) with (usp + -2112) by lia; exact IC4|]. split; [replace (usp + -2128 + 16) with (usp + -2112) by lia; exact TB1 | exact HTB]. }
  assert (AFC : af_cells (usp + -2128) (Z_to_bv 64 usp) (Z_to_bv 64 n) (Z_to_bv 64 0x1c328c) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2128))
                  (Z_to_bv 64 (usp + -81)) s6 s7 s8 s9 s10 s11 m1 j0).
  { split; replace (usp + -2128 + -144) with (usp + -2272) by lia; [exact AFr | exact J0]. }
  assert (LOR' : lo + 0x1000 <= usp + -2128 + -144) by (unfold RT_STACK in LOR; lia).
  assert (SPT' : usp + -2128 + 2144 <= USTACK_TOP) by lia.
  assert (SPA' : (usp + -2128) mod 16 = 0).
  { pose proof SPA as SPA0. apply Z.mod_divide in SPA0; [|lia]. destruct SPA0 as [q Hq]. apply Z.mod_divide; [lia|]. exists (q - 133). lia. }
  assert (K : forall c2, core_post Σ PMc (usp + -2128) gp (Z_to_bv 64 usp) (Z_to_bv 64 n) (Z_to_bv 64 0x1c328c) (Z_to_bv 64 1)
                           (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (usp + -81)) s6 s7 s8 s9 s10 s11 n lo m1 c2 -> realizes asegs c2 TT).
  { intros c2 Hc2'. exact (back_cps Σ PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m m1 n lo (wr_trace tr tb) (Z_to_bv 64 (Z.of_nat (length tr))) jp
                             MST ltac:(lia) ART0 LOW' ltac:(unfold RT_STACK in LOR; lia) SPT SPA MU1 WM1 IC1 IC2 IC3 TB1 ltac:(rewrite wr_trace_length by lia; exact HTB) IC4 IC5 TT c2 Hc2' Hk). }
  destruct (Z_le_gt_dec n 64512) as [Hp|Hs].
  - exact (CP Σ PMc m1 (usp + -2128) gp (Z_to_bv 64 usp) (Z_to_bv 64 n) (Z_to_bv 64 0x1c328c) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2128))
             (Z_to_bv 64 (usp + -81)) s6 s7 s8 s9 s10 s11 t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' F fc n lo tr tb j0
             FDO MST Hp ltac:(lia) Hlen Hcr ART1 MI1 ST1' LOW' LOR' SPT' SPA' Htr Htrl TRC AFC TT c1 Hc2 K).
  - exact (CS Σ PMc m1 (usp + -2128) gp (Z_to_bv 64 usp) (Z_to_bv 64 n) (Z_to_bv 64 0x1c328c) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2128))
             (Z_to_bv 64 (usp + -81)) s6 s7 s8 s9 s10 s11 t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' F fc n lo tr tb j0
             FDO MST ltac:(cbv beta; lia) ltac:(lia) Hlen Hcr ART1 MI1 ST1' LOW' LOR' SPT' SPA' Htr Htrl TRC AFC TT c1 Hc2 K).
Qed.
