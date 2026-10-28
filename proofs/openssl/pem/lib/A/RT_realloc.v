(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_unwind_defs R_quar_defs R_qput R_qenqueue R_asan_defs R_allocate1 R_asan_malloc R_asan_free R_prim_kit R_deallocate RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_facts RT_malpre RT_malstate RT_maltail RT_malcore_stmt RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeA2 RT_freestmt RT_freeE RT_freeI RT_freeS RT_freeN RT_sys_stmt RT_unwindk RT_artfacts R_asan_front_k RT_iface_pem R_asan_realloc RT_realloc_front RTR_defs RTR_fin RTR_Y RTR_A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition realloc_cf (usp p n : Z) (m : mem) : Prop :=
  (exists ws, u64arr asegs m (usp + -2120) ws /\ length ws = 255%nat)
  /\ (exists w, rw_cells asegs m (usp + -2136) [C8 (Z_to_bv 64 (usp + -2120)); C8 w])
  /\ (exists jq, rw_cells asegs m (usp + -2144) [CB 8 jq])
  /\ (exists ja, rw_cells asegs m (usp + -2160) [CB 8 ja; C8 (Z_to_bv 64 0x1c37d0)])
  /\ rw_cells asegs m (usp + -2208) [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0x1c3760); C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 usp);
                                      C8 (Z_to_bv 64 0x19b770)].

Lemma realloc_cf_ok : forall usp p n, cf_ok (realloc_cf usp p n) (usp + -80).
Proof.
  intros usp p n ma mb (F1 & F2 & F3 & F4 & F5) AG.
  assert (AGs : forall a k, usp + -2208 <= a -> a + k <= usp + -80 -> agree_on (fun x => a <= x < a + k) ma mb).
  { intros a k H1 H2 x Hx. apply AG. lia. }
  destruct F1 as (ws & F1 & F1l). destruct F2 as (w & F2). destruct F3 as (jq & F3). destruct F4 as (ja & F4).
  split; [exists ws; split; [|exact F1l]; apply (u64arr_agree_nw asegs ma mb _ _ F1); apply AGs; rewrite ?F1l; lia|].
  split; [exists w; apply (rw_cells_agree_nw asegs ma mb _ _ F2); apply AGs; cbn [cells_size csize Nat.add]; lia|].
  split; [exists jq; apply (rw_cells_agree_nw asegs ma mb _ _ F3); apply AGs; cbn [cells_size csize Nat.add]; lia|].
  split; [exists ja; apply (rw_cells_agree_nw asegs ma mb _ _ F4); apply AGs; cbn [cells_size csize Nat.add]; lia|].
  apply (rw_cells_agree_nw asegs ma mb _ _ F5); apply AGs; cbn [cells_size csize Nat.add]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma eps_realloc : In (e_realloc, PC_REALLOC) ALLOC_EPS. Proof. right; right; left; reflexivity. Qed.

Lemma realloc_front_spec : forall ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p n TCX T top bot lo : Z) (b : bool) (cg : cgraph) (r1 r2 : word),
  cg_wf cg ALLOC_EPS ALLOC_RAS N_TR ->
  (0 < p < 2^47)%Z -> (1 <= n <= 2^31)%Z ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2352)%Z -> (kHighShadowEnd + 8 <= lo)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  (0 <= bot < top)%Z -> (top < 2^64)%Z ->
  unwind_ok cg e_realloc m ra s0 sp -> (4096 <= top)%Z -> (top <= 2 ^ 63)%Z ->
  ia_state b m ->
  rw_cells asegs m 0x5a4598 [C8 (Z_to_bv 64 0x6fc5e0)] ->
  rw_cells asegs m g_GOT_common_flags [C8 (Z_to_bv 64 g_common_flags)] ->
  rw_cells asegs m i_max_user [C8 (Z_to_bv 64 (2^40))] -> rw_cells asegs m i_min_rz [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)] ->
  rw_cells asegs m g_asan_inited [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m g_malloc_context_size_cell [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m g_rss_limit_exceeded [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0x6fc5e0 [C8 (Z_to_bv 64 4096)] ->
  rw_cells asegs m (g_common_flags + 34) [C1 (Z_to_bv 8 1)] ->
  thread_cells TCX T m -> (0 < TCX)%Z -> (TCX + 0xa0 <= 0x10000 \/ 0xbc6000 <= TCX)%Z -> (TCX + 0xa0 <= lo)%Z ->
  (0 < T)%Z -> (T + 4096 <= 0x10000 \/ 0xbc6000 <= T)%Z -> (T + 4096 <= lo)%Z ->
  (TCX + 0xa0 <= T \/ T + 4096 <= TCX)%Z ->
  stack_cells T top bot m -> rw_cells asegs m (T + 3168) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (T + 2856) [C8 r1; C8 r2] ->
  mem_inv asegs m ->
  exists tr, uw_tr_shape cg e_realloc PC_REALLOC tr
    /\ evt asegs (realloc_A_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p n T lo tr m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 wrap_realloc_entry) fc None m (seg_rom asegs)).
Proof.
  intros until r2. intros WF Hp Hn ST HLO HLOH HSP Hbt Htop UWOK Ht1 Ht2 IS G60 GCF MX RZ AI MCS RSS PSC FUM TC HTCX HTCXi HTCXl HT0 HT HTl HTT SC UW STS MI.
  destruct (unwind_ok_trace cg e_realloc PC_REALLOC
              [(T + 3168, T + 3169); (T + 2856, T + 2872); (7325128, 7325132); (6741312, 7269744); (bv_unsigned sp - 2352, bv_unsigned sp)]
              m ra s0 sp bot top eps_realloc WF Ht1 Ht2) as (ch & tr & CCH & HTR & HS); [|exact UWOK|].
  { unfold kHighShadowEnd in HLOH. repeat constructor; cbn [snd]; lia. }
  exists tr. split; [exact HS|].
  change PC_REALLOC with realloc_pc in HTR.
  exact (realloc_Ak_spec ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n
           TCX T top bot lo ch b tr r1 r2 Hp Hn ST HLO HLOH HSP Hbt Htop CCH HTR IS G60 GCF MX RZ AI MCS RSS PSC FUM TC HTCX HTCXi HTCXl
           HT0 HT HTl HTT SC UW STS MI).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bytes_at_inj : forall (m : mem) a (b1 b2 : list byte), bytes_at asegs m a b1 -> bytes_at asegs m a b2 -> length b1 = length b2 -> b1 = b2.
Proof.
  intros m a b1 b2 (_ & _ & H1) (_ & _ & H2) HL. apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length b1)) as [Hi|Hi].
  - rewrite <- (H1 i Hi), <- (H2 i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None b1 i) Hi), (proj2 (nth_error_None b2 i) ltac:(lia)). reflexivity.
Qed.

Theorem rta_realloc : core_stmt_prim_g -> drain_stmt -> fixed_commit_node -> realloc_contract RTA.
Proof.
  intros CP DRAIN FC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n0 n lo
    FDO MST Hin Hn Hn0 Ea0 Ea1 Etp Hlen Hcr ART0 MI0 CALL HSL UWOK. subst a0 a1 tp.
  intros TT cf Hc Hk. cbn [ART rt_live rt_frames rt_sp0 rt_credit rt_cg RTA] in Hin, Hlen, Hcr, ART0, UWOK.
  unfold rtA_live, rtA_credit, rtA_cg in Hin, Hlen, Hcr, UWOK.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA). cbn [rt_sp0 RTA] in LOW. unfold rtA_sp0 in LOW.
  pose proof (mp_cells Σ m ART0) as (G60 & GCF & MX & RZ & AI & MCS & RSS & PSC & FUM & TC & SC & UB).
  pose proof (mp_layout Σ m sp lo ART0 CALL) as (HTCX & HTCXl & HTl & HTT & HLOH & Hbt & Htop & HT).
  pose proof (geo_grant Σ m ART0 (l_T (lay Σ)) 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (GT1 & _).
  pose proof (geo_grant Σ m ART0 (l_TCX (lay Σ)) 0x10000 ltac:(unfold startup_grants; right; right; right; left; reflexivity)) as (_ & _ & _ & _ & GX5).
  assert (LOW' : l_ACEIL (lay Σ) <= lo) by (unfold l_ACEIL; lia).
  set (usp := bv_unsigned sp) in *.
  assert (Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp) by (clear - LOW' LOR; unfold RT_STACK in *; lia).
  destruct (ART_ia Σ m ART0) as (b & IS).
  (* [comment removed for export] *)
  pose proof (ART_wf Σ m ART0) as (_ & _ & (_ & _ & V3 & _) & HSW & _).
  assert (Hp47 : 0 < p < 2 ^ 47).
  { pose proof (rta_live_range Σ m p n0 ART0 Hin) as (X1 & X2 & _). pose proof (rta_sp0_range Σ m ART0) as Y. unfold rtA_sp0, USTACK_TOP, STACK_WIN in *. lia. }
  (* [comment removed for export] *)
  pose proof (ART_consts Σ m ART0) as (_ & _ & _ & _ & _ & _ & _ & ICR).
  destruct ICR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & I32 & _).
  destruct (stk_two_words m (l_T (lay Σ) + 2856) ltac:(destruct (stk_split asegs m (l_T (lay Σ) + 2768) (l_T (lay Σ) + 2856) (l_T (lay Σ) + 3168) I32 ltac:(lia)) as [_ X];
              destruct (stk_split asegs m (l_T (lay Σ) + 2856) (l_T (lay Σ) + 2872) (l_T (lay Σ) + 3168) X ltac:(lia)) as [X' _];
              replace (l_T (lay Σ) + 2856 + 16) with (l_T (lay Σ) + 2872) by lia; exact X')) as (r1 & r2 & STS).
  assert (HW : exists tr, uw_tr_shape (l_cg (lay Σ)) e_realloc PC_REALLOC tr
             /\ evt asegs (realloc_A_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p n (l_T (lay Σ)) lo tr m)
                  (entry_st ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                     t3 t4 t5 t6 F fc e_realloc m)).
  { unfold entry_st, e_realloc.
    exact (realloc_front_spec ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n
             (l_TCX (lay Σ)) (l_T (lay Σ)) (l_top (lay Σ)) (l_top (lay Σ) - 0x800000) lo b (l_cg (lay Σ)) r1 r2 (ART_cg_wf Σ m ART0)
             Hp47 ltac:(clear - Hn; lia) ST ltac:(clear - LOR; unfold RT_STACK in LOR; fold usp; lia) HLOH ltac:(clear - SPT; unfold USTACK_TOP in SPT; fold usp; lia)
             ltac:(clear - Hbt; lia) ltac:(clear - Htop; lia) UWOK ltac:(clear - Htop; lia) ltac:(clear - Htop; lia) IS
             G60 GCF MX RZ AI MCS RSS PSC FUM TC HTCX ltac:(clear - GX5; unfold SEGTOP_A in GX5; lia) HTCXl GT1 HT HTl HTT SC UB STS MI0). }
  destruct HW as (tr & HS & W1). destruct (uw_tr_shape_main tr HS) as (Htr & Htrl & Htrr).
  assert (W1' : forall ms, eq (entry_st ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
                                   s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_realloc m) ms ->
                  evt asegs (realloc_A_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p n (l_T (lay Σ)) lo tr m) ms)
    by (intros ms <-; exact W1).
  clear W1.
  apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1') Hc).
  intros c1 Hc1. unfold realloc_A_post in Hc1.
  apply AST_exI in Hc1 as (t0' & Hc1). apply AST_exI in Hc1 as (t1' & Hc1). apply AST_exI in Hc1 as (t2' & Hc1).
  apply AST_exI in Hc1 as (a4' & Hc1). apply AST_exI in Hc1 as (a5' & Hc1). apply AST_exI in Hc1 as (a6' & Hc1).
  apply AST_exI in Hc1 as (a7' & Hc1). apply AST_exI in Hc1 as (t3' & Hc1). apply AST_exI in Hc1 as (t4' & Hc1).
  apply AST_exI in Hc1 as (t5' & Hc1). apply AST_exI in Hc1 as (t6' & Hc1). apply AST_exI in Hc1 as (tb & Hc1).
  apply AST_exI in Hc1 as (jp & Hc1). apply AST_exI in Hc1 as (jq & Hc1). apply AST_exI in Hc1 as (ja & Hc1).
  apply AST_exI in Hc1 as (j0 & Hc1). apply AST_exI in Hc1 as (r1' & Hc1). apply AST_exI in Hc1 as (r2' & Hc1).
  apply AST_exI in Hc1 as (m1 & Hc1).
  destruct Hc1 as (HM & HPm & HPM & HZ).
  destruct HPm as (Hms & MU1 & WM1 & MI1 & IS1 & IC1 & IC2 & IC3 & TB1 & HTB & IC4 & IC5 & IC6 & IC7 & AFr & J0 & STS1 & UB1 & ST1).
  fold usp in Hms, MU1, IC1, IC2, IC3, TB1, IC4, IC5, IC6, IC7, AFr, J0, ST1.
  assert (MU1' : munch (W_frR (l_T (lay Σ)) usp) m m1).
  { eapply (munch_weaken _ _ m m1); [|exact MU1]. intros x Hx. unfold W_frR in Hx. cbn [outside] in Hx |- *.
    destruct Hx as (X1 & X2 & X3 & X4 & _). split; [lia|]. split; [lia|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4 | exact I]. }
  pose proof (frontR_ART Σ m usp ART0 Hsp m1 true MU1' WM1 IS1 UB1) as ART1.
  set (B := usp + -2192). set (Bt := usp + -2136).
  assert (Hc2 : ASTA RTA Σ PMc (eq (core_entry_g Σ B Bt gp t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' F fc n m1)) c1).
  { split; [exact HM|]. split; [|split; [exact HPM | exact HZ]]. rewrite Hms. unfold core_entry_g, B, Bt.
    replace (usp + -2192 + -144) with (usp + -2336) by lia. reflexivity. }
  assert (ST1' : stk asegs m1 lo (B + -144)) by (unfold B; replace (usp + -2192 + -144) with (usp + -2336) by lia; exact ST1).
  assert (TRC : trc_cells Bt tr m1 tb).
  { unfold Bt. split; [replace (usp + -2136 + 16) with (usp + -2120) by lia; exact IC4|].
    split; [replace (usp + -2136 + 16) with (usp + -2120) by lia; exact TB1 | exact HTB]. }
  assert (AFC : af_cells_g B (Z_to_bv 64 0x19b7ec) (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 p) (Z_to_bv 64 INST) (Z_to_bv 64 n) (Z_to_bv 64 1)
                  (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 m1 j0).
  { unfold B. split; replace (usp + -2192 + -144) with (usp + -2336) by lia; [exact AFr | exact J0]. }
  assert (LOR' : lo + 0x1000 <= B + -144) by (unfold B; clear - LOR; unfold RT_STACK in LOR; lia).
  assert (SPT' : B + 2144 <= USTACK_TOP) by (unfold B; clear - SPT; fold usp in SPT; lia).
  assert (SPA' : B mod 16 = 0).
  { unfold B. pose proof SPA as SPA0. fold usp in SPA0. apply Z.mod_divide in SPA0; [|lia]. destruct SPA0 as [q Hq]. apply Z.mod_divide; [lia|]. exists (q - 137). lia. }
  assert (HBT : B <= Bt /\ Bt + 2144 <= USTACK_TOP) by (unfold B, Bt; clear - SPT; fold usp in SPT; lia).
  apply (CP Σ PMc m1 B Bt (Z_to_bv 64 0x19b7ec) gp (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 p) (Z_to_bv 64 INST) (Z_to_bv 64 n) (Z_to_bv 64 1)
            (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' F fc n lo tr tb j0
            FDO MST ltac:(clear - Hn; cbv beta; lia) ltac:(clear - Hn; lia) Hlen Hcr ART1 MI1 ST1' LOW' LOR' SPT' SPA' HBT Htr Htrl TRC AFC TT c1 Hc2).
  clear Hc2 W1'.
  intros c2 (Σ' & q & HAST & HL & HF & HSP0 & HCR & Hq0 & Hq16 & HqU & HLAY).
  (* [comment removed for export] *)
  destruct HAST as (HM2 & HPm2 & HPM2 & HZ2).
  destruct HPm2 as (m2 & RET2 & ART2 & MI2 & WM2 & ST2 & RP2 & WR2 & AC2).
  destruct RET2 as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & F2 & fc2 & Ems2).
  rewrite (ret_pc_even 0x19b7ec) in Ems2 by (lia || reflexivity).
  unfold B in ST2, RP2, Ems2. replace (usp + -2192 + -16) with (usp + -2208) in ST2, RP2, Ems2 by lia.
  (* [comment removed for export] *)
  assert (Hin' : In (p, n0) (live Σ')) by (rewrite HL; right; exact Hin).
  pose proof (ART_wf Σ' m2 ART2) as (_ & _ & (_ & _ & V3' & _) & HSW' & _).
  destruct (V3' p n0 Hin') as [(c & i & Hci & Hni & Ep)|(s & Hs & Hq & Hsn & Ep)].
  2:{ exfalso. destruct HSW' as (_ & _ & _ & HSF & _). pose proof (proj1 (Forall_forall _ _) HSF s Hs) as (X & _). clear - X Hsn Hn0. lia. }
  assert (Hn1 : 1 <= n0) by (clear - Hn0; lia).
  pose proof (sa_geo Σ' m2 c i n0 ART2 Hci Hni Hn1) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19 & K20
    & K21 & K22 & K23 & K24 & K25 & K26 & K27 & K28 & K29 & K30 & K31 & K32 & K33 & K34 & K35 & K36 & K37 & K38 & K39 & K40 & K41).
  set (SB := l_SB (lay Σ')) in *. set (AB := p_abeg SB c i) in *. set (M := AB + rz_size n0 - 16) in *.
  assert (EpM : p = M + 16) by (rewrite Ep; unfold p_ubeg, M, AB, SB; lia).
  destruct (ART_chunk Σ' m2 ART2) as [CP' _]. destruct (CP' c i (CkAlloc n0) Hci Hni) as (WrA & (b1 & ctx & Hb1 & HD) & _ & _ & _). clear CP'.
  fold SB in WrA, HD. fold AB in WrA, HD. fold M in HD.
  pose proof (bv_unsigned_in_range 8 b1) as Rb1. unfold bv_modulus in Rb1. change (2 ^ Z.of_N 8) with 256 in Rb1.
  assert (Eb : Z_to_bv 8 (bv_unsigned b1) = b1) by (apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; apply Z.mod_small; exact Rb1).
  rewrite <- Eb in HD.
  set (k := Z.min n n0).
  assert (Hkk : 1 <= k <= n /\ k <= n0) by (unfold k; clear - Hn Hn0; lia).
  destruct (fl_CB_of_wr m2 AB (ClassSize c) (M + 16) (Z.to_nat k) WrA ltac:(unfold M; clear - K11; lia) ltac:(unfold M; clear - K12 K14 Hkk; lia)) as (src & SRC).
  destruct (fl_CB_of_wr m2 q n q (Z.to_nat k) WR2 ltac:(lia) ltac:(clear - Hkk; lia)) as (junk & DST).
  assert (SRCb : bytes_at asegs m2 (M + 16) src /\ length src = Z.to_nat k).
  { destruct SRC as [[WF0 HB0] _]. cbn in WF0. destruct WF0 as (HL0 & _). cbn [cells_bytes cbytes] in HB0. rewrite app_nil_r in HB0. split; [exact HB0 | exact HL0]. }
  destruct SRCb as (SRCb & SRCl).
  pose proof (af_live_disj RTA rta_art_facts Σ' m2 q n p n0 [] (live Σ) ART2 HL Hin) as DISJ.
  pose proof (ART_consts Σ' m2 ART2) as (_ & _ & _ & _ & _ & _ & _ & ICR2).
  destruct ICR2 as (_ & _ & _ & _ & G42 & G74 & _).
  (* [comment removed for export] *)
  set (uv := usp + -80).
  assert (Esp8 : usp + -2208 = uv + -2128) by (unfold uv; lia).
  pose proof (af_live_range RTA rta_art_facts Σ' m2 q n ART2 ltac:(cbn [rt_live RTA]; unfold rtA_live; rewrite HL; left; reflexivity)) as (_ & QHI & QIMG).
  cbn [rt_sp0 RTA] in QHI. unfold rtA_sp0 in QHI. rewrite HLAY in QHI. fold (l_ACEIL (lay Σ)) in QHI.
  assert (AG12 : forall a k', usp + -2208 <= a -> a + k' <= USTACK_TOP -> agree_on (fun x => a <= x < a + k') m1 m2).
  { intros a k' H1 H2 x Hx. apply RP2. left. lia. }
  rewrite EpM in Ems2.
  set (retw := Z_to_bv 64 0x19b880). set (q0 := Z_to_bv 64 Bt). set (q1 := Z_to_bv 64 (M + 16)). set (q2 := Z_to_bv 64 INST).
  set (q3 := Z_to_bv 64 k). set (q4 := Z_to_bv 64 q). set (q5 := Z_to_bv 64 (usp + -2136)). set (s6A := Z_to_bv 64 (usp + -89)).
  assert (W3 : forall ms, eq (MS (mkR (Z_to_bv 64 0x19b7ec) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) u0 u1 u2 (Z_to_bv 64 (usp + -2136))
                                    (Z_to_bv 64 (M + 16)) (Z_to_bv 64 q) u3 u4 u5 u6 u7 u8 u9 (Z_to_bv 64 INST) (Z_to_bv 64 n) (Z_to_bv 64 1)
                                    (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 u10 u11 u12 u13)
                              F2 (Z_to_bv 64 0x19b7ec) fc2 None m2 (seg_rom asegs)) ms ->
             evt asegs (fun ms4 => exists (m3 : mem) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : word) (m4 : mem),
                          munch [(q, q + k)] m2 m3 /\ wmono asegs m2 m3 /\ rw_cells asegs m3 q [CB (Z.to_nat k) src]
                          /\ ms4 = enq_entry_st uv (l_T (lay Σ')) M n0 Bt gp y0 y1 y2 y3 y4 y5 s7 s8 s9 s10 s11 y6 y7 y8 y9 F2 fc2 m4
                          /\ ARTc (free_p Σ' c i n0 (AB + rz_size n0) (fst (depot_put (dep Σ') tr))) m4
                          /\ mem_inv asegs m4 /\ wmono asegs m3 m4
                          /\ munch (W_A1 (l_T (lay Σ')) (l_DNB (lay Σ')) (l_SSB (lay Σ')) M n0 uv) m3 m4
                          /\ stk asegs m4 lo (uv + -2208)
                          /\ qput_frame m4 (uv + -2208) (Z_to_bv 64 (l_T (lay Σ') + 208)) (Z_to_bv 64 Bt) retw q0 q1 q2 q3 q4 q5 s6A) ms).
  { intros ms <-.
    eapply evt_cut.
    { apply (realloc_mid_spec (Z_to_bv 64 0x19b7ec) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 (Z_to_bv 64 1)
               (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 u10 u11 u12 u13 F2 fc2 m2 M q n n0 (bv_unsigned b1) Bt ctx src junk).
      all: try assumption; try (fold k; assumption).
      all: try (clear - Hn; lia). all: try (clear - Hn0; lia). all: try (clear - Hq0 HqU Hn; unfold USTACK_TOP in *; lia).
      all: try (unfold M; clear - K38 K1 K11; lia). all: try (unfold M; clear - K39 K4 K28 K11 K12 K13 K14; lia).
      all: try (fold k; rewrite EpM in DISJ; clear - DISJ Hkk; lia). }
    intros ms3 P3. unfold realloc_mid_post in P3.
    destruct P3 as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & m3 & -> & MU3 & WM3 & MI3 & DST3 & SRC3). fold k in MU3, DST3.
    assert (QLO : q + k <= lo) by (clear - QHI LOW' Hkk; lia).
    assert (ART3 : ART_A Σ' m3).
    { apply (ART_client_frame Σ' m2 m3 usp ART2); [rewrite HSP0; unfold rtA_sp0; clear - LOW LOR; unfold RT_STACK in *; lia | | exact WM3].
      intros a Ha. apply MU3. cbn [outside]. split; [|exact I].
      intros XY. apply Ha. right. right. left. exists q, n. split; [rewrite HL; left; reflexivity | clear - XY Hkk; lia]. }
    assert (RW13 : forall a cs, usp + -2208 <= a -> a + Z.of_nat (cells_size cs) <= USTACK_TOP -> rw_cells asegs m1 a cs -> rw_cells asegs m3 a cs).
    { intros a cs H1 H2 X. apply (rw_cells_transport asegs [(q, q + k)] m2 m3 _ _ (rw_cells_agree asegs m1 m2 a cs X (AG12 a _ H1 H2) WM2) MU3 WM3).
      cbn [disjoint_from]. split; [right; clear - QLO LOR H1; unfold RT_STACK in *; lia | exact I]. }
    assert (TB3 : u64arr asegs m3 (Bt + 16) (wr_trace tr tb)).
    { destruct TRC as (_ & TBx & _).
      assert (LW : length (wr_trace tr tb) = 255%nat) by (rewrite wr_trace_length by (rewrite HTB; clear - Htrl; lia); exact HTB).
      assert (TB2 : u64arr asegs m2 (Bt + 16) (wr_trace tr tb)).
      { apply (u64arr_agree asegs m1 m2 _ _ TBx); [|exact WM2]. rewrite LW. apply AG12; [unfold Bt; lia | unfold Bt; clear - SPT; fold usp in SPT; lia]. }
      apply (u64arr_transport asegs [(q, q + k)] m2 m3 _ _ TB2 MU3 WM3). rewrite LW.
      cbn [disjoint_from]. split; [right; unfold Bt; clear - QLO LOR; unfold RT_STACK in *; lia | exact I]. }
    assert (BC3 : rw_cells asegs m3 Bt [C8 (Z_to_bv 64 (Bt + 16)); C8 (Z_to_bv 64 (Z.of_nat (length tr)))]).
    { destruct TRC as (BCx & _). apply (RW13 Bt _); [unfold Bt; lia | cbn [cells_size csize Nat.add]; unfold Bt; clear - SPT; fold usp in SPT; lia | exact BCx]. }
    assert (ST3 : stk asegs m3 lo (uv + -2128)).
    { rewrite <- Esp8. apply (stk_transport_disjoint asegs [(q, q + k)] m2 m3 lo (usp + -2208) ST2 MU3 WM3).
      cbn [disjoint_from]. split; [right; exact QLO | exact I]. }
    rewrite Esp8.
    pose proof (segA_run retw q0 q1 q2 q3 q4 q5 Bt Σ' m3 c i n0 uv lo tr tb ART3 Hci Hni Hn1
               ltac:(rewrite HLAY; unfold uv; clear - LOW' HSL; unfold RT_STACK in *; lia)
               ltac:(unfold uv; clear - SPT; fold usp in SPT; lia)
               ltac:(rewrite HLAY; exact LOW')
               ltac:(unfold uv; clear - HSL; unfold RT_STACK in *; lia)
               ST3 MI3 ltac:(unfold uv, Bt; clear - SPT; fold usp in SPT; lia) BC3 TB3 HTB
               ltac:(rewrite HLAY; exact (conj Htr (conj Htrl Htrr)))) as SEGA.
    eapply evt_mono; [apply SEGA|].
    intros ms4 P4. destruct P4 as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & m4 & -> & ARTc4 & MI4 & WM4 & MW4 & ST4 & FR4).
    exists m3, y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, m4. split; [exact MU3|]. split; [exact WM3|]. split; [exact DST3|].
    split; [reflexivity|]. split; [exact ARTc4|]. split; [exact MI4|]. split; [exact WM4|]. split; [exact MW4|]. split; [exact ST4 | exact FR4]. }
  (* [comment removed for export] *)
  lazymatch type of W3 with forall ms, eq ?X ms -> _ => assert (Hc2' : ASTA RTA Σ' PMc (eq X) c2) end.
  { split; [exact HM2|]. split; [symmetry; exact Ems2|]. split; [exact HPM2 | exact HZ2]. }
  apply (cps_realizes asegs _ _ _ c2 (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ') _ _ _ (fl_ASTA_mat_stable Σ' PMc MST) W3) Hc2').
  clear W3 Hc2'.
  intros c3 Hc3.
  apply AST_exI in Hc3 as (m3 & Hc3). apply AST_exI in Hc3 as (y0 & Hc3). apply AST_exI in Hc3 as (y1 & Hc3). apply AST_exI in Hc3 as (y2 & Hc3).
  apply AST_exI in Hc3 as (y3 & Hc3). apply AST_exI in Hc3 as (y4 & Hc3). apply AST_exI in Hc3 as (y5 & Hc3). apply AST_exI in Hc3 as (y6 & Hc3).
  apply AST_exI in Hc3 as (y7 & Hc3). apply AST_exI in Hc3 as (y8 & Hc3). apply AST_exI in Hc3 as (y9 & Hc3). apply AST_exI in Hc3 as (m4 & Hc3).
  pose proof Hc3 as (_ & (MU3 & WM3 & DST3 & _ & ARTc4 & MI4 & WM4 & MW4 & ST4 & FR4) & _ & _).
  set (D' := fst (depot_put (dep Σ') tr)) in *.
  set (Σ1 := free_p Σ' c i n0 (AB + rz_size n0) D') in *.
  (* [comment removed for export] *)
  set (spv := Z_to_bv 64 uv).
  assert (RUV : 0 <= uv < 2 ^ 64) by (unfold uv; pose proof (proj1 ST) as S0x; clear - S0x LOR SPT; fold usp in SPT; unfold RT_STACK, USTACK_TOP in *; lia).
  assert (Espv : bv_unsigned spv = uv) by (apply unsigned_lit; exact RUV).
  assert (Hspv : l_ACEIL (lay Σ') + 0x10000 <= uv) by (rewrite HLAY; unfold uv; clear - LOW' HSL; unfold RT_STACK in *; lia).
  pose proof (ART_wf Σ' m2 ART2) as (_ & _ & _ & _ & _ & _ & _ & DOK & DN & DT & DINV & _).
  assert (Htr' : In tr (T_MAIN (l_cg (lay Σ')))) by (rewrite HLAY; exact Htr).
  assert (Dok : depot_ok D' (l_DNB (lay Σ')) (l_SSB (lay Σ')) (l_ACEIL (lay Σ'))) by (apply (qc_depot_ok_put_ok _ _ _ _ _ DOK DN); clear - DT Htrl; lia).
  assert (Dinv : dep_inv (l_cg (lay Σ')) D') by exact (dep_inv_put _ _ DINV Htr' ltac:(clear - Htrl; lia)).
  pose proof (free_p_wf Σ' m2 c i n0 D' ART2 Hci Hni Dok Dinv) as HW1.
  pose proof (pend_e_p _ c i n0 (pend_free_p Σ' m2 c i n0 (AB + rz_size n0) D' ART2 Hci Hni)) as HP.
  assert (RP4 : rt_pres (live Σ1) (frames Σ1) uv m3 m4).
  { intros a Ha. exact (MW4 a (sa_client Σ' m2 c i n0 uv ART2 Hci Hni Hn1 Hspv _ Ha)). }
  (* [comment removed for export] *)
  assert (CF1 : realloc_cf usp p n m1).
  { split; [exists (wr_trace tr tb); split; [exact TB1 | rewrite wr_trace_length by (rewrite HTB; clear - Htrl; lia); exact HTB]|].
    split; [eexists; exact IC4|]. split; [exists jq; exact IC5|]. split; [exists ja; exact IC6 | exact IC7]. }
  assert (CF3 : realloc_cf usp p n m3).
  { apply (realloc_cf_ok usp p n m2 m3); [apply (realloc_cf_ok usp p n m1 m2 CF1); intros a Ha; apply RP2; left; clear - Ha SPT; fold usp in SPT; lia|].
    intros a Ha. apply MU3. cbn [outside]. split; [|exact I]. intros XY.
    assert (QLO : q + k <= lo) by (clear - QHI LOW' Hkk; lia). clear - XY Ha QLO LOR. unfold RT_STACK in *. lia. }
  assert (CF4 : realloc_cf usp p n m4).
  { apply (cft_of_cf_ok (realloc_cf usp p n) uv (realloc_cf_ok usp p n) _ m3 m4 CF3 MW4 WM4).
    unfold W_A1. cbn [disjoint_from]. clear - K20 K23 K26 K27 K31 K33 K4 Hspv. unfold uv, SHB in *. repeat split; try exact I; lia. }
  assert (Hc3' : AST SEGTOP_A (rtA_allow Σ1)
                   (eq (enq_entry_st uv (l_T (lay Σ')) M n0 Bt gp y0 y1 y2 y3 y4 y5 s7 s8 s9 s10 s11 y6 y7 y8 y9 F2 fc2 m4))
                   (fun mo => ARTM_A Σ1 mo /\ PMc mo) c3).
  { eapply AST_conseq; [exact Hc3 | intros ms (_ & _ & _ & E & _); symmetry; exact E |].
    intros mo (HMo & HP'). split; [|exact HP']. apply (artm_eq Σ'); [reflexivity | reflexivity | apply rt_eager_fp | exact HMo]. }
  pose proof (enq_stage (realloc_cf usp p n) retw q0 q1 q2 q3 q4 q5 Bt Σ' Σ1 PMc ra spv gp s0 s1 s2 s3 s4 s5 s6A s7 s8 s9 s10 s11
                y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 F2 fc2 m3 m4 lo M n0 (AB + rz_size n0) TT
                DRAIN FC FDO MST HW1 HP eq_refl eq_refl eq_refl eq_refl) as STAGE.
  rewrite Espv in STAGE.
  assert (HBT' : 0 <= Bt < 2 ^ 64) by (unfold Bt; pose proof (proj1 ST) as S0x; clear - S0x LOR SPT; fold usp in SPT; unfold RT_STACK, USTACK_TOP in *; lia).
  apply (STAGE ltac:(rewrite HLAY; exact LOW') ltac:(unfold uv; clear - HSL; unfold RT_STACK in *; lia)
               ltac:(unfold uv; clear - SPT; fold usp in SPT; lia) ARTc4 MI4 WM4 ST4 RP4
               (ret_pc_even 0x19b880 ltac:(lia) eq_refl) HBT'
               (realloc_cf_ok usp p n) CF4 FR4); [|exact Hc3'].
  clear STAGE Hc3' Hc3.
  intros Σ2 c4 EL2 EF2 ELY2 EC2 (Σ'' & HAST4 & EL4 & EF4 & ELY4 & EC4).
  (* [comment removed for export] *)
  assert (LBA : forall x, aclient (live Σ) (frames Σ) usp x -> ~ (q <= x < q + n)).
  { intros x Hx XY. destruct Hx as [H|[H|[H|[H|H]]]].
    - clear - H XY QHI LOW' LOR. unfold RT_STACK in *. lia.
    - destruct H as ((lo' & hi' & Hin0 & Hlh) & _). unfold CLIENT_STATIC in Hin0.
      destruct Hin0 as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hlh XY QIMG; unfold SEGTOP_A in *; lia.
    - destruct H as (p' & n' & Hin0 & Hpx).
      pose proof (af_live_disj RTA rta_art_facts Σ' m2 q n p' n' [] (live Σ) ART2 HL Hin0) as X. clear - X Hpx XY. lia.
    - destruct H as (f & k' & Hin0 & Hfx). rewrite <- HF in Hin0.
      pose proof (af_frames_range RTA rta_art_facts Σ' m2 f k' ART2 Hin0) as (_ & _ & _ & X).
      pose proof (X q n ltac:(cbn [rt_live RTA]; unfold rtA_live; rewrite HL; left; reflexivity)) as Y. clear - Y Hfx XY. lia.
    - destruct H as (f & k' & Hin0 & Hfx). rewrite <- HF in Hin0.
      destruct (sep_fshad Σ' m2 ART2 f k' Hin0) as (Y1 & Y2).
      destruct (geo_live Σ' m2 ART2 q n ltac:(rewrite HL; left; reflexivity)) as [(cq & iq & Hcq & _ & _ & Z1 & _ & Z3 & _)|(s & Hs & _ & Hsn & _)].
      + pose proof (geo_prb Σ' m2 ART2) as (P1 & _).
        pose proof (geo_grant Σ' m2 ART2 (l_PRB (lay Σ')) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (G1 & _ & _ & G4 & _).
        clear - Y2 Hfx XY Z1 Z3 Hcq P1 G1 G4. unfold rb, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia.
      + exfalso. destruct HSW' as (_ & _ & _ & HSF & _). pose proof (proj1 (Forall_forall _ _) HSF s Hs) as (X & _). clear - X Hsn Hn. lia. }
  assert (Eqp : AB + rz_size n0 = p) by (rewrite EpM; unfold M; lia).
  assert (Hqne : q <> p) by (clear - DISJ Hn Hn0; lia).
  assert (ELfin : live Σ'' = (q, n) :: live_remove p (live Σ)).
  { rewrite EL4, EL2. unfold Σ1. cbn [live free_p]. rewrite Eqp, HL, live_remove_cons. cbn [fst].
    destruct (Z.eqb_spec q p) as [E|_]; [exfalso; exact (Hqne E) | reflexivity]. }
  assert (ELAY : lay Σ'' = lay Σ) by (rewrite ELY4, ELY2; unfold Σ1; cbn [lay free_p]; exact HLAY).
  assert (QLO : q + n <= lo) by (clear - QHI LOW'; lia).
  (* [comment removed for export] *)
  assert (RW13 : forall a cs, usp + -2208 <= a -> a + Z.of_nat (cells_size cs) <= USTACK_TOP -> rw_cells asegs m1 a cs -> rw_cells asegs m3 a cs).
  { intros a cs H1 H2 X. apply (rw_cells_transport asegs [(q, q + k)] m2 m3 _ _ (rw_cells_agree asegs m1 m2 a cs X (AG12 a _ H1 H2) WM2) MU3 WM3).
    cbn [disjoint_from]. split; [right; clear - QLO Hkk LOR H1; unfold RT_STACK in *; lia | exact I]. }
  lazymatch type of IC1 with rw_cells _ _ ?a ?cs => assert (IC1c : rw_cells asegs m3 a cs) by (apply (RW13 a cs); [lia | cbn [cells_size csize Nat.add]; clear - SPT; fold usp in SPT; lia | exact IC1]) end.
  lazymatch type of IC2 with rw_cells _ _ ?a ?cs => assert (IC2c : rw_cells asegs m3 a cs) by (apply (RW13 a cs); [lia | cbn [cells_size csize Nat.add]; clear - SPT; fold usp in SPT; lia | exact IC2]) end.
  lazymatch type of IC3 with rw_cells _ _ ?a ?cs => assert (IC3c : rw_cells asegs m3 a cs) by (apply (RW13 a cs); [lia | cbn [cells_size csize Nat.add]; clear - SPT; fold usp in SPT; lia | exact IC3]) end.
  destruct HAST4 as (HM5 & HPm5 & HPM5 & HZ5).
  destruct HPm5 as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & F5 & fc5 & m5 & Ems5 & ART5 & MI5 & ST5 & RP5 & CF5).
  assert (AG35 : forall a k', uv <= a -> a + k' <= USTACK_TOP -> agree_on (fun x => a <= x < a + k') m3 m5).
  { intros a k' H1 H2 x Hx. apply RP5. left. lia. }
  rewrite Espv in Ems5, ST5, RP5. rewrite <- Esp8 in Ems5, ST5.
  lazymatch type of IC1c with rw_cells _ _ ?a ?cs => assert (IC1d : rw_cells asegs m5 a cs)
    by (apply (rw_cells_agree_nw asegs m3 m5 a cs IC1c); apply AG35; [unfold uv; lia | cbn [cells_size csize Nat.add]; clear - SPT; fold usp in SPT; lia]) end.
  lazymatch type of IC2c with rw_cells _ _ ?a ?cs => assert (IC2d : rw_cells asegs m5 a cs)
    by (apply (rw_cells_agree_nw asegs m3 m5 a cs IC2c); apply AG35; [unfold uv; lia | cbn [cells_size csize Nat.add]; clear - SPT; fold usp in SPT; lia]) end.
  lazymatch type of IC3c with rw_cells _ _ ?a ?cs => assert (IC3d : rw_cells asegs m5 a cs)
    by (apply (rw_cells_agree_nw asegs m3 m5 a cs IC3c); apply AG35; [unfold uv; lia | cbn [cells_size csize Nat.add]; clear - SPT; fold usp in SPT; lia]) end.
  (* [comment removed for export] *)
  lazymatch type of Ems5 with _ = ?X =>
    assert (W5 : forall ms, eq X ms ->
      evt asegs (fun ms' => exists m6, ret_st ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 q) m6 ms'
                   /\ munch [(usp - 2208, usp)] m5 m6 /\ wmono asegs m5 m6 /\ mem_inv asegs m6 /\ stk asegs m6 lo usp) ms) end.
  { intros ms <-. destruct CF5 as ((ws & G1 & G1l) & (w & G2) & (jq' & G3) & (ja' & G4) & G5).
    pose proof (realloc_B_spec ra sp gp (Z_to_bv 64 tpA) z0 z1 z2 q0 q1 z3 z4 z5 z6 z7 z8 z9 z10 q2 q3 q5 s6A s7 s8 s9 s10 s11 z11 z12 z13 z14
                  retw s0 s1 s2 s3 s4 s5 s6 (Z_to_bv 64 usp) (Z_to_bv 64 n) (Z_to_bv 64 p) (Z_to_bv 64 0x1c3760) (Z_to_bv 64 1)
                  F5 fc5 m5 q lo ws w (Z_to_bv 64 usp) jp jq' ja'
                  ltac:(clear - Hq0 HqU Hn; unfold USTACK_TOP in *; lia) ST5 ltac:(clear - LOR; unfold RT_STACK in *; lia)
                  ltac:(clear - HLOH; unfold kHighShadowEnd in *; lia)
                  IC1d IC2d IC3d G1 G1l G2 G3 G4 G5 MI5) as BK.
    eapply evt_mono; [exact BK|].
    intros ms' (e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & e8 & e9 & e10 & e11 & e12 & e13 & m6 & -> & MU6 & WM6 & MI6 & ST6).
    exists m6. split; [exists e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, F5, fc5; reflexivity|].
    split; [exact MU6|]. split; [exact WM6|]. split; [exact MI6 | exact ST6]. }
  lazymatch type of Ems5 with _ = ?X => assert (Hc5' : ASTA RTA Σ'' PMc (eq X) c4) end.
  { split; [exact HM5|]. split; [symmetry; exact Ems5|]. split; [exact HPM5 | exact HZ5]. }
  apply (cps_realizes asegs _ _ _ c4 (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ'') _ _ _ (fl_ASTA_mat_stable Σ'' PMc MST) W5) Hc5').
  clear W5 Hc5'.
  intros c5 Hc5. apply Hk. exists Σ'', q.
  cbn [rt_live rt_frames rt_sp0 rt_credit rt_cg RTA]. unfold rtA_live, rtA_frames, rtA_sp0, rtA_credit, rtA_cg.
  split.
  2:{ split; [exact ELfin|]. split; [rewrite EF4, EF2; unfold Σ1; cbn [frames free_p]; exact HF|]. split; [rewrite ELAY; reflexivity|].
      split; [rewrite EC4, EC2; unfold Σ1; cbn [credit free_p]; exact HCR|]. split; [exact Hq0|]. split; [exact Hq16|]. split; [exact HqU|].
      rewrite ELAY. reflexivity. }
  unfold ASTA. eapply AST_conseq; [exact Hc5 | | intros mo X; exact X].
  intros ms' (m6 & RET6 & MU6 & WM6 & MI6 & ST6). exists m6. split; [exact RET6|].
  assert (ART6 : ART_A Σ'' m6).
  { assert (MUC : munch (W_client Σ'' (usp + -2208)) m5 m6).
    { eapply (munch_weaken _ _ m5 m6); [|exact MU6]. intros x Hx. unfold W_client in Hx. cbn [app outside] in Hx |- *.
      destruct Hx as (X1 & _). split; [clear - X1 SPT; fold usp in SPT; lia | exact I]. }
    assert (Hsp'' : rtA_sp0 Σ'' - STACK_WIN <= usp + -2208) by (unfold rtA_sp0; rewrite ELAY; clear - LOW LOR; unfold RT_STACK in *; lia).
    exact (ART_transport _ Σ'' m5 m6 ART5 MUC WM6 (art_avoid_client Σ'' m5 (usp + -2208) ART5 Hsp'')). }
  split; [split; [exact ART6 | split; [exact MI6 | exact ST6]]|].
  split.
  { (* [comment removed for export] *)
    intros a Ha. pose proof (aclient_live_remove _ _ _ _ _ Ha) as Ha'.
    pose proof (frontR_client Σ m usp ART0 Hsp _ Ha') as Ho. pose proof Ho as (_ & _ & _ & O4 & _).
    rewrite (MU6 a ltac:(cbn [outside]; split; [clear - O4; lia | exact I])).
    rewrite (RP5 a).
    2:{ destruct Ha as [H|[H|[H|[H|H]]]]; [left; unfold uv; clear - H; lia | right; left; exact H | | right; right; right; left; rewrite HF; exact H
                                          | right; right; right; right; rewrite HF; exact H].
        right; right; left. destruct H as (p' & n' & Hin0 & Hpx). exists p', n'. split; [|exact Hpx].
        apply live_remove_In in Hin0 as (Hin1 & Hne).
        rewrite EL2. unfold Σ1. cbn [live free_p]. rewrite Eqp. apply live_remove_In. split; [rewrite HL; right; exact Hin1 | exact Hne]. }
    rewrite (MU3 a ltac:(cbn [outside]; split; [pose proof (LBA _ Ha') as X; clear - X Hkk; lia | exact I])).
    rewrite (RP2 a ltac:(destruct Ha' as [H|H]; [left; clear - H; lia | right; exact H])).
    exact (MU1' a Ho). }
  pose proof (af_acc_live RTA rta_art_facts Σ'' m6 q n ART6 ltac:(cbn [rt_live RTA]; unfold rtA_live; rewrite ELfin; left; reflexivity)) as (WR6 & AC6).
  split; [exact WR6|]. split; [exact AC6|].
  (* [comment removed for export] *)
  intros bs Hbs Hbl.
  assert (Hlk : length bs = Z.to_nat k) by (unfold k; rewrite Z.min_comm; clear - Hbl; lia).
  assert (Hb2 : bytes_at asegs m2 p bs).
  { apply (bytes_at_agree asegs m m2 p bs Hbs). intros a Ha.
    assert (Hac : aclient (live Σ) (frames Σ) usp (bv_unsigned a)).
    { right; right; left. exists p, n0. split; [exact Hin|]. rewrite Hlk in Ha. clear - Ha Hkk. lia. }
    rewrite (RP2 a ltac:(destruct Hac as [H|H]; [left; clear - H; lia | right; exact H])).
    exact (MU1' a (frontR_client Σ m usp ART0 Hsp _ Hac)). }
  assert (Esrc : bs = src) by (rewrite EpM in Hb2; apply (bytes_at_inj m2 (M + 16) bs src Hb2 SRCb); rewrite Hlk, SRCl; reflexivity).
  subst bs.
  assert (Hb3 : bytes_at asegs m3 q src).
  { destruct DST3 as [[_ HB3] _]. cbn [cells_bytes cbytes] in HB3. rewrite app_nil_r in HB3. exact HB3. }
  apply (bytes_at_transport asegs [(usp - 2208, usp)] m5 m6 q src); [|exact MU6|].
  - apply (bytes_at_agree asegs m3 m5 q src Hb3). intros a Ha. apply RP5. right; right; left. exists q, n.
    split; [rewrite EL2; unfold Σ1; cbn [live free_p]; rewrite Eqp; apply live_remove_In; split; [rewrite HL; left; reflexivity | cbn [fst]; exact Hqne]|].
    rewrite Hlk in Ha. clear - Ha Hkk. lia.
  - cbn [disjoint_from]. rewrite Hlk. split; [left; clear - QLO Hkk LOR; unfold RT_STACK in *; lia | exact I].
Qed.
