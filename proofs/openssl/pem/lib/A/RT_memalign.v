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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_unwind_defs R_asan_defs R_allocate1 R_asan_malloc R_asan_free R_prim_kit RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_facts RT_malpre RT_malstate RT_maltail RT_malcore_stmt RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_sys_stmt RT_unwindk RT_artfacts R_asan_front_k I_lkit RT_malcore_m RT_iface_pem RM_allocate1 R_asan_memalign RT_realloc_front RTM_maltail RTM_malcore_stmt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

Lemma eps_memalign : In (e_posix_memalign, PC_MEMALIGN) ALLOC_EPS. Proof. right; right; right; left; reflexivity. Qed.

Lemma memalign_front_spec : forall ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (pp n TCX T top bot lo : Z) (cg : cgraph),
  cg_wf cg ALLOC_EPS ALLOC_RAS N_TR ->
  (0 <= pp < 2^63)%Z -> (1 <= n <= 2^31)%Z -> (n mod 64 = 0)%Z -> (needed n + 64 <= 64512)%Z ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2336)%Z -> (kHighShadowEnd + 8 <= lo)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  (0 <= bot < top)%Z -> (top < 2^64)%Z ->
  unwind_ok cg e_posix_memalign m ra s0 sp -> (4096 <= top)%Z -> (top <= 2 ^ 63)%Z ->
  rw_cells asegs m 0x5a4598 [C8 (Z_to_bv 64 0x6fc5e0)] ->
  rw_cells asegs m g_GOT_common_flags [C8 (Z_to_bv 64 g_common_flags)] ->
  rw_cells asegs m i_max_user [C8 (Z_to_bv 64 (2^40))] -> rw_cells asegs m i_min_rz [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)] ->
  rw_cells asegs m g_asan_inited [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m g_malloc_context_size_cell [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m g_rss_limit_exceeded [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0x6fc5e0 [C8 (Z_to_bv 64 4096)] ->
  rw_cells asegs m (g_common_flags + 34) [C1 (Z_to_bv 8 1)] ->
  thread_cells TCX T m -> (0 < TCX)%Z -> (TCX + 0xa0 <= lo)%Z -> (0 < T)%Z -> (T + 4096 <= 0x10000 \/ 0xbc6000 <= T)%Z ->
  (T + 4096 <= lo)%Z ->
  (TCX + 0xa0 <= T \/ T + 4096 <= TCX)%Z ->
  stack_cells T top bot m -> rw_cells asegs m (T + 3168) [C1 (Z_to_bv 8 0)] ->
  mem_inv asegs m ->
  exists tr, uw_tr_shape cg e_posix_memalign PC_MEMALIGN tr
    /\ evt asegs (memalign_A_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc pp n T lo tr m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 pp) (Z_to_bv 64 64) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 wrap_memalign_entry) fc None m (seg_rom asegs)).
Proof.
  intros until cg. intros WF Hpp Hn Hn64 HND ST HLO HLOH HSP Hbt Htop UWOK Ht1 Ht2 G60 GCF MX RZ AI MCS RSS PSC FUM TC HTCX HTCXl HT0 HT HTl HTT SC UW MI.
  destruct (unwind_ok_trace cg e_posix_memalign PC_MEMALIGN
              [(T + 3168, T + 3169); (bv_unsigned sp - 2336, bv_unsigned sp)]
              m ra s0 sp bot top eps_memalign WF Ht1 Ht2) as (ch & tr & CCH & HTR & HS); [|exact UWOK|].
  { unfold kHighShadowEnd in HLOH. repeat constructor; cbn [snd]; lia. }
  exists tr. split; [exact HS|].
  change PC_MEMALIGN with memalign_pc in HTR.
  exact (memalign_Ak_spec ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m pp n
           TCX T top bot lo ch tr Hpp Hn Hn64 HND ST HLO HLOH HSP Hbt Htop CCH HTR G60 GCF MX RZ AI MCS RSS PSC FUM TC HTCX HTCXl
           HT0 HT HTl HTT SC UW MI).
Qed.

(* [comment removed for export] *)
Lemma live_al64 : forall Σ (m : mem) p n, ART_A Σ m -> In (p, n) (live Σ) -> n <= 64512 -> rz_size n mod 64 = 0 ->
  ClassSize (ClassID (needed n)) mod 64 = 0 -> p mod 64 = 0.
Proof.
  intros Σ m p n HA Hin Hn HRZ HCS.
  pose proof (ART_wf Σ m HA) as (_ & HR & HV & HS & _). destruct HV as (_ & _ & HVin & _).
  destruct (HVin p n Hin) as [(c & i & Hc & Hnth & ->)|(s & Hs & Hq & Hsn & ->)].
  - destruct HR as (HR & _). pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
    pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hnth)) as (_ & _ & Ec). cbv beta iota in Ec.
    pose proof (geo_prb Σ m HA) as (_ & _ & P3). subst c.
    unfold p_ubeg, p_abeg. apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [apply Z.divide_add_r; [apply Z.divide_add_r|]|].
    + apply Z.mod_divide in P3; [|lia]. apply (Z.divide_trans 64 (2 ^ 16)); [exists 1024; reflexivity | exact P3].
    + exists (ClassID (needed n) * 2 ^ 26). lia.
    + apply Z.divide_mul_r. apply Z.mod_divide in HCS; [|lia]. exact HCS.
    + apply Z.mod_divide in HRZ; [|lia]. exact HRZ.
  - exfalso. destruct HS as (_ & _ & _ & HSF & _). pose proof (proj1 (Forall_forall _ _) HSF s Hs) as (X & _). lia.
Qed.

Theorem rta_memalign : core_stmt_prim_al64 -> memalign_contract RTA.
Proof.
  intros CP Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m pp al n lo
    FDO MST Ea0 Ea1 Ea2 Etp HPL Hpp CHK Hlen Hcr ART0 MI0 CALL UWOK. subst a0 a1 a2 tp.
  destruct HPL as (-> & Hn1 & Hn64 & HND & HRZ & HCLS & HCS).
  intros TT cf Hc Hk. cbn [ART rt_live rt_frames rt_sp0 rt_credit rt_cg RTA] in Hlen, Hcr, ART0, UWOK, CHK.
  unfold rtA_live, rtA_credit, rtA_cg in Hlen, Hcr, UWOK.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA). cbn [rt_sp0 RTA] in LOW. unfold rtA_sp0 in LOW.
  pose proof (mp_cells Σ m ART0) as (G60 & GCF & MX & RZ & AI & MCS & RSS & PSC & FUM & TC & SC & UB).
  pose proof (mp_layout Σ m sp lo ART0 CALL) as (HTCX & HTCXl & HTl & HTT & HLOH & Hbt & Htop & HT).
  pose proof (geo_grant Σ m ART0 (l_T (lay Σ)) 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (GT1 & _).
  assert (LOW' : l_ACEIL (lay Σ) <= lo) by (unfold l_ACEIL; lia).
  set (usp := bv_unsigned sp) in *.
  assert (Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp) by (clear - LOW' LOR; unfold RT_STACK in *; lia).
  destruct (ART_ia Σ m ART0) as (b & IS).
  (* [comment removed for export] *)
  pose proof (rz_size_range n) as RZR. pose proof (rounded_range n ltac:(lia)) as (RR1 & RR2 & RR3).
  assert (Hn : 1 <= n <= 64512) by (unfold needed in HND; lia).
  assert (FP : from_primary n = true) by (unfold from_primary; apply Z.leb_le; lia).
  assert (EN : needed2 n = needed n) by (unfold needed2; rewrite FP; lia).
  (* [comment removed for export] *)
  destruct CHK as (_ & CKA & CKW).
  assert (PPS : pp + 8 <= lo \/ usp <= pp).
  { pose proof (RT_malcore_m.aclient_split Σ m usp pp ART0 ltac:(replace pp with (pp + 0) by lia; apply CKA; lia)) as X0.
    pose proof (RT_malcore_m.aclient_split Σ m usp (pp + 7) ART0 ltac:(apply CKA; lia)) as X7.
    clear - X0 X7 LOW' LOR. unfold RT_STACK in *. lia. }
  assert (HW : exists tr, uw_tr_shape (l_cg (lay Σ)) e_posix_memalign PC_MEMALIGN tr
             /\ evt asegs (memalign_A_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc pp n (l_T (lay Σ)) lo tr m)
                  (entry_st ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 (Z_to_bv 64 pp) (Z_to_bv 64 64) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                     t3 t4 t5 t6 F fc e_posix_memalign m)).
  { unfold entry_st, e_posix_memalign.
    exact (memalign_front_spec ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m pp n
             (l_TCX (lay Σ)) (l_T (lay Σ)) (l_top (lay Σ)) (l_top (lay Σ) - 0x800000) lo (l_cg (lay Σ)) (ART_cg_wf Σ m ART0)
             ltac:(clear - Hpp; lia) ltac:(clear - Hn; lia) Hn64 HND ST ltac:(clear - LOR; unfold RT_STACK in LOR; fold usp; lia) HLOH
             ltac:(clear - SPT; unfold USTACK_TOP in SPT; fold usp; lia)
             ltac:(clear - Hbt; lia) ltac:(clear - Htop; lia) UWOK ltac:(clear - Htop; lia) ltac:(clear - Htop; lia)
             G60 GCF MX RZ AI MCS RSS PSC FUM TC HTCX HTCXl GT1 HT HTl HTT SC UB MI0). }
  destruct HW as (tr & HS & W1). destruct (uw_tr_shape_main tr HS) as (Htr & Htrl & Htrr).
  assert (W1' : forall ms, eq (entry_st ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 (Z_to_bv 64 pp) (Z_to_bv 64 64) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
                                   s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_posix_memalign m) ms ->
                  evt asegs (memalign_A_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc pp n (l_T (lay Σ)) lo tr m) ms)
    by (intros ms <-; exact W1).
  clear W1.
  apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1') Hc).
  intros c1 Hc1. unfold memalign_A_post in Hc1.
  apply AST_exI in Hc1 as (t0' & Hc1). apply AST_exI in Hc1 as (t1' & Hc1). apply AST_exI in Hc1 as (t2' & Hc1).
  apply AST_exI in Hc1 as (a4' & Hc1). apply AST_exI in Hc1 as (a5' & Hc1). apply AST_exI in Hc1 as (a6' & Hc1).
  apply AST_exI in Hc1 as (a7' & Hc1). apply AST_exI in Hc1 as (t3' & Hc1). apply AST_exI in Hc1 as (t4' & Hc1).
  apply AST_exI in Hc1 as (t5' & Hc1). apply AST_exI in Hc1 as (t6' & Hc1). apply AST_exI in Hc1 as (tb & Hc1).
  apply AST_exI in Hc1 as (jp & Hc1). apply AST_exI in Hc1 as (j0 & Hc1).
  apply AST_exI in Hc1 as (m1 & Hc1).
  destruct Hc1 as (HM & HPm & HPM & HZ).
  destruct HPm as (Hms & MU1 & WM1 & MI1 & IC1 & IC2 & IC3 & TB1 & HTB & IC4 & IC5 & AFr & J0 & UB1 & ST1).
  fold usp in Hms, MU1, IC1, IC2, IC3, TB1, IC4, IC5, AFr, J0, ST1.
  assert (MU1' : munch (W_frR (l_T (lay Σ)) usp) m m1).
  { eapply (munch_weaken _ _ m m1); [|exact MU1]. intros x Hx. unfold W_frR in Hx. cbn [outside] in Hx |- *.
    destruct Hx as (X1 & X2 & X3 & X4 & _). split; [lia|]. split; [lia | exact I]. }
  assert (IS1 : ia_state b m1).
  { apply (ia_state_frame b _ m m1 IS MU1 WM1). pose proof (fr_geo Σ m ART0) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
    cbn [disjoint_from]. unfold SEGTOP_A, SHB in *. split; [clear - K4; lia|]. split; [clear - K10 Hsp; lia | exact I]. }
  pose proof (frontR_ART Σ m usp ART0 Hsp m1 b MU1' WM1 IS1 UB1) as ART1.
  set (B := usp + -2176). set (Bt := usp + -2144).
  assert (Hc2 : ASTA RTA Σ PMc (eq (core_entry_al64 Σ B Bt gp t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' F fc n m1)) c1).
  { split; [exact HM|]. split; [|split; [exact HPM | exact HZ]]. rewrite Hms. unfold core_entry_al64, B, Bt.
    replace (usp + -2176 + -144) with (usp + -2320) by lia. reflexivity. }
  assert (ST1' : stk asegs m1 lo (B + -144)) by (unfold B; replace (usp + -2176 + -144) with (usp + -2320) by lia; exact ST1).
  assert (TRC : RT_maltail.trc_cells Bt tr m1 tb).
  { unfold Bt. split; [replace (usp + -2144 + 16) with (usp + -2128) by lia; exact IC4|]. split; [replace (usp + -2144 + 16) with (usp + -2128) by lia; exact TB1 | exact HTB]. }
  assert (AFC : af_cells_g64 B (Z_to_bv 64 0x19b934) (Z_to_bv 64 pp) (Z_to_bv 64 64) (Z_to_bv 64 64) (Z_to_bv 64 63) (Z_to_bv 64 0x1c3a08) (Z_to_bv 64 1)
                  (Z_to_bv 64 (usp + -2144)) (Z_to_bv 64 (usp + -97)) s8 s9 s10 s11 m1 j0).
  { unfold B. split; replace (usp + -2176 + -144) with (usp + -2320) by lia; [exact AFr | exact J0]. }
  assert (LOR' : lo + 0x1000 <= B + -144) by (unfold B; clear - LOR; unfold RT_STACK in LOR; lia).
  assert (SPT' : B + 2144 <= USTACK_TOP) by (unfold B; clear - SPT; fold usp in SPT; lia).
  assert (SPA' : B mod 16 = 0).
  { unfold B. pose proof SPA as SPA0. fold usp in SPA0. apply Z.mod_divide in SPA0; [|lia]. destruct SPA0 as [q Hq]. apply Z.mod_divide; [lia|]. exists (q - 136). lia. }
  assert (HBT : B <= Bt /\ Bt + 2144 <= USTACK_TOP) by (unfold B, Bt; clear - SPT; fold usp in SPT; lia).
  apply (CP Σ PMc m1 B Bt (Z_to_bv 64 0x19b934) gp (Z_to_bv 64 pp) (Z_to_bv 64 64) (Z_to_bv 64 64) (Z_to_bv 64 63) (Z_to_bv 64 0x1c3a08) (Z_to_bv 64 1)
            (Z_to_bv 64 (usp + -2144)) (Z_to_bv 64 (usp + -97)) s8 s9 s10 s11 t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' F fc n lo tr tb j0
            FDO MST ltac:(clear - Hn; cbv beta; lia) ltac:(clear - Hn; lia) HRZ ltac:(rewrite EN; exact HCLS) ltac:(rewrite EN; exact HCS) ltac:(rewrite EN; exact HND)
            Hlen Hcr ART1 MI1 ST1' LOW' LOR' SPT' SPA' HBT Htr Htrl TRC AFC TT c1 Hc2).
  clear Hc2 W1'.
  intros c2 (Σ' & q & HAST & HL & HF & HSP0 & HCR & Hq0 & Hq16 & HqU & HLAY).
  destruct HAST as (HM2 & HPm2 & HPM2 & HZ2).
  destruct HPm2 as (m2 & RET2 & ART2 & MI2 & WM2 & ST2 & RP2 & WR2 & AC2).
  destruct RET2 as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & F2 & fc2 & Ems2).
  rewrite (ret_pc_even 0x19b934) in Ems2 by (lia || reflexivity).
  unfold B in ST2, RP2, Ems2. replace (usp + -2176 + -16) with (usp + -2192) in ST2, RP2, Ems2 by lia.
  assert (Hq64 : q mod 64 = 0) by (apply (live_al64 Σ' m2 q n ART2 ltac:(rewrite HL; left; reflexivity) ltac:(lia) HRZ HCS)).
  (* [comment removed for export] *)
  assert (AGS : forall a k, usp + -2192 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m1 m2).
  { intros a k H1 H2 x Hx. apply RP2. left. lia. }
  assert (SPT2 : usp + 16 <= USTACK_TOP) by (clear - SPT; fold usp in SPT; exact SPT).
  pose proof (rw_cells_agree_nw asegs m1 m2 _ _ IC1 ltac:(apply AGS; cbn [cells_size csize Nat.add]; lia)) as IC1'.
  pose proof (rw_cells_agree_nw asegs m1 m2 _ _ IC2 ltac:(apply AGS; cbn [cells_size csize Nat.add]; lia)) as IC2'.
  pose proof (rw_cells_agree_nw asegs m1 m2 _ _ IC3 ltac:(apply AGS; cbn [cells_size csize Nat.add]; lia)) as IC3'.
  pose proof (rw_cells_agree_nw asegs m1 m2 _ _ IC4 ltac:(apply AGS; cbn [cells_size csize Nat.add]; lia)) as IC4'.
  pose proof (rw_cells_agree_nw asegs m1 m2 _ _ IC5 ltac:(apply AGS; cbn [cells_size csize Nat.add]; lia)) as IC5'.
  assert (HWL : length (wr_trace tr tb) = 255%nat) by (rewrite wr_trace_length by lia; exact HTB).
  pose proof (u64arr_agree_nw asegs m1 m2 _ _ TB1 ltac:(apply AGS; rewrite ?HWL; lia)) as TB1'.
  destruct (wr_at_rw_CB m2 pp 8 (wr_at_transport asegs m1 m2 _ _ (wr_at_transport asegs m m1 _ _ CKW WM1) WM2) ltac:(lia)) as (jpp & PPC).
  change (Z.to_nat 8) with 8%nat in PPC.
  (* [comment removed for export] *)
  pose proof (memalign_B_spec ra sp gp (Z_to_bv 64 tpA) u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 (Z_to_bv 64 64) (Z_to_bv 64 64) (Z_to_bv 64 0x1c3a08) (Z_to_bv 64 1)
                (Z_to_bv 64 (usp + -2144)) (Z_to_bv 64 (usp + -97)) s8 s9 s10 s11 u10 u11 u12 u13 (Z_to_bv 64 0x19b934) s0 s1 s2 s3 s4 s5 s6 s7
                (Z_to_bv 64 usp) (Z_to_bv 64 n) (Z_to_bv 64 64) (Z_to_bv 64 pp) (Z_to_bv 64 0x1c3a08) F2 fc2 m2 pp q lo (wr_trace tr tb)
                (Z_to_bv 64 (Z.of_nat (length tr))) (Z_to_bv 64 usp) jp jpp
                ltac:(clear - Hq0 HqU Hn; unfold USTACK_TOP in HqU; lia) Hq64 ltac:(clear - Hpp; lia) PPS ltac:(clear - Hpp; lia)
                ST2 ltac:(fold usp; clear - LOR; unfold RT_STACK in LOR; lia) ltac:(clear - HLOH; unfold kHighShadowEnd in HLOH; lia)
                IC1' IC2' IC3' TB1' HWL IC4' IC5' PPC MI2) as W3.
  fold usp in W3.
  lazymatch type of Ems2 with _ = ?X => assert (Hc3 : ASTA RTA Σ' PMc (eq X) c2) end.
  { split; [exact HM2|]. split; [symmetry; exact Ems2|]. split; [exact HPM2 | exact HZ2]. }
  lazymatch type of Ems2 with _ = ?X =>
    assert (W3' : forall ms, eq X ms -> evt asegs (memalign_B_post ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F2 fc2 pp q lo m2) ms)
      by (intros ms <-; exact W3) end.
  clear W3.
  apply (cps_realizes asegs _ _ _ c2 (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ') _ _ _ (fl_ASTA_mat_stable Σ' PMc MST) W3') Hc3).
  clear W3' Hc3.
  intros c3 Hc3. apply Hk. exists Σ', q.
  cbn [rt_live rt_frames rt_sp0 rt_credit rt_cg RTA]. unfold rtA_live, rtA_frames, rtA_sp0, rtA_credit, rtA_cg.
  split.
  2:{ split; [exact HL|]. split; [exact HF|]. split; [rewrite HLAY; reflexivity|]. split; [exact HCR|]. split; [exact Hq0|]. split; [exact Hq64|].
      split; [exact HqU|]. rewrite HLAY. reflexivity. }
  unfold ASTA. eapply AST_conseq; [exact Hc3 | | intros mo X; exact X].
  intros ms' (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & m3 & -> & MU3 & WM3 & MI3 & PPV & ST3). exists m3.
  fold usp in MU3, ST3.
  split; [exists v0, v1, v2, d1, d2, d3, d4, d5, d6, d7, v3, v4, v5, v6, F2, fc2; reflexivity|].
  (* [comment removed for export] *)
  assert (CK' : forall i, 0 <= i < 8 -> aclient (live Σ') (frames Σ') (usp + -2192) (pp + i)).
  { intros i Hi. specialize (CKA i Hi). cbn [rt_live rt_frames RTA] in CKA. unfold rtA_live, rtA_frames in CKA. fold usp in CKA.
    destruct CKA as [H|[H|[H|[H|H]]]]; [left; clear - H; lia | right; left; exact H | | right; right; right; left; rewrite HF; exact H
                                        | right; right; right; right; rewrite HF; exact H].
    right; right; left. destruct H as (p' & n' & Hin0 & Hpx). exists p', n'. split; [rewrite HL; right; exact Hin0 | exact Hpx]. }
  assert (ART3 : ART_A Σ' m3).
  { assert (Hsp'' : rtA_sp0 Σ' - STACK_WIN <= usp + -2192) by (unfold rtA_sp0; rewrite HLAY; clear - LOW LOR; unfold RT_STACK in *; lia).
    apply (ART_client_frame Σ' m2 m3 (usp + -2192) ART2 Hsp''); [| exact WM3].
    intros a Ha. apply MU3. cbn [outside]. split; [| split; [| exact I]]; intros Hin; apply Ha.
    - replace (bv_unsigned a) with (pp + (bv_unsigned a - pp)) by lia. apply CK'. lia.
    - left. clear - Hin SPT2. lia. }
  split; [split; [exact ART3 | split; [exact MI3 | split; [exact (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 WM3)) | exact ST3]]]|].
  split.
  { intros a Ha Hnp. pose proof (frontR_client Σ m usp ART0 Hsp _ Ha) as Ho. pose proof Ho as (_ & _ & _ & O4 & _).
    rewrite (MU3 a ltac:(cbn [outside]; split; [exact Hnp | split; [clear - O4; lia | exact I]])).
    rewrite (RP2 a ltac:(destruct Ha as [H|H]; [left; clear - H; lia | right; exact H])).
    exact (MU1' a Ho). }
  split; [exact PPV|].
  exact (af_acc_live RTA rta_art_facts Σ' m3 q n ART3 ltac:(cbn [rt_live RTA]; unfold rtA_live; rewrite HL; left; reflexivity)).
Qed.
