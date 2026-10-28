(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep ZBridge.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import LhPure.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_mkit Fz_G_kit Th_mutex Fz_T_lock Fz_env Fz_M_malloc Fz_M_zalloc Fz_M_realloc Fz_M_realloc_array Fz_G_CRYPTO_calloc Fz_T_sk Fz_I1_insw Fz_I1_insx Fz_K_hash Fz_K_rep Fz_K_getrn Fz_K_retrieve Fz_K_insw Fz_K_insert Fz_K_skw Fz_K_sk Fz_I2_ppis Fz_K_pstw Fz_K_pstw2 Fz_K_pstrs Fz_W2_gets Fz_K_pstrh Fz_K_pstrt Fz_K_pstr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation wz := (Z_to_bv 64) (only parsing).
Notation z64 := (Z_to_bv 64 0) (only parsing).

Section CPstrF.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis SM0 : stack_malloc_contract RT 0.
Hypothesis SLC : strlen_icontract RT.
Hypothesis MCP : memcpy_icontract RT e_asan_memcpy.
Hypothesis C_CM : crypto_malloc_env_stmt RT.
Hypothesis C_CALLOC : CRYPTO_calloc_stmt RT.
Hypothesis GO_ctx : GOBJ PPI_CTX 328.

Theorem pstr_first_cps : pstr_first_stmt RT GOBJ.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary
    nm S b sz str slack ps pk pl1 pl2 ni vi pq1 pq2 B items bks pad nalloc comp cmpt freet copyt PRE HC.
  pose proof PRE as (FDO & MST & _ & _ & _ & _ & Etp & ART0 & MI0 & CALL & HSTK & CTX & UWC & CGH & Hfr & Hlen & Hcr & ENV
     & ROB & NONUL & NE & LEN & SLK & HG & Hbs & Hse & HS0 & HSE
     & CELL & INPS & PSAL & PSC & NI & VI & INPK & PKAL & LKC & REP & INL & ITEMS & HASHES & INA & AAL).
  subst tp. intros T c HA Hk.
  apply (pstr_head RT GOBJ AF AFP SM0 SLC MCP C_CM GO_ctx Σ PMc ra sp gp _ t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary
           nm S b sz str slack ps pk pl1 pl2 ni vi pq1 pq2 B items bks PRE T c HA).
  clear HA PRE. intros c8 (Σ2 & f & pn & m8 & u0 & u1 & u2 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F8 & fc8 & HA8 & LV2 & MID8).
  pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof MID8 as ((ART8 & MI8 & ST8) & (FRS2 & SP2 & CG2 & CR2) & ENV8 & WMH & A08 & AGS08 & (INC2 & INPS2 & INPK2 & INL2 & INQ2) & ((j8 & FR8) & _) & _ & _ & QFRESH & QOK).
  set (usp := bv_unsigned sp) in *. unfold PSTR_STK in HSTK.
  set (pd := usp mod 32) in *.
  assert (HP : pd = 0 \/ pd = 16) by (unfold pd; clear - SPA; Z.div_mod_to_equations; lia).
  assert (ERB : ps_RB sp = usp + -160 - pd) by reflexivity. clearbody pd.
  set (len := Z.of_nat (length str)) in *. assert (Hl0 : 1 <= len) by (unfold len; clear - NE; destruct str; [congruence| cbn [length]; lia]).
  set (t := t_of nm pl1 pl2) in *. set (A := q_of nm pq1 pq2) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 704 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (clear - HSTK LOW SP0R SP0W SPT; unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -160 - pd) in *.
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; clear - NUM HSTK HP SP0R; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (BLK : forall p n, In (p, n) (rt_live RT Σ) -> 1 <= n <= 64512 -> 0 < p /\ p + n <= lo /\ 0x10007fff8000 <= p /\ p + n <= 2 ^ 47).
  { intros p n Hin Hn. pose proof (af_live_range RT AF Σ m p n ART0 Hin) as (P0 & P1 & _).
    pose proof (afp_live_hi RT GOBJ AFP Σ m p n ART0 Hin ltac:(clear - Hn; lia)) as PH. pose proof (afp_live_mem RT GOBJ AFP Σ m p n ART0 Hin ltac:(clear - Hn; lia)) as [_ PM]. clear - P0 P1 PH PM LOW. lia. }
  destruct (BLK A 56 INA ltac:(clear; lia)) as (A0 & ALO & AHI & ATOP).
  destruct (BLK ps 48 INPS ltac:(clear; lia)) as (PS0 & PSLO & PSHI & PSTOP). destruct (BLK pk 40 INPK ltac:(clear; lia)) as (PK0 & PKLO & PKHI & PKTOP).
  assert (AP : forall x y, In x (rt_live RT Σ) -> In y (rt_live RT Σ) -> x <> y -> fst x + snd x <= fst y \/ fst y + snd y <= fst x) by (intros x y; exact (live_ne_apart2 RT AF Σ m x y ART0)).
  pose proof (AP (A, 56) (ps, 48) INA INPS ltac:(clear; intros E; injection E; lia)) as APS. pose proof (AP (A, 56) (pk, 40) INA INPK ltac:(clear; intros E; injection E; lia)) as APK.
  cbn [fst snd] in APS, APK.
  assert (WM08 : wmono asegs m m8) by exact (WMH eq_refl).
  assert (HC8 : rw_cells asegs m8 A (sk_cells z64 pad z64 (Z_to_bv 64 1) nalloc comp cmpt freet copyt)).
  { apply (rw_cells_agree asegs m m8 _ _ HC); [| exact WM08]. intros x Hx. cbv beta in Hx. unfold sk_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply A08; [exact (acl_live _ _ _ A 56 (bv_unsigned x) INA ltac:(clear - Hx; lia))|]. unfold PS_WH, G_ALLOW_CUST. cbn [outside]. clear - Hx AHI APS APK. lia. }
  assert (INA2 : In (A, 56) (rt_live RT Σ2)) by (apply INC2; exact INA).
  rewrite ERB in ST8. fold usp1 in ST8.
  (* [comment removed for export] *)
  unfold ps_ftail in FR8.
  assert (FRR8 : rw_cells asegs m8 (usp - 16) [C8 s0; C8 ra]).
  { lazymatch type of FR8 with rw_cells _ _ _ [?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10; ?c11; ?c12; ?c13; ?c14] =>
      pose proof (rw_cells_skip m8 _ [c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12] [c13; c14] FR8) as X end.
    cbn [cells_size csize Nat.add] in X. replace (usp + -160 + Z.of_nat 144) with (usp - 16) in X by (clear; lia). exact X. }
  destruct (cl_chain_call (rt_cg RT Σ) e_property_string e_sk_push SITE_ps_push m m8 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH (SITE_ps_push, e_property_string) ltac:(unfold PSTR_SITES; right; left; reflexivity)) (proj2 CGH (SITE_ps_push, e_sk_push) ltac:(unfold PSTR_CALLS; right; left; reflexivity))
              UWC AGS08 FRR8 ltac:(rewrite EU1; fold usp; unfold usp1; clear - HP; lia) SPT) as (CTX8 & UWC8).
  unfold ps_push_entry in HA8. rewrite ERB in HA8. fold usp1 A in HA8.
  (* [comment removed for export] *)
  apply (sk_push_first_cps RT GOBJ AF AFP C_CALLOC Σ2 PMc (Z_to_bv 64 SITE_ps_push) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 A) (Z_to_bv 64 (pn + 12)) (Z_to_bv 64 0) (Z_to_bv 64 0) b4 b5 b6 b7
           (Z_to_bv 64 f) (Z_to_bv 64 ps) (Z_to_bv 64 (Z.shiftr ps 3 + 2147450880)) (Z_to_bv 64 (ps + off_idx nm)) (Z_to_bv 64 2147450880) (Z_to_bv 64 pn)
           (Z_to_bv 64 A) (Z_to_bv 64 (Z.shiftr (ps + off_idx nm) 3 + 2147450880)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) u3 u4 u5 u6 F8 fc8 m8 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary
           A pad nalloc comp cmpt freet copyt FDO MST eq_refl eq_refl ART8 MI8).
  { unfold call_ok. rewrite EU1, SP2. split; [exact ST8|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; clear - HSTK HP; lia|]. split; [unfold USTACK_TOP in *; clear - NUM HP; lia|].
    fold usp in SPA. clear - SPA HP. Z.div_mod_to_equations. lia. }
  { rewrite EU1. unfold usp1, RT_STACK in *. clear - HSTK HP. lia. }
  { rewrite (unsigned_lit SITE_ps_push) by (unfold SITE_ps_push; clear; lia). rewrite CG2. exact CTX8. }
  { exact UWC8. }
  { rewrite (unsigned_lit SITE_ps_push) by (unfold SITE_ps_push; clear; lia). rewrite CG2. apply (proj2 CGH). unfold PSTR_CALLS. right; right; left. reflexivity. }
  { rewrite CG2. clear - CGH. unfold PSTR_SITES, PSTR_CALLS in CGH. split; intros x Hx; [apply (proj1 CGH)| apply (proj2 CGH)]; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hx. }
  { rewrite LV2. cbn [length]. clear - Hlen. lia. }
  { rewrite CR2. clear - Hcr. lia. }
  { exact ENV8. } { exact INA2. } { exact AAL. } { exact HC8. }
  { exact HA8. }
  clear HA8. intros c9 (Σ3 & D & Hc9 & LV3 & FRS3 & SP3 & CR3 & D0 & D16 & DU & CG3).
  destruct (ASTA_unpack RT Σ3 _ _ c9 Hc9) as (ms9 & (m9 & RS9 & (ART9 & MI9 & WM9 & ST9) & PRES9 & ENV9 & HC9 & DC9) & Hc9'). clear Hc9.
  rewrite EU1 in ST9, PRES9.
  (* [comment removed for export] *)
  pose proof (af_frames_range RT AF Σ2 m8 f 0%nat ART8 ltac:(rewrite FRS2; left; reflexivity)) as (F0 & FLO & _ & PF).
  pose proof (af_frames_align RT AF Σ2 m8 f 0%nat ART8 ltac:(rewrite FRS2; left; reflexivity)) as (F64 & FIMG).
  pose proof (proj1 (af_fshadow_apart RT AF Σ2 m8 f 0%nat ART8 ltac:(rewrite FRS2; left; reflexivity))) as SLF.
  change (fs_size 0) with 64 in FLO, PF, SLF. unfold SEGTOP_A in FIMG.
  assert (SHF : shad (f + 64) = shad f + 8) by (replace (f + 64) with (f + 64 * 1) by (clear; lia); rewrite (shad_add64 f 1 F64); clear; lia).
  rewrite SHF in SLF. unfold shad, SHB in SLF.
  assert (FPOK : forall x, ps_kept sp nm str ps pk pl1 pl2 B bks f pn x -> outside [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (A, A + 56)] x).
  { intros x Hx. unfold ps_kept in Hx. rewrite ERB in Hx. fold usp1 t len in Hx. cbn [outside]. unfold G_ALLOW_CUST.
    pose proof (PF A 56 INA2) as X1. pose proof (SLF A 56 INA2) as X3. pose proof (QFRESH A 56 INA) as X5. destruct QOK as (Q0 & _ & _).
    pose proof (Z.div_pos f 8 ltac:(clear - F0; lia) ltac:(clear; lia)) as FD.
    destruct Hx as [H|[H|[H|[H|[H|[H|[H|H]]]]]]].
    - unfold usp1 in H. clear - H ALO HSTK HP NUM. unfold RT_STACK in *. lia.
    - unfold CTX_PSD in H. clear - H AHI. lia.
    - clear - H X1 FIMG. lia.
    - clear - H X3 FD. lia.
    - clear - H APS PSHI. lia.
    - clear - H APK PKHI. lia.
    - assert (X : exists p n, In (p, n) (plh_L t B bks) /\ p <= x < p + n /\ (n = 104 \/ n = 128 \/ n = 24)).
      { destruct H as [H|[H|(n & Hn & H)]]; [exists t, 104; split; [left; reflexivity| clear - H; lia]| exists B, 128; split; [right; left; reflexivity| clear - H; lia]|
          exists (fst n), 24; split; [exact (plh_L_node t B bks n Hn)| clear - H; lia]]. }
      destruct X as (p & n & Hin & Hpx & Hn).
      pose proof (AP (A, 56) (p, n) INA (INL _ Hin) ltac:(intros E; injection E; clear - Hn; lia)) as Y1. cbn [fst snd] in Y1.
      destruct (BLK p n (INL _ Hin) ltac:(clear - Hn; lia)) as (_ & _ & PH & _). clear - Hpx Y1 PH. lia.
    - pose proof (afp_live_hi RT GOBJ AFP Σ2 m8 pn (len + 16) ART8 INQ2 ltac:(clear - LEN; unfold len; lia)) as QH. clear - H X5 QH. lia. }
  pose proof (ps_mid_step RT AF Σ m ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo canary nm S str ps pk pl1 pl2 ni vi pq1 pq2 B items bks f pn Σ2 Σ3 m8 m9
                (rt_live RT Σ) (rt_live RT Σ) (PS_WH ps pk) [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (A, A + 56)] (rt_live RT Σ2) true true
                MID8 ART9 MI9 ltac:(rewrite ERB; exact ST9) ENV9 FRS3 SP3 CG3 CR3 (fun _ => conj eq_refl WM9) ltac:(rewrite ERB; exact PRES9)
                ltac:(intros e He; rewrite LV3; right; exact He) (fun e He => He) INC2 INPS2 INPK2 INL2 INQ2 ltac:(clear - NUM; lia) FPOK) as MID9.
  (* [comment removed for export] *)
  assert (HA9 : ASTA RT Σ3 PMc (ps_push_ret sp gp (Z_to_bv 64 0xba3ef0) nm f ps pn pq1 pq2 (Z_to_bv 64 1) m9) c9).
  { apply (ASTA_conseq RT Σ3 PMc _ _ c9 Hc9'). intros ms <-. unfold ps_push_ret. rewrite ERB. fold usp1 A. exact RS9. }
  assert (INC3 : forall e, In e (rt_live RT Σ2) -> In e (rt_live RT Σ3)) by (intros e He; rewrite LV3; right; exact He).
  apply (pstr_tail RT GOBJ AF AFP C_CM Σ PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo outer canary nm S str ps pk pl1 pl2 ni vi pq1 pq2 B items bks Σ3 m9 f pn 1
           (rt_live RT Σ) (PS_WH ps pk ++ [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (A, A + 56)]) true
           FDO MST ART0 CALL ltac:(unfold PSTR_STK; exact HSTK) CTX UWC CGH Hcr NONUL NE LEN PSAL PKAL NI VI ITEMS HASHES INPS INPK INL (fun e He => He) ltac:(clear; lia) MID9
           ltac:(rewrite LV3, LV2; cbn [length]; clear - Hlen; lia) T c9 HA9).
  clear HA9 Hc9'. intros c14 (Σ5 & pnn & Hc14 & LV5 & FRS5 & SP5 & CR5 & NOK & CG5).
  apply Hk. exists Σ5, pn, D, pnn.
  split; [| split; [rewrite LV5, LV3, LV2; reflexivity| split; [exact FRS5| split; [exact SP5| split; [exact CR5| split; [exact QOK| split; [exact (conj D0 (conj D16 DU))| split; [exact NOK| exact CG5]]]]]]]].
  apply (ASTA_conseq RT Σ5 PMc _ _ c14 Hc14). intros ms (m14 & RS & (ART14 & MI14 & ST14) & WM14 & PRES14 & PM14 & A914).
  pose proof (rw_cells_blur m9 D [C8 (Z_to_bv 64 (pn + 12)); CB 24 (zeros 24)] [] ltac:(rewrite app_nil_r; exact DC9)) as DB9. cbn [cells_size csize Nat.add app] in DB9.
  eexists m14, _.
  split; [exact RS|]. split; [exact (conj ART14 (conj MI14 (conj (WM14 eq_refl) ST14)))|].
  assert (COVER : forall x, outside (pstr_W (pstr_L nm ps pk pl1 pl2 pq1 pq2 B bks)) x ->
            outside ((PS_WH ps pk ++ [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (A, A + 56)]) ++ PS_WT nm pk pl1 pl2 B bks str) x).
  { intros x Ho. destruct (ps_W_cover nm ps pk pl1 pl2 pq1 pq2 B bks str [] x Ho) as (O1 & O2 & O3 & O4). fold A in O2.
    apply outside_app_intro; [| exact O4]. apply outside_app_intro; [exact O1|]. unfold PS_WH in O1. cbn [outside] in O1, O2 |- *. exact (conj (proj1 O1) (conj (proj1 O2) I)). }
  split. { apply (pres_fp_sub _ _ _ _ _ _ _ _ m m14 PRES14). intros x Hx Ho. exact (conj Hx (COVER _ Ho)). }
  split; [exact PM14|].
  assert (OUTT : forall p n, In (p, n) (rt_live RT Σ3) -> (n = 56 \/ n = 32 \/ n = 48) -> forall x, p <= x < p + n -> outside (PS_WT nm pk pl1 pl2 B bks str) x).
  { intros p n Hin Hn. exact (ps_out_WT RT GOBJ AF AFP Σ3 m9 nm pk pl1 pl2 B bks str p n ART9 (fun e He => INC3 _ (INL2 _ He)) (INC3 _ INPK2) Hin Hn). }
  split.
  - apply (rw_cells_agree_nw asegs m9 m14 _ _ HC9). intros x Hx. cbv beta in Hx. unfold sk_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply A914; [exact (acl_live _ _ _ A 56 (bv_unsigned x) (INC3 _ INA2) ltac:(clear - Hx; lia))|]. exact (OUTT A 56 (INC3 _ INA2) ltac:(left; reflexivity) (bv_unsigned x) ltac:(clear - Hx; lia)).
  - apply (rw_cells_agree_nw asegs m9 m14 _ _ DB9). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    assert (IND3 : In (D, 32) (rt_live RT Σ3)) by (rewrite LV3; left; reflexivity).
    apply A914; [exact (acl_live _ _ _ D 32 (bv_unsigned x) IND3 ltac:(clear - Hx; lia))|].
    exact (OUTT D 32 IND3 ltac:(right; left; reflexivity) (bv_unsigned x) ltac:(clear - Hx; lia)).
Qed.
End CPstrF.
