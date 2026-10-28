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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_mkit Fz_G_kit Th_mutex Fz_T_lock Fz_env Fz_M_malloc Fz_M_zalloc Fz_M_realloc Fz_M_realloc_array Fz_G_CRYPTO_calloc Fz_T_sk Fz_I1_insw Fz_I1_insx Fz_K_hash Fz_K_rep Fz_K_getrn Fz_K_retrieve Fz_K_insw Fz_K_insert Fz_K_skw Fz_K_sk Fz_I2_ppis Fz_K_pstw Fz_K_pstw2 Fz_K_pstrs Fz_W2_gets Fz_K_pstrh Fz_K_pstrt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation wz := (Z_to_bv 64) (only parsing).
Notation z64 := (Z_to_bv 64 0) (only parsing).

Lemma ps_outside_rngs : forall (L : list (Z * Z)) p n x, outside (rngs L) x -> In (p, n) L -> ~ (p <= x < p + n).
Proof. induction L as [|e0 L IH]; intros p n x H Hin; [destruct Hin|]. cbn in H. destruct H as [H1 H2]. destruct Hin as [-> | Hin]; [exact H1 | exact (IH _ _ _ H2 Hin)]. Qed.

(* [comment removed for export] *)
Lemma ps_W_cover : forall (nm : bool) (ps pk pl1 pl2 pq1 pq2 B : Z) (bks : list (list pnode)) (str : list byte) (Lx : list (Z * Z)) x,
  outside (pstr_W (Lx ++ pstr_L nm ps pk pl1 pl2 pq1 pq2 B bks)) x ->
  outside (PS_WH ps pk) x /\ outside [(q_of nm pq1 pq2, q_of nm pq1 pq2 + 56)] x /\ outside (rngs Lx) x /\ outside (PS_WT nm pk pl1 pl2 B bks str) x.
Proof.
  intros nm ps pk pl1 pl2 pq1 pq2 B bks str Lx x H. unfold pstr_W in H. cbn [outside] in H. destruct H as [OL H].
  unfold rngs in H. rewrite map_app in H. destruct (ps_outside_appD _ _ _ H) as [OX OP]. fold (rngs Lx) in OX. fold (rngs (pstr_L nm ps pk pl1 pl2 pq1 pq2 B bks)) in OP.
  assert (IN : forall p n, In (p, n) (pstr_L nm ps pk pl1 pl2 pq1 pq2 B bks) -> ~ (p <= x < p + n)) by (intros p n Hin; exact (ps_outside_rngs _ p n x OP Hin)).
  pose proof (IN ps 48 ltac:(left; reflexivity)) as N1. pose proof (IN pk 40 ltac:(right; left; reflexivity)) as N2.
  pose proof (IN (q_of nm pq1 pq2) 56 ltac:(right; right; left; reflexivity)) as N3.
  pose proof (IN (t_of nm pl1 pl2) 104 ltac:(do 3 right; left; reflexivity)) as N4. pose proof (IN B 128 ltac:(do 4 right; left; reflexivity)) as N5.
  split; [unfold PS_WH; cbn [outside]; clear - OL N1 N2; lia|]. split; [cbn [outside]; clear - N3; lia|]. split; [exact OX|].
  unfold PS_WT. cbn [outside]. split; [exact OL|]. split; [clear - N4; lia|]. split; [| clear - N2; lia].
  set (bi := lh_strhash str mod 8). assert (BIR : 0 <= bi < 8) by (subst bi; apply Z.mod_pos_bound; lia).
  destruct (pend_where (nth (Z.to_nat bi) bks []) (B + 8 * bi)) as [[E1 E2]|(pre & Ar & hr & E1 & E2)]; rewrite E2.
  - clear - N5 BIR. lia.
  - pose proof (IN Ar 24 ltac:(do 5 right; apply in_map_iff; exists (Ar, hr); split; [reflexivity|]; eapply in_concat_nthZ; rewrite E1; apply in_or_app; right; left; reflexivity)) as N6.
    clear - N6. lia.
Qed.
Section CPstr.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.

(* [comment removed for export] *)
Definition ps_kept (sp : word) (nm : bool) (str : list byte) (ps pk pl1 pl2 B : Z) (bks : list (list pnode)) (f pn : Z) (x : Z) : Prop :=
  (ps_RB sp <= x < USTACK_TOP) \/ (CTX_PSD <= x < CTX_PSD + 8) \/ (f <= x < f + 56) \/ (f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 8)
  \/ (ps <= x < ps + 48) \/ (pk <= x < pk + 40) \/ plh_fp (t_of nm pl1 pl2) B bks x \/ (pn <= x < pn + (Z.of_nat (length str) + 16)).

(* [comment removed for export] *)
Lemma ps_mid_step : forall (Σ : rts RT) (m : mem) (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (lo : Z) (canary : word)
    (nm : bool) (S : Z) (str : list byte) (ps pk pl1 pl2 ni vi pq1 pq2 B items : Z) (bks : list (list pnode)) (f pn : Z)
    (Σ2 Σ3 : rts RT) (m8 m9 : mem) (LIVE0 LIVE0' Wk FP KL : list (Z * Z)) (WMF WMF' : bool),
  ps_mid RT Σ m ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo canary nm S str ps pk pl1 pl2 ni vi pq1 pq2 B items bks f pn Σ2 m8 LIVE0 Wk WMF ->
  ART RT Σ3 m9 -> mem_inv asegs m9 -> stk asegs m9 lo (ps_RB sp) -> cl_env m9 (Z_to_bv 8 1) canary ->
  rt_frames RT Σ3 = rt_frames RT Σ2 -> rt_sp0 RT Σ3 = rt_sp0 RT Σ2 -> rt_cg RT Σ3 = rt_cg RT Σ2 -> rt_credit RT Σ3 = rt_credit RT Σ2 ->
  (WMF' = true -> WMF = true /\ wmono asegs m8 m9) ->
  (forall x : word, aclient KL (rt_frames RT Σ2) (ps_RB sp) (bv_unsigned x) -> outside FP (bv_unsigned x) -> m9 x = m8 x) ->
  incl KL (rt_live RT Σ3) -> incl LIVE0' LIVE0 -> incl LIVE0' KL ->
  In (ps, 48) KL -> In (pk, 40) KL -> incl (plh_L (t_of nm pl1 pl2) B bks) KL -> In (pn, Z.of_nat (length str) + 16) KL ->
  bv_unsigned sp <= USTACK_TOP ->
  (forall x, ps_kept sp nm str ps pk pl1 pl2 B bks f pn x -> outside FP x) ->
  ps_mid RT Σ m ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo canary nm S str ps pk pl1 pl2 ni vi pq1 pq2 B items bks f pn Σ3 m9 LIVE0' (Wk ++ FP) WMF'.
Proof.
  intros Σ m ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo canary nm S str ps pk pl1 pl2 ni vi pq1 pq2 B items bks f pn Σ2 Σ3 m8 m9 LIVE0 LIVE0' Wk FP KL WMF WMF'
    MID ART9 MI9 ST9 ENV9 FRS SP0 CG CR WMX PRESK INCK3 INC00 INC0K INPSK INPKK INLK INQK SPTOP FPOK.
  assert (RBLE : ps_RB sp <= bv_unsigned sp - 160) by (unfold ps_RB; pose proof (Z.mod_pos_bound (bv_unsigned sp) 32 ltac:(lia)); lia).
  unfold ps_mid in *. set (usp := bv_unsigned sp) in *. set (RB := ps_RB sp) in *. set (t := t_of nm pl1 pl2) in *. set (len := Z.of_nat (length str)) in *.
  destruct MID as ((ART8 & MI8 & ST8) & (FRS2 & SP2 & CG2 & CR2) & ENV8 & WMH & A08 & AGS08 & (INC2 & INPS2 & INPK2 & INL2 & INQ2)
                   & ((j8 & FR8) & GAP8 & NMC8 & TC8) & ((hj1 & hj2 & FFC8) & FFS8) & (CELL8 & PSC8 & LKC8 & REP8 & QC8 & STR8) & QFRESH & QOK).
  assert (INF2 : In (f, 0%nat) (rt_frames RT Σ2)) by (rewrite FRS2; left; reflexivity).
  assert (SHF : shad (f + 64) = shad f + 8).
  { pose proof (af_frames_align RT AF Σ2 m8 f 0%nat ART8 INF2) as (F64 & _). replace (f + 64) with (f + 64 * 1) by lia. rewrite (shad_add64 f 1 F64). lia. }
  (* [comment removed for export] *)
  assert (AGK : forall x : word, ps_kept sp nm str ps pk pl1 pl2 B bks f pn (bv_unsigned x) -> m9 x = m8 x).
  { intros x Hx. apply PRESK; [| exact (FPOK _ Hx)]. unfold ps_kept in Hx. fold RB t len in Hx.
    destruct Hx as [H|[H|[H|[H|[H|[H|[H|H]]]]]]].
    - left. exact H.
    - apply acl_static. unfold CTX_PSD in H. apply client_static_intro. lia.
    - apply (acl_frame _ _ _ f 0%nat); [exact INF2| change (fs_size 0) with 64; lia].
    - apply (acl_fshadow _ _ _ f 0%nat); [exact INF2| change (fs_size 0) with 64; rewrite SHF; unfold shad, SHB; lia].
    - exact (acl_live _ _ _ ps 48 _ INPSK H).
    - exact (acl_live _ _ _ pk 40 _ INPKK H).
    - destruct H as [H|[H|(n & Hn & H)]].
      + exact (acl_live _ _ _ t 104 _ (INLK _ ltac:(left; reflexivity)) H).
      + exact (acl_live _ _ _ B 128 _ (INLK _ ltac:(right; left; reflexivity)) H).
      + exact (acl_live _ _ _ (fst n) 24 _ (INLK _ (plh_L_node t B bks n Hn)) H).
    - exact (acl_live _ _ _ pn (len + 16) _ INQK H). }
  assert (KC : forall a cs, rw_cells asegs m8 a cs -> (forall x, a <= x < a + Z.of_nat (cells_size cs) -> ps_kept sp nm str ps pk pl1 pl2 B bks f pn x) -> rw_cells asegs m9 a cs).
  { intros a cs H HK. apply (rw_cells_agree_nw asegs m8 m9 _ _ H). intros x Hx. exact (AGK x (HK _ Hx)). }
  split; [exact (conj ART9 (conj MI9 ST9))|].
  split; [split; [rewrite FRS; exact FRS2| split; [rewrite SP0; exact SP2| split; [rewrite CG; exact CG2| rewrite CR; exact CR2]]]|].
  split; [exact ENV9|].
  split. { intros E. destruct (WMX E) as [E1 W89]. exact (wmono_trans asegs _ _ _ (WMH E1) W89). }
  split. { intros x Hx Ho. destruct (ps_outside_appD _ _ _ Ho) as [O1 O2].
           rewrite (PRESK x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [exact INC0K| rewrite FRS2; intros e' He'; right; exact He'| fold RB usp in RBLE; lia]) O2).
           apply A08; [| exact O1]. apply (aclient_mono _ _ _ _ _ _ _ Hx); [exact INC00| auto| lia]. }
  split. { intros a Ha. cbv beta in Ha. rewrite (AGK a ltac:(left; fold RB usp; fold usp in Ha; lia)). exact (AGS08 a Ha). }
  split. { split; [intros e He; exact (INCK3 _ (INC0K _ He))|]. split; [exact (INCK3 _ INPSK)|]. split; [exact (INCK3 _ INPKK)|]. split; [intros e He; exact (INCK3 _ (INLK _ He))| exact (INCK3 _ INQK)]. }
  split. { split; [exists j8; apply (KC _ _ FR8); unfold ps_ftail; cbn [cells_size csize Nat.add]; intros x Hx; left; fold RB usp in RBLE |- *; unfold USTACK_TOP in *; lia|].
           split; [apply (stk_agree_nw asegs m8 m9 _ _ GAP8); intros x Hx; cbv beta in Hx; apply AGK; left; fold RB usp in RBLE |- *; unfold USTACK_TOP in *; lia|].
           split; [apply (KC _ _ NMC8)| apply (KC _ _ TC8)]; cbn [cells_size csize Nat.add]; intros x Hx; left; fold RB usp in RBLE |- *; unfold USTACK_TOP in *; lia. }
  split. { split; [exists hj1, hj2; apply (KC _ _ FFC8); cbn [cells_size csize Nat.add]; intros x Hx; right; right; left; lia|].
           apply (KC _ _ FFS8). unfold ps_shadow. cbn [cells_size csize Nat.add]. intros x Hx. right; right; right; left. lia. }
  split; [| exact (conj QFRESH QOK)].
  split; [apply (KC _ _ CELL8); cbn [cells_size csize Nat.add]; intros x Hx; right; left; lia|].
  split; [apply (KC _ _ PSC8); destruct nm; unfold psd_bump, psd_cells; cbn [cells_size csize Nat.add]; intros x Hx; do 4 right; left; lia|].
  split; [apply (KC _ _ LKC8); unfold mutex_cells; cbn [cells_size csize Nat.add]; intros x Hx; do 5 right; left; lia|].
  split; [apply (plh_rep_agree m8 m9 t B items bks REP8); intros x Hx; apply AGK; do 6 right; left; exact Hx|].
  split; [apply (KC _ _ QC8); cbn [cells_size csize Nat.add]; intros x Hx; do 7 right; fold len; pose proof (Zle_0_nat (length str)); fold len in H; lia|].
  apply (bytes_at_agree asegs m8 m9 _ _ STR8). intros x Hx. cbv beta in Hx. rewrite length_app in Hx. cbn [length] in Hx. apply AGK. do 7 right. fold len. unfold len. lia.
Qed.
(* [comment removed for export] *)
Lemma ps_out_WT : forall (Σ3 : rts RT) (m9 : mem) (nm : bool) (pk pl1 pl2 B : Z) (bks : list (list pnode)) (str : list byte) p n,
  ART RT Σ3 m9 -> incl (plh_L (t_of nm pl1 pl2) B bks) (rt_live RT Σ3) -> In (pk, 40) (rt_live RT Σ3) -> In (p, n) (rt_live RT Σ3) ->
  (n = 56 \/ n = 32 \/ n = 48) -> forall x, p <= x < p + n -> outside (PS_WT nm pk pl1 pl2 B bks str) x.
Proof using AF AFP.
  intros Σ3 m9 nm pk pl1 pl2 B bks str p n ART9 INL INPK Hin Hn x Hx. unfold PS_WT. set (t := t_of nm pl1 pl2) in *. cbn [outside]. unfold G_ALLOW_CUST.
  assert (AP : forall y, In y (rt_live RT Σ3) -> (p, n) <> y -> p + n <= fst y \/ fst y + snd y <= p).
  { intros y Hy NE'. pose proof (live_ne_apart2 RT AF Σ3 m9 (p, n) y ART9 Hin Hy NE') as X. cbn [fst snd] in X. exact X. }
  pose proof (afp_live_hi RT GOBJ AFP Σ3 m9 p n ART9 Hin ltac:(clear - Hn; lia)) as PH.
  pose proof (AP (t, 104) (INL _ ltac:(left; reflexivity)) ltac:(intros E; injection E; clear - Hn; lia)) as Y1. cbn [fst snd] in Y1.
  pose proof (AP (pk, 40) INPK ltac:(intros E; injection E; clear - Hn; lia)) as Y3. cbn [fst snd] in Y3.
  set (bi := lh_strhash str mod 8). assert (BIR : 0 <= bi < 8) by (subst bi; apply Z.mod_pos_bound; clear; lia).
  split; [clear - Hx PH; lia|]. split; [clear - Hx Y1; lia|]. split; [| split; [clear - Hx Y3; lia| exact I]].
  destruct (pend_where (nth (Z.to_nat bi) bks []) (B + 8 * bi)) as [[E1 E2]|(pre & Ar & hr & E1 & E2)]; rewrite E2.
  - pose proof (AP (B, 128) (INL _ ltac:(right; left; reflexivity)) ltac:(intros E; injection E; clear - Hn; lia)) as Y2. cbn [fst snd] in Y2. clear - Hx Y2 BIR. lia.
  - assert (INN : In (Ar, 24) (plh_L t B bks)) by (apply (plh_L_node t B bks (Ar, hr)); eapply in_concat_nthZ; rewrite E1; apply in_or_app; right; left; reflexivity).
    pose proof (AP (Ar, 24) (INL _ INN) ltac:(intros E; injection E; clear - Hn; lia)) as Y2. cbn [fst snd] in Y2. clear - Hx Y2. lia.
Qed.

Hypothesis SM0 : stack_malloc_contract RT 0.
Hypothesis SLC : strlen_icontract RT.
Hypothesis MCP : memcpy_icontract RT e_asan_memcpy.
Hypothesis C_CM : crypto_malloc_env_stmt RT.
Hypothesis GO_ctx : GOBJ PPI_CTX 328.

Theorem pstr_room_cps : pstr_room_stmt RT GOBJ.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary
    nm S b sz str slack ps pk pl1 pl2 ni vi pq1 pq2 B items bks D num nalloc s01 pad cmpt freet copyt junk PRE HC S01 NUM1 NUM2 NAL IND DAL DNE DC.
  pose proof PRE as (FDO & MST & _ & _ & _ & _ & Etp & ART0 & MI0 & CALL & HSTK & CTX & UWC & CGH & Hfr & Hlen & Hcr & ENV
     & ROB & NONUL & NE & LEN & SLK & HG & Hbs & Hse & HS0 & HSE
     & CELL & INPS & PSAL & PSC & NI & VI & INPK & PKAL & LKC & REP & INL & ITEMS & HASHES & INA & AAL).
  subst tp. intros T c HA Hk.
  apply (pstr_head RT GOBJ AF AFP SM0 SLC MCP C_CM GO_ctx Σ PMc ra sp gp _ t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary
           nm S b sz str slack ps pk pl1 pl2 ni vi pq1 pq2 B items bks PRE T c HA).
  clear HA PRE. intros c8 (Σ2 & f & pn & m8 & u0 & u1 & u2 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F8 & fc8 & HA8 & LV2 & MID8).
  pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof MID8 as ((ART8 & MI8 & ST8) & (FRS2 & SP2 & CG2 & CR2) & ENV8 & WMH & A08 & AGS08 & (INC2 & INPS2 & INPK2 & INL2 & INQ2) & _ & _ & _ & QFRESH & QOK).
  set (usp := bv_unsigned sp) in *. unfold PSTR_STK in HSTK.
  set (pd := usp mod 32) in *.
  assert (HP : pd = 0 \/ pd = 16) by (unfold pd; clear - SPA; Z.div_mod_to_equations; lia).
  assert (ERB : ps_RB sp = usp + -160 - pd) by reflexivity. clearbody pd.
  set (len := Z.of_nat (length str)) in *. assert (Hl0 : 1 <= len) by (unfold len; clear - NE; destruct str; [congruence| cbn [length]; lia]).
  set (t := t_of nm pl1 pl2) in *. set (A := q_of nm pq1 pq2) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 704 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (clear - HSTK LOW SP0R SP0W SPT; unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -160 - pd) in *.
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; clear - NUM HSTK HP SP0R; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (N8 : 1 <= 8 * nalloc <= 64512) by (clear - NAL; lia).
  (* [comment removed for export] *)
  assert (BLK : forall p n, In (p, n) (rt_live RT Σ) -> 1 <= n <= 64512 -> 0 < p /\ p + n <= lo /\ 0x10007fff8000 <= p /\ p + n <= 2 ^ 47).
  { intros p n Hin Hn. pose proof (af_live_range RT AF Σ m p n ART0 Hin) as (P0 & P1 & _).
    pose proof (afp_live_hi RT GOBJ AFP Σ m p n ART0 Hin ltac:(clear - Hn; lia)) as PH. pose proof (afp_live_mem RT GOBJ AFP Σ m p n ART0 Hin ltac:(clear - Hn; lia)) as [_ PM]. clear - P0 P1 PH PM LOW. lia. }
  destruct (BLK A 56 INA ltac:(clear; lia)) as (A0 & ALO & AHI & ATOP). destruct (BLK D (8 * nalloc) IND N8) as (D0 & DLO & DHI & DTOP).
  destruct (BLK ps 48 INPS ltac:(clear; lia)) as (PS0 & PSLO & PSHI & PSTOP). destruct (BLK pk 40 INPK ltac:(clear; lia)) as (PK0 & PKLO & PKHI & PKTOP).
  assert (AP : forall x y, In x (rt_live RT Σ) -> In y (rt_live RT Σ) -> x <> y -> fst x + snd x <= fst y \/ fst y + snd y <= fst x) by (intros x y; exact (live_ne_apart2 RT AF Σ m x y ART0)).
  pose proof (AP (A, 56) (ps, 48) INA INPS ltac:(clear; intros E; injection E; lia)) as APS. pose proof (AP (A, 56) (pk, 40) INA INPK ltac:(clear; intros E; injection E; lia)) as APK.
  pose proof (AP (D, 8 * nalloc) (ps, 48) IND INPS ltac:(intros E; injection E; intros; apply DNE; assumption)) as DPS.
  pose proof (AP (D, 8 * nalloc) (pk, 40) IND INPK ltac:(intros E; injection E; clear - NAL; lia)) as DPK.
  pose proof (AP (A, 56) (D, 8 * nalloc) INA IND ltac:(intros E; injection E; clear - NAL; lia)) as AD.
  cbn [fst snd] in APS, APK, DPS, DPK, AD.
  assert (WM08 : wmono asegs m m8) by exact (WMH eq_refl).
  assert (HC8 : rw_cells asegs m8 A (sk_cells (Z_to_bv 64 num) pad (Z_to_bv 64 D) (Z_to_bv 64 s01) (Z_to_bv 64 nalloc) z64 cmpt freet copyt)).
  { apply (rw_cells_agree asegs m m8 _ _ HC); [| exact WM08]. intros x Hx. cbv beta in Hx. unfold sk_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply A08; [exact (acl_live _ _ _ A 56 (bv_unsigned x) INA ltac:(clear - Hx; lia))|]. unfold PS_WH, G_ALLOW_CUST. cbn [outside]. clear - Hx AHI APS APK. lia. }
  assert (DC8 : rw_cells asegs m8 D [CB (Z.to_nat (8 * nalloc)) junk]).
  { apply (rw_cells_agree asegs m m8 _ _ DC); [| exact WM08]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply A08; [exact (acl_live _ _ _ D (8 * nalloc) (bv_unsigned x) IND ltac:(clear - Hx N8; lia))|]. unfold PS_WH, G_ALLOW_CUST. cbn [outside]. clear - Hx N8 DHI DPS DPK. lia. }
  assert (INA2 : In (A, 56) (rt_live RT Σ2)) by (apply INC2; exact INA). assert (IND2 : In (D, 8 * nalloc) (rt_live RT Σ2)) by (apply INC2; exact IND).
  destruct (af_client_consts RT AF Σ2 m8 ART8) as (_ & SHC8 & _ & _ & UT8).
  rewrite ERB in ST8. fold usp1 in ST8.
  (* [comment removed for export] *)
  unfold ps_push_entry, entry_st in HA8. rewrite ERB in HA8. fold usp1 A in HA8.
  pose proof (T_sk_push_room_proof (Z_to_bv 64 SITE_ps_push) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 A) (Z_to_bv 64 (pn + 12)) (Z_to_bv 64 0) (Z_to_bv 64 0) b4 b5 b6 b7
                (Z_to_bv 64 f) (Z_to_bv 64 ps) (Z_to_bv 64 (Z.shiftr ps 3 + 2147450880)) (Z_to_bv 64 (ps + off_idx nm)) (Z_to_bv 64 2147450880) (Z_to_bv 64 pn)
                (Z_to_bv 64 A) (Z_to_bv 64 (Z.shiftr (ps + off_idx nm) 3 + 2147450880)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) u3 u4 u5 u6 F8 fc8 m8 lo A D num nalloc s01 pad cmpt freet copyt junk
                eq_refl AHI AAL ALO HC8 (proj2 (af_acc_live RT AF Σ2 m8 A 56 ART8 INA2)) S01 NUM1 NUM2 ltac:(clear - NAL; lia) DHI DAL DLO DC8
                (proj2 (af_acc_live RT AF Σ2 m8 D (8 * nalloc) ART8 IND2)) AD UT8 SHC8 ltac:(rewrite EU1; exact ST8) ltac:(clear - NUM; lia)
                ltac:(rewrite EU1; unfold SK_PUSH_ROOM_STACK, usp1, RT_STACK in *; clear - HSTK HP; lia) ltac:(rewrite EU1; unfold usp1, USTACK_TOP in *; clear - NUM HP; lia) MI8) as WP.
  rewrite EU1 in WP. unfold SK_PUSH_ROOM_STACK in WP.
  cl_lift WP HA8 c9 Hc9.
  destruct (ASTA_unpack RT Σ2 _ _ c9 Hc9) as (ms9 & (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & junk9 & m9 & -> & MU9 & WM9 & MI9 & ST9 & HC9 & DC9) & Hc9'). clear Hc9.
  (* [comment removed for export] *)
  pose proof (af_frames_range RT AF Σ2 m8 f 0%nat ART8 ltac:(rewrite FRS2; left; reflexivity)) as (F0 & FLO & _ & PF).
  pose proof (af_frames_align RT AF Σ2 m8 f 0%nat ART8 ltac:(rewrite FRS2; left; reflexivity)) as (F64 & FIMG).
  pose proof (proj1 (af_fshadow_apart RT AF Σ2 m8 f 0%nat ART8 ltac:(rewrite FRS2; left; reflexivity))) as SLF.
  change (fs_size 0) with 64 in FLO, PF, SLF. unfold SEGTOP_A in FIMG.
  assert (SHF : shad (f + 64) = shad f + 8) by (replace (f + 64) with (f + 64 * 1) by (clear; lia); rewrite (shad_add64 f 1 F64); clear; lia).
  rewrite SHF in SLF. unfold shad, SHB in SLF.
  assert (ART9 : ART RT Σ2 m9).
  { apply (af_frame RT AF Σ2 m8 m9 (usp1 - 208) ART8 ltac:(rewrite SP2; unfold usp1; clear - NUM HP; lia)); [| exact WM9].
    intros a Ha. apply MU9. cbn [outside]. split; [| split; [| split; [| exact I]]]; intros Hin; apply Ha.
    - apply acl_stack. unfold usp1, USTACK_TOP in *. clear - Hin HP NUM. lia.
    - exact (acl_live _ _ _ A 56 _ INA2 Hin).
    - exact (acl_live _ _ _ D (8 * nalloc) _ IND2 Hin). }
  assert (ENV9 : cl_env m9 (Z_to_bv 8 1) canary).
  { apply (cl_env_seg _ m8 m9 _ canary ENV8 MU9). intros x Hx. pose proof (client_static_range x (cl_cell_static x Hx)) as CR. unfold SEGTOP_A in CR. cbn [outside]. unfold usp1. clear - CR AHI DHI HSTK NUM HP. unfold RT_STACK in *. lia. }
  assert (PRESK : forall x : word, aclient (rt_live RT Σ2) (rt_frames RT Σ2) (ps_RB sp) (bv_unsigned x) -> outside [(A, A + 56); (D, D + 8 * nalloc)] (bv_unsigned x) -> m9 x = m8 x).
  { intros x Hx Ho. rewrite ERB in Hx. fold usp1 in Hx. cbn [outside] in Ho.
    pose proof (cl_split RT AF Σ2 m8 usp1 208 _ ART8 ltac:(rewrite SP2; unfold usp1; clear - NUM HP; lia) ltac:(clear; lia) Hx) as N3.
    apply MU9. cbn [outside]. clear - N3 Ho. lia. }
  assert (FPOK : forall x, ps_kept sp nm str ps pk pl1 pl2 B bks f pn x -> outside [(A, A + 56); (D, D + 8 * nalloc)] x).
  { intros x Hx. unfold ps_kept in Hx. rewrite ERB in Hx. fold usp1 t len in Hx. cbn [outside].
    pose proof (PF A 56 INA2) as X1. pose proof (PF D (8 * nalloc) IND2) as X2. pose proof (SLF A 56 INA2) as X3. pose proof (SLF D (8 * nalloc) IND2) as X4.
    pose proof (QFRESH A 56 INA) as X5. pose proof (QFRESH D (8 * nalloc) IND) as X6.
    destruct Hx as [H|[H|[H|[H|[H|[H|[H|H]]]]]]].
    - unfold usp1 in H. clear - H ALO DLO HSTK HP. unfold RT_STACK in *. lia.
    - unfold CTX_PSD in H. clear - H AHI DHI. lia.
    - clear - H X1 X2. lia.
    - clear - H X3 X4. lia.
    - clear - H APS DPS. lia.
    - clear - H APK DPK. lia.
    - assert (X : exists p n, In (p, n) (plh_L t B bks) /\ p <= x < p + n /\ (n = 104 \/ n = 128 \/ n = 24)).
      { destruct H as [H|[H|(n & Hn & H)]]; [exists t, 104; split; [left; reflexivity| clear - H; lia]| exists B, 128; split; [right; left; reflexivity| clear - H; lia]|
          exists (fst n), 24; split; [exact (plh_L_node t B bks n Hn)| clear - H; lia]]. }
      destruct X as (p & n & Hin & Hpx & Hn).
      pose proof (AP (A, 56) (p, n) INA (INL _ Hin) ltac:(intros E; injection E; clear - Hn; lia)) as Y1.
      pose proof (AP (D, 8 * nalloc) (p, n) IND (INL _ Hin) ltac:(intros E; injection E; clear - Hn NAL; lia)) as Y2. cbn [fst snd] in Y1, Y2. clear - Hpx Y1 Y2. lia.
    - clear - H X5 X6. lia. }
  pose proof (ps_mid_step Σ m ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo canary nm S str ps pk pl1 pl2 ni vi pq1 pq2 B items bks f pn Σ2 Σ2 m8 m9
                (rt_live RT Σ) (rt_live RT Σ) (PS_WH ps pk) [(A, A + 56); (D, D + 8 * nalloc)] (rt_live RT Σ2) true true
                MID8 ART9 MI9 ltac:(rewrite ERB; exact ST9) ENV9 eq_refl eq_refl eq_refl eq_refl (fun _ => conj eq_refl WM9) PRESK
                (fun e He => He) (fun e He => He) INC2 INPS2 INPK2 INL2 INQ2 ltac:(clear - NUM; lia) FPOK) as MID9.
  (* [comment removed for export] *)
  assert (HA9 : ASTA RT Σ2 PMc (ps_push_ret sp gp (Z_to_bv 64 0xba3ef0) nm f ps pn pq1 pq2 (Z_to_bv 64 (num + 1)) m9) c9).
  { apply (ASTA_conseq RT Σ2 PMc _ _ c9 Hc9'). intros ms <-. unfold ps_push_ret, ret_st. rewrite ERB. fold usp1 A.
    exists w0, w1, w2, e1, e2, e3, e4, e5, e6, e7, w3, w4, w5, w6, F8, fc8. reflexivity. }
  apply (pstr_tail RT GOBJ AF AFP C_CM Σ PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo outer canary nm S str ps pk pl1 pl2 ni vi pq1 pq2 B items bks Σ2 m9 f pn (num + 1)
           (rt_live RT Σ) (PS_WH ps pk ++ [(A, A + 56); (D, D + 8 * nalloc)]) true
           FDO MST ART0 CALL ltac:(unfold PSTR_STK; exact HSTK) CTX UWC CGH Hcr NONUL NE LEN PSAL PKAL NI VI ITEMS HASHES INPS INPK INL (fun e He => He) ltac:(clear - NUM1 NUM2 NAL; lia) MID9
           ltac:(rewrite LV2; cbn [length]; clear - Hlen; lia) T c9 HA9).
  clear HA9 Hc9'. intros c14 (Σ5 & pnn & Hc14 & LV5 & FRS5 & SP5 & CR5 & NOK & CG5).
  apply Hk. exists Σ5, pn, pnn.
  split; [| split; [rewrite LV5, LV2; reflexivity| split; [exact FRS5| split; [exact SP5| split; [exact CR5| split; [exact QOK| split; [exact NOK| exact CG5]]]]]]].
  apply (ASTA_conseq RT Σ5 PMc _ _ c14 Hc14). intros ms (m14 & RS & (ART14 & MI14 & ST14) & WM14 & PRES14 & PM14 & A914). exists m14, junk9.
  split; [exact RS|]. split; [exact (conj ART14 (conj MI14 (conj (WM14 eq_refl) ST14)))|].
  assert (COVER : forall x, outside (pstr_W ((D, 8 * nalloc) :: pstr_L nm ps pk pl1 pl2 pq1 pq2 B bks)) x ->
            outside ((PS_WH ps pk ++ [(A, A + 56); (D, D + 8 * nalloc)]) ++ PS_WT nm pk pl1 pl2 B bks str) x).
  { intros x Ho. destruct (ps_W_cover nm ps pk pl1 pl2 pq1 pq2 B bks str [(D, 8 * nalloc)] x Ho) as (O1 & O2 & O3 & O4). fold A in O2.
    apply outside_app_intro; [| exact O4]. apply outside_app_intro; [exact O1|]. cbn [outside rngs map fst snd] in O2, O3 |- *. exact (conj (proj1 O2) (conj (proj1 O3) I)). }
  split. { apply (pres_fp_sub _ _ _ _ _ _ _ _ m m14 PRES14). intros x Hx Ho. exact (conj Hx (COVER _ Ho)). }
  split; [exact PM14|].
  (* [comment removed for export] *)
  assert (OUTT : forall p n, In (p, n) (rt_live RT Σ2) -> (n = 56 \/ n = 32 \/ n = 48) -> forall x, p <= x < p + n -> outside (PS_WT nm pk pl1 pl2 B bks str) x).
  { intros p n Hin Hn. exact (ps_out_WT Σ2 m9 nm pk pl1 pl2 B bks str p n ART9 INL2 INPK2 Hin Hn). }
  split.
  - apply (rw_cells_agree_nw asegs m9 m14 _ _ HC9). intros x Hx. cbv beta in Hx. unfold sk_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply A914; [exact (acl_live _ _ _ A 56 (bv_unsigned x) INA2 ltac:(clear - Hx; lia))|]. exact (OUTT A 56 INA2 ltac:(left; reflexivity) (bv_unsigned x) ltac:(clear - Hx; lia)).
  - apply (rw_cells_agree_nw asegs m9 m14 _ _ DC9). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply A914; [exact (acl_live _ _ _ D (8 * nalloc) (bv_unsigned x) IND2 ltac:(clear - Hx N8; lia))|].
    exact (OUTT D (8 * nalloc) IND2 ltac:(clear - NAL; lia) (bv_unsigned x) ltac:(clear - Hx N8; lia)).
Qed.

End CPstr.
