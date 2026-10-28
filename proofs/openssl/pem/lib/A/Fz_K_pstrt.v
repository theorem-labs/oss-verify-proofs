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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_mkit Fz_G_kit Th_mutex Fz_T_lock Fz_env Fz_M_malloc Fz_M_zalloc Fz_M_realloc Fz_M_realloc_array Fz_G_CRYPTO_calloc Fz_T_sk Fz_I1_insw Fz_I1_insx Fz_K_hash Fz_K_rep Fz_K_getrn Fz_K_retrieve Fz_K_insw Fz_K_insert Fz_K_skw Fz_K_sk Fz_I2_ppis Fz_K_pstw Fz_K_pstw2 Fz_K_pstrs Fz_W2_gets Fz_K_pstrh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation wz := (Z_to_bv 64) (only parsing).
Notation z64 := (Z_to_bv 64 0) (only parsing).

Lemma ps_outside_appD : forall (W1 W2 : list (Z * Z)) x, outside (W1 ++ W2) x -> outside W1 x /\ outside W2 x.
Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 x H; cbn in *; [split; [exact I | exact H]|]. destruct H as [H1 H2]. destruct (IH _ _ H2) as [A B]. repeat split; assumption. Qed.

(* [comment removed for export] *)
Lemma ps_blob_munch : forall W (m m' : mem) A (n : nat) j tl, rw_cells asegs m A (CB n j :: tl) -> munch W m m' -> wmono asegs m m' ->
  (forall x, A + Z.of_nat n <= x < A + Z.of_nat n + Z.of_nat (cells_size tl) -> outside W x) ->
  exists j', rw_cells asegs m' A (CB n j' :: tl).
Proof.
  intros W m m' A n j tl H MU WM HO. change (CB n j :: tl) with ([CB n j] ++ tl) in H. apply (proj1 (rw_cells_app m _ _ _)) in H. destruct H as [H1 H2].
  cbn [cells_size csize Nat.add] in H2. rewrite Nat.add_0_r in H2.
  pose proof (rw_cells_wr_at asegs m A [CB n j] (Z.of_nat n) H1 ltac:(cbn [cells_size csize Nat.add]; lia)) as WR.
  destruct (wr_at_rw_CB m' A (Z.of_nat n) (wr_at_wm m m' A _ WR WM) ltac:(lia)) as (j' & H1'). rewrite Nat2Z.id in H1'.
  exists j'. change (CB n j' :: tl) with ([CB n j'] ++ tl). apply (proj2 (rw_cells_app m' _ _ _)). split; [exact H1'|].
  cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r.
  apply (rw_cells_agree asegs m m' _ _ H2); [| exact WM]. exact (agree_of_munch W m m' _ MU HO).
Qed.

(* [comment removed for export] *)
Lemma ps_bks_fp : forall lh B (bks : list (list pnode)) (str : list byte) pnn a, length bks = 16%nat ->
  plh_fp lh B (pstr_bks bks str pnn) a -> plh_fp lh B bks a \/ pnn <= a < pnn + 24.
Proof.
  intros lh B bks str pnn a LEN [H|[H|(n & Hn & H)]]; [left; left; exact H| left; right; left; exact H|]. unfold pstr_bks in Hn.
  assert (LI : (Z.to_nat (lh_strhash str mod 8) < length bks)%nat) by (rewrite LEN; pose proof (Z.mod_pos_bound (lh_strhash str) 8 ltac:(lia)); lia).
  pose proof (concat_lupd bks _ (nth (Z.to_nat (lh_strhash str mod 8)) bks [] ++ [(pnn, lh_strhash str)]) LI) as P1.
  pose proof (concat_split_perm bks _ LI) as P2.
  apply (Permutation_in _ P1) in Hn. rewrite <- app_assoc in Hn. apply in_app_or in Hn. destruct Hn as [Hn|Hn].
  - left. right; right. exists n. split; [| exact H]. apply (Permutation_in _ (Permutation_sym P2)). apply in_or_app. left. exact Hn.
  - cbn [app] in Hn. destruct Hn as [<-|Hn]; [right; exact H|]. left. right; right. exists n. split; [| exact H].
    apply (Permutation_in _ (Permutation_sym P2)). apply in_or_app. right. exact Hn.
Qed.

Definition PS_WT (nm : bool) (pk pl1 pl2 B : Z) (bks : list (list pnode)) (str : list byte) : list (Z * Z) :=
  [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (t_of nm pl1 pl2 + 88, t_of nm pl1 pl2 + 104);
   (pend (B + 8 * (lh_strhash str mod 8)) (nth (Z.to_nat (lh_strhash str mod 8)) bks []), pend (B + 8 * (lh_strhash str mod 8)) (nth (Z.to_nat (lh_strhash str mod 8)) bks []) + 8);
   (pk + 4, pk + 8)].

Section CPstrT.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_CM : crypto_malloc_env_stmt RT.

Definition pstr_tail_post (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (lo : Z) (m : mem) (canary : word)
    (nm : bool) (str : list byte) (ps pk pl1 pl2 ni vi pq1 pq2 B items : Z) (bks : list (list pnode))
    (Σ3 : rts RT) (m9 : mem) (LIVE0 Wk : list (Z * Z)) (WMF : bool) : config -> Prop :=
  fun c => exists (Σ5 : rts RT) (pnn : Z),
       ASTA RT Σ5 PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (cnt_of nm ni vi + 1)) m' ms
           /\ (ART RT Σ5 m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp))
           /\ (WMF = true -> wmono asegs m m')
           /\ rt_pres_fp LIVE0 (rt_frames RT Σ) (bv_unsigned sp) (Wk ++ PS_WT nm pk pl1 pl2 B bks str) m m'
           /\ pstr_post_mem m' canary nm str ps pk pl1 pl2 ni vi pq1 pq2 B items bks pnn
           /\ (forall x : word, aclient (rt_live RT Σ3) (rt_frames RT Σ) (bv_unsigned sp) (bv_unsigned x) -> outside (PS_WT nm pk pl1 pl2 B bks str) (bv_unsigned x) -> m' x = m9 x)) c
       /\ rt_live RT Σ5 = (pnn, 24) :: rt_live RT Σ3 /\ rt_frames RT Σ5 = rt_frames RT Σ /\ rt_sp0 RT Σ5 = rt_sp0 RT Σ
       /\ rt_credit RT Σ5 = rt_credit RT Σ - 1 /\ blk_ok pnn 24 /\ rt_cg RT Σ5 = rt_cg RT Σ.
Theorem pstr_tail : forall (Σ : rts RT) PMc (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) (lo : Z) (outer : list Z) (canary : word)
    (nm : bool) (S : Z) (str : list byte) (ps pk pl1 pl2 ni vi pq1 pq2 B items : Z) (bks : list (list pnode))
    (Σ3 : rts RT) (m9 : mem) (f pn r : Z) (LIVE0 Wk : list (Z * Z)) (WMF : bool),
  fdfs_only PMc -> mat_stable PMc -> ART RT Σ m -> call_ok RT Σ m sp lo -> lo + RT_STACK + PSTR_STK <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_property_string (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) PSTR_SITES PSTR_CALLS ->
  1 <= rt_credit RT Σ ->
  ~ In (Z_to_bv 8 0) str -> str <> [] -> Z.of_nat (length str) + 16 <= 64512 ->
  ps mod 16 = 0 -> pk mod 16 = 0 -> 0 <= ni < 2 ^ 20 -> 0 <= vi < 2 ^ 20 -> items < 15 ->
  Forall (fun n : pnode => snd n <> lh_strhash str) (nth (Z.to_nat (lh_strhash str mod 8)) bks []) ->
  In (ps, 48) (rt_live RT Σ) -> In (pk, 40) (rt_live RT Σ) -> incl (plh_L (t_of nm pl1 pl2) B bks) (rt_live RT Σ) ->
  incl LIVE0 (rt_live RT Σ) -> 1 <= r < 2 ^ 31 ->
  ps_mid RT Σ m ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo canary nm S str ps pk pl1 pl2 ni vi pq1 pq2 B items bks f pn Σ3 m9 LIVE0 Wk WMF ->
  Z.of_nat (length (rt_live RT Σ3)) < LIVE_MAX ->
  cps asegs (ASTA RT Σ3 PMc (ps_push_ret sp gp (Z_to_bv 64 0xba3ef0) nm f ps pn pq1 pq2 (Z_to_bv 64 r) m9))
    (pstr_tail_post Σ PMc ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m canary nm str ps pk pl1 pl2 ni vi pq1 pq2 B items bks Σ3 m9 LIVE0 Wk WMF).
Proof.
  intros Σ PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo outer canary nm S str ps pk pl1 pl2 ni vi pq1 pq2 B items bks Σ3 m9 f pn r LIVE0 Wk WMF
    FDO MST ART0 CALL HSTK CTX UWC CGH Hcr NONUL NE LEN PSAL PKAL NI VI ITEMS HASHES INPS INPK INL INC0 HR MID Hlen3.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  unfold ps_mid in MID. set (usp := bv_unsigned sp) in *. unfold PSTR_STK in HSTK.
  set (pd := usp mod 32) in *.
  assert (HP : pd = 0 \/ pd = 16) by (unfold pd; clear - SPA; Z.div_mod_to_equations; lia).
  assert (HPM : usp mod 32 = pd) by reflexivity.
  assert (ERB : ps_RB sp = usp + -160 - pd) by reflexivity. rewrite ERB in MID. unfold ps_push_ret in HA. rewrite ERB in HA. clearbody pd.
  set (len := Z.of_nat (length str)) in *. assert (Hl0 : 1 <= len) by (unfold len; destruct str; [congruence| cbn [length]; lia]).
  set (t := t_of nm pl1 pl2) in *. set (idx := cnt_of nm ni vi + 1) in *.
  assert (IDX : 0 <= idx < 2 ^ 31) by (unfold idx; destruct nm; cbn [cnt_of]; lia).
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 704 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLOI : SEGTOP_A <= lo) by (unfold SEGTOP_A, STACK_WIN in *; lia).
  set (usp1 := usp + -160 - pd) in *.
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  destruct MID as ((ART9 & MI9 & ST9) & (FRS3 & SP3 & CG3 & CR3) & ENV9 & WMH & A09 & AGS09 & (INC3 & INPS3 & INPK3 & INL3 & INQ3)
                   & ((j9 & FR9) & GAP9 & NMC9 & TC9) & ((hj1 & hj2 & FFC9) & FFS9) & (CELL9 & PSC9 & LKC9 & REP9 & QC9 & STR9) & QFRESH & (_ & Q16 & QU)).
  destruct (ASTA_unpack RT Σ3 _ _ c HA) as (ms9 & RS9 & Hc9). clear HA.
  destruct RS9 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F9 & fc9 & ->).
  rewrite (ret_pc_even SITE_ps_push) in Hc9 by (unfold SITE_ps_push; lia).
  (* [comment removed for export] *)
  assert (INF : In (f, 0%nat) (rt_frames RT Σ3)) by (rewrite FRS3; left; reflexivity).
  pose proof (af_frames_range RT AF Σ3 m9 f 0%nat ART9 INF) as (F0 & FLO & _ & PF).
  pose proof (af_frames_align RT AF Σ3 m9 f 0%nat ART9 INF) as (F64 & FIMG).
  pose proof (af_frames_hi RT AF Σ3 m9 f 0%nat ART9 INF) as FSH.
  pose proof (proj1 (af_fshadow_apart RT AF Σ3 m9 f 0%nat ART9 INF)) as SLF.
  rewrite SP3 in FLO. change (fs_size 0) with 64 in FLO, FSH, PF, SLF. unfold SEGTOP_A in FIMG.
  assert (SHF : shad (f + 64) = shad f + 8) by (replace (f + 64) with (f + 64 * 1) by lia; rewrite (shad_add64 f 1 F64); lia).
  rewrite SHF in SLF. unfold shad, SHB in SLF.
  pose proof (div8_facts f) as Q1.
  assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 8 <= 0x10007fff8000)
    by (pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)); assert (f / 8 + 8 <= 2^44) by (clear - FLO NUM SP0R; unfold USTACK_TOP, STACK_WIN in *; Z.div_mod_to_equations; lia); lia).
  assert (BLK : forall (Σx : rts RT) (mx : mem) p n, ART RT Σx mx -> rt_sp0 RT Σx = rt_sp0 RT Σ -> In (p, n) (rt_live RT Σx) -> 1 <= n <= 64512 ->
            acc asegs mx p n /\ 0 < p /\ p + n <= lo /\ 0x10007fff8000 <= p /\ p + n <= 2 ^ 47).
  { intros Σx mx p n ARTx SPx Hin Hn.
    pose proof (af_live_range RT AF Σx mx p n ARTx Hin) as (P0 & P1 & _). rewrite SPx in P1.
    pose proof (afp_live_hi RT GOBJ AFP Σx mx p n ARTx Hin ltac:(lia)) as PH. pose proof (afp_live_mem RT GOBJ AFP Σx mx p n ARTx Hin ltac:(lia)) as [_ PM].
    split; [exact (proj2 (af_acc_live RT AF Σx mx p n ARTx Hin))|]. lia. }
  destruct (BLK Σ3 m9 ps 48 ART9 SP3 INPS3 ltac:(lia)) as (_ & PS0 & PSLO & PSHI & PSTOP).
  destruct (BLK Σ3 m9 pk 40 ART9 SP3 INPK3 ltac:(lia)) as (_ & PK0 & PKLO & PKHI & PKTOP).
  destruct (BLK Σ3 m9 pn (len + 16) ART9 SP3 INQ3 ltac:(lia)) as (_ & Q0 & QLO & QHI & QTOP).
  assert (INT3 : In (t, 104) (rt_live RT Σ3)) by (apply INL3; left; reflexivity).
  assert (INB3 : In (B, 128) (rt_live RT Σ3)) by (apply INL3; right; left; reflexivity).
  destruct (BLK Σ3 m9 t 104 ART9 SP3 INT3 ltac:(lia)) as (_ & L0 & LLO & LHI & LTOP).
  destruct (BLK Σ3 m9 B 128 ART9 SP3 INB3 ltac:(lia)) as (_ & B0 & BLO & BHI & BTOP).
  pose proof (live_ne_apart2 RT AF Σ3 m9 (ps, 48) (pk, 40) ART9 INPS3 INPK3 ltac:(intros E; injection E; lia)) as PSPK. cbn [fst snd] in PSPK.
  pose proof (live_ne_apart2 RT AF Σ3 m9 (t, 104) (pk, 40) ART9 INT3 INPK3 ltac:(intros E; injection E; lia)) as LPK. cbn [fst snd] in LPK.
  pose proof (live_ne_apart2 RT AF Σ3 m9 (ps, 48) (t, 104) ART9 INPS3 INT3 ltac:(intros E; injection E; lia)) as PSL. cbn [fst snd] in PSL.
  (* [comment removed for export] *)
  assert (NSTK3 : forall (Σx : rts RT) (mx : mem) x, ART RT Σx mx -> rt_sp0 RT Σx = rt_sp0 RT Σ -> aclient (rt_live RT Σx) (rt_frames RT Σx) usp x -> usp <= x \/ x < usp - 704).
  { intros Σx mx x ARTx SPx Hx. exact (cl_split RT AF Σx mx usp 704 _ ARTx ltac:(rewrite SPx; lia) ltac:(lia) Hx). }
  (* [comment removed for export] *)
  pose proof (ps_w11 sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F9 fc9 m9 nm usp1 f ps pn pl1 pl2 pq1 pq2 r
                ltac:(unfold usp1; lia) ltac:(unfold usp1, USTACK_TOP in *; lia) HR NMC9 TC9 ltac:(lia) PSTOP MI9) as W11.
  cl_lift W11 Hc9 c10 Hc10.
  destruct (ASTA_unpack RT Σ3 _ _ c10 Hc10) as (ms10 & (m10 & -> & MU10 & WM10 & MI10 & SPL10 & TC10) & Hc10'). clear Hc10. fold t in TC10, Hc10'.
  assert (MU10' : munch ([] ++ [(usp - 704, usp)]) m9 m10) by (eapply munch_weaken; [| exact MU10]; unfold sub_fp; cbn [outside app]; unfold usp1; clear - HP; intros; lia).
  pose proof (cl_seg_ART RT AF Σ3 m9 m10 usp 704 [] ART9 ltac:(rewrite SP3; lia) ltac:(lia) MU10' ltac:(intros x Hx; exfalso; apply Hx; exact I) WM10) as ART10.
  assert (KEEP10 : forall a cs, rw_cells asegs m9 a cs -> (a + Z.of_nat (cells_size cs) <= usp1 + 16 \/ usp1 + 24 <= a) -> rw_cells asegs m10 a cs).
  { intros a cs H H1. apply (rw_cells_transport asegs _ m9 m10 _ _ H MU10 WM10). cbn [disjoint_from]. clear - H1. lia. }
  unfold ps_ftail in FR9.
  destruct (ps_blob_munch _ m9 m10 (usp + -160) 56 j9 _ FR9 MU10 WM10 ltac:(intros x Hx; cbn [outside]; unfold usp1; clear - Hx HP; lia)) as (j10 & FR10).
  assert (FRR10 : rw_cells asegs m10 (usp - 16) [C8 s0; C8 ra]).
  { lazymatch type of FR10 with rw_cells _ _ _ [?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10; ?c11; ?c12; ?c13; ?c14] =>
      pose proof (rw_cells_skip m10 _ [c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12] [c13; c14] FR10) as X end.
    cbn [cells_size csize Nat.add] in X. replace (usp + -160 + Z.of_nat 144) with (usp - 16) in X by lia. exact X. }
  assert (AGS010 : agree_on (fun x => usp <= x < USTACK_TOP) m m10).
  { intros a Ha. cbv beta in Ha. rewrite (MU10 a ltac:(cbn [outside]; unfold usp1; clear - Ha HP; lia)). exact (AGS09 a Ha). }
  destruct (cl_chain_call (rt_cg RT Σ) e_property_string e_lh_insert SITE_ps_insert m m10 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH (SITE_ps_insert, e_property_string) ltac:(unfold PSTR_SITES; right; right; left; reflexivity)) (proj2 CGH (SITE_ps_insert, e_lh_insert) ltac:(unfold PSTR_CALLS; right; right; right; left; reflexivity))
              UWC AGS010 FRR10 ltac:(rewrite EU1; fold usp; unfold usp1; clear - HP; lia) SPT) as (CTX10 & UWC10).
  assert (GAP10 : stk asegs m10 usp1 (usp + -160)).
  { destruct HP as [-> | ->].
    - replace usp1 with (usp + -160) in * by (unfold usp1; lia). destruct GAP9 as (G1 & G2 & G3). split; [lia|]. split; [lia|]. intros a Ha. lia.
    - apply (stk_munch _ m9 m10 _ _ GAP9 MU10 WM10). intros x Hx. cbn [outside]. unfold usp1 in *. lia. }
  (* [comment removed for export] *)
  assert (NODES3 : forall n, In n (concat bks) -> fst n + 24 <= lo /\ 0 < fst n).
  { intros n Hn. destruct (BLK Σ3 m9 (fst n) 24 ART9 SP3 (INL3 _ (plh_L_node t B bks n Hn)) ltac:(lia)) as (_ & X2 & X3 & _). exact (conj X3 X2). }
  assert (REP10 : plh_rep m10 t B items bks).
  { apply (plh_rep_munch _ m9 m10 _ _ _ _ REP9 MU10). intros a [Ha|[Ha|(n & Hn & Ha)]]; cbn [outside]; unfold usp1.
    - clear - Ha LLO HSTK HP. unfold RT_STACK in *. lia.
    - clear - Ha BLO HSTK HP. unfold RT_STACK in *. lia.
    - destruct (NODES3 n Hn) as (X & _). clear - Ha X HSTK HP. unfold RT_STACK in *. lia. }
  assert (DC10 : rw_cells asegs m10 pn [C8 (Z_to_bv 64 (pn + 12))]).
  { apply (KEEP10 _ _ (rw_cells_head m9 pn _ _ QC9)). cbn [cells_size csize Nat.add]. unfold usp1. clear - QLO Hl0 HSTK HP. unfold RT_STACK in *. lia. }
  assert (QC10 : rw_cells asegs m10 pn [C8 (Z_to_bv 64 (pn + 12)); C4 (Z_to_bv 64 idx)]).
  { apply (KEEP10 _ _ QC9). cbn [cells_size csize Nat.add]. unfold usp1. clear - QLO Hl0 HSTK HP. unfold RT_STACK in *. lia. }
  assert (SBL : Z.of_nat (length (str ++ [Z_to_bv 8 0])) = len + 1) by (rewrite length_app; cbn [length]; unfold len; lia).
  assert (STR10 : bytes_at asegs m10 (pn + 12) (str ++ [Z_to_bv 8 0])).
  { apply (bytes_at_transport asegs _ m9 m10 _ _ STR9 MU10). cbn [disjoint_from]. rewrite SBL. unfold usp1. clear - QLO HSTK HP. unfold RT_STACK in *. lia. }
  assert (ENV10 : cl_env m10 (Z_to_bv 8 1) canary).
  { apply (cl_env_seg _ m9 m10 _ canary ENV9 MU10). intros x Hx. pose proof (client_static_range x (cl_cell_static x Hx)) as CR. unfold SEGTOP_A in CR. cbn [outside]. unfold usp1. clear - CR HSTK NUM HP. unfold RT_STACK in *. lia. }
  pose proof (QFRESH t 104 (INL _ ltac:(left; reflexivity))) as QT.
  assert (ST10 : stk asegs m10 lo usp1).
  { apply (stk_munch _ m9 m10 _ _ ST9 MU10 WM10). intros x Hx. cbn [outside]. clear - Hx. lia. }
  apply (plh_insert_cps RT GOBJ AF AFP C_CM Σ3 PMc (Z_to_bv 64 SITE_ps_insert) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 t) (Z_to_bv 64 pn)
           b2 b3 b4 b5 b6 b7 (Z_to_bv 64 f) (Z_to_bv 64 ps) (Z_to_bv 64 (Z.shiftr ps 3 + 2147450880)) (Z_to_bv 64 (ps + off_idx nm)) (Z_to_bv 64 2147450880) (Z_to_bv 64 pn)
           (Z_to_bv 64 (q_of nm pq1 pq2)) (Z_to_bv 64 t) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) u3 u4 u5 u6 F9 fc9 m10 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary
           t B items bks pn (len + 16) (pn + 12) str FDO MST eq_refl eq_refl eq_refl ART10 MI10).
  { unfold call_ok. rewrite EU1, SP3. split; [exact ST10|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|].
    fold usp in SPA. clear - SPA HP HPM. Z.div_mod_to_equations. lia. }
  { rewrite EU1. unfold usp1, RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ps_insert) by (unfold SITE_ps_insert; lia). rewrite CG3. exact CTX10. }
  { exact UWC10. }
  { rewrite CG3. clear - CGH. unfold PSTR_SITES, PSTR_CALLS in CGH. split; intros x Hx; [apply (proj1 CGH)| apply (proj2 CGH)]; apply in_or_app; right; apply in_or_app; left; exact Hx. }
  { exact Hlen3. }
  { rewrite CR3. lia. }
  { exact ENV10. } { exact REP10. } { exact INL3. } { exact ITEMS. } { exact INQ3. } { lia. } { exact DC10. }
  { clear - Q16. Z.div_mod_to_equations. lia. }
  { exact QT. }
  { lia. } { lia. } { exact STR10. } { exact NONUL. } { exact NE. } { fold len. lia. } { exact HASHES. }
  { exact Hc10'. }
  clear Hc10'. intros c11 (Σ4 & pnn & Hc11 & LV4 & FRS4 & SP4 & CR4 & N0 & N16 & NU & CG4).
  destruct (ASTA_unpack RT Σ4 _ _ c11 Hc11) as (ms11 & (m11 & RS11 & (ART11 & MI11 & WM11 & ST11) & PRES11 & ENV11 & REP11 & NODE11) & Hc11'). clear Hc11.
  destruct RS11 as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F11 & fc11 & ->).
  rewrite EU1 in ST11, PRES11. rewrite (ret_pc_even SITE_ps_insert) in Hc11' by (unfold SITE_ps_insert; lia).
  (* [comment removed for export] *)
  set (h := lh_strhash str) in *. set (bi := h mod 8) in *. assert (BIR : 0 <= bi < 8) by (subst bi; apply Z.mod_pos_bound; lia).
  set (rn := pend (B + 8 * bi) (nth (Z.to_nat bi) bks [])) in *.
  assert (RNP : exists pa na, In (pa, na) (plh_L t B bks) /\ pa <= rn /\ rn + 8 <= pa + na /\ (na = 128 \/ na = 24)).
  { destruct (pend_where (nth (Z.to_nat bi) bks []) (B + 8 * bi)) as [[E1 E2]|(pre & Ar & hr & E1 & E2)]; fold rn in E2.
    - exists B, 128. split; [right; left; reflexivity|]. rewrite E2. lia.
    - exists Ar, 24. split; [| rewrite E2; lia]. apply (plh_L_node t B bks (Ar, hr)). eapply in_concat_nthZ. rewrite E1. apply in_or_app. right. left. reflexivity. }
  destruct RNP as (pa & na & INPA & PA1 & PA2 & NA).
  (* [comment removed for export] *)
  assert (OUT11 : forall p n, In (p, n) (rt_live RT Σ3) -> 1 <= n <= 64512 -> (p + n <= t \/ t + 104 <= p) -> (p + n <= pa \/ pa + na <= p) ->
            forall x, p <= x < p + n -> outside [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (t + 88, t + 104); (rn, rn + 8)] x).
  { intros p n Hin Hn H1 H2 x Hx. pose proof (afp_live_hi RT GOBJ AFP Σ3 m9 p n ART9 Hin ltac:(lia)) as PH. cbn [outside]. unfold G_ALLOW_CUST. clear - Hx PH H1 H2 PA1 PA2. lia. }
  assert (APT : forall p n, In (p, n) (rt_live RT Σ3) -> (p, n) <> (t, 104) -> p + n <= t \/ t + 104 <= p).
  { intros p n Hin NE'. pose proof (live_ne_apart2 RT AF Σ3 m9 (p, n) (t, 104) ART9 Hin INT3 NE') as X. cbn [fst snd] in X. exact X. }
  assert (APA : forall p n, In (p, n) (rt_live RT Σ3) -> (p, n) <> (pa, na) -> p + n <= pa \/ pa + na <= p).
  { intros p n Hin NE'. pose proof (live_ne_apart2 RT AF Σ3 m9 (p, n) (pa, na) ART9 Hin (INL3 _ INPA) NE') as X. cbn [fst snd] in X. exact X. }
  assert (AGL1011 : forall p n, In (p, n) (rt_live RT Σ3) -> 1 <= n <= 64512 -> (p + n <= t \/ t + 104 <= p) -> (p + n <= pa \/ pa + na <= p) -> agree_on (fun x => p <= x < p + n) m10 m11).
  { intros p n Hin Hn H1 H2 x Hx. cbv beta in Hx. apply PRES11; [exact (acl_live _ _ _ p n _ Hin Hx)| exact (OUT11 p n Hin Hn H1 H2 _ Hx)]. }
  destruct (BLK Σ3 m9 pa na ART9 SP3 (INL3 _ INPA) ltac:(clear - NA; lia)) as (_ & PA0 & PALO & PAHI & PATOP).
  assert (NLO : forall x, lo <= x -> outside [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (t + 88, t + 104); (rn, rn + 8)] x).
  { intros x Hx. cbn [outside]. unfold G_ALLOW_CUST. clear - Hx HLOI LLO PA1 PA2 PALO. unfold SEGTOP_A in *. lia. }
  assert (NFRM : forall x, (f <= x < f + 64) \/ (f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 8) -> outside [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (t + 88, t + 104); (rn, rn + 8)] x).
  { intros x Hx. pose proof (PF t 104 INT3) as X1. pose proof (PF pa na (INL3 _ INPA)) as X2. pose proof (SLF t 104 INT3) as X3. pose proof (SLF pa na (INL3 _ INPA)) as X4.
    cbn [outside]. unfold G_ALLOW_CUST. clear - Hx X1 X2 X3 X4 FIMG SHR PA1 PA2. lia. }
  assert (AGS1011 : forall a k, usp1 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m10 m11).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES11; [left; lia| apply NLO; unfold usp1; clear - Hx H1 HSTK HP; unfold RT_STACK in *; lia]. }
  assert (AGF1011 : forall a k, (f <= a /\ a + k <= f + 56) \/ (f / 8 + 2147450880 <= a /\ a + k <= f / 8 + 2147450880 + 8) -> agree_on (fun x => a <= x < a + k) m10 m11).
  { intros a k H x Hx. cbv beta in Hx. destruct H as [H|H].
    - apply PRES11; [apply (acl_frame _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; lia]| apply NFRM; left; lia].
    - apply PRES11; [apply (acl_fshadow _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; rewrite SHF; unfold shad, SHB; lia]| apply NFRM; right; lia]. }
  (* [comment removed for export] *)
  assert (NE_PS_T : (ps, 48) <> (t, 104)) by (intros E; injection E; lia). assert (NE_PK_T : (pk, 40) <> (t, 104)) by (intros E; injection E; lia).
  assert (NE_PS_PA : (ps, 48) <> (pa, na)) by (intros E; injection E; lia). assert (NE_PK_PA : (pk, 40) <> (pa, na)) by (intros E; injection E; lia).
  pose proof (QFRESH pa na (INL _ INPA)) as QPA.
  assert (FR11 : rw_cells asegs m11 (usp + -160) (CB 56 j10 :: [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
  { apply (rw_cells_agree asegs m10 m11 _ _ FR10); [| exact WM11]. apply AGS1011; [unfold usp1; clear - HP; lia| cbn [cells_size csize Nat.add]; unfold USTACK_TOP in *; lia]. }
  assert (GAP11 : stk asegs m11 usp1 (usp + -160)).
  { apply (stk_agree_nw asegs m10 m11 _ _ GAP10). intros x Hx. cbv beta in Hx. exact (AGS1011 usp1 (usp + -160 - usp1) ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) x ltac:(cbv beta; lia)). }
  assert (FFC11 : rw_cells asegs m11 f [C8 (Z_to_bv 64 PS_MAGIC); C8 (Z_to_bv 64 PS_DESCR); C8 (Z_to_bv 64 e_property_string); CB 8 hj1; C8 (Z_to_bv 64 S); CB 16 hj2]).
  { assert (FFC10 : rw_cells asegs m10 f [C8 (Z_to_bv 64 PS_MAGIC); C8 (Z_to_bv 64 PS_DESCR); C8 (Z_to_bv 64 e_property_string); CB 8 hj1; C8 (Z_to_bv 64 S); CB 16 hj2]).
    { apply (KEEP10 _ _ FFC9). cbn [cells_size csize Nat.add]. unfold usp1. clear - FLO LOW HSTK HP. unfold RT_STACK in *. lia. }
    apply (rw_cells_agree asegs m10 m11 _ _ FFC10); [| exact WM11]. apply AGF1011. left. cbn [cells_size csize Nat.add]. lia. }
  assert (FFS11 : rw_cells asegs m11 (f / 8 + 2147450880) ps_shadow).
  { assert (FFS10 : rw_cells asegs m10 (f / 8 + 2147450880) ps_shadow).
    { apply (KEEP10 _ _ FFS9). unfold ps_shadow. cbn [cells_size csize Nat.add]. unfold usp1. clear - SHR NUM HSTK HP. unfold RT_STACK in *. lia. }
    apply (rw_cells_agree asegs m10 m11 _ _ FFS10); [| exact WM11]. apply AGF1011. right. unfold ps_shadow. cbn [cells_size csize Nat.add]. lia. }
  assert (PSC11 : rw_cells asegs m11 ps (psd_bump nm pk pl1 pl2 ni vi pq1 pq2)).
  { assert (PSC10 : rw_cells asegs m10 ps (psd_bump nm pk pl1 pl2 ni vi pq1 pq2)).
    { apply (KEEP10 _ _ PSC9). destruct nm; unfold psd_bump, psd_cells; cbn [cells_size csize Nat.add]; unfold usp1; clear - PSLO HSTK HP; unfold RT_STACK in *; lia. }
    apply (rw_cells_agree asegs m10 m11 _ _ PSC10); [| exact WM11]. eapply agree_sub; [exact (AGL1011 ps 48 INPS3 ltac:(lia) (APT _ _ INPS3 NE_PS_T) (APA _ _ INPS3 NE_PS_PA))|].
    destruct nm; unfold psd_bump, psd_cells; cbn [cells_size csize Nat.add]; intros x Hx; lia. }
  assert (LKC11 : rw_cells asegs m11 pk (mutex_cells z64 (Z_to_bv 64 16))).
  { assert (LKC10 : rw_cells asegs m10 pk (mutex_cells z64 (Z_to_bv 64 16))).
    { apply (KEEP10 _ _ LKC9). unfold mutex_cells; cbn [cells_size csize Nat.add]; unfold usp1; clear - PKLO HSTK HP; unfold RT_STACK in *; lia. }
    apply (rw_cells_agree asegs m10 m11 _ _ LKC10); [| exact WM11]. eapply agree_sub; [exact (AGL1011 pk 40 INPK3 ltac:(lia) (APT _ _ INPK3 NE_PK_T) (APA _ _ INPK3 NE_PK_PA))|].
    unfold mutex_cells; cbn [cells_size csize Nat.add]; intros x Hx; lia. }
  assert (QC11 : rw_cells asegs m11 pn [C8 (Z_to_bv 64 (pn + 12)); C4 (Z_to_bv 64 idx)]).
  { apply (rw_cells_agree asegs m10 m11 _ _ QC10); [| exact WM11]. eapply agree_sub; [exact (AGL1011 pn (len + 16) INQ3 ltac:(lia) QT QPA)|].
    cbn [cells_size csize Nat.add]; intros x Hx; lia. }
  assert (CELL11 : rw_cells asegs m11 CTX_PSD [C8 (Z_to_bv 64 ps)]).
  { assert (CELL10 : rw_cells asegs m10 CTX_PSD [C8 (Z_to_bv 64 ps)]).
    { apply (KEEP10 _ _ CELL9). cbn [cells_size csize Nat.add]. unfold usp1, CTX_PSD. clear - NUM HSTK HP. unfold RT_STACK in *. lia. }
    apply (rw_cells_agree asegs m10 m11 _ _ CELL10); [| exact WM11]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. unfold CTX_PSD in Hx.
    apply PRES11; [apply acl_static; apply client_static_intro; lia|]. cbn [outside]. unfold G_ALLOW_CUST. clear - Hx LHI PAHI PA1. lia. }
  (* [comment removed for export] *)
  assert (IN4 : forall e, In e (rt_live RT Σ3) -> In e (rt_live RT Σ4)) by (intros e He; rewrite LV4; right; exact He).
  destruct (af_client_consts RT AF Σ4 m11 ART11) as (_ & SHC11 & _ & _ & UT11).
  pose proof (QFRESH pk 40 INPK) as QPK. pose proof (QFRESH ps 48 INPS) as QPS.
  assert (PSCX : psd_bump nm pk pl1 pl2 ni vi pq1 pq2 = psd_cells pk pl1 pl2 (if nm then ni + 1 else ni) (if nm then vi else vi + 1) pq1 pq2) by (destruct nm; reflexivity).
  rewrite PSCX in PSC11.
  pose proof (ps_w14a sp gp (Z_to_bv 64 0xba3ef0) v0 v1 v2 (Z_to_bv 64 0) d1 d2 d3 d4 d5 d6 d7 v3 v4 v5 v6 F11 fc11 m11 nm usp1 f ps pn pk pl1 pl2
                (if nm then ni + 1 else ni) (if nm then vi else vi + 1) pq1 pq2 idx lo B (items + 1)
                ltac:(lia) ltac:(unfold usp1, RT_STACK in *; clear - HSTK HP; lia) ltac:(unfold usp1, USTACK_TOP in *; clear - NUM HP; lia) ST11 UT11 SHC11
                (proj1 REP11) (proj2 (af_acc_live RT AF Σ4 m11 t 104 ART11 (IN4 _ INT3))) L0 ltac:(destruct REP9 as (_ & X & _); clear - X; Z.div_mod_to_equations; lia) LLO
                PS0 PSAL PSHI PSLO PSC11 (proj2 (af_acc_live RT AF Σ4 m11 ps 48 ART11 (IN4 _ INPS3)))
                PK0 PKAL PKHI PKLO LKC11 Q0 ltac:(clear - Q16; Z.div_mod_to_equations; lia) QHI ltac:(clear - QLO Hl0; lia) QC11
                (acc_sub asegs m11 pn (len + 16) pn 16 (proj2 (af_acc_live RT AF Σ4 m11 pn (len + 16) ART11 (IN4 _ INQ3))) ltac:(lia) ltac:(lia)) IDX
                PSPK ltac:(clear - QPK Hl0; lia) LPK ltac:(clear - F0 FLO SP0R; unfold USTACK_TOP, STACK_WIN in *; lia) MI11) as W14a.
  fold t in W14a.
  cl_lift W14a Hc11' c12 Hc12.
  destruct (ASTA_unpack RT Σ4 _ _ c12 Hc12) as (ms12 & (a2' & a3' & m12 & -> & MU12 & WM12 & MI12 & ST12 & LKC12) & Hc12'). clear Hc12. fold t in Hc12'.
  (* [comment removed for export] *)
  assert (KEEP12 : forall a cs, rw_cells asegs m11 a cs -> (a + Z.of_nat (cells_size cs) <= usp1 - 112 \/ usp1 <= a) -> (a + Z.of_nat (cells_size cs) <= pk + 4 \/ pk + 8 <= a) -> rw_cells asegs m12 a cs).
  { intros a cs H H1 H2. apply (rw_cells_transport asegs _ m11 m12 _ _ H MU12 WM12). cbn [disjoint_from]. clear - H1 H2. lia. }
  pose proof (PF pk 40 INPK3) as PKF. pose proof (SLF pk 40 INPK3) as PKSF.
  assert (FFC12 : rw_cells asegs m12 f [C8 (Z_to_bv 64 PS_MAGIC); C8 (Z_to_bv 64 PS_DESCR); C8 (Z_to_bv 64 e_property_string); CB 8 hj1; C8 (Z_to_bv 64 S); CB 16 hj2]).
  { apply (KEEP12 _ _ FFC11); cbn [cells_size csize Nat.add]; [unfold usp1; clear - FLO LOW HSTK HP; unfold RT_STACK in *; lia| clear - PKF; lia]. }
  assert (FFS12 : rw_cells asegs m12 (f / 8 + 2147450880) ps_shadow).
  { apply (KEEP12 _ _ FFS11); unfold ps_shadow; cbn [cells_size csize Nat.add]; [unfold usp1; clear - SHR NUM HSTK HP; unfold RT_STACK in *; lia| clear - PKSF; lia]. }
  pose proof (ps_w14b sp gp (Z_to_bv 64 0xba3ef0) v0 v1 v2 (Z_to_bv 64 0) a2' a3' d4 d5 d6 d7 (Z_to_bv 64 ps) (Z_to_bv 64 (Z.shiftr ps 3 + 2147450880)) (Z_to_bv 64 (ps + off_idx nm)) (Z_to_bv 64 2147450880) (Z_to_bv 64 pn)
                (Z_to_bv 64 (q_of nm pq1 pq2)) (Z_to_bv 64 t) v3 v4 v5 v6 F11 fc11 m12 usp1 f idx S hj1 hj2
                F0 F64 FIMG ltac:(clear - FLO SP0R; unfold USTACK_TOP, STACK_WIN in *; lia) ltac:(destruct FSH; [left | right]; lia) IDX FFC12 FFS12 MI12) as W14b.
  cl_lift W14b Hc12' c13 Hc13.
  destruct (ASTA_unpack RT Σ4 _ _ c13 Hc13) as (ms13 & (m13 & -> & MU13 & WM13 & MI13 & FFC13 & FFS13) & Hc13'). clear Hc13.
  (* [comment removed for export] *)
  assert (INF4 : In (f, 0%nat) (rt_frames RT Σ4)) by (rewrite FRS4; exact INF).
  assert (ART12 : ART RT Σ4 m12).
  { apply (af_frame RT AF Σ4 m11 m12 (usp - 704) ART11 ltac:(rewrite SP4, SP3; lia)); [| exact WM12].
    intros a Ha. apply MU12. cbn [outside]. split; [| split; [| exact I]]; intros Hin; apply Ha.
    - apply acl_stack. unfold usp1, USTACK_TOP in *. clear - Hin HP NUM. lia.
    - apply (acl_live _ _ _ pk 40); [exact (IN4 _ INPK3)| lia]. }
  assert (ART13 : ART RT Σ4 m13).
  { apply (af_frame RT AF Σ4 m12 m13 usp1 ART12 ltac:(rewrite SP4, SP3; unfold usp1; lia)); [| exact WM13].
    intros a Ha. apply MU13. cbn [outside]. split; [| split; [| exact I]]; intros Hin; apply Ha.
    - apply (acl_frame _ _ _ f 0%nat); [exact INF4 | change (fs_size 0) with 64; lia].
    - apply (acl_fshadow _ _ _ f 0%nat); [exact INF4 | change (fs_size 0) with 64; rewrite SHF; unfold shad, SHB; lia]. }
  (* [comment removed for export] *)
  destruct (af_frame_release RT AF Σ4 m13 f 0%nat (rt_frames RT Σ) ART13 ltac:(rewrite FRS4; exact FRS3)) as (Σ5 & flg & FLC & NAC & FL0 & FLW & FW & REL).
  change (fs_size 0) with 64 in FW. replace (f + 64 - 8) with (f + 56) in FW by lia. rewrite SP4, SP3 in FLW.
  assert (KEEP13 : forall a cs, rw_cells asegs m12 a cs -> (a + Z.of_nat (cells_size cs) <= f \/ f + 8 <= a) -> (a + Z.of_nat (cells_size cs) <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 8 <= a) -> rw_cells asegs m13 a cs).
  { intros a cs H H1 H2. apply (rw_cells_transport asegs _ m12 m13 _ _ H MU13 WM13). cbn [disjoint_from]. clear - H1 H2. lia. }
  assert (FR13 : rw_cells asegs m13 (usp + -160) (CB 56 j10 :: ps_ftail s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)).
  { unfold ps_ftail. apply KEEP13; [apply (KEEP12 _ _ FR11)| |]; cbn [cells_size csize Nat.add]; unfold usp1; [clear - HP; lia| clear - PKLO HSTK; unfold RT_STACK in *; lia| clear - FLO LOW HSTK; unfold RT_STACK in *; lia| clear - SHR NUM HSTK; unfold RT_STACK in *; lia]. }
  assert (GAP13 : stk asegs m13 usp1 (usp + -160)).
  { apply (stk_munch _ m12 m13 _ _ (stk_munch _ m11 m12 _ _ GAP11 MU12 WM12 ltac:(intros x Hx; cbn [outside]; unfold usp1 in *; clear - Hx PKLO HSTK HP; unfold RT_STACK in *; lia)) MU13 WM13).
    intros x Hx. cbn [outside]. unfold usp1 in Hx. clear - Hx FLO LOW SHR NUM HSTK HP. unfold RT_STACK in *. lia. }
  assert (ST13 : stk asegs m13 lo usp1).
  { apply (stk_munch _ m12 m13 _ _ ST12 MU13 WM13). intros x Hx. cbn [outside]. clear - Hx FLO LOW SHR NUM. lia. }
  pose proof (ps_w14c sp gp (Z_to_bv 64 0xba3ef0) v0 v1 v2 (Z_to_bv 64 (-11)) a2' a3' d4 d5 d6 d7 (Z_to_bv 64 ps) (Z_to_bv 64 (Z.shiftr ps 3 + 2147450880)) (Z_to_bv 64 (ps + off_idx nm)) (Z_to_bv 64 2147450880) (Z_to_bv 64 pn)
                (Z_to_bv 64 (q_of nm pq1 pq2)) (Z_to_bv 64 t) v3 v4 v5 v6 F11 fc11 m13 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 f flg lo pd idx j10
                HP ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia) F0 ltac:(clear - FLO LOW; lia) FL0 ltac:(clear - FLW LOW; lia) IDX
                ST13 GAP13 FR13 FW FLC MI13) as W14c.
  fold usp usp1 in W14c.
  cl_lift W14c Hc13' c14 Hc14.
  destruct (ASTA_unpack RT Σ4 _ _ c14 Hc14) as (ms14 & (m14 & -> & MU14 & WM14 & MI14 & ST14 & FLC14) & Hc14'). clear Hc14. fold usp in ST14.
  destruct (REL m14 MU14 WM14 FLC14) as (ART14 & FRS5 & LV5 & SP5 & CR5 & AL5 & AM5 & CG5).
  (* [comment removed for export] *)
  assert (NFL4 : forall x, aclient (rt_live RT Σ4) (rt_frames RT Σ4) USTACK_TOP x -> x <> flg) by (intros x Hx E; apply NAC; rewrite <- E; exact Hx).
  assert (A914 : forall x : word, aclient (rt_live RT Σ3) (rt_frames RT Σ) usp (bv_unsigned x) -> outside (PS_WT nm pk pl1 pl2 B bks str) (bv_unsigned x) -> m14 x = m9 x).
  { intros x Hx Ho. unfold PS_WT in Ho. fold t h bi rn in Ho. cbn [outside] in Ho. destruct Ho as (O1 & O2 & O3 & O4 & _).
    assert (Hx3 : aclient (rt_live RT Σ3) (rt_frames RT Σ3) usp (bv_unsigned x)) by (apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto| rewrite FRS3; intros e' He'; right; exact He'| lia]).
    pose proof (NSTK3 Σ3 m9 _ ART9 SP3 Hx3) as N3.
    destruct (frame_apart RT AF Σ3 m9 f 0%nat (rt_frames RT Σ) usp _ ART9 FRS3 ltac:(rewrite SP3; lia) Hx) as (N1 & N2).
    change (fs_size 0) with 64 in N1, N2. rewrite SHF in N2. unfold shad, SHB in N2.
    assert (NF : bv_unsigned x <> flg).
    { destruct Hx3 as [H|H]; [clear - H FLW NUM; lia|]. apply NFL4. right. rewrite LV4, FRS4.
      destruct H as [H|[H|[H|H]]]; [left; exact H| right; left; destruct H as (p & n & Hin & Hp); exists p, n; split; [right; exact Hin| exact Hp]| right; right; left; exact H| right; right; right; exact H]. }
    rewrite (MU14 x ltac:(cbn [outside]; clear - NF; lia)).
    rewrite (MU13 x ltac:(cbn [outside]; clear - N1 N2; lia)).
    rewrite (MU12 x ltac:(cbn [outside]; unfold usp1; clear - N3 O4 HP; lia)).
    rewrite (PRES11 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx3); [auto| auto| unfold usp1; clear - HP; lia]) ltac:(cbn [outside]; exact (conj O1 (conj O2 (conj O3 I))))).
    apply MU10. cbn [outside]. unfold usp1. clear - N3 HP. lia. }
  pose proof (af_frames_range RT AF Σ4 m13 f 0%nat ART13 INF4) as (_ & _ & _ & PF4). change (fs_size 0) with 64 in PF4.
  pose proof (proj1 (af_fshadow_apart RT AF Σ4 m13 f 0%nat ART13 INF4)) as SLF4. change (fs_size 0) with 64 in SLF4. rewrite SHF in SLF4. unfold shad, SHB in SLF4.
  assert (AGL1114 : forall p n, In (p, n) (rt_live RT Σ4) -> 1 <= n <= 64512 -> (p + n <= pk \/ pk + 40 <= p) -> agree_on (fun x => p <= x < p + n) m11 m14).
  { intros p n Hin Hn HPK x Hx. cbv beta in Hx.
    destruct (BLK Σ4 m11 p n ART11 ltac:(rewrite SP4; exact SP3) Hin Hn) as (_ & _ & PLO & _).
    pose proof (PF4 p n Hin) as X1. pose proof (SLF4 p n Hin) as X2.
    rewrite (MU14 x ltac:(cbn [outside]; pose proof (NFL4 _ (acl_live _ _ _ p n _ Hin Hx)); lia)).
    rewrite (MU13 x ltac:(cbn [outside]; clear - Hx X1 X2; lia)).
    apply MU12. cbn [outside]. unfold usp1. clear - Hx PLO HPK HSTK HP. unfold RT_STACK in *. lia. }
  assert (WM1114 : wmono asegs m11 m14) by exact (wmono_trans asegs _ _ _ WM12 (wmono_trans asegs _ _ _ WM13 WM14)).
  apply Hk. exists Σ5, pnn.
  split; [| split; [rewrite LV5; exact LV4| split; [exact FRS5| split; [rewrite SP5, SP4; exact SP3| split; [rewrite CR5, CR4, CR3; change (mcost 24) with 0; lia| split; [exact (conj N0 (conj N16 NU))| rewrite CG5, CG4; exact CG3]]]]]].
  eapply ASTA_conseq; [exact (ASTA_switch RT Σ4 Σ5 PMc _ c14 Hc14' AL5 AM5)|]. intros ms <-. exists m14.
  split; [exists v0, v1, v2, (Z_to_bv 64 flg), a2', a3', d4, d5, d6, d7, v3, v4, v5, v6, F11, fc11; reflexivity|].
  split; [exact (conj ART14 (conj MI14 ST14))|].
  split. { intros E. exact (wmono_trans asegs _ _ _ (WMH E) (wmono_trans asegs _ _ _ WM10 (wmono_trans asegs _ _ _ WM11 WM1114))). }
  split. { intros x Hx Ho. destruct (ps_outside_appD _ _ _ Ho) as [O1 O2].
           rewrite (A914 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [exact INC3| auto| lia]) O2). exact (A09 x Hx O1). }
  split; [| exact A914].
  unfold pstr_post_mem. fold t.
  split. { assert (ENV12 : cl_env m12 (Z_to_bv 8 1) canary).
           { apply (cl_env_seg _ m11 m12 _ canary ENV11 MU12). intros x Hx. pose proof (client_static_range x (cl_cell_static x Hx)) as CR. unfold SEGTOP_A in CR. cbn [outside]. unfold usp1. clear - CR PKHI HSTK NUM HP. unfold RT_STACK in *. lia. }
           assert (ENV13 : cl_env m13 (Z_to_bv 8 1) canary).
           { apply (cl_env_seg _ m12 m13 _ canary ENV12 MU13). intros x Hx. pose proof (client_static_range x (cl_cell_static x Hx)) as CR. unfold SEGTOP_A in CR. cbn [outside]. clear - CR FIMG SHR. lia. }
           apply (cl_env_seg _ m13 m14 _ canary ENV13 MU14). intros x Hx. cbn [outside]. pose proof (NFL4 x (acl_static _ _ _ _ (cl_cell_static x Hx))). lia. }
  split. { apply (rw_cells_agree asegs m11 m14 _ _ CELL11); [| exact WM1114]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. unfold CTX_PSD in Hx.
           assert (CS : client_static (bv_unsigned x)) by (apply client_static_intro; lia).
           rewrite (MU14 x ltac:(cbn [outside]; pose proof (NFL4 _ (acl_static _ _ _ _ CS)); lia)).
           rewrite (MU13 x ltac:(cbn [outside]; clear - Hx FIMG SHR; lia)).
           apply MU12. cbn [outside]. unfold usp1. clear - Hx PKHI HSTK NUM HP. unfold RT_STACK in *. lia. }
  split. { rewrite PSCX. apply (rw_cells_agree asegs m11 m14 _ _ PSC11); [| exact WM1114]. eapply agree_sub; [exact (AGL1114 ps 48 (IN4 _ INPS3) ltac:(lia) PSPK)|].
           unfold psd_cells; cbn [cells_size csize Nat.add]; intros x Hx; lia. }
  split. { apply (rw_cells_transport asegs _ m13 m14 _ _ (KEEP13 _ _ LKC12 ltac:(unfold mutex_cells; cbn [cells_size csize Nat.add]; clear - PKF; lia) ltac:(unfold mutex_cells; cbn [cells_size csize Nat.add]; clear - PKSF; lia)) MU14 WM14).
           cbn [disjoint_from]. unfold mutex_cells; cbn [cells_size csize Nat.add]. split; [| exact I].
           destruct (Z_le_gt_dec (pk + 40) flg) as [G|G]; [left; lia|]. destruct (Z_le_gt_dec (flg + 1) pk) as [G'|G']; [right; lia|].
           exfalso. apply (NFL4 flg); [apply (acl_live _ _ _ pk 40); [exact (IN4 _ INPK3)| lia]| reflexivity]. }
  unfold pstr_bks. fold h bi.
  apply (plh_rep_agree m11 m14 t B (items + 1) _ REP11). intros a Ha.
  destruct (ps_bks_fp t B bks str pnn (bv_unsigned a) ltac:(destruct REP9 as (_ & _ & _ & X & _); exact X) Ha) as [[Hx|[Hx|(n & Hn & Hx)]]|Hx].
  - exact (AGL1114 t 104 (IN4 _ INT3) ltac:(lia) LPK a Hx).
  - pose proof (live_ne_apart2 RT AF Σ3 m9 (B, 128) (pk, 40) ART9 INB3 INPK3 ltac:(intros E; injection E; lia)) as X. cbn [fst snd] in X.
    exact (AGL1114 B 128 (IN4 _ INB3) ltac:(lia) X a Hx).
  - pose proof (live_ne_apart2 RT AF Σ3 m9 (fst n, 24) (pk, 40) ART9 (INL3 _ (plh_L_node t B bks n Hn)) INPK3 ltac:(intros E; injection E; lia)) as X. cbn [fst snd] in X.
    exact (AGL1114 (fst n) 24 (IN4 _ (INL3 _ (plh_L_node t B bks n Hn))) ltac:(lia) X a Hx).
  - pose proof (wg_live_apart RT AF Σ4 m11 [] pnn 24 (rt_live RT Σ3) pk 40 ART11 LV4 INPK3) as X.
    exact (AGL1114 pnn 24 ltac:(rewrite LV4; left; reflexivity) ltac:(lia) X a Hx).
Qed.

End CPstrT.
