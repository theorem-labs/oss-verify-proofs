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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_mkit Fz_G_kit Th_mutex Fz_T_lock Fz_env Fz_M_malloc Fz_M_zalloc Fz_M_realloc Fz_M_realloc_array Fz_G_CRYPTO_calloc Fz_T_sk Fz_I1_insw Fz_I1_insx Fz_K_hash Fz_K_rep Fz_K_getrn Fz_K_retrieve Fz_K_insw Fz_K_insert Fz_K_skw Fz_K_sk Fz_I2_ppis Fz_K_pstw Fz_K_pstw2 Fz_K_pstrs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation wz := (Z_to_bv 64) (only parsing).
Notation z64 := (Z_to_bv 64 0) (only parsing).

Definition ps_RB (sp : word) : Z := bv_unsigned sp + -160 - bv_unsigned sp mod 32.
Definition PS_WH (ps pk : Z) : list (Z * Z) := [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (ps + 24, ps + 32); (pk + 4, pk + 8)].

(* [comment removed for export] *)
Definition ps_push_entry (sp gp tp t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (nm : bool) (f ps pn pq1 pq2 : Z) (m : mem) : machine_state :=
  entry_st (Z_to_bv 64 SITE_ps_push) (Z_to_bv 64 (ps_RB sp)) gp tp t0 t1 t2 sp (Z_to_bv 64 (ps_RB sp)) (Z_to_bv 64 (q_of nm pq1 pq2)) (Z_to_bv 64 (pn + 12)) (Z_to_bv 64 0) (Z_to_bv 64 0) a4 a5 a6 a7
     (Z_to_bv 64 f) (Z_to_bv 64 ps) (Z_to_bv 64 (Z.shiftr ps 3 + 2147450880)) (Z_to_bv 64 (ps + off_idx nm)) (Z_to_bv 64 2147450880) (Z_to_bv 64 pn)
     (Z_to_bv 64 (q_of nm pq1 pq2)) (Z_to_bv 64 (Z.shiftr (ps + off_idx nm) 3 + 2147450880)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) t3 t4 t5 t6 F fc e_sk_push m.
Definition ps_push_ret (sp gp tp : word) (nm : bool) (f ps pn pq1 pq2 : Z) (v : word) (m' : mem) (ms : machine_state) : Prop :=
  ret_st (Z_to_bv 64 SITE_ps_push) (Z_to_bv 64 (ps_RB sp)) gp tp sp (Z_to_bv 64 (ps_RB sp))
     (Z_to_bv 64 f) (Z_to_bv 64 ps) (Z_to_bv 64 (Z.shiftr ps 3 + 2147450880)) (Z_to_bv 64 (ps + off_idx nm)) (Z_to_bv 64 2147450880) (Z_to_bv 64 pn)
     (Z_to_bv 64 (q_of nm pq1 pq2)) (Z_to_bv 64 (Z.shiftr (ps + off_idx nm) 3 + 2147450880)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) v m' ms.

Section CPstrH.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.

(* [comment removed for export] *)
Definition ps_mid (Σ : rts RT) (m : mem) (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (lo : Z) (canary : word)
    (nm : bool) (S : Z) (str : list byte) (ps pk pl1 pl2 ni vi pq1 pq2 B items : Z) (bks : list (list pnode)) (f pn : Z)
    (Σk : rts RT) (mk : mem) (LIVE0 : list (Z * Z)) (Wk : list (Z * Z)) (WMF : bool) : Prop :=
  let usp := bv_unsigned sp in let RB := ps_RB sp in
     (ART RT Σk mk /\ mem_inv asegs mk /\ stk asegs mk lo RB)
  /\ (rt_frames RT Σk = (f, 0%nat) :: rt_frames RT Σ /\ rt_sp0 RT Σk = rt_sp0 RT Σ /\ rt_cg RT Σk = rt_cg RT Σ /\ rt_credit RT Σk = rt_credit RT Σ - 1)
  /\ cl_env mk (Z_to_bv 8 1) canary
  /\ (WMF = true -> wmono asegs m mk)
  /\ (forall x : word, aclient LIVE0 (rt_frames RT Σ) usp (bv_unsigned x) -> outside Wk (bv_unsigned x) -> mk x = m x)
  /\ agree_on (fun x => usp <= x < USTACK_TOP) m mk
  /\ (incl LIVE0 (rt_live RT Σk) /\ In (ps, 48) (rt_live RT Σk) /\ In (pk, 40) (rt_live RT Σk) /\ incl (plh_L (t_of nm pl1 pl2) B bks) (rt_live RT Σk)
      /\ In (pn, Z.of_nat (length str) + 16) (rt_live RT Σk))
  /\ ((exists j, rw_cells asegs mk (usp + -160) (CB 56 j :: ps_ftail s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) /\ stk asegs mk RB (usp + -160)
      /\ rw_cells asegs mk (RB + 16) [C8 (Z_to_bv 64 (nmz nm))] /\ rw_cells asegs mk (RB + 24) [C8 (Z_to_bv 64 (t_of nm pl1 pl2))])
  /\ ((exists hj1 hj2, rw_cells asegs mk f [C8 (Z_to_bv 64 PS_MAGIC); C8 (Z_to_bv 64 PS_DESCR); C8 (Z_to_bv 64 e_property_string); CB 8 hj1; C8 (Z_to_bv 64 S); CB 16 hj2])
      /\ rw_cells asegs mk (f / 8 + 2147450880) ps_shadow)
  /\ (rw_cells asegs mk CTX_PSD [C8 (Z_to_bv 64 ps)] /\ rw_cells asegs mk ps (psd_bump nm pk pl1 pl2 ni vi pq1 pq2)
      /\ rw_cells asegs mk pk (mutex_cells z64 (Z_to_bv 64 16)) /\ plh_rep mk (t_of nm pl1 pl2) B items bks
      /\ rw_cells asegs mk pn [C8 (Z_to_bv 64 (pn + 12)); C4 (Z_to_bv 64 (cnt_of nm ni vi + 1))] /\ bytes_at asegs mk (pn + 12) (str ++ [Z_to_bv 8 0]))
  /\ ((forall p n, In (p, n) (rt_live RT Σ) -> pn + (Z.of_nat (length str) + 16) <= p \/ p + n <= pn) /\ blk_ok pn (Z.of_nat (length str) + 16)).

Hypothesis SM0 : stack_malloc_contract RT 0.
Hypothesis SLC : strlen_icontract RT.
Hypothesis MCP : memcpy_icontract RT e_asan_memcpy.
Hypothesis C_CM : crypto_malloc_env_stmt RT.
Hypothesis GO_ctx : GOBJ PPI_CTX 328.

Definition pstr_head_post (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (lo : Z) (m : mem) (canary : word)
    (nm : bool) (S : Z) (str : list byte) (ps pk pl1 pl2 ni vi pq1 pq2 B items : Z) (bks : list (list pnode)) : config -> Prop :=
  fun c => exists (Σ2 : rts RT) (f pn : Z) (m8 : mem) (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F8 : bvmap 5 word) (fc8 : bv 32),
       ASTA RT Σ2 PMc (eq (ps_push_entry sp gp tp t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' F8 fc8 nm f ps pn pq1 pq2 m8)) c
    /\ rt_live RT Σ2 = (pn, Z.of_nat (length str) + 16) :: rt_live RT Σ
    /\ ps_mid Σ m ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo canary nm S str ps pk pl1 pl2 ni vi pq1 pq2 B items bks f pn Σ2 m8 (rt_live RT Σ) (PS_WH ps pk) true.

Theorem pstr_head : forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word)
    (nm : bool) (S b sz : Z) (str slack : list byte) (ps pk pl1 pl2 ni vi pq1 pq2 B items : Z) (bks : list (list pnode)),
  pstr_pre RT GOBJ Σ PMc ra sp tp s0 a0 a1 a2 a3 m lo outer lb canary nm S b sz str slack ps pk pl1 pl2 ni vi pq1 pq2 B items bks ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_property_string m)))
    (pstr_head_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m canary nm S str ps pk pl1 pl2 ni vi pq1 pq2 B items bks).
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary
    nm S b sz str slack ps pk pl1 pl2 ni vi pq1 pq2 B items bks
    (FDO & MST & -> & -> & -> & -> & -> & ART0 & MI0 & CALL & HSTK & CTX & UWC & CGH & Hfr & Hlen & Hcr & ENV
     & ROB & NONUL & NE & LEN & SLK & HG & Hbs & Hse & HS0 & HSE
     & CELL & INPS & PSAL & PSC & NI & VI & INPK & PKAL & LKC & REP & INL & ITEMS & HASHES & INA & AAL).
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  unfold PSTR_STK in HSTK.
  set (pd := usp mod 32).
  assert (HP : pd = 0 \/ pd = 16) by (unfold pd; clear - SPA; Z.div_mod_to_equations; lia).
  assert (HPM : usp mod 32 = pd) by reflexivity.
  assert (ERB : ps_RB sp = usp + -160 - pd) by reflexivity. clearbody pd.
  set (len := Z.of_nat (length str)) in *. assert (Hl0 : 1 <= len) by (unfold len; destruct str; [congruence| cbn [length]; lia]).
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 704 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLOI : SEGTOP_A <= lo) by (unfold SEGTOP_A, STACK_WIN in *; lia).
  set (usp1 := usp + -160 - pd) in *.
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & UAR & UT).

  (* [comment removed for export] *)
  pose proof (ps_w0 ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pd PPI_CTX (nmz nm) 1 S
                HP HPM ltac:(unfold PPI_CTX; lia) ltac:(destruct nm; cbn [nmz]; lia) ltac:(lia) ltac:(unfold SEGTOP_A in *; lia)
                ST ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia) UT SHC UAR MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (a1' & a2' & j8 & m1 & -> & MU1 & WM1 & MI1 & FR1 & GAP1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, GAP1, ST1, Hc1'. fold usp1 in GAP1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 160 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 160 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  (* [comment removed for export] *)
  apply (SM0 Σ PMc (Z_to_bv 64 SITE_ps_smalloc) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 64) a1' a2' (Z_to_bv 64 S) a4 a5 a6 a7
           s2 (Z_to_bv 64 PPI_CTX) s4 (Z_to_bv 64 S) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (nmz nm)) (Z_to_bv 64 1) s9 s10 s11 t3 t4 t5 t6 F fc m1 lo FDO MST ltac:(left; reflexivity) eq_refl
           Hfr ltac:(clear - Hcr; lia) ART1 MI1).
  { unfold call_ok. rewrite EU1. split; [exact ST1|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|].
    fold usp in SPA. clear - SPA HP HPM. Z.div_mod_to_equations. lia. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & f & Hc2 & FRS1 & LV1 & SP1 & CR1 & F0 & F64 & FU & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WF2 & WS2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_ps_smalloc) in Hc2' by (unfold SITE_ps_smalloc; lia).
  assert (INF : In (f, 0%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  pose proof (af_frames_range RT AF Σ1 m2 f 0%nat ART2 INF) as (_ & FLO & _ & PF).
  pose proof (af_frames_align RT AF Σ1 m2 f 0%nat ART2 INF) as (_ & FIMG).
  pose proof (af_frames_hi RT AF Σ1 m2 f 0%nat ART2 INF) as FSH.
  pose proof (proj1 (af_fshadow_apart RT AF Σ1 m2 f 0%nat ART2 INF)) as SLF.
  rewrite SP1 in FLO. change (fs_size 0) with 64 in FLO, FSH, FU, WF2, WS2, PF, SLF. change (64 - 8) with 56 in WF2. change (64 / 8) with 8 in WS2.
  unfold shad, SHB in WS2. unfold SEGTOP_A in FIMG.
  assert (SHF : shad (f + 64) = shad f + 8) by (replace (f + 64) with (f + 64 * 1) by lia; rewrite (shad_add64 f 1 F64); lia).
  rewrite SHF in SLF. unfold shad, SHB in SLF.
  assert (AG2 : forall a n, usp1 <= a -> a + n <= USTACK_TOP -> agree_on (fun x => a <= x < a + n) m1 m2).
  { intros a n H1 H2 x Hx. cbv beta in Hx. apply PRES2. left. lia. }
  unfold ps_ftail in FR1. cl_keep FR1 AG2 WM2 FR2.
  assert (GAP2 : stk asegs m2 usp1 (usp + -160)).
  { apply (stk_agree_nw asegs m1 m2 _ _ GAP1). intros x Hx. cbv beta in Hx. apply PRES2. left. unfold USTACK_TOP in *. lia. }
  destruct (wr_at_rw_CB m2 f 56 WF2 ltac:(lia)) as (fj & FB2). destruct (wr_at_rw_CB m2 (f / 8 + 2147450880) 8 WS2 ltac:(lia)) as (sj & SB2).
  change (Z.to_nat 56) with 56%nat in FB2. change (Z.to_nat 8) with 8%nat in SB2.

  (* [comment removed for export] *)
  pose proof (ps_w1a sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s2 (Z_to_bv 64 PPI_CTX) s4 (Z_to_bv 64 S) (Z_to_bv 64 (nmz nm)) (Z_to_bv 64 1) s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2
                ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 f lo pd j8 fj sj
                HP F0 F64 FIMG ltac:(lia) ltac:(destruct FSH; [left | right]; lia) ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia)
                FR2 GAP2 ST2 FB2 SB2 MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (j0 & hj & m3 & -> & MU3 & WM3 & MI3 & FR3 & GAP3 & ST3 & FFC3 & FFS3) & Hc3'). clear Hc3.
  fold usp in MU3, FR3, GAP3, Hc3'. fold usp1 in GAP3, ST3, Hc3'.
  assert (ART3 : ART RT Σ1 m3).
  { apply (af_frame RT AF Σ1 m2 m3 (usp - 176) ART2 ltac:(rewrite SP1; lia)); [| exact WM3].
    intros a Ha. apply MU3. cbn [outside]. split; [| split; [| split; [| exact I]]]; intros Hin; apply Ha.
    - apply (acl_frame _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; lia].
    - apply (acl_fshadow _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; rewrite SHF; unfold shad, SHB; lia].
    - apply acl_stack. unfold USTACK_TOP in *. lia. }

  (* [comment removed for export] *)
  assert (NFR : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) usp x -> ~ (f <= x < f + 64) /\ ~ (f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 8)).
  { intros x Hx. destruct (newframe_apart RT AF Σ Σ1 m2 f 0%nat usp _ ART2 FRS1 LV1 SP1 ltac:(lia) Hx) as (N1 & N2).
    change (fs_size 0) with 64 in N1, N2. rewrite SHF in N2. unfold shad, SHB in N2. exact (conj N1 N2). }
  assert (NSTK : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) usp x -> usp <= x \/ x < usp - 704).
  { intros x Hx. exact (cl_split RT AF Σ m usp 704 _ ART0 ltac:(lia) ltac:(lia) Hx). }
  assert (A03 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> m3 x = m x).
  { intros x Hx. destruct (NFR _ Hx) as (N1 & N2). pose proof (NSTK _ Hx) as N3.
    rewrite (MU3 x ltac:(cbn [outside]; clear - N1 N2 N3; lia)).
    rewrite (PRES2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; clear - HP; lia])).
    apply MU1. cbn [outside]. clear - N3. lia. }
  assert (WM03 : wmono asegs m m3) by exact (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 WM3)).

  assert (AGL03 : forall p n, In (p, n) (rt_live RT Σ) -> agree_on (fun x => p <= x < p + n) m m3).
  { intros p n Hin x Hx. cbv beta in Hx. apply A03. exact (acl_live _ _ _ p n _ Hin Hx). }
  assert (BLK : forall p n, In (p, n) (rt_live RT Σ) -> 1 <= n <= 64512 ->
            acc asegs m3 p n /\ 0 < p /\ p + n <= lo /\ 0x10007fff8000 <= p /\ p + n <= 2 ^ 47 /\ (p + n <= f \/ f + 64 <= p)).
  { intros p n Hin Hn. assert (Hin1 : In (p, n) (rt_live RT Σ1)) by (rewrite LV1; exact Hin).
    pose proof (af_live_range RT AF Σ1 m3 p n ART3 Hin1) as (P0 & P1 & _). rewrite SP1 in P1.
    pose proof (afp_live_hi RT GOBJ AFP Σ1 m3 p n ART3 Hin1 ltac:(lia)) as PH. pose proof (afp_live_mem RT GOBJ AFP Σ1 m3 p n ART3 Hin1 ltac:(lia)) as [_ PM].
    split; [exact (proj2 (af_acc_live RT AF Σ1 m3 p n ART3 Hin1))|]. destruct (PF p n Hin1); lia. }
  destruct (BLK ps 48 INPS ltac:(lia)) as (PSA & PS0 & PSLO & PSHI & PSTOP & PSF).
  destruct (BLK pk 40 INPK ltac:(lia)) as (PKA & PK0 & PKLO & PKHI & PKTOP & PKF).
  assert (PSC3 : rw_cells asegs m3 ps (psd_cells pk pl1 pl2 ni vi pq1 pq2)).
  { apply (rw_cells_agree asegs m m3 _ _ PSC); [| exact WM03]. eapply agree_sub; [exact (AGL03 ps 48 INPS)|]. unfold psd_cells. cbn [cells_size csize Nat.add]. intros x Hx. lia. }
  assert (LKC3 : rw_cells asegs m3 pk (mutex_cells z64 z64)).
  { apply (rw_cells_agree asegs m m3 _ _ LKC); [| exact WM03]. eapply agree_sub; [exact (AGL03 pk 40 INPK)|]. unfold mutex_cells. cbn [cells_size csize Nat.add]. intros x Hx. lia. }
  assert (CELL3 : rw_cells asegs m3 CTX_PSD [C8 (Z_to_bv 64 ps)]).
  { apply (rw_cells_agree asegs m m3 _ _ CELL); [| exact WM03]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply A03. apply acl_static.
    unfold CTX_PSD in Hx. apply client_static_intro. lia. }

  set (t := t_of nm pl1 pl2) in *.
  assert (INL0 : forall x, In x (plh_L t B bks) -> In x (rt_live RT Σ)) by (intros x Hx; exact (INL _ Hx)).
  assert (AGT03 : agree_on (plh_fp t B bks) m m3).
  { intros x [Hx|[Hx|(n & Hn & Hx)]]; apply A03.
    - exact (acl_live _ _ _ t 104 _ (INL0 _ ltac:(left; reflexivity)) Hx).
    - exact (acl_live _ _ _ B 128 _ (INL0 _ ltac:(right; left; reflexivity)) Hx).
    - exact (acl_live _ _ _ (fst n) 24 _ (INL0 _ (plh_L_node t B bks n Hn)) Hx). }
  pose proof (plh_rep_agree m m3 t B items bks REP AGT03) as REP3.
  assert (INL1 : incl (plh_L t B bks) (rt_live RT Σ1)) by (rewrite LV1; exact INL).
  destruct (plh_live_facts RT GOBJ AF AFP Σ1 m3 t B items bks lo ART3 REP3 INL1 ltac:(rewrite SP1; exact LOW))
    as ((ACL & L0 & LAL8 & LLO & LHI & LTOP) & (ACB & B0 & BAL8 & BLO & BHI & BTOP) & NODESF & APLB & APN & APNN).
  destruct (BLK t 104 (INL0 _ ltac:(left; reflexivity)) ltac:(lia)) as (_ & _ & _ & _ & _ & LHF).
  destruct (BLK B 128 (INL0 _ ltac:(right; left; reflexivity)) ltac:(lia)) as (_ & _ & _ & _ & _ & BF).
  assert (NODES3 : forall n, In n (concat bks) -> acc asegs m3 (fst n) 24 /\ 0 < fst n /\ fst n + 24 <= lo /\ (fst n + 24 <= f \/ f + 64 <= fst n) /\ (fst n + 24 <= pk \/ pk + 40 <= fst n)).
  { intros n Hn. destruct (BLK (fst n) 24 (INL0 _ (plh_L_node t B bks n Hn)) ltac:(lia)) as (X1 & X2 & X3 & _ & _ & X6).
    split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X6|].
    pose proof (live_ne_apart2 RT AF Σ m (fst n, 24) (pk, 40) ART0 (INL0 _ (plh_L_node t B bks n Hn)) INPK ltac:(intros E; injection E; lia)) as X. cbn [fst snd] in X. exact X. }
  pose proof (live_ne_apart2 RT AF Σ m (ps, 48) (t, 104) ART0 INPS (INL0 _ ltac:(left; reflexivity)) ltac:(intros E; injection E; lia)) as PSLH. cbn [fst snd] in PSLH.
  pose proof (live_ne_apart2 RT AF Σ m (pk, 40) (t, 104) ART0 INPK (INL0 _ ltac:(left; reflexivity)) ltac:(intros E; injection E; lia)) as PKLH. cbn [fst snd] in PKLH.
  pose proof (live_ne_apart2 RT AF Σ m (ps, 48) (pk, 40) ART0 INPS INPK ltac:(intros E; injection E; lia)) as PSPK. cbn [fst snd] in PSPK.
  pose proof (live_ne_apart2 RT AF Σ m (pk, 40) (B, 128) ART0 INPK (INL0 _ ltac:(right; left; reflexivity)) ltac:(intros E; injection E; lia)) as PKB. cbn [fst snd] in PKB.
  (* [comment removed for export] *)
  assert (LENS : Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack)) = len + 1 + Z.of_nat (length slack)) by (rewrite length_app; cbn [length]; unfold len; lia).
  assert (BYT : forall mm : mem, mem_inv asegs mm -> bytes_at asegs mm S (str ++ Z_to_bv 8 0 :: slack)).
  { intros mm MIm. apply ro_bytes_at; [exact MIm | lia | rewrite LENS; unfold SEGTOP_A in *; lia | exact ROB]. }
  assert (BYS : forall mm : mem, mem_inv asegs mm -> bytes_at asegs mm S (str ++ [Z_to_bv 8 0])).
  { intros mm MIm. pose proof (BYT mm MIm) as X. change (str ++ Z_to_bv 8 0 :: slack) with (str ++ [Z_to_bv 8 0] ++ slack) in X. rewrite app_assoc in X.
    exact (proj1 (proj1 (bytes_at_app asegs mm S _ _) X)). }
  assert (CHK : forall (Σx : rts RT) (mx : mem) (spx : word), ART RT Σx mx -> checked_src RT Σx mx spx lo S (len + 1)).
  { intros Σx mx spx ARTx. split; [intros _; split | left; unfold SEGTOP_A in *; lia].
    - exact (afp_acc_global RT GOBJ AFP Σx mx b sz S (len + 1) ARTx HG Hbs ltac:(lia)).
    - right; right; right. unfold SEGTOP_A in *. lia. }
  pose proof (afp_gsh_byte RT GOBJ AFP Σ1 m3 _ _ (PPI_CTX + 168) ART3 GO_ctx ltac:(lia) ltac:(lia) ltac:(reflexivity)) as GSH3.

  assert (GSH3' : ro_cells asegs m3 2148974277 [C1 (Z_to_bv 8 0)]) by exact GSH3. clear GSH3.
  destruct (af_client_consts RT AF Σ1 m3 ART3) as (_ & SHC3 & _ & _ & UT3).
  pose proof (af_acc_stack RT AF Σ1 m3 (usp1 - 144) 144 ART3 ltac:(rewrite SP1; unfold usp1; lia) ltac:(unfold usp1, USTACK_TOP in *; lia)) as ACCS3.
  pose proof (afp_acc_global RT GOBJ AFP Σ1 m3 b sz S (len + 1) ART3 HG Hbs ltac:(lia)) as SACC3.

  (* [comment removed for export] *)
  pose proof (ps_w1b sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 b3 b4 b5 b6 b7 s4 s9 u3 u4 u5 u6 F2 fc2 m3
                nm lo pd f S ps pk pl1 pl2 ni vi pq1 pq2 B items bks str j0 hj ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                HP ltac:(fold usp; fold usp1; clear - SPA HP HPM; unfold usp1; Z.div_mod_to_equations; lia) F0 F64 FIMG ltac:(lia) ltac:(destruct FSH; [left | right]; lia)
                ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia)
                UT3 SHC3 FR3 GAP3 ST3 ACCS3 FFC3 FFS3 CELL3 GSH3' PSC3 PSA PS0 PSAL PSLO PSHI PSF LKC3 PK0 PKAL PKLO PKHI PKF
                REP3 ACL L0 LLO LHF ACB B0 BLO BF NODES3 ltac:(lia) (BYS m3 MI3) NONUL NE ltac:(fold len; lia) SACC3 ltac:(fold len; unfold SEGTOP_A in *; lia) HASHES
                PSLH PKLH PSPK PKB MI3) as W2.

  fold usp usp1 t in W2.
  cl_lift W2 Hc3' c4 Hc4.
  destruct (ASTA_unpack RT Σ1 _ _ c4 Hc4) as (ms4 & (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & j4 & hj1 & hj2 & m4 & -> & MU4 & WM4 & MI4 & FR4 & GAP4 & ST4 & OFFC4 & NMC4 & TC4 & FFC4 & FFS4 & CELL4 & PSC4 & LKC4 & REP4) & Hc4'). clear Hc4.
  fold usp in MU4, FR4, GAP4, ST4, OFFC4, NMC4, TC4, Hc4'. fold usp1 in GAP4, ST4, OFFC4, NMC4, TC4, Hc4'. fold t in TC4, REP4, Hc4'.
  assert (ART4 : ART RT Σ1 m4).
  { apply (af_frame RT AF Σ1 m3 m4 (usp - 320) ART3 ltac:(rewrite SP1; lia)); [| exact WM4].
    intros a Ha. apply MU4. cbn [outside]. split; [| split; [| split; [| exact I]]]; intros Hin; apply Ha.
    - apply (acl_frame _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; lia].
    - apply acl_stack. unfold USTACK_TOP in *. clear - Hin HP NUM. lia.
    - apply (acl_live _ _ _ pk 40); [rewrite LV1; exact INPK| lia]. }
  (* [comment removed for export] *)
  assert (A04 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> outside [(pk + 4, pk + 8)] (bv_unsigned x) -> m4 x = m x).
  { intros x Hx Ho. destruct (NFR _ Hx) as (N1 & N2). pose proof (NSTK _ Hx) as N3. cbn [outside] in Ho.
    rewrite (MU4 x ltac:(cbn [outside]; clear - N1 N3 Ho HP; lia)). exact (A03 x Hx). }
  assert (WM04 : wmono asegs m m4) by exact (wmono_trans asegs _ _ _ WM03 WM4).

  (* [comment removed for export] *)
  assert (CO4 : call_ok RT Σ1 m4 (Z_to_bv 64 usp1) lo).
  { unfold call_ok. rewrite EU1, SP1. split; [exact ST4|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|].
    fold usp in SPA. clear - SPA HP HPM. Z.div_mod_to_equations. lia. }
  apply (SLC Σ1 PMc (Z_to_bv 64 SITE_ps_strlen) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) v0 v1 v2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 S) d1 d2 d3 d4 d5 d6 d7
           (Z_to_bv 64 f) (Z_to_bv 64 ps) (Z_to_bv 64 (Z.shiftr ps 3 + 2147450880)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) (Z_to_bv 64 (nmz nm)) (Z_to_bv 64 t)
           (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) v3 v4 v5 v6 F2 fc2 m4 S str slack lo FDO MST eq_refl (BYT m4 MI4) NONUL ltac:(fold len; lia) SLK
           ltac:(unfold SEGTOP_A in *; lia) ltac:(left; fold len; unfold SEGTOP_A in *; lia) ltac:(fold len; exact (CHK Σ1 m4 _ ART4)) ART4 MI4 CO4).
  { exact Hc4'. }
  clear Hc4'. intros c5 Hc5.
  destruct (ASTA_unpack RT Σ1 _ _ c5 Hc5) as (ms5 & (m5 & RS5 & (ART5 & MI5 & WM5 & ST5) & PRES5 & _) & Hc5'). clear Hc5.
  destruct RS5 as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F5 & fc5 & ->).
  rewrite EU1 in ST5, PRES5. rewrite (ret_pc_even SITE_ps_strlen) in Hc5' by (unfold SITE_ps_strlen; lia).
  fold len in Hc5'.

  (* [comment removed for export] *)
  pose proof (ps_w8 (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 sp (Z_to_bv 64 usp1) e1 e2 e3 e4 e5 e6 e7
                (Z_to_bv 64 f) (Z_to_bv 64 ps) (Z_to_bv 64 (Z.shiftr ps 3 + 2147450880)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) (Z_to_bv 64 (nmz nm)) (Z_to_bv 64 t)
                (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) w3 w4 w5 w6 F5 fc5 m5 len ltac:(lia) MI5) as W8.
  cl_lift W8 Hc5' c6 Hc6.
  destruct (ASTA_unpack RT Σ1 _ _ c6 Hc6) as (ms6 & -> & Hc6'). clear Hc6.
  (* [comment removed for export] *)
  assert (AG5 : forall a k, usp1 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m4 m5).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES5; [left; lia | lia]. }
  unfold ps_ftail in FR4. cl_keep FR4 AG5 WM5 FR5.
  assert (A05 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> outside [(pk + 4, pk + 8)] (bv_unsigned x) -> m5 x = m x).
  { intros x Hx Ho. rewrite (PRES5 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [rewrite LV1; auto | rewrite FRS1; intros e' He'; right; exact He' | unfold usp1; clear - HP; lia]) ltac:(lia)).
    exact (A04 x Hx Ho). }
  assert (AGS05 : agree_on (fun x => usp <= x < USTACK_TOP) m m5).
  { intros a Ha. cbv beta in Ha. apply A05; [left; exact Ha|]. cbn [outside]. split; [clear - Ha PKLO NUM HSTK; unfold RT_STACK in *; lia| exact I]. }
  assert (FRR5 : rw_cells asegs m5 (usp - 16) [C8 s0; C8 ra]).
  { lazymatch type of FR5 with rw_cells _ _ _ [?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10; ?c11; ?c12; ?c13; ?c14] =>
      pose proof (rw_cells_skip m5 _ [c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12] [c13; c14] FR5) as X end.
    cbn [cells_size csize Nat.add] in X. replace (usp + -160 + Z.of_nat 144) with (usp - 16) in X by lia. exact X. }
  destruct (cl_chain_call (rt_cg RT Σ) e_property_string e_CRYPTO_malloc SITE_ps_malloc m m5 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH _ ltac:(left; reflexivity)) (proj2 CGH _ ltac:(left; reflexivity)) UWC AGS05 FRR5 ltac:(rewrite EU1; fold usp; unfold usp1; clear - HP; lia) SPT) as (CTX5 & UWC5).
  assert (ENV5 : cl_env m5 lb canary).
  { apply (cl_env_agree m m5 lb canary ENV). intros a Ha. apply A05; [apply acl_static; exact (cl_cell_static _ Ha)|].
    cbn [outside]. pose proof (client_static_range _ (cl_cell_static _ Ha)) as CR. unfold SEGTOP_A in CR. split; [clear - CR PKHI; lia| exact I]. }

  (* [comment removed for export] *)
  apply (C_CM Σ1 PMc (Z_to_bv 64 SITE_ps_malloc) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 (len + 16)) (Z_to_bv 64 PS_FILE) (Z_to_bv 64 129) e3 e4 e5 e6 e7
           (Z_to_bv 64 f) (Z_to_bv 64 ps) (Z_to_bv 64 (Z.shiftr ps 3 + 2147450880)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) (Z_to_bv 64 (nmz nm)) (Z_to_bv 64 len)
           (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) w3 w4 w5 w6 F5 fc5 m5 (len + 16) lo (bv_unsigned ra :: outer) lb canary FDO MST eq_refl eq_refl ltac:(lia) ART5 MI5).
  { unfold call_ok. rewrite EU1, SP1. split; [exact ST5|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|].
    fold usp in SPA. clear - SPA HP HPM. Z.div_mod_to_equations. lia. }
  { rewrite EU1. unfold usp1, RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ps_malloc) by (unfold SITE_ps_malloc; lia). rewrite CG1. exact CTX5. }
  { exact UWC5. }
  { rewrite CG1. clear - CGH. unfold PSTR_SITES, PSTR_CALLS in CGH. split; intros x Hx; [apply (proj1 CGH)| apply (proj2 CGH)]; cbn [In app] in Hx |- *; tauto. }
  { rewrite LV1. lia. }
  { rewrite CR1. unfold mcost. destruct (Z.leb_spec (len + 16) 64512); lia. }
  { exact ENV5. }
  { exact Hc6'. }
  clear Hc6'. intros c7 (Σ2 & pn & Hc7 & LV2 & FRS2 & SP2 & CR2 & Q0 & Q16 & QU & CG2).
  destruct (ASTA_unpack RT Σ2 _ _ c7 Hc7) as (ms7 & (m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & ENV6 & WRQ & ACQ) & Hc7'). clear Hc7.
  destruct RS6 as (x0 & x1 & x2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & x3 & x4 & x5 & x6 & F6 & fc6 & ->).
  rewrite EU1 in ST6, PRES6. rewrite (ret_pc_even SITE_ps_malloc) in Hc7' by (unfold SITE_ps_malloc; lia).

  assert (INQ2 : In (pn, len + 16) (rt_live RT Σ2)) by (rewrite LV2; left; reflexivity).
  pose proof (af_live_range RT AF Σ2 m6 pn (len + 16) ART6 INQ2) as (_ & QLO & QI). rewrite SP2, SP1 in QLO.
  pose proof (afp_live_hi RT GOBJ AFP Σ2 m6 pn (len + 16) ART6 INQ2 ltac:(lia)) as QHI.
  (* [comment removed for export] *)
  pose proof (ps_w9 (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) x0 x1 x2 sp (Z_to_bv 64 usp1) g1 g2 g3 g4 g5 g6 g7
                (Z_to_bv 64 f) (Z_to_bv 64 ps) (Z_to_bv 64 (Z.shiftr ps 3 + 2147450880)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) (Z_to_bv 64 (nmz nm))
                (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) x3 x4 x5 x6 F6 fc6 m6 len pn S ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(clear - Q16; Z.div_mod_to_equations; lia) eq_refl MI6) as W9.
  cl_lift W9 Hc7' c8 Hc8.
  destruct (ASTA_unpack RT Σ2 _ _ c8 Hc8) as (ms8 & -> & Hc8'). clear Hc8.
  assert (SBL : Z.of_nat (length (str ++ [Z_to_bv 8 0])) = len + 1) by (rewrite length_app; cbn [length]; unfold len; lia).
  assert (CO6 : call_ok RT Σ2 m6 (Z_to_bv 64 usp1) lo).
  { unfold call_ok. rewrite EU1, SP2, SP1. split; [exact ST6|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|].
    fold usp in SPA. clear - SPA HP HPM. Z.div_mod_to_equations. lia. }
  apply (MCP Σ2 PMc (Z_to_bv 64 SITE_ps_memcpy) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) x0 x1 x2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 (pn + 12)) (Z_to_bv 64 S) (Z_to_bv 64 (len + 1))
           g3 g4 g5 g6 g7 (Z_to_bv 64 f) (Z_to_bv 64 ps) (Z_to_bv 64 (Z.shiftr ps 3 + 2147450880)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) (Z_to_bv 64 pn) (Z_to_bv 64 len)
           (Z_to_bv 64 (pn + 12)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) x3 x4 x5 x6 F6 fc6 m6 (pn + 12) S (str ++ [Z_to_bv 8 0]) lo FDO MST eq_refl eq_refl
           ltac:(rewrite SBL; reflexivity) ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold SEGTOP_A in *; lia) ltac:(rewrite SBL; lia) (BYS m6 MI6)).
  { rewrite SBL. exact (CHK Σ2 m6 _ ART6). }
  { rewrite SBL. exact (live_checked_dst RT AF Σ2 m6 _ pn (len + 16) (pn + 12) (len + 1) ART6 INQ2 ltac:(lia) ltac:(lia) ltac:(lia)). }
  { rewrite SBL. unfold SEGTOP_A in *. right. lia. }
  { exact ART6. } { exact MI6. } { exact CO6. }
  { exact Hc8'. }
  clear Hc8'. intros c9 Hc9.
  destruct (ASTA_unpack RT Σ2 _ _ c9 Hc9) as (ms9 & (m7 & RS7 & (ART7 & MI7 & WM7 & ST7) & PRES7 & CPY7) & Hc9'). clear Hc9.
  destruct RS7 as (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & F7 & fc7 & ->).
  rewrite EU1 in ST7, PRES7. rewrite SBL in PRES7. rewrite (ret_pc_even SITE_ps_memcpy) in Hc9' by (unfold SITE_ps_memcpy; lia).

  (* [comment removed for export] *)
  assert (A47 : forall x : word, aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp1 (bv_unsigned x) -> outside [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] (bv_unsigned x) -> m7 x = m4 x).
  { intros x Hx Ho.
    pose proof (newchunk_apart RT AF Σ1 Σ2 m6 pn (len + 16) usp1 _ ART6 LV2 FRS2 SP2 ltac:(rewrite SP1; unfold usp1; lia) ltac:(lia) Hx) as NQ.
    rewrite (PRES7 x ltac:(rewrite LV2, FRS2; apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e' He'; right; exact He' | auto | lia]) ltac:(clear - NQ; lia)).
    rewrite (PRES6 x Hx Ho). apply PRES5; [exact Hx| lia]. }
  assert (WM47 : wmono asegs m4 m7) by exact (wmono_trans asegs _ _ _ WM5 (wmono_trans asegs _ _ _ WM6 WM7)).
  assert (NLAT : forall x, usp1 - 704 <= x \/ 0x10007fff8000 <= x -> outside [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] x).
  { intros x Hx. cbn [outside]. unfold G_ALLOW_CUST. split; [unfold usp1, RT_STACK in *; clear - Hx HSTK NUM HP; lia| exact I]. }
  assert (AGS47 : forall a k, usp1 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m4 m7).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply A47; [left; lia| apply NLAT; left; lia]. }
  assert (AGF47 : forall a k, (f <= a /\ a + k <= f + 56) \/ (f / 8 + 2147450880 <= a /\ a + k <= f / 8 + 2147450880 + 8) -> agree_on (fun x => a <= x < a + k) m4 m7).
  { intros a k H x Hx. cbv beta in Hx. pose proof (div8_facts f) as Q1. destruct H as [H|H].
    - apply A47; [apply (acl_frame _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; lia]|]. cbn [outside]. unfold G_ALLOW_CUST. split; [clear - H Hx FIMG; lia| exact I].
    - apply A47; [apply (acl_fshadow _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; rewrite SHF; unfold shad, SHB; lia]|]. cbn [outside]. unfold G_ALLOW_CUST. split; [clear - H Hx FIMG Q1; lia| exact I]. }
  assert (AGL47 : forall p n, In (p, n) (rt_live RT Σ) -> n <= 64512 -> agree_on (fun x => p <= x < p + n) m4 m7).
  { intros p n Hin Hn x Hx. cbv beta in Hx. apply A47; [apply (acl_live _ _ _ p n); [rewrite LV1; exact Hin| exact Hx]|].
    apply NLAT. right. pose proof (afp_live_hi RT GOBJ AFP Σ m p n ART0 Hin Hn). lia. }
  cl_keep FR4 AGS47 WM47 FR7. cl_keep OFFC4 AGS47 WM47 OFFC7. cl_keep NMC4 AGS47 WM47 NMC7. cl_keep TC4 AGS47 WM47 TC7.
  assert (GAP7 : stk asegs m7 usp1 (usp + -160)).
  { apply (stk_agree_nw asegs m4 m7 _ _ GAP4). intros x Hx. cbv beta in Hx. apply A47; [left; unfold USTACK_TOP in *; clear - Hx NUM; lia| apply NLAT; left; lia]. }
  assert (FFC7 : rw_cells asegs m7 f [C8 (Z_to_bv 64 PS_MAGIC); C8 (Z_to_bv 64 PS_DESCR); C8 (Z_to_bv 64 e_property_string); CB 8 hj1; C8 (Z_to_bv 64 S); CB 16 hj2]).
  { apply (rw_cells_agree asegs m4 m7 _ _ FFC4); [| exact WM47]. apply AGF47. left. cbn [cells_size csize Nat.add]. lia. }
  assert (FFS7 : rw_cells asegs m7 (f / 8 + 2147450880) ps_shadow).
  { apply (rw_cells_agree asegs m4 m7 _ _ FFS4); [| exact WM47]. apply AGF47. right. unfold ps_shadow. cbn [cells_size csize Nat.add]. lia. }
  assert (CELL7 : rw_cells asegs m7 CTX_PSD [C8 (Z_to_bv 64 ps)]).
  { apply (rw_cells_agree asegs m4 m7 _ _ CELL4); [| exact WM47]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. unfold CTX_PSD in Hx.
    apply A47; [apply acl_static; apply client_static_intro; lia|]. cbn [outside]. unfold G_ALLOW_CUST. split; [lia| exact I]. }
  assert (PSC7 : rw_cells asegs m7 ps (psd_cells pk pl1 pl2 ni vi pq1 pq2)).
  { apply (rw_cells_agree asegs m4 m7 _ _ PSC4); [| exact WM47]. eapply agree_sub; [exact (AGL47 ps 48 INPS ltac:(lia))|]. unfold psd_cells. cbn [cells_size csize Nat.add]. intros x Hx. lia. }
  assert (LKC7 : rw_cells asegs m7 pk (mutex_cells z64 (Z_to_bv 64 16))).
  { apply (rw_cells_agree asegs m4 m7 _ _ LKC4); [| exact WM47]. eapply agree_sub; [exact (AGL47 pk 40 INPK ltac:(lia))|]. unfold mutex_cells. cbn [cells_size csize Nat.add]. intros x Hx. lia. }
  assert (AGT47 : agree_on (plh_fp t B bks) m4 m7).
  { intros x [Hx|[Hx|(n & Hn & Hx)]].
    - exact (AGL47 t 104 (INL0 _ ltac:(left; reflexivity)) ltac:(lia) x Hx).
    - exact (AGL47 B 128 (INL0 _ ltac:(right; left; reflexivity)) ltac:(lia) x Hx).
    - exact (AGL47 (fst n) 24 (INL0 _ (plh_L_node t B bks n Hn)) ltac:(lia) x Hx). }
  pose proof (plh_rep_agree m4 m7 t B items bks REP4 AGT47) as REP7.

  (* [comment removed for export] *)
  destruct (af_acc_live RT AF Σ2 m7 pn (len + 16) ART7 INQ2) as (WRQ7 & ACQ7).
  destruct (wr_at_rw_CB m7 pn 12 (wr_at_sub m7 pn (len + 16) pn 12 WRQ7 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (qj & QC7). change (Z.to_nat 12) with 12%nat in QC7.
  assert (INPS2 : In (ps, 48) (rt_live RT Σ2)) by (rewrite LV2, LV1; right; exact INPS).
  pose proof (wg_live_apart RT AF Σ2 m7 [] pn (len + 16) (rt_live RT Σ1) ps 48 ART7 LV2 ltac:(rewrite LV1; exact INPS)) as QPS.
  pose proof (W10 := ps_w10 sp gp (Z_to_bv 64 0xba3ef0) y0 y1 y2 h1 h2 h3 h4 h5 h6 h7 y3 y4 y5 y6 F7 fc7 m7 nm usp1 f ps pn pk pl1 pl2 ni vi pq1 pq2 len S qj
                ltac:(unfold usp1; lia) ltac:(unfold usp1, USTACK_TOP in *; lia) OFFC7 NMC7 Q0 ltac:(clear - Q16; Z.div_mod_to_equations; lia) QHI ltac:(unfold USTACK_TOP in *; lia) QC7
                (acc_sub asegs m7 pn (len + 16) pn 16 ACQ7 ltac:(lia) ltac:(lia))
                PS0 PSAL PSHI PSTOP PSC7 (proj2 (af_acc_live RT AF Σ2 m7 ps 48 ART7 INPS2)) NI VI ltac:(unfold USTACK_TOP in *; lia) ltac:(lia)
                ltac:(unfold usp1; clear - QLO HP NUM; lia) ltac:(unfold usp1; clear - PSLO HSTK HP; unfold RT_STACK in *; lia) ltac:(clear - QPS Hl0; lia) MI7).
  cl_lift W10 Hc9' c10 Hc10.
  destruct (ASTA_unpack RT Σ2 _ _ c10 Hc10) as (ms10 & (m8 & -> & MU8 & WM8 & MI8 & QC8 & PSC8) & Hc10'). clear Hc10.

  (* [comment removed for export] *)
  assert (INPK2 : In (pk, 40) (rt_live RT Σ2)) by (rewrite LV2, LV1; right; exact INPK).
  assert (INL2 : incl (plh_L t B bks) (rt_live RT Σ2)) by (intros x Hx; rewrite LV2, LV1; right; exact (INL _ Hx)).
  pose proof (wg_live_apart RT AF Σ2 m7 [] pn (len + 16) (rt_live RT Σ1) pk 40 ART7 LV2 ltac:(rewrite LV1; exact INPK)) as QPK.
  pose proof (af_frames_range RT AF Σ2 m7 f 0%nat ART7 ltac:(rewrite FRS2; exact INF)) as (_ & _ & _ & PF2). change (fs_size 0) with 64 in PF2.
  pose proof (proj1 (af_fshadow_apart RT AF Σ2 m7 f 0%nat ART7 ltac:(rewrite FRS2; exact INF))) as SLF2. change (fs_size 0) with 64 in SLF2. rewrite SHF in SLF2. unfold shad, SHB in SLF2.
  pose proof (PF2 pn (len + 16) INQ2) as QF. pose proof (SLF2 pn (len + 16) INQ2) as QSF. pose proof (SLF2 ps 48 INPS2) as PSSF.
  assert (ART8 : ART RT Σ2 m8).
  { apply (af_frame RT AF Σ2 m7 m8 usp1 ART7 ltac:(rewrite SP2, SP1; unfold usp1; lia)); [| exact WM8].
    intros a Ha. apply MU8. cbn [outside]. split; [| split; [| exact I]]; intros Hin; apply Ha.
    - apply (acl_live _ _ _ pn (len + 16)); [exact INQ2| lia].
    - apply (acl_live _ _ _ ps 48); [exact INPS2| lia]. }
  assert (KEEP8 : forall a cs, rw_cells asegs m7 a cs -> (a + Z.of_nat (cells_size cs) <= pn \/ pn + 12 <= a) -> (a + Z.of_nat (cells_size cs) <= ps + 24 \/ ps + 32 <= a) -> rw_cells asegs m8 a cs).
  { intros a cs H H1 H2. apply (rw_cells_transport asegs _ m7 m8 _ _ H MU8 WM8). cbn [disjoint_from]. clear - H1 H2. lia. }
  apply Hk. exists Σ2, f, pn, m8, y0, y1, y2, h4, h5, h6, h7, y3, y4, y5, y6, F7, fc7.
  split; [unfold ps_push_entry, entry_st; rewrite ERB; exact Hc10'|].
  split; [rewrite LV2, LV1; reflexivity|].
  unfold ps_mid. fold usp. rewrite ERB. fold t. fold len.
  split. { split; [exact ART8|]. split; [exact MI8|]. apply (stk_munch _ m7 m8 _ _ ST7 MU8 WM8). intros x Hx. cbn [outside]. clear - Hx QLO PSLO LOW Hl0. lia. }
  split. { split; [rewrite FRS2; exact FRS1|]. split; [rewrite SP2; exact SP1|]. split; [rewrite CG2; exact CG1|]. rewrite CR2, CR1. unfold mcost. destruct (Z.leb_spec (len + 16) 64512); lia. }
  split. { assert (ENV7 : cl_env m7 (Z_to_bv 8 1) canary).
           { apply (cl_env_pres_ex _ _ _ (pn + 12) (len + 1) m6 m7 _ canary ENV6 PRES7). intros x Hx. pose proof (client_static_range x (cl_cell_static x Hx)). unfold SEGTOP_A in *. lia. }
           apply (cl_env_seg _ m7 m8 _ canary ENV7 MU8).
           intros x Hx. pose proof (client_static_range x (cl_cell_static x Hx)) as CR. unfold SEGTOP_A in CR. cbn [outside]. clear - CR QHI PSHI. lia. }
  split. { intros _. exact (wmono_trans asegs _ _ _ WM04 (wmono_trans asegs _ _ _ WM47 WM8)). }
  assert (A08 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> outside (PS_WH ps pk) (bv_unsigned x) -> m8 x = m x).
  { intros x Hx Ho. unfold PS_WH in Ho. cbn [outside] in Ho. destruct Ho as (O1 & O2 & O3 & _).
    assert (Hx1 : aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp1 (bv_unsigned x)).
    { apply (aclient_mono _ _ _ _ _ _ _ Hx); [rewrite LV1; auto | rewrite FRS1; intros e' He'; right; exact He' | unfold usp1; clear - HP; lia]. }
    pose proof (newchunk_apart RT AF Σ1 Σ2 m6 pn (len + 16) usp1 _ ART6 LV2 FRS2 SP2 ltac:(rewrite SP1; unfold usp1; lia) ltac:(lia) Hx1) as NQ.
    rewrite (MU8 x ltac:(cbn [outside]; clear - NQ O2; lia)).
    rewrite (A47 x Hx1 ltac:(cbn [outside]; exact (conj O1 I))).
    exact (A04 x Hx ltac:(cbn [outside]; exact (conj O3 I))). }
  split; [exact A08|].
  split. { intros a Ha. cbv beta in Ha. apply A08; [left; exact Ha|]. unfold PS_WH, G_ALLOW_CUST. cbn [outside]. clear - Ha PKLO PSLO NUM HSTK. unfold RT_STACK in *. lia. }
  split. { split; [intros x Hx; rewrite LV2, LV1; right; exact Hx|]. split; [exact INPS2|]. split; [exact INPK2|]. split; [exact INL2| exact INQ2]. }
  split. { split; [exists j4; unfold ps_ftail; apply (KEEP8 _ _ FR7); cbn [cells_size csize Nat.add]; clear - QLO LOW Hl0 PSLO HSTK; unfold RT_STACK in *; lia|].
           split; [apply (stk_munch _ m7 m8 _ _ GAP7 MU8 WM8); intros x Hx; cbn [outside]; unfold usp1 in Hx; clear - Hx QLO LOW Hl0 PSLO HSTK HP; unfold RT_STACK in *; lia|].
           split; [apply (KEEP8 _ _ NMC7)| apply (KEEP8 _ _ TC7)]; cbn [cells_size csize Nat.add]; unfold usp1; clear - QLO LOW Hl0 PSLO HSTK HP; unfold RT_STACK in *; lia. }
  split. { split; [exists hj1, hj2; apply (KEEP8 _ _ FFC7); cbn [cells_size csize Nat.add]; clear - QF PSF Hl0; lia|].
           apply (KEEP8 _ _ FFS7); unfold ps_shadow; cbn [cells_size csize Nat.add]; clear - QSF PSSF Hl0; lia. }
  split; [| split; [intros p n Hin; exact (wg_live_apart RT AF Σ2 m7 [] pn (len + 16) (rt_live RT Σ1) p n ART7 LV2 ltac:(rewrite LV1; exact Hin))| exact (conj Q0 (conj Q16 QU))]].
  split; [apply (KEEP8 _ _ CELL7); cbn [cells_size csize Nat.add]; unfold CTX_PSD; clear - QHI PSHI; lia|].
  split; [exact PSC8|].
  split; [apply (KEEP8 _ _ LKC7); unfold mutex_cells; cbn [cells_size csize Nat.add]; clear - QPK PSPK Hl0; lia|].
  split. { apply (plh_rep_munch _ m7 m8 _ _ _ _ REP7 MU8). intros a Ha. cbn [outside].
           assert (X : exists p n, In (p, n) (plh_L t B bks) /\ p <= a < p + n).
           { destruct Ha as [Ha|[Ha|(n & Hn & Ha)]]; [exists t, 104; split; [left; reflexivity| lia]| exists B, 128; split; [right; left; reflexivity| lia]|
               exists (fst n), 24; split; [exact (plh_L_node t B bks n Hn)| lia]]. }
           destruct X as (p & n & Hin & Hpa).
           pose proof (wg_live_apart RT AF Σ2 m7 [] pn (len + 16) (rt_live RT Σ1) p n ART7 LV2 ltac:(rewrite LV1; exact (INL _ Hin))) as X1.
           assert (NE48 : (ps, 48) <> (p, n)) by (clear - Hin; intros E; destruct Hin as [H|[H|H]]; [congruence| congruence|]; apply in_map_iff in H; destruct H as (? & H & _); congruence).
           pose proof (live_ne_apart2 RT AF Σ m (ps, 48) (p, n) ART0 INPS (INL _ Hin) NE48) as X2. cbn [fst snd] in X2. clear - X1 X2 Hpa Hl0. lia. }
  split; [exact QC8|].
  apply (bytes_at_transport asegs _ m7 m8 _ _ CPY7 MU8). cbn [disjoint_from]. rewrite SBL. clear - QPS Hl0. lia.
Qed.

End CPstrH.
