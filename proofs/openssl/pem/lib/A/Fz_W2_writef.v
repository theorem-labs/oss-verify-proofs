(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_ckit Fz_env Fz_M_malloc Fz_M_secure Fz_W1_defs Fz_W1_misc Fz_W1_write0 Fz_W1_writec Fz_W1_writes Fz_W1_grow Fz_W1_puts Fz_W2_puts Fz_W2_write Fz_W2_writec Fz_W3_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

Section CBwriteF.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis SM0 : stack_malloc_contract RT 0.
Hypothesis GO_memmeth : GOBJ M_MEM_A 112.
Hypothesis GO_secmeth : GOBJ M_SECMEM_A 112.
(* [comment removed for export] *)
Hypothesis C_WFW : write_fitw_stmt RT.
Hypothesis C_WR : write_re_stmt RT.
Hypothesis C_WRS : write_res_stmt RT.
(* [comment removed for export] *)
Variables FZ_SITES FZ_CALLS : list (Z * Z).
Definition BW_SITES : list (Z * Z) := (SITE_bw_intern, FZ_BIO_WRITE) :: (SITE_bwi_bwc, e_bio_write_intern) :: (SITE_bwc_mw, e_bwrite_conv) :: WR_SITES ++ WRS_SITES.
Definition BW_CALLS : list (Z * Z) := (SITE_bw_intern, e_bio_write_intern) :: (SITE_bwi_bwc, e_bwrite_conv) :: (SITE_bwc_mw, e_mem_write) :: WR_CALLS ++ WRS_CALLS.
Hypothesis HCG : cg_sub BW_SITES BW_CALLS FZ_SITES FZ_CALLS.

(* [comment removed for export] *)
Theorem bio_write0_proof : bio_write0_stmt RT.
Proof.
  unfold bio_write0_stmt.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo canary n FDO MST -> -> HN ART0 MI0 CALL HSTK ENV.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA). set (usp := bv_unsigned sp) in *.
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 32 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  pose proof (bw0_walk ra sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo n
                ltac:(fold usp; unfold RT_STACK in *; clear - HSTK; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; clear - NUM; lia) ST HN MI0) as W0.
  fold usp in W0. unfold FZ_BIO_WRITE. cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & m1 & -> & MU1 & WM1 & MI1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, ST1.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 32 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 32 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  apply Hk. unfold apost. eapply ASTA_conseq; [exact Hc1'|]. cbv beta. intros ms <-. exists (Z_to_bv 64 0), m1.
  split; [exists y0, y1, y2, h1, h2, h3, h4, h5, h6, h7, y3, y4, y5, y6, F, fc; reflexivity|].
  split; [exact (conj ART1 (conj MI1 ST1))|]. split; [exact PR1|].
  split; [apply (cl_env_agree m m1 _ _ ENV); intros a Ha; apply MU1; cbn [outside]; split; [| exact I];
          pose proof (client_static_range _ (cl_cell_static _ Ha)); unfold SEGTOP_A, RT_STACK in *; clear - H HSTK LOW SP0R; unfold STACK_WIN in *; lia|].
  split; [reflexivity| exact WM1].
Qed.

Theorem bio_writeg_proof : bio_writeg_stmt RT FZ_SITES FZ_CALLS.
Proof.
  unfold bio_writeg_stmt.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer canary K BI meth len max off IN n src
    FDO MST -> -> -> -> MB GRN HN SRC0 LSRC SB ART0 MI0 CALL HSTK ENV SEC CTX UW CGH Hfr Hlv Hcr.
  destruct MB as (BM & fl & rrw & numw & padw & nr & nw & EBI & EBM & INBI & BIAL & ND & HM & BH & BW & FLOK & BT & INNER).
  destruct INNER as (rmaxw & INBB & BBAL & BBC & INBM & BMAL & INR & RAL & OFF0 & LEN & MAXB & KD).
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  unfold BWRITE_STACK in HSTK.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 736 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLOI : SEGTOP_A <= lo) by (unfold SEGTOP_A, STACK_WIN in *; lia).
  assert (HM' : meth = M_MEM_A \/ meth = M_SECMEM_A) by exact HM.
  pose proof (af_live_range RT AF Σ m BI 128 ART0 INBI) as (BI0 & BILO' & BISEG). assert (BILO : BI + 128 <= lo) by (clear - BILO' LOW; lia). clear BILO'.
  pose proof (af_live_range RT AF Σ m (k_bm K) 32 ART0 INBM) as (BM0 & BMLO' & BMSEG). assert (BMLO : k_bm K + 32 <= lo) by (clear - BMLO' LOW; lia). clear BMLO'.
  pose proof (af_live_range RT AF Σ m (k_rp K) 32 ART0 INR) as (R0 & RLO' & RSEG). assert (RLO : k_rp K + 32 <= lo) by (clear - RLO' LOW; lia). clear RLO'.
  pose proof (af_live_range RT AF Σ m (k_bb K) 16 ART0 INBB) as (BB0 & BBLO' & _). assert (BBLO : k_bb K + 16 <= lo) by (clear - BBLO' LOW; lia). clear BBLO'.
  (* [comment removed for export] *)
  unfold mbio_blocks in ND. rewrite <- EBI in ND.
  assert (LSRCZ : Z.of_nat (length src) = n) by (clear - LSRC HN; lia).
  assert (GRP : 0 < gr_n (len - off + n) /\ len - off + n <= gr_n (len - off + n)) by (pose proof (gr_n_gt (len - off + n) ltac:(clear - OFF0 HN; lia)); clear - H OFF0 HN; lia).
  assert (HN2 : 1 <= n < 2 ^ 31 - 1) by (clear - HN GRN GRP OFF0; lia).
  (* [comment removed for export] *)
  set (D0 := match k_d K with Some d => d | None => 0 end).
  assert (SB' : src_blk (rt_live RT Σ) IN n [BI; k_bm K; k_rp K; D0]).
  { destruct SB as [SBS | (p & k & Hp & P1 & P2 & NP)]; [left; exact SBS| right]. exists p, k. split; [exact Hp|]. split; [exact P1|]. split; [exact P2|].
    intros X. apply NP. unfold mbio_blocks. rewrite <- EBI. cbn [In app] in X |- *. subst D0.
    destruct X as [X|[X|[X|[X|[]]]]]; [left; exact X | do 2 right; left; exact X | do 3 right; left; exact X |].
    destruct (k_d K) as [d|]; [do 4 right; left; exact X | exfalso]. pose proof (af_live_range RT AF Σ m p k ART0 Hp) as (P0 & _). clear - X P0 P1 P2 HN. lia. }
  set (FP := [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (BI + 48, BI + 52); (k_bm K, k_bm K + 32); (k_rp K, k_rp K + 32)]
              ++ match k_d K with Some d => [(d, d + max)] | None => [] end).
  set (PQ := fun (Σ2 : rts RT) (m5 : mem) =>
         sec_off m5 /\ cl_env m5 (Z_to_bv 8 1) canary
         /\ exists (d' max' : Z) (rmaxw' : word), (max' = max \/ (max < len - off + n /\ max' = gr_n (len - off + n))) /\ len - off + n <= max' /\ 0 < max'
            /\ rw_cells asegs m5 (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) (fl - fl mod 16) rrw numw padw (Z_to_bv 64 (k_bb K)))
            /\ rw_cells asegs m5 (k_bb K) [C8 (Z_to_bv 64 (k_bm K)); C8 (Z_to_bv 64 (k_rp K))]
            /\ rw_cells asegs m5 (k_bm K) [C8 (Z_to_bv 64 (len - off + n)); C8 (Z_to_bv 64 d'); C8 (Z_to_bv 64 max'); C8 (Z_to_bv 64 (msec meth))]
            /\ rw_cells asegs m5 (k_rp K) (readp_cells (len - off + n) d' 0 rmaxw' (Z_to_bv 64 (msec meth)))
            /\ In (d', max') (rt_live RT Σ2) /\ In (BI, 128) (rt_live RT Σ2) /\ In (k_bb K, 16) (rt_live RT Σ2) /\ In (k_bm K, 32) (rt_live RT Σ2) /\ In (k_rp K, 32) (rt_live RT Σ2)
            /\ ~ In d' [BI; k_bb K; k_bm K; k_rp K]
            /\ puts_lists K (Some d') max max' (rt_live RT Σ) (rt_live RT Σ2)
            /\ rt_credit RT Σ - puts_cost (len - off) n max <= rt_credit RT Σ2 /\ rt_cg RT Σ2 = rt_cg RT Σ).
  assert (NOI : forall (W : list (Z * Z)) x, ~ outside W x -> exists lo hi, In (lo, hi) W /\ lo <= x < hi).
  { clear. induction W as [|[lo hi] W IH]; intros x Hx; [exfalso; apply Hx; exact I|]. cbn [outside] in Hx.
    destruct (Z_lt_le_dec x lo) as [L|L]; [| destruct (Z_lt_le_dec x hi) as [L'|L']; [exists lo, hi; split; [left; reflexivity| lia]|]].
    all: destruct (IH x) as (lo' & hi' & Hin & R); [intros X; apply Hx; split; [lia| exact X]| exists lo', hi'; split; [right; exact Hin| exact R]]. }
  assert (FPOK : forall x, ~ outside FP x -> aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) x).
  { intros x Hx. destruct (NOI FP x Hx) as (lo' & hi' & Hin & R). subst FP. apply in_app_iff in Hin. cbn [In] in Hin.
    destruct Hin as [[E|[E|[E|[E|[]]]]]|Hin]; try (injection E as <- <-).
    - apply acl_static. apply cl_cell_static. exists G_ALLOW_CUST, (G_ALLOW_CUST + 1). split; [cbn; do 4 right; left; reflexivity| exact R].
    - apply (acl_live _ _ _ BI 128); [exact INBI | clear - R; lia].
    - apply (acl_live _ _ _ (k_bm K) 32); [exact INBM | exact R].
    - apply (acl_live _ _ _ (k_rp K) 32); [exact INR | exact R].
    - destruct (k_d K) as [d|]; [| destruct Hin]. destruct KD as (junk & IND & _). destruct Hin as [E|[]]. injection E as <- <-.
      apply (acl_live _ _ _ d max); [exact IND | exact R]. }
  assert (FPBI : forall x, BI <= x < BI + 40 \/ BI + 72 <= x < BI + 128 -> outside FP x).
  { intros x Hx. subst FP.
    pose proof (live_ne_apart RT AF Σ m _ _ _ _ ART0 INBM INBI ltac:(intros E; injection E; lia)) as A1.
    pose proof (live_ne_apart RT AF Σ m _ _ _ _ ART0 INR INBI ltac:(intros E; injection E; lia)) as A2.
    assert (A0 : ~ (G_ALLOW_CUST <= x < G_ALLOW_CUST + 1)) by (unfold G_ALLOW_CUST, SEGTOP_A in *; clear - Hx BISEG; lia).
    destruct (k_d K) as [d|].
    - destruct KD as (junk & IND & _).
      assert (NDd : d <> BI) by (intros E; apply NoDup_cons_iff in ND as [X _]; apply X; clear - E; cbn [app In]; subst d; tauto).
      pose proof (live_ne_apart RT AF Σ m _ _ _ _ ART0 IND INBI ltac:(intros E; injection E; intros; exact (NDd ltac:(assumption)))) as A3.
      cbn [outside app]. clear - Hx A0 A1 A2 A3. lia.
    - cbn [outside app]. clear - Hx A0 A1 A2. lia. }
  assert (STAP : forall p k x, In (p, k) (rt_live RT Σ) -> client_static x -> ~ (p <= x < p + k)).
  { intros p k x Hin Hs. pose proof (af_live_range RT AF Σ m p k ART0 Hin) as (_ & _ & SG). pose proof (client_static_range x Hs). unfold SEGTOP_A in *. clear - SG H. lia. }
  pose proof (cg_has_of_sub _ _ _ _ _ CGH HCG) as CGB.
  assert (MC0 : 0 <= mcost (gr_n (len - off + n))) by (unfold mcost; destruct (gr_n (len - off + n) <=? 64512); clear - GRP; lia).
  assert (PC1 : 1 <= puts_cost (len - off) n max /\ (max < len - off + n -> puts_cost (len - off) n max = 1 + mcost (gr_n (len - off + n)))).
  { unfold puts_cost. destruct (max <? len - off + n) eqn:E; [apply Z.ltb_lt in E| apply Z.ltb_ge in E]; split; clear - E MC0; lia. }
  assert (MSPEC : mwrite_specB RT Σ PMc sp gp (Z_to_bv 64 TP_A) s0 ra usp lo BI IN n m FP PQ).
  { unfold mwrite_specB. intros Σ1 f pd m4 x0 x1 x2 y4 y5 y6 y7 x3 x4 x5 x6 F' fc' HP HPM LV1 FRS1 SP1 CR1 CG1 F0 F64 ART4 MI4 WM04 CO4 A04 FRR4 RECi RECc.
    set (usp1 := usp + -32 + -160 - pd) in *. set (spm := usp1 + -32) in *.
    assert (EUS : bv_unsigned (Z_to_bv 64 spm) = spm) by (apply unsigned_lit; unfold spm, usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; clear - NUM HSTK HP LOW SP0W; lia).
    assert (EUI : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp + -32) by (apply unsigned_lit; unfold USTACK_TOP, RT_STACK, STACK_WIN in *; clear - NUM HSTK LOW SP0W; lia).
    assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; clear - NUM HSTK HP LOW SP0W; lia).
    (* [comment removed for export] *)
    assert (AGlo : forall p q a k, In (p, q) (rt_live RT Σ) -> p <= a -> a + k <= p + q -> agree_on (fun x => a <= x < a + k) m m4).
    { intros p q a k Hin H1 H2 x Hx. cbv beta in Hx. pose proof (af_live_range RT AF Σ m p q ART0 Hin) as (_ & PL & _).
      apply A04; [apply (acl_live _ _ _ p q); [exact Hin| clear - Hx H1 H2; lia] | left; unfold RT_STACK, STACK_WIN in *; clear - Hx H2 PL LOW HSTK; lia]. }
    assert (AGst : forall x : word, client_static (bv_unsigned x) -> m4 x = m x).
    { intros x Hs. apply A04; [apply acl_static; exact Hs| left]. pose proof (client_static_range _ Hs). unfold SEGTOP_A, RT_STACK in *. clear - H HLOI HSTK. lia. }
    assert (BW4 : rw_cells asegs m4 (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 (k_bb K)))).
    { apply (rw_cells_agree asegs m m4 _ _ BW); [apply (AGlo BI 128); [exact INBI| lia| unfold bio_w1_cells; cbn [cells_size csize Nat.add]; lia] | exact WM04]. }
    assert (BBC4 : rw_cells asegs m4 (k_bb K) [C8 (Z_to_bv 64 (k_bm K)); C8 (Z_to_bv 64 (k_rp K))]).
    { apply (rw_cells_agree asegs m m4 _ _ BBC); [apply (AGlo (k_bb K) 16); [exact INBB| lia| cbn [cells_size csize Nat.add]; lia] | exact WM04]. }
    assert (ENV4 : cl_env m4 (Z_to_bv 8 1) canary) by (apply (cl_env_agree m m4 _ _ ENV); intros a Ha; apply AGst; exact (cl_cell_static _ Ha)).
    assert (SEC4 : sec_off m4) by (apply (sec_off_agree m m4 SEC); intros a Ha; apply AGst; rewrite Ha; exact sec_init_static).
    assert (SRC4 : bytes_at asegs m4 IN src).
    { apply (bytes_at_agree asegs m m4 _ _ SRC0). destruct SB as [SBS | (p & k & Hp & P1 & P2 & _)].
      - intros x Hx. cbv beta in Hx. apply AGst. rewrite LSRC in Hx. apply client_static_intro. right; left. clear - Hx SBS HN. lia.
      - apply (AGlo p k); [exact Hp| exact P1| rewrite LSRC; clear - P2 HN; lia]. }
    assert (SB1 : src_blk (rt_live RT Σ1) IN n [BI; k_bm K; k_rp K; D0]) by (rewrite LV1; exact SB').
    assert (INBI1 : In (BI, 128) (rt_live RT Σ1)) by (rewrite LV1; exact INBI).
    assert (INBB1 : In (k_bb K, 16) (rt_live RT Σ1)) by (rewrite LV1; exact INBB).
    assert (INBM1 : In (k_bm K, 32) (rt_live RT Σ1)) by (rewrite LV1; exact INBM).
    assert (INR1 : In (k_rp K, 32) (rt_live RT Σ1)) by (rewrite LV1; exact INR).
    assert (STK4 : lo + RT_STACK + 0x100 + 224 <= bv_unsigned (Z_to_bv 64 spm)) by (rewrite EUS; unfold spm, usp1; clear - HSTK HP; lia).
    pose proof CO4 as (ST4 & _ & _ & SPT4 & _).
    pose proof ND as ND'. apply NoDup_cons_iff in ND' as [NBI ND2]. apply NoDup_cons_iff in ND2 as [NBB ND3]. apply NoDup_cons_iff in ND3 as [NBM ND4]. apply NoDup_cons_iff in ND4 as [NR _].
    cbn [In app] in NBI, NBB, NBM, NR.
    assert (NEMR : k_bm K <> k_rp K) by (clear - NBM; intros E; apply NBM; rewrite E; cbn [In app]; destruct (k_d K); cbn [In]; tauto).
    (* [comment removed for export] *)
    assert (FPW : forall x, outside FP x -> match k_d K with Some d => ~ (d <= x < d + max) | None => True end
                             /\ ~ (BI + 48 <= x < BI + 52) /\ ~ (k_bm K <= x < k_bm K + 32) /\ ~ (k_rp K <= x < k_rp K + 32) /\ ~ (G_ALLOW_CUST <= x < G_ALLOW_CUST + 1)).
    { intros x Hx. subst FP. destruct (k_d K); cbn [outside app] in Hx; clear - Hx; tauto. }
    destruct (Z_lt_le_dec max (len - off + n)) as [GROW | FIT]; [| ]; swap 1 2.
    - (* [comment removed for export] *)
      destruct (k_d K) as [d|] eqn:EKD; [| exfalso; clear - KD FIT HN OFF0; lia].
      destruct KD as (junk & IND & MAXP & BMC & RC & LJ & DC).
      assert (INd1 : In (d, max) (rt_live RT Σ1)) by (rewrite LV1; exact IND).
      assert (NDd : ~ In d [BI; k_bb K; k_bm K; k_rp K]).
      { intros X. cbn [In] in X. destruct X as [E|[E|[E|[E|[]]]]]; [apply NBI| apply NBB| apply NBM| apply NR]; clear - E; cbn [In app]; subst d; tauto. }
      cbn [In] in NDd.
      assert (BMC4 : rw_cells asegs m4 (k_bm K) (bufmem_cells len d max (Z_to_bv 64 (msec meth)))).
      { apply (rw_cells_agree asegs m m4 _ _ BMC); [apply (AGlo (k_bm K) 32); [exact INBM| lia| cbn [cells_size csize Nat.add]; lia] | exact WM04]. }
      assert (RC4 : rw_cells asegs m4 (k_rp K) (readp_cells len d off rmaxw (Z_to_bv 64 (msec meth)))).
      { apply (rw_cells_agree asegs m m4 _ _ RC); [apply (AGlo (k_rp K) 32); [exact INR| lia| unfold readp_cells; cbn [cells_size csize Nat.add]; lia] | exact WM04]. }
      subst D0.
      eapply cps_conseq; [eapply (C_WFW Σ1 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' m4 lo BI (k_bb K) (k_bm K) (k_rp K) d len max off fl IN n
                              rrw numw padw rmaxw (Z_to_bv 64 (msec meth)) src FDO MST eq_refl eq_refl eq_refl eq_refl INBI1 BIAL BW4 FLOK INBB1 BBAL BBC4 INBM1 BMAL BMC4 INR1 RAL RC4
                              NEMR INd1 ltac:(clear - NDd; intros E; apply NDd; subst d; tauto) ltac:(clear - NDd; intros E; apply NDd; subst d; tauto) ltac:(clear - NDd; intros E; apply NDd; subst d; tauto) ltac:(clear - NDd; intros E; apply NDd; subst d; tauto)
                              OFF0 LEN FIT ltac:(clear - MAXB; lia) ltac:(clear - HN; lia) SRC4 LSRCZ SB1 ART4 MI4 CO4 ltac:(clear - STK4; lia))
                         | intros cc X; exact X |].
      cbv beta. intros cc POST. exists Σ1.
      split; [| split; [reflexivity| split; [reflexivity| split; [exact INBI1| intros p k Hp; left; exact Hp]]]].
      eapply ASTA_conseq; [exact POST|]. cbv beta. intros ms (m5 & RS & (ART5 & MI5 & WM5 & ST5) & PRES5 & BW5 & BMC5 & RC5). exists m5.
      rewrite EUS in ST5, PRES5.
      assert (P5 : forall x : word, aclient (rt_live RT Σ1) (rt_frames RT Σ1) spm (bv_unsigned x) -> outside FP (bv_unsigned x) -> m5 x = m4 x).
      { intros x Hx Ho. apply (PRES5 x Hx). pose proof (FPW _ Ho) as (W1 & W2 & W3 & W4 & W5). unfold WRF_W. cbn [outside]. clear - W1 W2 W3 W4. lia. }
      split; [exact RS|]. split; [exact ART5|]. split; [exact MI5|]. split; [exact ST5|]. split; [exact P5|].
      (* [comment removed for export] *)
      subst PQ. cbv beta.
      assert (P5s : forall x : word, client_static (bv_unsigned x) -> m5 x = m4 x).
      { intros x Hs. apply PRES5; [apply acl_static; exact Hs|]. unfold WRF_W. cbn [outside].
        pose proof (STAP _ _ _ INBI Hs). pose proof (STAP _ _ _ INBM Hs). pose proof (STAP _ _ _ INR Hs). pose proof (STAP _ _ _ IND Hs). clear - H H0 H1 H2. lia. }
      split; [apply (sec_off_agree m4 m5 SEC4); intros a Ha; apply P5s; rewrite Ha; exact sec_init_static|].
      split; [apply (cl_env_agree m4 m5 _ _ ENV4); intros a Ha; apply P5s; exact (cl_cell_static _ Ha)|].
      exists d, max, (Z_to_bv 64 max).
      split; [left; reflexivity|]. split; [exact FIT|]. split; [exact MAXP|]. split; [exact BW5|].
      split. { apply (rw_cells_agree_nw asegs m4 m5 _ _ BBC4). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
               apply PRES5; [apply (acl_live _ _ _ (k_bb K) 16); [exact INBB1 | clear - Hx; lia]|]. unfold WRF_W. cbn [outside].
               pose proof (live_ne_apart RT AF Σ m _ _ _ _ ART0 INBB INBI ltac:(intros E; injection E; clear; lia)).
               pose proof (live_ne_apart RT AF Σ m _ _ _ _ ART0 INBB INBM ltac:(intros E; injection E; clear; lia)).
               pose proof (live_ne_apart RT AF Σ m _ _ _ _ ART0 INBB INR ltac:(intros E; injection E; clear; lia)).
               pose proof (live_ne_apart RT AF Σ m _ _ _ _ ART0 INBB IND ltac:(intros E; injection E as E1 E2; apply NDd; clear - E1; subst d; cbn [In]; tauto)).
               pose proof (af_live_range RT AF Σ m _ _ ART0 INBB) as (_ & _ & BBSEG). unfold G_ALLOW_CUST, SEGTOP_A in *. clear - Hx H H0 H1 H2 BBSEG. lia. }
      split; [exact BMC5|]. split; [exact RC5|]. split; [exact INd1|]. split; [exact INBI1|]. split; [exact INBB1|]. split; [exact INBM1|]. split; [exact INR1|].
      split; [clear - NDd; cbn [In]; intuition|].
      split; [left; split; [exact (eq_sym EKD)| split; [reflexivity| exact LV1]]|].
      split; [rewrite CR1; clear - PC1; lia| exact CG1].
    - (* [comment removed for export] *)
      assert (WD : wdata_opt (rt_live RT Σ1) BI (k_bb K) (k_bm K) (k_rp K) D0 len max off
                   /\ rw_cells asegs m4 (k_bm K) (bufmem_cells len D0 max (Z_to_bv 64 (msec meth)))
                   /\ rw_cells asegs m4 (k_rp K) (readp_cells len D0 off rmaxw (Z_to_bv 64 (msec meth)))
                   /\ ~ In D0 [BI; k_bb K; k_bm K; k_rp K]
                   /\ (forall p q, In (p, q) (rt_live RT Σ) -> p = D0 -> q <= 0 \/ q = max)).
      { subst D0. destruct (k_d K) as [d|] eqn:EKD.
        - destruct KD as (junk & IND & MAXP & BMC & RC & LJ & DC).
          assert (NDd : ~ In d [BI; k_bb K; k_bm K; k_rp K]).
          { intros X. cbn [In] in X. destruct X as [E|[E|[E|[E|[]]]]]; [apply NBI| apply NBB| apply NBM| apply NR]; clear - E; cbn [In app]; subst d; tauto. }
          cbn [In] in NDd.
          split; [right; rewrite LV1; split; [exact IND|]; split; [clear - MAXP; lia|]; repeat split; clear - NDd; intros E; apply NDd; subst d; tauto|].
          split; [apply (rw_cells_agree asegs m m4 _ _ BMC); [apply (AGlo (k_bm K) 32); [exact INBM| lia| cbn [cells_size csize Nat.add]; lia] | exact WM04]|].
          split; [apply (rw_cells_agree asegs m m4 _ _ RC); [apply (AGlo (k_rp K) 32); [exact INR| lia| unfold readp_cells; cbn [cells_size csize Nat.add]; lia] | exact WM04]|].
          split; [exact NDd|].
          intros p q Hin E. subst p. destruct (Z.eq_dec q max) as [->|NEq]; [right; reflexivity| left].
          pose proof (live_ne_apart RT AF Σ m _ _ _ _ ART0 Hin IND ltac:(intros X; injection X; intros; exact (NEq ltac:(assumption)))) as AP.
          clear - AP MAXP. lia.
        - destruct KD as (MAX0 & BMC & RC).
          assert (LEN0 : len = 0 /\ off = 0) by (clear - MAX0 LEN OFF0; lia). destruct LEN0 as [LEN0 OFFZ]. subst max.
          split; [left; clear - LEN0 OFFZ; lia|].
          split; [apply (rw_cells_agree asegs m m4 _ _ BMC); [apply (AGlo (k_bm K) 32); [exact INBM| lia| cbn [cells_size csize Nat.add]; lia] | exact WM04]|].
          split. { rewrite LEN0, OFFZ. unfold readp_cells in RC |- *. replace (0 - 0) with 0 by lia. replace (0 + 0) with 0 by lia.
                   apply (rw_cells_agree asegs m m4 _ _ RC); [apply (AGlo (k_rp K) 32); [exact INR| lia| cbn [cells_size csize Nat.add]; lia] | exact WM04]. }
          split; [cbn [In]; clear - BI0 BB0 BM0 R0; lia|].
          intros p q Hin E. subst p. exfalso. pose proof (af_live_range RT AF Σ m 0 q ART0 Hin) as (Q0 & _). clear - Q0. lia. }
      destruct WD as (WDO & BMC4 & RC4 & NDd & DUQ). cbn [In] in NDd.
      (* [comment removed for export] *)
      set (outer' := SITE_bwi_bwc :: SITE_bw_intern :: bv_unsigned ra :: outer).
      assert (CTX1 : cg_ctx (rt_cg RT Σ1) e_mem_write (bv_unsigned (Z_to_bv 64 SITE_bwc_mw) :: outer') /\ uw_chain m4 (Z_to_bv 64 spm) (Z_to_bv 64 usp1) outer').
      { rewrite CG1. rewrite (unsigned_lit SITE_bwc_mw) by (unfold SITE_bwc_mw; clear; lia). subst outer'.
        destruct (cl_chain_call (rt_cg RT Σ) FZ_BIO_WRITE e_bio_write_intern SITE_bw_intern m m4 ra s0 sp (Z_to_bv 64 (usp + -32)) outer CTX
                    ltac:(apply (cg_has_site _ _ _ _ _ CGB); left; reflexivity) ltac:(apply (cg_has_call _ _ _ _ _ CGB); left; reflexivity) UW
                    ltac:(intros x Hx; cbv beta in Hx; apply A04; [apply acl_stack; exact Hx| right; clear - Hx; lia])
                    ltac:(fold usp; exact FRR4) ltac:(rewrite EUI; clear; lia) SPT) as [CTXa UWa].
        pose proof (cl_chain_call (rt_cg RT Σ) e_bio_write_intern e_bwrite_conv SITE_bwi_bwc m4 m4 (Z_to_bv 64 SITE_bw_intern) sp (Z_to_bv 64 (usp + -32)) (Z_to_bv 64 usp1) (bv_unsigned ra :: outer)) as CC2.
        rewrite (unsigned_lit SITE_bw_intern) in CC2 by (unfold SITE_bw_intern; clear; lia). rewrite EUI, EU1 in CC2.
        destruct (CC2 CTXa ltac:(apply (cg_has_site _ _ _ _ _ CGB); right; left; reflexivity) ltac:(apply (cg_has_call _ _ _ _ _ CGB); right; left; reflexivity) UWa
                    ltac:(intros x _; reflexivity) RECi ltac:(unfold usp1; clear - HP; lia) ltac:(fold usp; clear - SPT; lia)) as [CTXb UWb]. clear CC2.
        pose proof (cl_chain_call (rt_cg RT Σ) e_bwrite_conv e_mem_write SITE_bwc_mw m4 m4 (Z_to_bv 64 SITE_bwi_bwc) (Z_to_bv 64 (usp + -32)) (Z_to_bv 64 usp1) (Z_to_bv 64 spm) (SITE_bw_intern :: bv_unsigned ra :: outer)) as CC3.
        rewrite (unsigned_lit SITE_bwi_bwc) in CC3 by (unfold SITE_bwi_bwc; clear; lia). rewrite EU1, EUS in CC3.
        destruct (CC3 CTXb ltac:(apply (cg_has_site _ _ _ _ _ CGB); right; right; left; reflexivity) ltac:(apply (cg_has_call _ _ _ _ _ CGB); right; right; left; reflexivity) UWb
                    ltac:(intros x _; reflexivity) RECc ltac:(unfold spm; clear; lia) ltac:(unfold usp1, USTACK_TOP in *; clear - NUM HP; lia)) as [CTXc UWc]. clear CC3.
        exact (conj CTXc UWc). }
      destruct CTX1 as [CTX1 UW1].
        assert (CGW : cg_has (rt_cg RT Σ1) WR_SITES WR_CALLS) by (rewrite CG1; apply (cg_has_weaken _ _ _ _ _ CGB); vm_compute; reflexivity).
      assert (CGWS : cg_has (rt_cg RT Σ1) WRS_SITES WRS_CALLS) by (rewrite CG1; apply (cg_has_weaken _ _ _ _ _ CGB); vm_compute; reflexivity).
      assert (LVM : Z.of_nat (length (rt_live RT Σ1)) < LIVE_MAX) by (rewrite LV1; clear - Hlv; lia).
      assert (CRM : mcost (gr_n (len - off + n)) <= rt_credit RT Σ1) by (rewrite CR1; pose proof (proj2 PC1 GROW); clear - Hcr H; lia).
      assert (GRB : gr_n (len - off + n) <= 0x8000000) by (clear - GRN; lia).
      (* [comment removed for export] *)
      assert (POSTG : forall (cc : config) (flw : word),
        (exists (Σ' : rts RT) (q : Z),
          ASTA RT Σ' PMc (fun ms => exists m' : mem,
              mwrite_ret gp (Z_to_bv 64 TP_A) usp1 BI IN n (usp + -24) f (Z_to_bv 64 n) m' ms
              /\ rt_after_f RT Σ' (bv_unsigned (Z_to_bv 64 spm)) lo m4 m' /\ rt_pres_fp (live_remove D0 (rt_live RT Σ1)) (rt_frames RT Σ1) (bv_unsigned (Z_to_bv 64 spm)) (WRG_W BI (k_bm K) (k_rp K)) m4 m'
              /\ cl_env m' (Z_to_bv 8 1) canary
              /\ rw_cells asegs m' (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) (fl - fl mod 16) rrw numw padw (Z_to_bv 64 (k_bb K)))
              /\ rw_cells asegs m' (k_bm K) (bufmem_cells (len - off + n) q (gr_n (len - off + n)) flw)
              /\ rw_cells asegs m' (k_rp K) (readp_cells (len - off + n) q 0 (Z_to_bv 64 (gr_n (len - off + n))) flw)) cc
          /\ rt_live RT Σ' = (q, gr_n (len - off + n)) :: live_remove D0 (rt_live RT Σ1) /\ rt_frames RT Σ' = rt_frames RT Σ1 /\ rt_sp0 RT Σ' = rt_sp0 RT Σ1
          /\ rt_credit RT Σ' = rt_credit RT Σ1 - mcost (gr_n (len - off + n)) /\ 0 < q /\ q mod 16 = 0
          /\ q + gr_n (len - off + n) < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ1) ->
        flw = Z_to_bv 64 (msec meth) ->
        exists (Σ2 : rts RT),
          ASTA RT Σ2 PMc (fun ms => exists m5 : mem,
              mwrite_ret gp (Z_to_bv 64 TP_A) usp1 BI IN n (usp + -24) f (Z_to_bv 64 n) m5 ms
              /\ ART RT Σ2 m5 /\ mem_inv asegs m5 /\ stk asegs m5 lo spm
              /\ (forall x : word, aclient (rt_live RT Σ1) (rt_frames RT Σ1) spm (bv_unsigned x) -> outside FP (bv_unsigned x) -> m5 x = m4 x)
              /\ PQ Σ2 m5) cc
          /\ rt_frames RT Σ2 = rt_frames RT Σ1 /\ rt_sp0 RT Σ2 = rt_sp0 RT Σ1 /\ In (BI, 128) (rt_live RT Σ2)
          /\ (forall p k, In (p, k) (rt_live RT Σ1) -> In (p, k) (rt_live RT Σ2) \/ (forall x, p <= x < p + k -> ~ outside FP x))).
      { intros cc flw (Σ' & q & HAS & LV2 & FRS2 & SP2 & CR2 & Q0 & QAL & QU & CG2) EFL.
        rewrite EUS in HAS.
        assert (KEEPD : forall p k, In (p, k) (rt_live RT Σ1) -> p <> D0 -> In (p, k) (rt_live RT Σ')) by (intros p k Hp NE; rewrite LV2; right; apply live_remove_keep; [exact Hp| exact NE]).
        assert (INBI2 : In (BI, 128) (rt_live RT Σ')) by (apply KEEPD; [exact INBI1| clear - NDd; intros E; apply NDd; tauto]).
        assert (INBB2 : In (k_bb K, 16) (rt_live RT Σ')) by (apply KEEPD; [exact INBB1| clear - NDd; intros E; apply NDd; tauto]).
        assert (INBM2 : In (k_bm K, 32) (rt_live RT Σ')) by (apply KEEPD; [exact INBM1| clear - NDd; intros E; apply NDd; tauto]).
        assert (INR2 : In (k_rp K, 32) (rt_live RT Σ')) by (apply KEEPD; [exact INR1| clear - NDd; intros E; apply NDd; tauto]).
        assert (LVK : forall p k, In (p, k) (rt_live RT Σ1) -> In (p, k) (live_remove D0 (rt_live RT Σ1)) \/ (forall x, p <= x < p + k -> ~ outside FP x)).
        { intros p k Hp. destruct (Z.eq_dec p D0) as [E|NE]; [right| left; apply live_remove_keep; [exact Hp| exact NE]].
          rewrite LV1 in Hp. destruct (DUQ _ _ Hp E) as [LE| ->]; [intros x Hx; exfalso; clear - Hx LE; lia|]. subst p. intros x Hx Ho. pose proof (FPW _ Ho) as (W1 & _).
          subst D0. destruct (k_d K) as [d|]; [exact (W1 Hx)|]. destruct KD as (MAX0 & _). clear - Hx MAX0. lia. }
        assert (FPG : forall x, outside FP x -> outside (WRG_W BI (k_bm K) (k_rp K)) x).
        { intros x Ho. pose proof (FPW _ Ho) as (W1 & W2 & W3 & W4 & W5). unfold WRG_W. cbn [outside]. clear - W2 W3 W4 W5. lia. }
        exists Σ'.
        split; [| split; [exact FRS2| split; [exact SP2| split; [exact INBI2| intros p k Hp; destruct (LVK p k Hp) as [X|X]; [left; rewrite LV2; right; exact X| right; exact X]]]]].
        eapply ASTA_conseq; [exact HAS|]. cbv beta. intros ms (m5 & RS & (ART5 & MI5 & ST5) & PRES5 & ENV5 & BW5 & BMC5 & RC5). exists m5.
        assert (P5 : forall x : word, aclient (rt_live RT Σ1) (rt_frames RT Σ1) spm (bv_unsigned x) -> outside FP (bv_unsigned x) -> m5 x = m4 x).
        { intros x Hx Ho. apply PRES5; [exact (acl_keep _ _ _ _ FP _ LVK Hx Ho)| exact (FPG _ Ho)]. }
        assert (P5s : forall x : word, client_static (bv_unsigned x) -> bv_unsigned x <> G_ALLOW_CUST -> m5 x = m4 x).
        { intros x Hs NG. apply PRES5; [apply acl_static; exact Hs|]. unfold WRG_W. cbn [outside].
          pose proof (STAP _ _ _ INBI Hs). pose proof (STAP _ _ _ INBM Hs). pose proof (STAP _ _ _ INR Hs). clear - H H0 H1 NG. lia. }
        split; [exact RS|]. split; [exact ART5|]. split; [exact MI5|]. split; [exact ST5|]. split; [exact P5|].
        subst PQ. cbv beta.
        split; [apply (sec_off_agree m4 m5 SEC4); intros a Ha; apply P5s; [rewrite Ha; exact sec_init_static| rewrite Ha; unfold SEC_INIT, G_ALLOW_CUST; clear; lia]|].
        split; [exact ENV5|].
        exists q, (gr_n (len - off + n)), (Z_to_bv 64 (gr_n (len - off + n))).
        split; [right; split; [exact GROW| reflexivity]|]. split; [clear - GRP; lia|]. split; [clear - GRP; lia|]. split; [exact BW5|].
        split. { apply (rw_cells_agree_nw asegs m4 m5 _ _ BBC4). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
                 apply PRES5; [apply (acl_live _ _ _ (k_bb K) 16); [apply live_remove_keep; [exact INBB1| clear - NDd; intros E; apply NDd; tauto] | clear - Hx; lia]|].
                 unfold WRG_W. cbn [outside].
                 pose proof (live_ne_apart RT AF Σ m _ _ _ _ ART0 INBB INBI ltac:(intros E; injection E; clear; lia)).
                 pose proof (live_ne_apart RT AF Σ m _ _ _ _ ART0 INBB INBM ltac:(intros E; injection E; clear; lia)).
                 pose proof (live_ne_apart RT AF Σ m _ _ _ _ ART0 INBB INR ltac:(intros E; injection E; clear; lia)).
                 pose proof (af_live_range RT AF Σ m _ _ ART0 INBB) as (_ & _ & BBSEG). unfold G_ALLOW_CUST, SEGTOP_A in *. clear - Hx H H0 H1 BBSEG. lia. }
        rewrite EFL in BMC5, RC5. split; [exact BMC5|]. split; [exact RC5|].
        split; [rewrite LV2; left; reflexivity|]. split; [exact INBI2|]. split; [exact INBB2|]. split; [exact INBM2|]. split; [exact INR2|].
        split. { assert (APQ : forall p k, In (p, k) (live_remove D0 (rt_live RT Σ1)) -> 0 < k -> q <> p).
                 { intros p k Hp Hk0 E. subst p. destruct (af_live_disj RT AF Σ' m5 q (gr_n (len - off + n)) q k [] (live_remove D0 (rt_live RT Σ1)) ART5 ltac:(rewrite LV2; reflexivity) Hp); clear - H GRP Hk0; lia. }
                 cbn [In]. intros [E|[E|[E|[E|[]]]]]; symmetry in E.
                 - exact (APQ _ _ ltac:(apply live_remove_keep; [exact INBI1| clear - NDd; intros X; apply NDd; tauto]) ltac:(clear; lia) E).
                 - exact (APQ _ _ ltac:(apply live_remove_keep; [exact INBB1| clear - NDd; intros X; apply NDd; tauto]) ltac:(clear; lia) E).
                 - exact (APQ _ _ ltac:(apply live_remove_keep; [exact INBM1| clear - NDd; intros X; apply NDd; tauto]) ltac:(clear; lia) E).
                 - exact (APQ _ _ ltac:(apply live_remove_keep; [exact INR1| clear - NDd; intros X; apply NDd; tauto]) ltac:(clear; lia) E). }
        split. { subst D0. destruct (k_d K) as [d|] eqn:EKD.
                 - right; right. exists q, d. split; [reflexivity|]. split; [exact EKD|]. rewrite LV2, LV1. reflexivity.
                 - right; left. exists q. split; [reflexivity|]. split; [exact EKD|]. rewrite LV2, LV1. rewrite live_remove_notin; [reflexivity|].
                   intros [p k] Hp. cbn [fst]. pose proof (af_live_range RT AF Σ m p k ART0 Hp) as (P0 & _). clear - P0. lia. }
        split; [rewrite CR2, CR1; pose proof (proj2 PC1 GROW); clear - H; lia| rewrite CG2; exact CG1]. }
      destruct HM' as [EM | EM].
      + (* [comment removed for export] *)
        assert (FLW : Z_to_bv 64 (msec meth) = Z_to_bv 64 0) by (rewrite EM; reflexivity). rewrite FLW in BMC4, RC4.
        eapply cps_conseq; [eapply (C_WR Σ1 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' m4 lo BI (k_bb K) (k_bm K) (k_rp K) D0 len max off fl IN n
                                rrw numw padw rmaxw src outer' (Z_to_bv 8 1) canary FDO MST eq_refl eq_refl eq_refl eq_refl INBI1 BIAL BW4 FLOK INBB1 BBAL BBC4 INBM1 BMAL BMC4 INR1 RAL RC4
                                NEMR WDO OFF0 LEN GROW GRB ltac:(clear - HN; lia) SRC4 LSRCZ SB1 ART4 MI4 CO4 STK4 CTX1 UW1 CGW LVM CRM ENV4)
                           | intros cc X; exact X |].
        cbv beta. intros cc POST. apply (POSTG cc (Z_to_bv 64 0) POST (eq_sym FLW)).
      + (* [comment removed for export] *)
        assert (FLW : Z_to_bv 64 (msec meth) = Z_to_bv 64 1) by (rewrite EM; reflexivity). rewrite FLW in BMC4, RC4.
        eapply cps_conseq; [eapply (C_WRS Σ1 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' m4 lo BI (k_bb K) (k_bm K) (k_rp K) D0 len max off fl IN n
                                rrw numw padw rmaxw src outer' (Z_to_bv 8 1) canary FDO MST eq_refl eq_refl eq_refl eq_refl INBI1 BIAL BW4 FLOK INBB1 BBAL BBC4 INBM1 BMAL BMC4 INR1 RAL RC4
                                NEMR WDO OFF0 LEN GROW GRB ltac:(clear - HN; lia) SRC4 LSRCZ SB1 ART4 MI4 CO4 STK4 CTX1 UW1 CGWS LVM CRM ENV4 SEC4)
                           | intros cc X; exact X |].
        cbv beta. intros cc POST. apply (POSTG cc (Z_to_bv 64 1) POST (eq_sym FLW)). }
  (* [comment removed for export] *)
  assert (FLOK' : fl_ok (fl - fl mod 16)).
  { destruct FLOK as [R1 R2]. split; [clear - R1; Z.div_mod_to_equations; lia|].
    replace (fl - fl mod 16) with (Z.shiftl (Z.shiftr fl 4) 4) by (rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia; clear - R1; Z.div_mod_to_equations; lia).
    apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_le_dec i 4) as [L|L]; [rewrite Z.shiftl_spec_low by lia; reflexivity|].
    rewrite Z.shiftl_spec_high, Z.shiftr_spec by lia. replace (i - 4 + 4) with i by lia.
    apply (f_equal (fun z => Z.testbit z i)) in R2. rewrite Z.land_spec, Z.bits_0 in R2. exact R2. }
  assert (CRD1 : 1 <= rt_credit RT Σ) by (clear - Hcr PC1; lia).
  assert (STK1 : lo + RT_STACK + 240 <= usp) by (clear - HSTK; lia).
  assert (INR' : 0 <= IN < 2 ^ 64) by (destruct SRC0 as (S0 & S1 & _); rewrite LSRC in S1; clear - S0 S1 HN; lia).
  apply (bio_write_wrap RT AF GOBJ AFP SM0 GO_memmeth GO_secmeth Σ PMc ra sp gp _ t0 t1 t2 s0 s1 _ _ _ a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m lo BI IN n meth fl (Z_to_bv 64 1) rrw numw padw (Z_to_bv 64 (k_bb K)) nr nw FP PQ FDO MST eq_refl eq_refl eq_refl eq_refl HM INBI BIAL BH BW BT
           INR' HN2 FPOK FPBI ART0 MI0 CALL STK1 Hfr CRD1 MSPEC T c HA).
  intros c' (Σ2 & Σ3 & m5 & HAS & HPQ & LV3 & FRS3 & SP3 & CR3 & CG3).
  subst PQ. cbv beta in HPQ. destruct HPQ as (SEC5 & ENV5 & d' & max' & rmaxw' & HMAX & FIT' & MAXP' & BW5 & BBC5 & BMC5 & RC5 & IND2 & INBI2 & INBB2 & INBM2 & INR2 & NDq & PL & CR2 & CG2).
  apply Hk. exists Σ3.
  split; [| split; [exact FRS3| split; [exact SP3| split; [rewrite CR3; exact CR2| rewrite CG3; exact CG2]]]].
  unfold apost. eapply ASTA_conseq; [exact HAS|]. cbv beta. intros ms (m' & RS & ART7 & MI7 & ST7 & WM57 & PRm & PRm5 & BH7 & BT7).
  exists (Z_to_bv 64 n), m'. split; [exact RS|]. split; [exact (conj ART7 (conj MI7 ST7))|].
  (* [comment removed for export] *)
  assert (FPsubW : forall x, outside ((G_ALLOW_CUST, G_ALLOW_CUST + 1) :: mbio_W K max) x -> outside FP x /\ ~ (BI + 104 <= x < BI + 112)).
  { intros x Ho. unfold mbio_W, mbio_ent in Ho. rewrite <- EBI in Ho. subst FP. destruct (k_d K) as [d|]; cbn [outside app map fst snd] in Ho |- *; clear - Ho; lia. }
  split. { intros x Hx Ho. destruct (FPsubW _ Ho) as [Ho1 Ho2]. apply PRm; [| exact Ho1| exact Ho2].
           apply (aclient_mono _ _ _ _ _ _ _ Hx); [| auto| clear; lia]. destruct (k_d K); [intros e He; exact (live_remove_sub _ _ _ He)| auto]. }
  assert (P57s : forall x : word, client_static (bv_unsigned x) -> m' x = m5 x).
  { intros x Hs. apply PRm5; [apply acl_static; exact Hs|]. intros R. exact (STAP _ _ _ INBI Hs ltac:(clear - R; lia)). }
  split; [apply (cl_env_agree m5 m' _ _ ENV5); intros a Ha; apply P57s; exact (cl_cell_static _ Ha)|].
  split; [apply (sec_off_agree m5 m' SEC5); intros a Ha; apply P57s; rewrite Ha; exact sec_init_static|].
  (* [comment removed for export] *)
  exists (Some d'), max'. split; [reflexivity|]. split; [exact HMAX|]. split; [exact FIT'|]. split; [| rewrite LV3; exact PL].
  rewrite LV3.
  assert (INBI3 : In (BI, 128) (rt_live RT Σ3)) by (rewrite LV3; exact INBI2).
  assert (AG57 : forall p q a k, In (p, q) (rt_live RT Σ2) -> (p, q) <> (BI, 128) -> p <= a -> a + k <= p + q -> agree_on (fun x => a <= x < a + k) m5 m').
  { intros p q a k Hp NE H1 H2 x Hx. cbv beta in Hx.
    pose proof (live_ne_apart RT AF Σ3 m' p q BI 128 ART7 ltac:(rewrite LV3; exact Hp) INBI3 NE) as AP.
    apply PRm5; [apply (acl_live _ _ _ p q); [exact Hp| clear - Hx H1 H2; lia]| clear - Hx H1 H2 AP; lia]. }
  assert (BW7 : rw_cells asegs m' (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) (fl - fl mod 16) rrw numw padw (Z_to_bv 64 (k_bb K)))).
  { apply (rw_cells_agree_nw asegs m5 m' _ _ BW5). intros x Hx. cbv beta in Hx. unfold bio_w1_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply PRm5; [apply (acl_live _ _ _ BI 128); [exact INBI2| clear - Hx; lia]| clear - Hx; lia]. }
  pose proof (proj1 (af_acc_live RT AF Σ3 m' d' max' ART7 ltac:(rewrite LV3; exact IND2))) as WRD.
  destruct (wr_at_rw_CB m' d' max' WRD ltac:(clear - MAXP'; lia)) as (junk' & DC7).
  exists (k_bm K). exists (fl - fl mod 16), rrw, numw, padw, nr, (Z_to_bv 64 (bv_unsigned nw + n)).
  cbn [k_bi k_bb k_bm k_rp k_d mbk_data].
  split; [exact EBI|]. split; [reflexivity|]. split; [exact INBI2|]. split; [exact BIAL|].
  split. { unfold mbio_blocks. cbn [k_bi k_bb k_bm k_rp k_d mbk_data app]. rewrite <- EBI. cbn [In] in NDq.
           pose proof ND as NDc. cbn [app] in NDc.
           apply NoDup_cons_iff in NDc as [XBI NDc]. apply NoDup_cons_iff in NDc as [XBB NDc]. apply NoDup_cons_iff in NDc as [XBM NDc]. apply NoDup_cons_iff in NDc as [XR _].
           cbn [In] in XBI, XBB, XBM, XR.
           apply NoDup_cons. { intros [E|[E|[E|[E|[]]]]]; [apply XBI| apply XBI| apply XBI| apply NDq]; [left; exact E| right; left; exact E| right; right; left; exact E| left; symmetry; exact E]. }
           apply NoDup_cons. { intros [E|[E|[E|[]]]]; [apply XBB; left; exact E| apply XBB; right; left; exact E| apply NDq; right; left; symmetry; exact E]. }
           apply NoDup_cons. { intros [E|[E|[]]]; [apply XBM; left; exact E| apply NDq; right; right; left; symmetry; exact E]. }
           apply NoDup_cons. { intros [E|[]]. apply NDq; right; right; right; left; symmetry; exact E. }
           apply NoDup_cons; [intros []| apply NoDup_nil]. }
  split; [exact HM|]. split; [exact BH7|]. split; [exact BW7|]. split; [exact FLOK'|]. split; [exact BT7|].
  exists rmaxw'.
  split; [exact INBB2|]. split; [exact BBAL|].
  split. { apply (rw_cells_agree_nw asegs m5 m' _ _ BBC5). apply (AG57 (k_bb K) 16); [exact INBB2| intros E; injection E; clear; lia| lia| cbn [cells_size csize Nat.add]; lia]. }
  split; [exact INBM2|]. split; [exact BMAL|]. split; [exact INR2|]. split; [exact RAL|].
  split; [clear - OFF0 HN; lia|]. split; [exact FIT'|]. split; [clear - HMAX MAXB GRN; lia|].
  exists junk'. split; [exact IND2|]. split; [exact MAXP'|].
  split. { apply (rw_cells_agree_nw asegs m5 m' _ _ BMC5). apply (AG57 (k_bm K) 32); [exact INBM2| intros E; injection E; clear; lia| lia| cbn [cells_size csize Nat.add]; lia]. }
  split. { apply (rw_cells_agree_nw asegs m5 m' _ _ RC5). apply (AG57 (k_rp K) 32); [exact INR2| intros E; injection E; clear; lia| lia| unfold readp_cells; cbn [cells_size csize Nat.add]; lia]. }
  split; [| exact DC7]. destruct DC7 as [[WF _] _]. cbn in WF. clear - WF MAXP'. destruct WF as [WF _]. rewrite WF. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem bio_write_proof : bio_write_stmt RT FZ_SITES FZ_CALLS.
Proof.
  unfold bio_write_stmt.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer canary K BI meth len max IN n src
    FDO MST Htp Ha0 Ha1 Ha2 MB.
  pose proof (bio_writeg_proof Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer canary K BI meth len max 0 IN n src
                FDO MST Htp Ha0 Ha1 Ha2 MB) as X.
  rewrite !Z.sub_0_r in X. exact X.
Qed.
End CBwriteF.
