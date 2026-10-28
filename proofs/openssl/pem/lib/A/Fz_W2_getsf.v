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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_ckit Fz_env Fz_M_malloc Fz_M_secure Fz_W1_defs Fz_W1_misc Fz_W1_write0 Fz_W1_writec Fz_W1_writes Fz_W1_grow Fz_W1_puts Fz_W1_read Fz_W1_gets Fz_W2_puts Fz_W2_gets Fz_W3_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

Section CBgetsF.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis SM0 : stack_malloc_contract RT 0.
Hypothesis GO_memmeth : GOBJ M_MEM_A 112.
Hypothesis GO_secmeth : GOBJ M_SECMEM_A 112.
(* [comment removed for export] *)
Hypothesis C_GD : gets_data_stmt RT.
Hypothesis C_GE : gets_empty_stmt RT.

Theorem bio_gets_proof : bio_gets_stmt RT.
Proof.
  unfold bio_gets_stmt.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo canary K BI meth len max off LB bs
    FDO MST -> -> -> -> MB INLB LBAL NLB LBS LBC ART0 MI0 CALL HSTK ENV Hfr Hcr.
  destruct MB as (BM & fl & rrw & numw & padw & nr & nw & EBI & EBM & INBI & BIAL & ND & HM & BH & BW & FLOK & BT & INNER).
  destruct INNER as (rmaxw & INBB & BBAL & BBC & INBM & BMAL & INR & RAL & OFF0 & LEN & MAXB & KD).
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  unfold BGETS_STACK in HSTK.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 352 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLOI : SEGTOP_A <= lo) by (unfold SEGTOP_A, STACK_WIN in *; lia).
  assert (HM' : meth = M_MEM_A \/ meth = M_SECMEM_A) by exact HM.
  pose proof (af_live_range RT AF Σ m BI 128 ART0 INBI) as (BI0 & BILO' & BISEG). assert (BILO : BI + 128 <= lo) by (clear - BILO' LOW; lia). clear BILO'.
  pose proof (af_live_range RT AF Σ m LB 256 ART0 INLB) as (LB0 & LBLO' & LBSEG). assert (LBLO : LB + 256 <= lo) by (clear - LBLO' LOW; lia). clear LBLO'.
  pose proof (af_live_range RT AF Σ m (k_bm K) 32 ART0 INBM) as (BM0 & BMLO' & BMSEG). assert (BMLO : k_bm K + 32 <= lo) by (clear - BMLO' LOW; lia). clear BMLO'.
  pose proof (af_live_range RT AF Σ m (k_rp K) 32 ART0 INR) as (R0 & RLO' & RSEG). assert (RLO : k_rp K + 32 <= lo) by (clear - RLO' LOW; lia). clear RLO'.
  pose proof (af_live_range RT AF Σ m (k_bb K) 16 ART0 INBB) as (BB0 & BBLO' & _). assert (BBLO : k_bb K + 16 <= lo) by (clear - BBLO' LOW; lia). clear BBLO'.
  unfold mbio_blocks in ND. rewrite <- EBI in ND.
  pose proof ND as ND'. apply NoDup_cons_iff in ND' as [NBI ND2]. apply NoDup_cons_iff in ND2 as [NBB ND3]. apply NoDup_cons_iff in ND3 as [NBM ND4]. apply NoDup_cons_iff in ND4 as [NR _].
  cbn [In app] in NBI, NBB, NBM, NR.
  (* [comment removed for export] *)
  set (D0 := match k_d K with Some d => d | None => 0 end).
  assert (NLB5 : ~ In LB [BI; k_bb K; k_bm K; k_rp K; D0]).
  { intros X. apply NLB. unfold mbio_T, mbio_blocks. rewrite <- EBI. cbn [In app] in X |- *. subst D0.
    destruct X as [X|[X|[X|[X|[X|[]]]]]]; [left; exact X | right; left; exact X| do 2 right; left; exact X| do 3 right; left; exact X |].
    destruct (k_d K) as [d|]; [do 4 right; left; exact X | exfalso; clear - X LB0; lia]. }
  assert (NLB' : ~ In LB [BI; k_rp K; D0]) by (clear - NLB5; cbn [In] in NLB5 |- *; tauto).
  set (FP := [(BI + 48, BI + 52); (k_rp K, k_rp K + 24); (LB, LB + 256)]).
  set (PQ := fun (Σ2 : rts RT) (n : Z) (m5 : mem) =>
         wmono asegs m m5 /\ cl_env m5 (Z_to_bv 8 1) canary
         /\ (exists rmaxw' : word,
               rw_cells asegs m5 (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) (fl - fl mod 16) rrw numw padw (Z_to_bv 64 (k_bb K)))
            /\ rw_cells asegs m5 (k_bb K) [C8 (Z_to_bv 64 (k_bm K)); C8 (Z_to_bv 64 (k_rp K))]
            /\ rw_cells asegs m5 (k_rp K) (readp_cells len D0 (off + n) rmaxw' (Z_to_bv 64 (msec meth)))
            /\ match k_d K with
               | Some d => exists junk, rw_cells asegs m5 (k_bm K) [C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 d); C8 (Z_to_bv 64 max); C8 (Z_to_bv 64 (msec meth))]
                                        /\ length junk = Z.to_nat max /\ rw_cells asegs m5 d [CB (Z.to_nat max) junk]
               | None => rw_cells asegs m5 (k_bm K) [C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (msec meth))]
               end)
         /\ rw_cells asegs m5 (LB + n) [C1 (Z_to_bv 8 0)]
         /\ (n = 0 -> off = len) /\ (1 <= n -> n <= Z.min (len - off) 254)
         /\ (exists bsr : list byte, bytes_at asegs m5 LB bsr /\ Z.of_nat (length bsr) = n /\ (n < Z.min (len - off) 254 -> nth_error bsr (Z.to_nat (n - 1)) = Some (Z_to_bv 8 10)))).
  set (PS := fun (Σ2 : rts RT) => rt_live RT Σ2 = rt_live RT Σ /\ rt_credit RT Σ2 = rt_credit RT Σ - 1 /\ rt_cg RT Σ2 = rt_cg RT Σ).

  assert (NOI : forall (W : list (Z * Z)) x, ~ outside W x -> exists lo hi, In (lo, hi) W /\ lo <= x < hi).
  { clear. induction W as [|[lo hi] W IH]; intros x Hx; [exfalso; apply Hx; exact I|]. cbn [outside] in Hx.
    destruct (Z_lt_le_dec x lo) as [L|L]; [| destruct (Z_lt_le_dec x hi) as [L'|L']; [exists lo, hi; split; [left; reflexivity| lia]|]].
    all: destruct (IH x) as (lo' & hi' & Hin & R); [intros X; apply Hx; split; [lia| exact X]| exists lo', hi'; split; [right; exact Hin| exact R]]. }
  assert (FPOK : forall x, ~ outside FP x -> aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) x).
  { intros x Hx. destruct (NOI FP x Hx) as (lo' & hi' & Hin & R). subst FP. cbn [In] in Hin.
    destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-.
    - apply (acl_live _ _ _ BI 128); [exact INBI | clear - R; lia].
    - apply (acl_live _ _ _ (k_rp K) 32); [exact INR | clear - R; lia].
    - apply (acl_live _ _ _ LB 256); [exact INLB | exact R]. }
  assert (STAP : forall p k x, In (p, k) (rt_live RT Σ) -> client_static x -> ~ (p <= x < p + k)).
  { intros p k x Hin Hs. pose proof (af_live_range RT AF Σ m p k ART0 Hin) as (_ & _ & SG). pose proof (client_static_range x Hs). unfold SEGTOP_A in *. clear - SG H. lia. }
  assert (NLBI : LB <> BI) by (clear - NLB'; intros E; apply NLB'; left; symmetry; exact E).
  pose proof (live_ne_apart RT AF Σ m _ _ _ _ ART0 INR INBI ltac:(intros E; injection E; lia)) as APR.
  pose proof (live_ne_apart RT AF Σ m _ _ _ _ ART0 INLB INBI ltac:(intros E; injection E; intros; exact (NLBI ltac:(assumption)))) as APL.
  assert (FPBI : forall x, BI <= x < BI + 40 \/ BI + 72 <= x < BI + 128 -> outside FP x).
  { intros x Hx. subst FP. cbn [outside app]. clear - Hx APR APL. lia. }
  assert (LBR : 0 <= LB < 2 ^ 64) by (clear - LB0 LBLO NUM HSTK; unfold USTACK_TOP, RT_STACK in *; lia).
  assert (STK1 : lo + RT_STACK + 176 <= usp) by (clear - HSTK; lia).
  assert (FLOK' : fl_ok (fl - fl mod 16)).
  { destruct FLOK as [R1 R2]. split; [clear - R1; Z.div_mod_to_equations; lia|].
    replace (fl - fl mod 16) with (Z.shiftl (Z.shiftr fl 4) 4) by (rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia; clear - R1; Z.div_mod_to_equations; lia).
    apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_le_dec i 4) as [L|L]; [rewrite Z.shiftl_spec_low by lia; reflexivity|].
    rewrite Z.shiftl_spec_high, Z.shiftr_spec by lia. replace (i - 4 + 4) with i by lia.
    apply (f_equal (fun z => Z.testbit z i)) in R2. rewrite Z.land_spec, Z.bits_0 in R2. exact R2. }
  (* [comment removed for export] *)
  assert (BSPEC : bgets_spec RT Σ PMc sp gp (Z_to_bv 64 TP_A) s0 ra usp lo BI LB 255 m FP PQ PS).
  { unfold bgets_spec. intros Σ1 f pd m4 u0 u1 u2 b4 b5 b6 b7 u3 u4 u5 u6 F' fc' HP HPM LV1 FRS1 SP1 CR1 CG1 ART4 MI4 WM04 CO4 A04 FRR4.
    set (usp1 := usp + -160 - pd) in *.
    assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; clear - NUM HSTK HP LOW SP0W; lia).
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
    assert (INBI1 : In (BI, 128) (rt_live RT Σ1)) by (rewrite LV1; exact INBI).
    assert (INBB1 : In (k_bb K, 16) (rt_live RT Σ1)) by (rewrite LV1; exact INBB).
    assert (INR1 : In (k_rp K, 32) (rt_live RT Σ1)) by (rewrite LV1; exact INR).
    assert (INLB1 : In (LB, 256) (rt_live RT Σ1)) by (rewrite LV1; exact INLB).
    pose proof CO4 as (ST4 & _ & _ & SPT4 & _).
    (* [comment removed for export] *)
    assert (KD4 : match k_d K with
                  | Some d => exists junk, In (d, max) (rt_live RT Σ) /\ 0 < max
                       /\ rw_cells asegs m4 (k_bm K) [C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 d); C8 (Z_to_bv 64 max); C8 (Z_to_bv 64 (msec meth))]
                       /\ rw_cells asegs m4 (k_rp K) (readp_cells len d off rmaxw (Z_to_bv 64 (msec meth))) /\ length junk = Z.to_nat max /\ rw_cells asegs m4 d [CB (Z.to_nat max) junk]
                  | None => max = 0 /\ rw_cells asegs m4 (k_bm K) [C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (msec meth))]
                       /\ rw_cells asegs m4 (k_rp K) (readp_cells 0 0 0 rmaxw (Z_to_bv 64 (msec meth))) end).
    { subst D0. destruct (k_d K) as [d|].
      - destruct KD as (junk & IND & MAXP & BMC & RC & LJ & DC). exists junk. split; [exact IND|]. split; [exact MAXP|].
        split; [apply (rw_cells_agree asegs m m4 _ _ BMC); [apply (AGlo (k_bm K) 32); [exact INBM| lia| cbn [cells_size csize Nat.add]; lia] | exact WM04]|].
        split; [apply (rw_cells_agree asegs m m4 _ _ RC); [apply (AGlo (k_rp K) 32); [exact INR| lia| unfold readp_cells; cbn [cells_size csize Nat.add]; lia] | exact WM04]|].
        split; [exact LJ|]. apply (rw_cells_agree asegs m m4 _ _ DC); [apply (AGlo d max); [exact IND| lia| cbn [cells_size csize Nat.add]; clear - LJ MAXP; lia] | exact WM04].
      - destruct KD as (MAX0 & BMC & RC). split; [exact MAX0|].
        split; [apply (rw_cells_agree asegs m m4 _ _ BMC); [apply (AGlo (k_bm K) 32); [exact INBM| lia| cbn [cells_size csize Nat.add]; lia] | exact WM04]|].
        apply (rw_cells_agree asegs m m4 _ _ RC); [apply (AGlo (k_rp K) 32); [exact INR| lia| unfold readp_cells; cbn [cells_size csize Nat.add]; lia] | exact WM04]. }
    assert (FPW : forall x, outside FP x -> ~ (BI + 48 <= x < BI + 52) /\ ~ (k_rp K <= x < k_rp K + 24) /\ ~ (LB <= x < LB + 256)).
    { intros x Hx. subst FP. cbn [outside app] in Hx. clear - Hx. tauto. }
  
    (* [comment removed for export] *)
    assert (POSTK : forall (cc : config) (W : Z -> list (Z * Z)),
      ASTA RT Σ1 PMc (fun ms => exists (n : Z) (rmaxw' : word) (m' : mem),
          ret_st (Z_to_bv 64 SITE_bg_gets) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) sp (Z_to_bv 64 usp1) (Z_to_bv 64 f) (Z_to_bv 64 255) (Z_to_bv 64 LB) (Z_to_bv 64 BI) (Z_to_bv 64 (BI + 16))
                 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BI + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 n) m' ms
          /\ ((n = 0 /\ off = len) \/ 1 <= n <= Z.min (len - off) 254)
          /\ rt_after RT Σ1 (bv_unsigned (Z_to_bv 64 usp1)) lo m4 m' /\ rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) (bv_unsigned (Z_to_bv 64 usp1)) (W n) m4 m'
          /\ rw_cells asegs m' (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) (fl - fl mod 16) rrw numw padw (Z_to_bv 64 (k_bb K)))
          /\ rw_cells asegs m' (k_rp K) (readp_cells len D0 (off + n) rmaxw' (Z_to_bv 64 (msec meth)))
          /\ rw_cells asegs m' (LB + n) [C1 (Z_to_bv 8 0)]
          /\ (exists bsr : list byte, bytes_at asegs m' LB bsr /\ Z.of_nat (length bsr) = n /\ (n < Z.min (len - off) 254 -> nth_error bsr (Z.to_nat (n - 1)) = Some (Z_to_bv 8 10)))) cc ->
      (forall n x, 0 <= n <= 254 -> outside FP x -> outside (W n) x) ->
      exists (Σ2 : rts RT),
        ASTA RT Σ2 PMc (fun ms => exists (n0 : Z) (m5 : mem),
            bgets_ret sp gp (Z_to_bv 64 TP_A) usp1 BI LB 255 f (Z_to_bv 64 n0) m5 ms /\ 0 <= n0 <= 255
            /\ ART RT Σ2 m5 /\ mem_inv asegs m5 /\ stk asegs m5 lo usp1
            /\ (forall x : word, aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp1 (bv_unsigned x) -> outside FP (bv_unsigned x) -> m5 x = m4 x)
            /\ PQ Σ2 n0 m5) cc
        /\ rt_frames RT Σ2 = rt_frames RT Σ1 /\ rt_sp0 RT Σ2 = rt_sp0 RT Σ1 /\ In (BI, 128) (rt_live RT Σ2)
        /\ (forall p k, In (p, k) (rt_live RT Σ1) -> In (p, k) (rt_live RT Σ2) \/ (forall x, p <= x < p + k -> ~ outside FP x)) /\ PS Σ2).
    { intros cc W HAS HW. rewrite EU1 in HAS. exists Σ1.
      split; [| split; [reflexivity| split; [reflexivity| split; [exact INBI1| split; [intros p k Hp; left; exact Hp| subst PS; cbv beta; exact (conj LV1 (conj CR1 CG1))]]]]].
      eapply ASTA_conseq; [exact HAS|]. cbv beta. intros ms (n & rmaxw' & m5 & RS & HK & (ART5 & MI5 & WM5 & ST5) & PRES5 & BW5 & RC5 & NUL5 & LF5). exists n, m5.
      assert (HN : 0 <= n <= 254) by (clear - HK; lia).
      assert (P5 : forall x : word, aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp1 (bv_unsigned x) -> outside FP (bv_unsigned x) -> m5 x = m4 x)
        by (intros x Hx Ho; exact (PRES5 x Hx (HW n _ HN Ho))).
      assert (P5s : forall x : word, client_static (bv_unsigned x) -> m5 x = m4 x).
      { intros x Hs. apply P5; [apply acl_static; exact Hs|]. subst FP. cbn [outside].
        pose proof (STAP _ _ _ INBI Hs). pose proof (STAP _ _ _ INR Hs). pose proof (STAP _ _ _ INLB Hs). clear - H H0 H1. lia. }
      assert (AGK : forall p q a k, In (p, q) (rt_live RT Σ) -> ~ In p [BI; k_rp K; LB] -> p <= a -> a + k <= p + q -> agree_on (fun x => a <= x < a + k) m4 m5).
      { intros p q a k Hp NP H1 H2 x Hx. cbv beta in Hx. cbn [In] in NP. apply P5; [rewrite LV1; apply (acl_live _ _ _ p q); [exact Hp| clear - Hx H1 H2; lia]|].
        subst FP. cbn [outside].
        pose proof (live_ne_apart RT AF Σ m _ _ _ _ ART0 Hp INBI ltac:(intros E; injection E; intros; apply NP; left; symmetry; assumption)).
        pose proof (live_ne_apart RT AF Σ m _ _ _ _ ART0 Hp INR ltac:(intros E; injection E; intros; apply NP; right; left; symmetry; assumption)).
        pose proof (live_ne_apart RT AF Σ m _ _ _ _ ART0 Hp INLB ltac:(intros E; injection E; intros; apply NP; right; right; left; symmetry; assumption)).
        clear - Hx H1 H2 H H0 H3. lia. }
      split; [exact RS|]. split; [clear - HN; lia|]. split; [exact ART5|]. split; [exact MI5|]. split; [exact ST5|]. split; [exact P5|].
      subst PQ. cbv beta. split; [exact (wmono_trans asegs _ _ _ WM04 WM5)|].
      split; [apply (cl_env_agree m4 m5 _ _ ENV4); intros a Ha; apply P5s; exact (cl_cell_static _ Ha)|].
      split.
      { exists rmaxw'. split; [exact BW5|].
        split. { apply (rw_cells_agree_nw asegs m4 m5 _ _ BBC4). apply (AGK (k_bb K) 16); [exact INBB| cbn [In]; clear - NBI NBB NLB5; cbn [In] in NLB5; intuition congruence| lia| cbn [cells_size csize Nat.add]; lia]. }
        split; [exact RC5|].
        subst D0. destruct (k_d K) as [d|].
        - destruct KD4 as (junk & IND & MAXP & BMC4 & RC4 & LJ & DC4). exists junk.
          split. { apply (rw_cells_agree_nw asegs m4 m5 _ _ BMC4). apply (AGK (k_bm K) 32); [exact INBM| cbn [In]; clear - NBI NBM NLB5; cbn [In] in NLB5; intuition congruence| lia| cbn [cells_size csize Nat.add]; lia]. }
          split; [exact LJ|].
          apply (rw_cells_agree_nw asegs m4 m5 _ _ DC4). apply (AGK d max); [exact IND| | lia| cbn [cells_size csize Nat.add]; clear - LJ MAXP; lia].
          cbn [In]. clear - NBI NR NLB5. cbn [In] in NBI, NR, NLB5. intuition congruence.
        - destruct KD4 as (MAX0 & BMC4 & RC4).
          apply (rw_cells_agree_nw asegs m4 m5 _ _ BMC4). apply (AGK (k_bm K) 32); [exact INBM| cbn [In]; clear - NBI NBM NLB5; cbn [In] in NLB5; intuition congruence| lia| cbn [cells_size csize Nat.add]; lia]. }
      split; [exact NUL5|]. split; [clear - HK; lia|]. split; [clear - HK; lia|]. exact LF5. }
  
    assert (STK4 : lo + RT_STACK + 160 <= bv_unsigned (Z_to_bv 64 usp1)) by (rewrite EU1; unfold usp1; clear - HSTK HP; lia).
    assert (NEQR : k_rp K <> BI) by (clear - NBI; intros E; apply NBI; tauto).
    destruct (Z_lt_le_dec off len) as [DATA | EMPTY].
    - (* [comment removed for export] *)
      subst D0. destruct (k_d K) as [d|] eqn:EKD; [| exfalso; destruct KD4 as (MAX0 & _); clear - MAX0 DATA LEN OFF0; lia].
      destruct KD4 as (junk & IND & MAXP & BMC4 & RC4 & LJ & DC4).
      assert (INd1 : In (d, max) (rt_live RT Σ1)) by (rewrite LV1; exact IND).
      assert (NDd : d <> BI /\ d <> k_rp K) by (clear - NBI NR; split; intros E; [apply NBI| apply NR]; cbn [In app]; rewrite E; tauto).
      assert (DST : dst_blk (rt_live RT Σ1) LB 255 [BI; k_rp K; d]) by (exists LB, 256; split; [exact INLB1|]; split; [lia|]; split; [lia| exact NLB']).
      eapply cps_conseq; [eapply (C_GD Σ1 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' m4 lo BI (k_bb K) (k_bm K) (k_rp K) d len max off fl LB 255
                              rrw numw padw rmaxw (Z_to_bv 64 (msec meth)) FDO MST eq_refl eq_refl eq_refl eq_refl INBI1 BIAL BW4 FLOK INBB1 BBAL BBC4 INR1 RAL RC4 INd1
                              (proj1 NDd) (proj2 NDd) ltac:(clear - OFF0 DATA; lia) LEN MAXB ltac:(clear; lia) DST ART4 MI4 CO4 STK4)
                         | intros cc X; exact X |].
      cbv beta. intros cc POST. apply (POSTK cc (fun k => GT_W BI (k_rp K) LB k)).
      + eapply ASTA_conseq; [exact POST|]. cbv beta. intros ms (k & rmaxw' & m' & RS & HK & AFT & PRES & BW5 & RC5 & NUL5 & LFX). exists k, rmaxw', m'.
        change (255 - 1) with 254 in LFX.
        split; [exact RS|]. split; [right; exact HK|]. split; [exact AFT|]. split; [exact PRES|]. split; [exact BW5|]. split; [exact RC5|]. split; [exact NUL5| exact LFX].
      + intros k x Hk2 Ho. pose proof (FPW _ Ho) as (W1 & W2 & W3). unfold GT_W. cbn [outside]. clear - W1 W2 W3 Hk2. lia.
    - (* [comment removed for export] *)
      assert (OFFE : off = len) by (clear - EMPTY OFF0; lia).
      assert (RC4 : rw_cells asegs m4 (k_rp K) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (D0 + off)); C8 rmaxw; C8 (Z_to_bv 64 (msec meth))]).
      { subst D0. destruct (k_d K) as [d|].
        - destruct KD4 as (junk & IND & MAXP & BMC4 & RC4 & LJ & DC4). unfold readp_cells in RC4. rewrite OFFE, Z.sub_diag in RC4. rewrite OFFE. exact RC4.
        - destruct KD4 as (MAX0 & BMC4 & RC4). unfold readp_cells in RC4. replace (0 + off) with 0 by (clear - MAX0 LEN EMPTY OFF0; lia). exact RC4. }
      assert (DST : dst_blk (rt_live RT Σ1) LB 1 [BI]) by (exists LB, 256; split; [exact INLB1|]; split; [lia|]; split; [lia| cbn [In]; clear - NLB'; cbn [In] in NLB'; tauto]).
      eapply cps_conseq; [eapply (C_GE Σ1 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' m4 lo BI (k_bb K) (k_bm K) (k_rp K) LB 255 fl
                              rrw numw padw (Z_to_bv 64 (D0 + off)) rmaxw (Z_to_bv 64 (msec meth)) FDO MST eq_refl eq_refl eq_refl eq_refl INBI1 BIAL BW4 FLOK INBB1 BBAL BBC4 INR1 RAL RC4
                              ltac:(clear; lia) DST ART4 MI4 CO4 ltac:(clear - STK4; lia))
                         | intros cc X; exact X |].
      cbv beta. intros cc POST. apply (POSTK cc (fun k => [(BI + 48, BI + 52); (LB, LB + 1)])).
      + eapply ASTA_conseq; [exact POST|]. cbv beta. intros ms (m' & RS & AFT & PRES & BW5 & NUL5). exists 0, rmaxw, m'.
        split; [exact RS|]. split; [left; split; [reflexivity| exact OFFE]|]. split; [exact AFT|]. split; [exact PRES|]. split; [exact BW5|].
        split; [| split; [rewrite Z.add_0_r; exact NUL5| exists []; split; [split; [clear - LB0; lia| split; [cbn; clear - LB0 LBLO NUM HSTK; unfold USTACK_TOP, RT_STACK in *; lia| intros i Hi; cbn in Hi; exfalso; clear - Hi; lia]]| split; [reflexivity| intros HK0; exfalso; clear - HK0 OFFE LEN OFF0; lia]]]].
        unfold readp_cells. rewrite Z.add_0_r, <- OFFE, Z.sub_diag. apply (rw_cells_agree_nw asegs m4 m' _ _ RC4).
        intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply PRES; [apply (acl_live _ _ _ (k_rp K) 32); [exact INR1| clear - Hx; lia]|].
        cbn [outside]. pose proof (live_ne_apart RT AF Σ m _ _ _ _ ART0 INR INBI ltac:(intros E; injection E; lia)).
        pose proof (live_ne_apart RT AF Σ m _ _ _ _ ART0 INR INLB ltac:(intros E; injection E; intros; apply NLB5; cbn [In]; do 3 right; left; assumption)). clear - Hx H H0. lia.
      + intros k x Hk2 Ho. pose proof (FPW _ Ho) as (W1 & W2 & W3). cbn [outside]. clear - W1 W3. lia. }

  apply (bio_gets_wrap RT AF GOBJ AFP SM0 GO_memmeth GO_secmeth Σ PMc ra sp gp _ t0 t1 t2 s0 s1 _ _ _ a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m lo BI LB 255 meth fl (Z_to_bv 64 1) rrw numw padw (Z_to_bv 64 (k_bb K)) FP PQ PS FDO MST eq_refl eq_refl eq_refl eq_refl HM' INBI BIAL BH BW
           LBR ltac:(clear; lia) FPOK FPBI ART0 MI0 CALL STK1 Hfr Hcr BSPEC T c HA).
  intros c' (Σ2 & Σ3 & HAS & LV3 & FRS3 & SP3 & CR3 & CG3 & HPS). subst PS. cbv beta in HPS. destruct HPS as (LV2 & CR2 & CG2).
  apply Hk. exists Σ3.
  unfold apost. split.
  2: { unfold rts_same. rewrite LV3, LV2, FRS3, SP3, CR3, CR2, CG3, CG2. repeat split; try reflexivity; clear; lia. }
  eapply ASTA_conseq; [exact HAS|]. cbv beta. intros ms (n & m5 & m' & RS & HN & ART7 & MI7 & ST7 & WM57 & PRm & PRm5 & BH7 & HPQ).
  subst PQ. cbv beta in HPQ. destruct HPQ as (WM05 & ENV5 & (rmaxw' & BW5 & BBC5 & RC5 & KD5) & NUL5 & HN0 & HN1 & (bsq & OBq & LBq & LFq)).
  exists (Z_to_bv 64 n), m'. split; [exact RS|]. split; [exact (conj ART7 (conj MI7 ST7))|].
  assert (FPsubW : forall x, outside ((LB, LB + 256) :: mbio_W K max) x -> outside FP x).
  { intros x Ho. unfold mbio_W, mbio_ent in Ho. rewrite <- EBI in Ho. subst FP. destruct (k_d K) as [d|]; cbn [outside app map fst snd] in Ho |- *; clear - Ho; lia. }
  split. { intros x Hx Ho. apply PRm; [exact Hx| exact (FPsubW _ Ho)]. }
  assert (P57s : forall x : word, client_static (bv_unsigned x) -> m' x = m5 x) by (intros x Hs; apply PRm5; apply acl_static; exact Hs).
  split; [apply (cl_env_agree m5 m' _ _ ENV5); intros a Ha; apply P57s; exact (cl_cell_static _ Ha)|].
  split; [exact (wmono_trans asegs _ _ _ WM05 WM57)|].
  (* [comment removed for export] *)
  rewrite LV2 in PRm5.
  assert (AG57 : forall p q a k, In (p, q) (rt_live RT Σ) -> p <= a -> a + k <= p + q -> agree_on (fun x => a <= x < a + k) m5 m').
  { intros p q a k Hp H1 H2 x Hx. cbv beta in Hx. apply PRm5. apply (acl_live _ _ _ p q); [exact Hp| clear - Hx H1 H2; lia]. }
  assert (INLB3 : In (LB, 256) (rt_live RT Σ3)) by (rewrite LV3, LV2; exact INLB).
  pose proof (proj1 (af_acc_live RT AF Σ3 m' LB 256 ART7 INLB3)) as WRL.
  destruct (wr_at_rw_CB m' LB 256 WRL ltac:(clear; lia)) as (bs' & LBC7). change (Z.to_nat 256) with 256%nat in LBC7.
  assert (LBS' : length bs' = 256%nat) by (destruct LBC7 as [[WF _] _]; cbn in WF; destruct WF as [WF _]; exact WF).
  assert (NUL7 : rw_cells asegs m' (LB + n) [C1 (Z_to_bv 8 0)]).
  { apply (rw_cells_agree_nw asegs m5 m' _ _ NUL5). apply (AG57 LB 256); [exact INLB| clear - HN HN1; lia| cbn [cells_size csize Nat.add]; clear - HN HN1 OFF0 LEN; lia]. }
  (* [comment removed for export] *)
  assert (MB7 : forall off', 0 <= off' <= len ->
            rw_cells asegs m' (k_rp K) (readp_cells len D0 off' rmaxw' (Z_to_bv 64 (msec meth))) ->
            mbio_rep (rt_live RT Σ) m' K BI meth len max off').
  { intros off' HO RC7. exists (k_bm K). exists (fl - fl mod 16), rrw, numw, padw, nr, nw.
    split; [exact EBI|]. split; [reflexivity|]. split; [exact INBI|]. split; [exact BIAL|]. split; [unfold mbio_blocks; rewrite <- EBI; exact ND|]. split; [exact HM|].
    split; [exact BH7|].
    split; [apply (rw_cells_agree_nw asegs m5 m' _ _ BW5); apply (AG57 BI 128); [exact INBI| lia| unfold bio_w1_cells; cbn [cells_size csize Nat.add]; lia]|].
    split; [exact FLOK'|].
    split. { apply (rw_cells_agree_nw asegs m m' _ _ BT). intros x Hx. cbv beta in Hx. unfold bio_tail in Hx. cbn [cells_size csize Nat.add] in Hx.
             apply PRm; [apply (acl_live _ _ _ BI 128); [exact INBI| clear - Hx; lia] | apply FPBI; right; clear - Hx; lia]. }
    exists rmaxw'. split; [exact INBB|]. split; [exact BBAL|].
    split; [apply (rw_cells_agree_nw asegs m5 m' _ _ BBC5); apply (AG57 (k_bb K) 16); [exact INBB| lia| cbn [cells_size csize Nat.add]; lia]|].
    split; [exact INBM|]. split; [exact BMAL|]. split; [exact INR|]. split; [exact RAL|]. split; [exact HO|]. split; [exact LEN|]. split; [exact MAXB|].
    subst D0. destruct (k_d K) as [d|].
    - destruct KD5 as (junk & BMC5 & LJ & DC5). destruct KD as (junk0 & IND & MAXP & _). exists junk. split; [exact IND|]. split; [exact MAXP|].
      split; [apply (rw_cells_agree_nw asegs m5 m' _ _ BMC5); apply (AG57 (k_bm K) 32); [exact INBM| lia| cbn [cells_size csize Nat.add]; lia]|].
      split; [exact RC7|]. split; [exact LJ|].
      apply (rw_cells_agree_nw asegs m5 m' _ _ DC5). apply (AG57 d max); [exact IND| lia| cbn [cells_size csize Nat.add]; clear - LJ MAXP; lia].
    - destruct KD as (MAX0 & _). split; [exact MAX0|].
      split; [apply (rw_cells_agree_nw asegs m5 m' _ _ KD5); apply (AG57 (k_bm K) 32); [exact INBM| lia| cbn [cells_size csize Nat.add]; lia]|].
      unfold readp_cells in RC7 |- *. replace (len - off') with 0 in RC7 by (clear - MAX0 LEN HO; lia). replace (0 + off') with 0 in RC7 by (clear - MAX0 LEN HO; lia). exact RC7. }
  assert (RC7 : rw_cells asegs m' (k_rp K) (readp_cells len D0 (off + n) rmaxw' (Z_to_bv 64 (msec meth)))).
  { apply (rw_cells_agree_nw asegs m5 m' _ _ RC5). apply (AG57 (k_rp K) 32); [exact INR| lia| unfold readp_cells; cbn [cells_size csize Nat.add]; lia]. }
  exists n, bs'. split; [reflexivity|]. split; [exact LBS'|]. split; [exact LBC7|].
  destruct (Z.eq_dec n 0) as [N0|N1].
  - left. split; [exact N0|]. split; [exact (HN0 N0)|]. rewrite N0, Z.add_0_r in RC7. exact (MB7 off OFF0 RC7).
  - right. pose proof (HN1 ltac:(clear - N1 HN; lia)) as HK. split; [clear - HK N1 HN; lia|].
    split.
    + destruct (nth_error bs' (Z.to_nat n)) as [b|] eqn:Eb; [| exfalso; apply nth_error_None in Eb; rewrite LBS' in Eb; clear - Eb HN; lia].
      pose proof (rw_cells_bytes_at asegs m' _ _ LBC7) as B0. cbn [cells_bytes cbytes app] in B0. rewrite app_nil_r in B0.
      pose proof (bytes_at_nth1 asegs m' LB bs' (Z.to_nat n) b B0 Eb) as B1. rewrite Z2Nat.id in B1 by (clear - HN; lia).
      pose proof (rw_C1_bytes m' _ _ NUL7) as B2.
      pose proof (bytes_at_inj m' (LB + n) [b] _ B1 B2 eq_refl) as E. injection E as E1. rewrite E1. reflexivity.
    + split; [| apply MB7; [clear - HK OFF0 HN; lia| exact RC7]].
      (* [comment removed for export] *)
      intros HLT. pose proof (rw_cells_bytes_at asegs m' _ _ LBC7) as B0. cbn [cells_bytes cbytes app] in B0. rewrite app_nil_r in B0. destruct B0 as (_ & _ & B0I).
      pose proof (bytes_at_agree asegs m5 m' _ _ OBq ltac:(rewrite LBq; apply (AG57 LB 256); [exact INLB| clear; lia| clear - HN; lia])) as OB7. destruct OB7 as (_ & _ & OBI).
      assert (L1 : (Z.to_nat (n - 1) < length bsq)%nat) by (apply Nat2Z.inj_lt; rewrite Z2Nat.id by (clear - HK N1 HN; lia); rewrite LBq; clear - HK N1 HN; lia).
      assert (L2 : (Z.to_nat (n - 1) < length bs')%nat) by (rewrite LBS'; apply Nat2Z.inj_lt; rewrite Z2Nat.id by (clear - HK N1 HN; lia); clear - HN N1; cbn; lia).
      rewrite <- (B0I _ L2). rewrite (OBI _ L1). exact (LFq HLT).
Qed.
End CBgetsF.
