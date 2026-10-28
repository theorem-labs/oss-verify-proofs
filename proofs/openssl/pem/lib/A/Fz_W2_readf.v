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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_ckit Fz_env Fz_M_malloc Fz_M_secure Fz_W1_defs Fz_W1_misc Fz_W1_read Fz_W2_puts Fz_W2_gets Fz_W2_read Fz_W3_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma fl_ok_land : forall fl c, fl_ok fl -> 0 <= c -> fl_ok (Z.land fl c).
Proof.
  intros fl c [R H] Rc. split.
  - split; [apply Z.land_nonneg; lia|].
    destruct (Z.eq_dec (Z.land fl c) 0) as [E|NE]; [rewrite E; lia|].
    apply Z.log2_lt_pow2; [pose proof (proj2 (Z.land_nonneg fl c) ltac:(lia)); lia|].
    pose proof (Z.log2_land fl c ltac:(lia) Rc) as LL.
    destruct (Z.eq_dec fl 0) as [->|NF]; [rewrite Z.land_0_l in NE; lia|].
    pose proof (proj1 (Z.log2_lt_pow2 fl 31 ltac:(lia)) ltac:(lia)). lia.
  - rewrite <- Z.land_assoc, (Z.land_comm c 512), Z.land_assoc, H. reflexivity.
Qed.

Lemma fl_ok_clear16 : forall fl, fl_ok fl -> fl_ok (fl - fl mod 16).
Proof.
  intros fl [R1 R2]. split; [clear - R1; Z.div_mod_to_equations; lia|].
  replace (fl - fl mod 16) with (Z.shiftl (Z.shiftr fl 4) 4) by (rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia; clear - R1; Z.div_mod_to_equations; lia).
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z_lt_le_dec i 4) as [L|L]; [rewrite Z.shiftl_spec_low by lia; reflexivity|].
  rewrite Z.shiftl_spec_high, Z.shiftr_spec by lia. replace (i - 4 + 4) with i by lia.
  apply (f_equal (fun z => Z.testbit z i)) in R2. rewrite Z.land_spec, Z.bits_0 in R2. exact R2.
Qed.

Section CBreadF.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis SM0 : stack_malloc_contract RT 0.
Hypothesis GO_memmeth : GOBJ M_MEM_A 112.
Hypothesis GO_secmeth : GOBJ M_SECMEM_A 112.
(* [comment removed for export] *)
Hypothesis C_RD : read_data_stmt RT.

Theorem bio_read_proof : bio_read_stmt RT.
Proof.
  unfold bio_read_stmt.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo canary K BI BM meth len max off OUT no n blw ojunk
    FDO MST -> -> -> -> MB HN INO NT HNO LOJ OC ART0 MI0 CALL HSTK ENV Hfr Hcr.
  destruct MB as (fl & rrw & numw & padw & nr & nw & EBI & EBM & INBI & BIAL & ND & HM & BH & BW & FLOK & BT & INNER).
  destruct INNER as (rmaxw & INBB & BBAL & BBC & INBM & BMAL & INR & RAL & OFF0 & LEN & MAXB & KD).
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA). set (usp := bv_unsigned sp) in *.
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  unfold BREAD_STACK in HSTK.
  assert (HLOI : SEGTOP_A <= lo) by (unfold SEGTOP_A, STACK_WIN in *; lia).
  assert (HM' : meth = M_MEM_A \/ meth = M_SECMEM_A) by exact HM.
  (* [comment removed for export] *)
  destruct (k_d K) as [d|] eqn:EKD; [| exfalso; destruct KD as (MAX0 & _); clear - MAX0 HN LEN OFF0; lia].
  destruct KD as (junk & IND & MAXP & BMC & RC & LJ & DC).
  unfold mbio_blocks in ND. rewrite <- EBI, EKD in ND.
  pose proof ND as ND'. apply NoDup_cons_iff in ND' as [NBI ND2]. apply NoDup_cons_iff in ND2 as [NBB ND3]. apply NoDup_cons_iff in ND3 as [NBM ND4]. apply NoDup_cons_iff in ND4 as [NR _].
  cbn [In app] in NBI, NBB, NBM, NR.
  assert (NDBI : d <> BI) by (clear - NBI; intros E; apply NBI; do 3 right; left; exact E).
  assert (NDR : d <> k_rp K) by (clear - NR; intros E; apply NR; left; exact E).
  assert (NTA : ~ In OUT [BI; k_bb K; k_bm K; k_rp K; d]) by (intros X; apply NT; unfold mbio_T, mbio_blocks; rewrite <- EBI, EKD; cbn [In app] in X |- *; clear - X; tauto).
  assert (NT5 : ~ In OUT [BI; k_rp K; d]).
  { intros X. apply NT. unfold mbio_T, mbio_blocks. rewrite <- EBI, EKD. cbn [In app] in X |- *. clear - X. tauto. }
  assert (DST : dst_blk (rt_live RT Σ) OUT n [BI; k_rp K; d]) by (exists OUT, no; split; [exact INO|]; split; [clear; lia|]; split; [clear - HNO; lia| exact NT5]).
  assert (STK1 : lo + RT_STACK + 112 + 96 + 64 + 96 <= usp) by (clear - HSTK; lia).
  apply (bio_read_core_cps RT AF GOBJ AFP SM0 GO_memmeth GO_secmeth C_RD Σ PMc ra sp gp _ t0 t1 t2 s0 s1 _ _ _ a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m lo BI (k_bb K) (k_bm K) (k_rp K) d len max off fl OUT n meth rrw numw padw rmaxw (Z_to_bv 64 (msec meth)) nr nw
           FDO MST eq_refl eq_refl eq_refl eq_refl HM' BH INBI BIAL BW FLOK BT INBB BBAL BBC INR RAL RC IND NDBI NDR ltac:(clear - OFF0; lia) HN LEN MAXB DST ART0 MI0 CALL STK1 Hfr Hcr T c HA).
  intros c' (Σ3 & HAS & LV3 & FRS3 & SP3 & CR3 & CG3).
  apply Hk. exists Σ3.
  unfold apost. split.
  2: { unfold rts_same. rewrite LV3, FRS3, SP3, CG3. repeat split; try reflexivity. exact CR3. }
  eapply ASTA_conseq; [exact HAS|]. cbv beta. intros ms (rmaxw' & m' & RS & AFT & PRm & BH7 & BW7 & BT7 & RC7).
  pose proof AFT as (ART7 & MI7 & WM07 & ST7).
  exists (Z_to_bv 64 n), m'. split; [exact RS|]. split; [exact (conj ART7 (conj MI7 ST7))|].
  pose proof (live_ne_apart RT AF Σ m _ _ _ _ ART0 INR INBI ltac:(intros E; injection E; clear; lia)) as APR.
  assert (WsubW : forall x, outside ((OUT, OUT + n) :: mbio_W K max) x -> outside ((BI + 96, BI + 104) :: RD_W BI (k_rp K) OUT n) x).
  { intros x Ho. unfold mbio_W, mbio_ent in Ho. rewrite <- EBI, EKD in Ho. unfold RD_W. cbn [outside app map fst snd] in Ho |- *. clear - Ho. lia. }
  split. { intros x Hx Ho. apply PRm; [exact Hx| exact (WsubW _ Ho)]. }
  assert (STAP : forall p k x, In (p, k) (rt_live RT Σ) -> client_static x -> ~ (p <= x < p + k)).
  { intros p k x Hin Hs. pose proof (af_live_range RT AF Σ m p k ART0 Hin) as (_ & _ & SG). pose proof (client_static_range x Hs). unfold SEGTOP_A in *. clear - SG H. lia. }
  assert (P7s : forall x : word, client_static (bv_unsigned x) -> m' x = m x).
  { intros x Hs. apply PRm; [apply acl_static; exact Hs|]. unfold RD_W. cbn [outside].
    pose proof (STAP _ _ _ INBI Hs). pose proof (STAP _ _ _ INR Hs). pose proof (STAP _ _ _ INO Hs). clear - H H0 H1 HN HNO. lia. }
  split; [apply (cl_env_agree m m' _ _ ENV); intros a Ha; apply P7s; exact (cl_cell_static _ Ha)|].
  (* [comment removed for export] *)
  assert (AGK : forall p q a k, In (p, q) (rt_live RT Σ) -> ~ In p [BI; k_rp K; OUT] -> p <= a -> a + k <= p + q -> agree_on (fun x => a <= x < a + k) m m').
  { intros p q a k Hp NP H1 H2 x Hx. cbv beta in Hx. cbn [In] in NP. apply PRm; [apply (acl_live _ _ _ p q); [exact Hp| clear - Hx H1 H2; lia]|].
    unfold RD_W. cbn [outside].
    pose proof (live_ne_apart RT AF Σ m _ _ _ _ ART0 Hp INBI ltac:(intros E; injection E; intros; apply NP; left; symmetry; assumption)).
    pose proof (live_ne_apart RT AF Σ m _ _ _ _ ART0 Hp INR ltac:(intros E; injection E; intros; apply NP; right; left; symmetry; assumption)).
    pose proof (live_ne_apart RT AF Σ m _ _ _ _ ART0 Hp INO ltac:(intros E; injection E; intros; apply NP; right; right; left; symmetry; assumption)).
    clear - Hx H1 H2 H H0 H3 HN HNO. lia. }
  (* [comment removed for export] *)
  pose proof (wr_at_wm m m' OUT no (rw_cells_wr_at asegs m OUT _ no OC ltac:(cbn [cells_size csize Nat.add]; clear - LOJ; lia)) WM07) as WRO.
  destruct (wr_at_rw_CB m' OUT no WRO ltac:(clear - LOJ HNO HN; lia)) as (ojunk' & OC7).
  assert (LOJ' : length ojunk' = Z.to_nat no) by (destruct OC7 as [[WF _] _]; cbn in WF; destruct WF as [WF _]; exact WF).
  exists ojunk'. split; [reflexivity|]. split; [exact WM07|]. split; [| exact (conj LOJ' OC7)].
  (* [comment removed for export] *)
  pose proof (fl_ok_land _ 18446744073709551487 (fl_ok_clear16 _ FLOK) ltac:(clear; lia)) as FLOK'.
  exists (Z.land (fl - fl mod 16) 18446744073709551487), rrw, numw, padw, (Z_to_bv 64 (bv_unsigned nr + n)), nw.
  split; [exact EBI|]. split; [exact EBM|]. split; [exact INBI|]. split; [exact BIAL|]. split; [unfold mbio_blocks; rewrite <- EBI, EKD; exact ND|]. split; [exact HM|].
  split; [exact BH7|]. split; [exact BW7|]. split; [exact FLOK'|]. split; [exact BT7|].
  exists rmaxw'. split; [exact INBB|]. split; [exact BBAL|].
  split; [apply (rw_cells_agree asegs m m' _ _ BBC); [apply (AGK (k_bb K) 16); [exact INBB| cbn [In]; clear - NBI NBB NTA; cbn [In] in NBI, NBB, NTA; intuition congruence| lia| cbn [cells_size csize Nat.add]; lia] | exact WM07]|].
  split; [exact INBM|]. split; [exact BMAL|]. split; [exact INR|]. split; [exact RAL|]. split; [clear - OFF0 HN; lia|]. split; [exact LEN|]. split; [exact MAXB|].
  rewrite EKD. exists junk. split; [exact IND|]. split; [exact MAXP|].
  split; [apply (rw_cells_agree asegs m m' _ _ BMC); [apply (AGK (k_bm K) 32); [exact INBM| cbn [In]; clear - NBI NBM NTA; cbn [In] in NBI, NBM, NTA; intuition congruence| lia| cbn [cells_size csize Nat.add]; lia] | exact WM07]|].
  split; [exact RC7|]. split; [exact LJ|].
  apply (rw_cells_agree asegs m m' _ _ DC); [| exact WM07]. apply (AGK d max); [exact IND| | lia| cbn [cells_size csize Nat.add]; clear - LJ MAXP; lia].
  cbn [In]. clear - NBI NR NTA. cbn [In] in NBI, NR, NTA. intuition congruence.
Qed.
End CBreadF.
