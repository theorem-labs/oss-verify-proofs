(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Fz_T_ekit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_env Fz_W1_defs Fz_W1_misc Fz_W1_writec Fz_W2_puts Fz_W2_write.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

Section CBwrite.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis SM0 : stack_malloc_contract RT 0.
(* [comment removed for export] *)
Hypothesis GO_memmeth : GOBJ M_MEM_A 112.
Hypothesis GO_secmeth : GOBJ M_SECMEM_A 112.

Lemma meth_bwrite_sh : forall (Σ : rts RT) (m : mem) meth, ART RT Σ m -> (meth = M_MEM_A \/ meth = M_SECMEM_A) ->
  ro_cells asegs m ((meth + 16) / 8 + 2147450880) [C1 (Z_to_bv 8 0)].
Proof.
  intros Σ m meth HA [-> | ->].
  - pose proof (afp_gsh_byte RT GOBJ AFP Σ m _ _ (M_MEM_A + 16) HA GO_memmeth ltac:(unfold M_MEM_A; lia) ltac:(unfold M_MEM_A; lia) ltac:(reflexivity)) as X.
    cbn [Z.ltb Z.sub Z.add Z.leb M_MEM_A] in X. exact X.
  - pose proof (afp_gsh_byte RT GOBJ AFP Σ m _ _ (M_SECMEM_A + 16) HA GO_secmeth ltac:(unfold M_SECMEM_A; lia) ltac:(unfold M_SECMEM_A; lia) ltac:(reflexivity)) as X.
    cbn [Z.ltb Z.sub Z.add Z.leb M_SECMEM_A] in X. exact X.
Qed.
Lemma meth_bwrite_old_sh : forall (Σ : rts RT) (m : mem) meth, ART RT Σ m -> (meth = M_MEM_A \/ meth = M_SECMEM_A) ->
  ro_cells asegs m ((meth + 24) / 8 + 2147450880) [C1 (Z_to_bv 8 0)].
Proof.
  intros Σ m meth HA [-> | ->].
  - pose proof (afp_gsh_byte RT GOBJ AFP Σ m _ _ (M_MEM_A + 24) HA GO_memmeth ltac:(unfold M_MEM_A; lia) ltac:(unfold M_MEM_A; lia) ltac:(reflexivity)) as X.
    cbn [Z.ltb Z.sub Z.add Z.leb M_MEM_A] in X. exact X.
  - pose proof (afp_gsh_byte RT GOBJ AFP Σ m _ _ (M_SECMEM_A + 24) HA GO_secmeth ltac:(unfold M_SECMEM_A; lia) ltac:(unfold M_SECMEM_A; lia) ltac:(reflexivity)) as X.
    cbn [Z.ltb Z.sub Z.add Z.leb M_SECMEM_A] in X. exact X.
Qed.

(* [comment removed for export] *)
Definition mwrite_entry (gp tp : word) (usp1 BI IN n W f : Z) (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  entry_st (Z_to_bv 64 SITE_bwc_mw) (Z_to_bv 64 (usp1 + -32)) gp tp t0 t1 t2 (Z_to_bv 64 usp1) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 BI) (Z_to_bv 64 IN) (Z_to_bv 64 n) (Z_to_bv 64 e_mem_write) a4 a5 a6 a7
           (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 W) (Z_to_bv 64 ((BI + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 IN) (Z_to_bv 64 BI) (Z_to_bv 64 (BI + 16)) (Z_to_bv 64 (f + 32))
           (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) t3 t4 t5 t6 F fc e_mem_write m.
Definition mwrite_ret (gp tp : word) (usp1 BI IN n W f : Z) (v : word) (m' : mem) (ms : machine_state) : Prop :=
  ret_st (Z_to_bv 64 SITE_bwc_mw) (Z_to_bv 64 (usp1 + -32)) gp tp (Z_to_bv 64 usp1) (Z_to_bv 64 (f + 32))
         (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 W) (Z_to_bv 64 ((BI + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 IN) (Z_to_bv 64 BI) (Z_to_bv 64 (BI + 16)) (Z_to_bv 64 (f + 32))
         (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) v m' ms.

(* [comment removed for export] *)
Definition mwrite_spec (Σ : rts RT) (PMc : Model -> Prop) (sp gp tp s0 ra : word) (usp lo BI IN n W : Z) (m : mem)
    (FP : list (Z * Z)) (PQ : rts RT -> mem -> Prop) : Prop :=
  forall (Σ1 : rts RT) (f pd : Z) (m4 : mem) (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
  (pd = 0 \/ pd = 16) -> usp mod 32 = pd ->
  rt_live RT Σ1 = rt_live RT Σ -> rt_frames RT Σ1 = (f, 0%nat) :: rt_frames RT Σ -> rt_sp0 RT Σ1 = rt_sp0 RT Σ -> rt_credit RT Σ1 = rt_credit RT Σ - 1 -> rt_cg RT Σ1 = rt_cg RT Σ ->
  0 < f -> f mod 64 = 0 ->
  ART RT Σ1 m4 -> mem_inv asegs m4 -> wmono asegs m m4 -> call_ok RT Σ1 m4 (Z_to_bv 64 (usp + -160 - pd + -32)) lo ->
  (forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> (bv_unsigned x < usp - 208 \/ usp <= bv_unsigned x) -> ~ (W <= bv_unsigned x < W + 8) -> m4 x = m x) ->
  rw_cells asegs m4 (usp - 16) [C8 s0; C8 ra] -> rw_cells asegs m4 (usp + -160 - pd + -16) [C8 sp; C8 (Z_to_bv 64 SITE_bwi_bwc)] ->
  cps asegs (ASTA RT Σ1 PMc (eq (mwrite_entry gp tp (usp + -160 - pd) BI IN n W f t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc m4)))
    (fun c => exists (Σ2 : rts RT),
       ASTA RT Σ2 PMc (fun ms => exists m5, mwrite_ret gp tp (usp + -160 - pd) BI IN n W f (Z_to_bv 64 n) m5 ms
           /\ ART RT Σ2 m5 /\ mem_inv asegs m5 /\ stk asegs m5 lo (usp + -160 - pd + -32)
           /\ (forall x : word, aclient (rt_live RT Σ1) (rt_frames RT Σ1) (usp + -160 - pd + -32) (bv_unsigned x) -> outside FP (bv_unsigned x) -> m5 x = m4 x)
           /\ PQ Σ2 m5) c
       /\ rt_frames RT Σ2 = rt_frames RT Σ1 /\ rt_sp0 RT Σ2 = rt_sp0 RT Σ1 /\ In (BI, 128) (rt_live RT Σ2)
       /\ (forall p k, In (p, k) (rt_live RT Σ1) -> In (p, k) (rt_live RT Σ2) \/ (forall x, p <= x < p + k -> ~ outside FP x))).

(* [comment removed for export] *)
Definition bwi_wrap_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BI IN n W meth fl : Z) (shw rrw numw padw ptrw nr nw : word) (wj : list byte) (FP : list (Z * Z)) (PQ : rts RT -> mem -> Prop),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 IN -> a2 = Z_to_bv 64 n -> a3 = Z_to_bv 64 W ->
  (meth = M_MEM_A \/ meth = M_SECMEM_A) -> In (BI, 128) (rt_live RT Σ) -> BI mod 16 = 0 ->
  rw_cells asegs m BI (bio_head meth) -> rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) shw fl rrw numw padw ptrw) -> rw_cells asegs m (BI + 72) (bio_tail nr nw) ->
  0 <= IN < 2^64 -> 1 <= n < 2^31 - 1 ->
  rw_cells asegs m W [CB 8 wj] -> bv_unsigned sp <= W -> W mod 8 = 0 -> W + 8 <= USTACK_TOP ->
  (forall x, ~ outside FP x -> aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) x) ->
  (forall x, BI <= x < BI + 40 \/ BI + 72 <= x < BI + 128 \/ W <= x < W + 8 -> outside FP x) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 208 <= bv_unsigned sp ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  mwrite_spec Σ PMc sp gp tp s0 ra (bv_unsigned sp) lo BI IN n W m FP PQ ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_bio_write_intern m)))
    (fun c => exists (Σ2 Σ3 : rts RT) (m5 : mem),
       ASTA RT Σ3 PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
           /\ ART RT Σ3 m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ wmono asegs m5 m'
           /\ (forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (bv_unsigned x) -> outside FP (bv_unsigned x) ->
                 ~ (BI + 104 <= bv_unsigned x < BI + 112) -> ~ (W <= bv_unsigned x < W + 8) -> m' x = m x)
           /\ (forall x : word, aclient (rt_live RT Σ2) (rt_frames RT Σ) (bv_unsigned sp) (bv_unsigned x) -> ~ (BI + 104 <= bv_unsigned x < BI + 112) -> ~ (W <= bv_unsigned x < W + 8) -> m' x = m5 x)
           /\ rw_cells asegs m' BI (bio_head meth) /\ rw_cells asegs m' (BI + 72) (bio_tail nr (Z_to_bv 64 (bv_unsigned nw + n))) /\ rw_cells asegs m' W [C8 (Z_to_bv 64 n)]) c
       /\ PQ Σ2 m5
       /\ rt_live RT Σ3 = rt_live RT Σ2 /\ rt_frames RT Σ3 = rt_frames RT Σ /\ rt_sp0 RT Σ3 = rt_sp0 RT Σ /\ rt_credit RT Σ3 = rt_credit RT Σ2 /\ rt_cg RT Σ3 = rt_cg RT Σ2).

Theorem bwi_wrap : bwi_wrap_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI IN n W meth fl shw rrw numw padw ptrw nr nw wj FP PQ
    FDO MST -> -> -> -> -> HM INBI BIAL BH BW BT HIN HN WC WLO WAL WHI FPOK FPBI ART0 MI0 CALL HSTK Hfr Hcr MP.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  set (pd := usp mod 32).
  assert (HP : pd = 0 \/ pd = 16) by (unfold pd; clear - SPA; Z.div_mod_to_equations; lia).
  assert (HPM : usp mod 32 = pd) by reflexivity. clearbody pd.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 208 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLOI : SEGTOP_A <= lo) by (unfold SEGTOP_A, STACK_WIN in *; lia).
  set (usp1 := usp + -160 - pd).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & UAR & UT).
  pose proof (af_live_range RT AF Σ m BI 128 ART0 INBI) as (BI0 & BILO' & _). assert (BILO : BI + 128 <= lo) by (clear - BILO' LOW; lia). clear BILO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BI 128 ART0 INBI ltac:(lia)) as BIHI.
  assert (WR : 0 <= W < 2 ^ 64) by (clear - WLO WHI NUM SP0W; unfold USTACK_TOP, STACK_WIN in *; lia).
  (* [comment removed for export] *)
  pose proof (bwi_s0_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pd BI IN n W
                HP HPM ltac:(clear - BI0 BIHI BILO NUM HSTK; unfold USTACK_TOP, RT_STACK in *; lia) HIN ltac:(clear - HN; lia) WR ST ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia) UT SHC UAR MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (a1' & a2' & j8 & m1 & -> & MU1 & WM1 & MI1 & FR1 & GAP1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, GAP1, ST1, Hc1'. fold usp1 in GAP1, ST1, Hc1'. unfold bwi_ftail in FR1.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 160 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 160 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  (* [comment removed for export] *)
  apply (SM0 Σ PMc (Z_to_bv 64 SITE_bwi_smalloc) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 64) a1' a2' (Z_to_bv 64 W) a4 a5 a6 a7
           s2 (Z_to_bv 64 W) s4 (Z_to_bv 64 IN) (Z_to_bv 64 BI) (Z_to_bv 64 n) s8 s9 s10 (Z_to_bv 64 0x7fff8000) t3 t4 t5 t6 F fc m1 lo FDO MST ltac:(left; reflexivity) eq_refl ltac:(clear - Hfr; lia) ltac:(clear - Hcr; lia) ART1 MI1).
  { unfold call_ok. rewrite EU1. split; [exact ST1|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|].
    fold usp in SPA. clear - SPA HP HPM. Z.div_mod_to_equations. lia. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & f & Hc2 & FRS1 & LV1 & SP1 & CR1 & F0 & F64 & FU & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WF2 & WS2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_bwi_smalloc) in Hc2' by (unfold SITE_bwi_smalloc; lia).
  assert (INF : In (f, 0%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  pose proof (af_frames_range RT AF Σ1 m2 f 0%nat ART2 INF) as (_ & FLO & _ & PF).
  assert (INBI1 : In (BI, 128) (rt_live RT Σ1)) by (rewrite LV1; exact INBI).
  pose proof (PF BI 128 INBI1) as PFB. clear PF. pose proof (proj1 (af_fshadow_apart RT AF Σ1 m2 f 0%nat ART2 INF) BI 128 INBI1) as SLB.
  change (fs_size 0) with 64 in PFB, SLB.
  pose proof (af_frames_align RT AF Σ1 m2 f 0%nat ART2 INF) as (_ & FIMG).
  pose proof (af_frames_hi RT AF Σ1 m2 f 0%nat ART2 INF) as FSH.
  rewrite SP1 in FLO. change (fs_size 0) with 64 in FLO, FSH, FU, WF2, WS2. change (64 - 8) with 56 in WF2. change (64 / 8) with 8 in WS2.
  unfold shad, SHB in WS2. unfold SEGTOP_A in FIMG.
  assert (SHF : shad (f + 64) = shad f + 8) by (replace (f + 64) with (f + 64 * 1) by lia; rewrite (shad_add64 f 1 F64); lia).
  rewrite SHF in SLB. unfold shad, SHB in SLB.
  assert (AG2 : forall a k, usp1 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m1 m2).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES2. left. lia. }
  cl_keep FR1 AG2 WM2 FR2.
  assert (GAP2 : stk asegs m2 usp1 (usp + -160)).
  { apply (stk_agree_nw asegs m1 m2 _ _ GAP1). intros x Hx. cbv beta in Hx. apply PRES2. left. unfold USTACK_TOP in *. lia. }
  destruct (wr_at_rw_CB m2 f 56 WF2 ltac:(lia)) as (fj & FB2). destruct (wr_at_rw_CB m2 (f / 8 + 2147450880) 8 WS2 ltac:(lia)) as (sj & SB2).
  change (Z.to_nat 56) with 56%nat in FB2. change (Z.to_nat 8) with 8%nat in SB2.
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & _ & _ & _ & UT2).
  (* [comment removed for export] *)
  pose proof (bwi_s1a_walk sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s2 (Z_to_bv 64 W) s4 (Z_to_bv 64 IN) (Z_to_bv 64 BI) s8 s9 s10 (Z_to_bv 64 0x7fff8000) u3 u4 u5 u6
                ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F2 fc2 m2 f lo pd n j8 fj sj
                HP F0 FIMG ltac:(lia) ltac:(destruct FSH; [left | right]; lia) ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia)
                FR2 GAP2 ST2 FB2 SB2 MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (j0 & m3 & -> & MU3 & WM3 & MI3 & FR3 & GAP3 & ST3 & FB3 & SB3) & Hc3'). clear Hc3.
  fold usp in MU3, FR3, GAP3, Hc3'. fold usp1 in GAP3, ST3, Hc3'.
  assert (ART3 : ART RT Σ1 m3).
  { apply (af_frame RT AF Σ1 m2 m3 (usp - 176) ART2 ltac:(rewrite SP1; lia)); [| exact WM3].
    intros a Ha. apply MU3. cbn [outside]. split; [| exact I]. intros Hin; apply Ha. apply acl_stack. unfold USTACK_TOP in *. lia. }
  destruct (af_client_consts RT AF Σ1 m3 ART3) as (_ & _ & _ & _ & UT3).
  (* [comment removed for export] *)
  assert (A03 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> (bv_unsigned x < usp - 176 \/ usp <= bv_unsigned x) -> m3 x = m x).
  { intros x Hx Hlt.
    rewrite (MU3 x ltac:(cbn [outside]; clear - Hlt; lia)).
    rewrite (PRES2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; lia])).
    apply MU1. cbn [outside]. clear - Hlt. lia. }
  assert (AGB3 : forall a k, BI <= a -> a + k <= BI + 128 -> agree_on (fun x => a <= x < a + k) m m3).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply A03; [apply (acl_live _ _ _ BI 128); [exact INBI | lia] | left; clear - Hx H2 BILO HSTK; unfold RT_STACK in *; lia]. }
  assert (WM03 : wmono asegs m m3) by exact (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 WM3)).
  assert (BH3 : rw_cells asegs m3 BI (bio_head meth)) by (apply (rw_cells_agree asegs m m3 _ _ BH); [apply AGB3; unfold bio_head; cbn [cells_size csize Nat.add]; lia | exact WM03]).
  assert (BW3 : rw_cells asegs m3 (BI + 40) (bio_w1_cells (Z_to_bv 64 1) shw fl rrw numw padw ptrw))
    by (apply (rw_cells_agree asegs m m3 _ _ BW); [apply AGB3; unfold bio_w1_cells; cbn [cells_size csize Nat.add]; lia | exact WM03]).
  assert (BT3 : rw_cells asegs m3 (BI + 72) (bio_tail nr nw)) by (apply (rw_cells_agree asegs m m3 _ _ BT); [apply AGB3; unfold bio_tail; cbn [cells_size csize Nat.add]; lia | exact WM03]).
  assert (WC3 : rw_cells asegs m3 W [CB 8 wj]).
  { apply (rw_cells_agree asegs m m3 _ _ WC); [| exact WM03]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply A03; [apply acl_stack; clear - Hx WLO WHI; lia| right; clear - Hx WLO; lia]. }
  pose proof (proj2 (af_acc_live RT AF Σ1 m3 BI 128 ART3 INBI1)) as ACC3.
  pose proof (af_acc_stack RT AF Σ1 m3 W 8 ART3 ltac:(rewrite SP1; clear - WLO NUM; lia) ltac:(clear - WHI; lia)) as ACCW3.
  (* [comment removed for export] *)
  pose proof (bwi_s1b_walk sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s4 s8 s9 u3 u4 u5 u6
                ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F2 fc2 m3 f lo pd BI IN n W meth fl shw rrw numw padw ptrw j0 fj sj wj
                HP F0 F64 FIMG ltac:(lia) ltac:(destruct FSH; [left | right]; lia) ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia)
                UT3 FR3 GAP3 ST3 FB3 SB3 WC3 ACCW3 ltac:(fold usp; exact WLO) WAL ltac:(clear - WHI; unfold USTACK_TOP in *; lia) HM BH3 BW3 ACC3 BI0 BIAL BIHI BILO ltac:(clear - PFB; lia) (meth_bwrite_sh Σ1 m3 meth ART3 HM) HIN ltac:(clear - HN; lia) MI3) as W2.
  fold usp usp1 in W2.
  cl_lift W2 Hc3' c4 Hc4.
  destruct (ASTA_unpack RT Σ1 _ _ c4 Hc4) as (ms4 & (hj & rj & tj & j4 & m4 & -> & MU4 & WM4 & MI4 & HDR4 & SB4 & WC4 & FR4 & DL4 & SH4 & GAP4 & ST4) & Hc4'). clear Hc4.
  fold usp in MU4, FR4, DL4, SH4, GAP4, ST4, Hc4'. fold usp1 in MU4, DL4, SH4, GAP4, ST4, Hc4'.
  assert (ART4 : ART RT Σ1 m4).
  { apply (af_frame RT AF Σ1 m3 m4 usp1 ART3 ltac:(rewrite SP1; unfold usp1; lia)); [| exact WM4].
    intros a Ha. apply MU4. cbn [outside]. split; [| split; [| split; [| split; [| exact I]]]]; intros Hin; apply Ha.
    - apply (acl_frame _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; lia].
    - apply (acl_fshadow _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; rewrite SHF; unfold shad, SHB; lia].
    - apply acl_stack. unfold usp1, USTACK_TOP in *. clear - Hin WLO WHI NUM HP. lia.
    - apply acl_stack. unfold usp1, USTACK_TOP in *. lia. }
  destruct (af_client_consts RT AF Σ1 m4 ART4) as (_ & SHC4 & _ & _ & UT4).
  (* [comment removed for export] *)
  assert (A04 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> (bv_unsigned x < usp - 176 \/ usp <= bv_unsigned x) -> ~ (W <= bv_unsigned x < W + 8) -> m4 x = m x).
  { intros x Hx Hlt HW.
    destruct (newframe_apart RT AF Σ Σ1 m2 f 0%nat usp _ ART2 FRS1 LV1 SP1 ltac:(lia) Hx) as (N1 & N2).
    change (fs_size 0) with 64 in N1, N2. rewrite SHF in N2. unfold shad, SHB in N2.
    rewrite (MU4 x ltac:(cbn [outside]; unfold usp1; clear - N1 N2 Hlt HW HP; lia)). exact (A03 x Hx Hlt). }
  assert (WM04 : wmono asegs m m4) by exact (wmono_trans asegs _ _ _ WM03 WM4).
  assert (FRR4 : rw_cells asegs m4 (usp - 16) [C8 s0; C8 ra]).
  { unfold bwi_ftail in FR4. pose proof (rw_cells_skip m4 (usp + -160) [CB 56 j4; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] _ FR4) as X.
    cbn [cells_size csize Nat.add app] in X. replace (usp + -160 + Z.of_nat 144) with (usp - 16) in X by lia. exact X. }
  pose proof (proj2 (af_acc_live RT AF Σ1 m4 BI 128 ART4 INBI1)) as ACC4.
  assert (BH4 : rw_cells asegs m4 BI (bio_head meth)).
  { apply (rw_cells_agree asegs m3 m4 _ _ BH3); [| exact WM4]. intros x Hx. cbv beta in Hx. unfold bio_head in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply MU4. cbn [outside]. unfold usp1. clear - Hx PFB SLB BILO HSTK WLO FLO LOW HP. unfold RT_STACK in *. lia. }
  (* [comment removed for export] *)
  pose proof (bwc_s0_walk (Z_to_bv 64 SITE_bwi_bwc) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 e_bwrite_conv) b5 b6 b7
                (Z_to_bv 64 f) (Z_to_bv 64 W) (Z_to_bv 64 ((BI + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 IN) (Z_to_bv 64 BI) (Z_to_bv 64 (BI + 16)) (Z_to_bv 64 (f + 32))
                (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) u3 u4 u5 u6 F2 fc2 m4 lo BI IN n (f + 32) meth) as W3.
  rewrite EU1 in W3.
  specialize (W3 ltac:(unfold usp1, RT_STACK in *; clear - HSTK HP; lia) ltac:(lia) ltac:(unfold usp1, USTACK_TOP in *; clear - NUM HP; lia) ST4 UT4 SHC4 HM BH4 ACC4 BI0 BIAL BIHI BILO
                 (meth_bwrite_old_sh Σ1 m4 meth ART4 HM) HIN HN ltac:(clear - F0 FLO LOW NUM HSTK; unfold USTACK_TOP, RT_STACK in *; lia) MI4).
  cl_lift W3 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ1 _ _ c5 Hc5) as (ms5 & (a4x & m5 & -> & MU5 & WM5 & MI5 & FR5 & ST5) & Hc5'). clear Hc5.
  rewrite EU1 in MU5, FR5, ST5, Hc5'. unfold bwc_frame in FR5.
  assert (ART5 : ART RT Σ1 m5).
  { apply (af_frame RT AF Σ1 m4 m5 (usp1 - 32) ART4 ltac:(rewrite SP1; unfold usp1; lia)); [| exact WM5].
    intros a Ha. apply MU5. cbn [outside]. split; [| exact I]. intros Hin; apply Ha. apply acl_stack. unfold usp1, USTACK_TOP in *. lia. }
  assert (A05 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> (bv_unsigned x < usp - 208 \/ usp <= bv_unsigned x) -> ~ (W <= bv_unsigned x < W + 8) -> m5 x = m x).
  { intros x Hx Hlt HW. rewrite (MU5 x ltac:(cbn [outside]; unfold usp1; clear - Hlt HP; lia)). apply A04; [exact Hx| clear - Hlt; lia| exact HW]. }
  assert (WM05 : wmono asegs m m5) by exact (wmono_trans asegs _ _ _ WM04 WM5).
  assert (FRR5 : rw_cells asegs m5 (usp - 16) [C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m4 m5 _ _ FRR4); [| exact WM5]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply MU5. cbn [outside]. unfold usp1. clear - Hx HP. lia. }
  assert (REC5 : rw_cells asegs m5 (usp1 + -16) [C8 sp; C8 (Z_to_bv 64 SITE_bwi_bwc)]).
  { pose proof (rw_cells_skip m5 (usp1 + -32) [C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 usp1)] _ FR5) as X. cbn [cells_size csize Nat.add app] in X.
    replace (usp1 + -32 + Z.of_nat 16) with (usp1 + -16) in X by lia. exact X. }
  assert (CO5 : call_ok RT Σ1 m5 (Z_to_bv 64 (usp1 + -32)) lo).
  { fold usp in SPA. unfold call_ok. rewrite (unsigned_lit (usp1 + -32)) by (unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia). rewrite SP1.
    split; [exact ST5|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|]. clear - SPA HP HPM. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  apply (MP Σ1 f pd m5 u0 u1 u2 a4x b5 b6 b7 u3 u4 u5 u6 F2 fc2 HP HPM LV1 FRS1 SP1 CR1 CG1 F0 F64 ART5 MI5 WM05).
  { fold usp usp1. exact CO5. }
  { exact A05. }
  { exact FRR5. }
  { fold usp usp1. exact REC5. }
  { fold usp usp1. unfold mwrite_entry. exact Hc5'. }
  clear Hc5'. intros c6 (Σ2 & Hc6 & FRS2 & SP2 & INBI2 & LVK).
  destruct (ASTA_unpack RT Σ2 _ _ c6 Hc6) as (ms6 & (m6 & RS6 & ART6 & MI6 & ST6 & PRES6 & HPQ) & Hc6'). clear Hc6.
  destruct RS6 as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F6 & fc6 & ->).
  fold usp in ST6, PRES6, Hc6'. fold usp1 in ST6, PRES6, Hc6'.
  rewrite (ret_pc_even SITE_bwc_mw) in Hc6' by (unfold SITE_bwc_mw; lia).
  assert (INF2 : In (f, 0%nat) (rt_frames RT Σ2)) by (rewrite FRS2; exact INF).
  pose proof (af_frames_range RT AF Σ2 m6 f 0%nat ART6 INF2) as (_ & _ & _ & PF2).
  pose proof (PF2 BI 128 INBI2) as PFB2. pose proof (proj1 (af_fshadow_apart RT AF Σ2 m6 f 0%nat ART6 INF2) BI 128 INBI2) as SLB2.
  change (fs_size 0) with 64 in PFB2, SLB2. rewrite SHF in SLB2. unfold shad, SHB in SLB2.
  (* [comment removed for export] *)
  assert (NFP : forall x, (usp - 208 <= x < usp) \/ (f <= x < f + 64) \/ (f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 8) -> outside FP x).
  { intros x Hx. destruct (outside_dec FP x) as [H|H]; [exact H| exfalso]. pose proof (FPOK x H) as AC. fold usp in AC.
    destruct (newframe_apart RT AF Σ Σ1 m2 f 0%nat usp _ ART2 FRS1 LV1 SP1 ltac:(lia) AC) as (N1 & N2).
    change (fs_size 0) with 64 in N1, N2. rewrite SHF in N2. unfold shad, SHB in N2.
    pose proof (cl_split RT AF Σ m usp 208 _ ART0 ltac:(lia) ltac:(lia) AC) as N3. clear - Hx N1 N2 N3. lia. }
  assert (AG6 : forall a k, (usp1 - 32 <= a /\ a + k <= usp) \/ (f <= a /\ a + k <= f + 56) \/ (f / 8 + 2147450880 <= a /\ a + k <= f / 8 + 2147450880 + 8)
                            \/ (BI <= a /\ a + k <= BI + 40) \/ (BI + 72 <= a /\ a + k <= BI + 128) \/ (W <= a /\ a + k <= W + 8) ->
            agree_on (fun x => a <= x < a + k) m5 m6).
  { intros a k H x Hx. cbv beta in Hx. pose proof (div8_facts f) as Q1. destruct H as [H|[H|[H|[H|[H|H]]]]].
    - apply PRES6; [left; unfold usp1 in *; lia | apply NFP; left; unfold usp1 in *; clear - H Hx HP; lia].
    - apply PRES6; [apply (acl_frame _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; lia] | apply NFP; right; left; clear - H Hx; lia].
    - apply PRES6; [apply (acl_fshadow _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; rewrite SHF; unfold shad, SHB; lia] | apply NFP; right; right; clear - H Hx; lia].
    - apply PRES6; [apply (acl_live _ _ _ BI 128); [exact INBI1 | lia] | apply FPBI; left; clear - H Hx; lia].
    - apply PRES6; [apply (acl_live _ _ _ BI 128); [exact INBI1 | lia] | apply FPBI; right; left; clear - H Hx; lia].
    - apply PRES6; [apply acl_stack; unfold usp1, USTACK_TOP in *; clear - H Hx WLO WHI HP; lia | apply FPBI; right; right; clear - H Hx; lia]. }
  assert (FRB6 : rw_cells asegs m6 (usp1 + -32) [C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 usp1); C8 sp; C8 (Z_to_bv 64 SITE_bwi_bwc)]).
  { apply (rw_cells_agree_nw asegs m5 m6 _ _ FR5). apply AG6. left. cbn [cells_size csize Nat.add]. unfold usp1. clear - HP. lia. }
  assert (PRC6 : rw_cells asegs m6 (f + 32) [CB 8 rj]).
  { pose proof (rw_cells_skip m4 f [C8 (Z_to_bv 64 BP_MAGIC); C8 (Z_to_bv 64 BWI_DESCR); C8 (Z_to_bv 64 e_bio_write_intern); CB 8 hj] _ HDR4) as X.
    cbn [cells_size csize Nat.add app] in X. replace (f + Z.of_nat 32) with (f + 32) in X by lia. pose proof (rw_cells_head m4 (f + 32) _ _ X) as Y.
    apply (rw_cells_agree_nw asegs m5 m6); [apply (rw_cells_agree asegs m4 m5 _ _ Y); [| exact WM5] |].
    - intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply MU5. cbn [outside]. unfold usp1. clear - Hx FLO LOW HSTK HP. unfold RT_STACK in *. lia.
    - apply AG6. right; left. cbn [cells_size csize Nat.add]. clear; lia. }
  assert (ESH : (f + 32) / 8 + 2147450880 = f / 8 + 2147450880 + 4) by (clear - F64; Z.div_mod_to_equations; lia).
  assert (SB5 : rw_cells asegs m5 (f / 8 + 2147450880) bp_shadow).
  { apply (rw_cells_agree asegs m4 m5 _ _ SB4); [| exact WM5]. intros x Hx. cbv beta in Hx. unfold bp_shadow in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply MU5. cbn [outside]. unfold usp1. pose proof (div8_facts f) as Q1. clear - Hx FLO LOW HSTK HP FSH F0 Q1 NUM. unfold RT_STACK, USTACK_TOP in *. lia. }
  assert (SB6 : rw_cells asegs m6 (f / 8 + 2147450880) bp_shadow).
  { apply (rw_cells_agree_nw asegs m5 m6 _ _ SB5). apply AG6. right; right; left. cbn [bp_shadow cells_size csize Nat.add]. clear; lia. }
  assert (PSH6 : rw_cells asegs m6 ((f + 32) / 8 + 2147450880) [C1 (Z_to_bv 8 0)]).
  { rewrite ESH. unfold bp_shadow in SB6. pose proof (rw_cells_skip m6 (f / 8 + 2147450880) [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15))] _ SB6) as X.
    cbn [cells_size csize Nat.add app] in X. replace (f / 8 + 2147450880 + Z.of_nat 4) with (f / 8 + 2147450880 + 4) in X by lia. exact (rw_cells_head m6 _ _ _ X). }
  (* [comment removed for export] *)
  pose proof (bwc_s1_walk (Z_to_bv 64 SITE_bwi_bwc) (Z_to_bv 64 SITE_bwc_mw) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) v0 v1 v2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 f) d1 d2 d3 d4 d5 d6 d7
                (Z_to_bv 64 W) (Z_to_bv 64 ((BI + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 IN) (Z_to_bv 64 BI) (Z_to_bv 64 (BI + 16)) (Z_to_bv 64 (f + 32))
                (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) v3 v4 v5 v6 F6 fc6 m6 lo (f + 32) n rj) as W4.
  rewrite EU1 in W4.
  specialize (W4 ltac:(unfold usp1, RT_STACK in *; clear - HSTK HP; lia) ltac:(lia) ltac:(unfold usp1, USTACK_TOP in *; clear - NUM HP; lia) ST6 FRB6 PRC6 PSH6
                 ltac:(clear - F0; lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) ltac:(clear - FLO LOW; lia) ltac:(clear - FSH; lia) ltac:(clear - HN; lia) MI6).
  cl_lift W4 Hc6' c7 Hc7.
  destruct (ASTA_unpack RT Σ2 _ _ c7 Hc7) as (ms7 & (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & m7 & -> & MU7 & WM7 & MI7 & ST7 & LW7) & Hc7'). clear Hc7.
  rewrite (ret_pc_even SITE_bwi_bwc) in Hc7' by (unfold SITE_bwi_bwc; lia).
  rewrite EU1 in ST7.
  assert (ART7 : ART RT Σ2 m7).
  { apply (af_frame RT AF Σ2 m6 m7 usp1 ART6 ltac:(rewrite SP2, SP1; unfold usp1; lia)); [| exact WM7].
    intros a Ha. apply MU7. cbn [outside]. split; [| exact I]. intros Hin; apply Ha. apply (acl_frame _ _ _ f 0%nat); [exact INF2 | change (fs_size 0) with 64; lia]. }
  (* [comment removed for export] *)
  assert (AG47 : forall a k, (usp1 <= a /\ a + k <= usp) \/ (f <= a /\ a + k <= f + 32) \/ (f / 8 + 2147450880 <= a /\ a + k <= f / 8 + 2147450880 + 8)
                             \/ (BI <= a /\ a + k <= BI + 40) \/ (BI + 72 <= a /\ a + k <= BI + 128) \/ (W <= a /\ a + k <= W + 8) ->
            forall x : word, a <= bv_unsigned x < a + k -> m7 x = m4 x).
  { intros a k H x Hx. pose proof (div8_facts f) as Q1.
    rewrite (MU7 x ltac:(cbn [outside]; split; [| exact I]; unfold usp1 in H; clear - H Hx PFB SLB FLO LOW HSTK HP FSH F0 Q1 WLO NUM FU; unfold RT_STACK, USTACK_TOP in *; lia)).
    rewrite (AG6 a k ltac:(clear - H; lia) x Hx).
    apply MU5. cbn [outside]. split; [| exact I]. unfold usp1 in H |- *. clear - H Hx PFB SLB FLO LOW HSTK HP FSH F0 Q1 WLO BILO NUM FU. unfold RT_STACK, USTACK_TOP in *. lia. }
  assert (FR7 : rw_cells asegs m7 (usp + -160) (CB 56 j4 :: bwi_ftail s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)).
  { apply (rw_cells_agree_nw asegs m4 m7 _ _ FR4). intros x Hx. cbv beta in Hx. unfold bwi_ftail in Hx. cbn [cells_size csize Nat.add] in Hx. apply (AG47 (usp + -160) 160); [left; unfold usp1; clear - HP; lia| clear - Hx; lia]. }
  assert (DL7 : rw_cells asegs m7 (usp1 + 24) [C8 (Z_to_bv 64 n)]).
  { apply (rw_cells_agree_nw asegs m4 m7 _ _ DL4). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply (AG47 (usp1 + 24) 8); [left; unfold usp1; clear - HP; lia| clear - Hx; lia]. }
  assert (SH7 : rw_cells asegs m7 (usp1 + 16) [C8 (Z_to_bv 64 ((BI + 16) ≫ 3 + 2147450880))]).
  { apply (rw_cells_agree_nw asegs m4 m7 _ _ SH4). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply (AG47 (usp1 + 16) 8); [left; unfold usp1; clear - HP; lia| clear - Hx; lia]. }
  assert (GAP7 : stk asegs m7 usp1 (usp + -160)).
  { apply (stk_agree_nw asegs m4 m7 _ _ GAP4). intros x Hx. cbv beta in Hx. apply (AG47 usp1 pd); [left; unfold usp1; clear - HP; lia| clear - Hx HP; unfold usp1 in *; lia]. }
  assert (HDR7 : rw_cells asegs m7 f [C8 (Z_to_bv 64 BP_MAGIC); C8 (Z_to_bv 64 BWI_DESCR); C8 (Z_to_bv 64 e_bio_write_intern); CB 8 hj]).
  { destruct (proj1 (rw_cells_app m4 f [C8 (Z_to_bv 64 BP_MAGIC); C8 (Z_to_bv 64 BWI_DESCR); C8 (Z_to_bv 64 e_bio_write_intern); CB 8 hj] [CB 8 rj; CB 16 tj]) HDR4) as [X _].
    apply (rw_cells_agree_nw asegs m4 m7 _ _ X). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply (AG47 f 32); [right; left; clear; lia| clear - Hx; lia]. }
  assert (SB7 : rw_cells asegs m7 (f / 8 + 2147450880) bp_shadow).
  { apply (rw_cells_agree_nw asegs m4 m7 _ _ SB4). intros x Hx. cbv beta in Hx. unfold bp_shadow in Hx. cbn [cells_size csize Nat.add] in Hx. apply (AG47 (f / 8 + 2147450880) 8); [do 2 right; left; clear; lia| clear - Hx; lia]. }
  assert (WC7 : rw_cells asegs m7 W [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_agree_nw asegs m4 m7 _ _ WC4). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply (AG47 W 8); [do 5 right; clear; lia| clear - Hx; lia]. }
  assert (BH7 : rw_cells asegs m7 BI (bio_head meth)).
  { apply (rw_cells_agree_nw asegs m4 m7 _ _ BH4). intros x Hx. cbv beta in Hx. unfold bio_head in Hx. cbn [cells_size csize Nat.add] in Hx. apply (AG47 BI 40); [do 3 right; left; clear; lia| clear - Hx; lia]. }
  assert (BT7 : rw_cells asegs m7 (BI + 72) (bio_tail nr nw)).
  { apply (rw_cells_agree_nw asegs m4 m7); [apply (rw_cells_agree asegs m m4 _ _ BT); [| exact WM04] |].
    - intros x Hx. cbv beta in Hx. unfold bio_tail in Hx. cbn [cells_size csize Nat.add] in Hx. apply A04; [apply (acl_live _ _ _ BI 128); [exact INBI | clear - Hx; lia] | left; clear - Hx BILO HSTK; unfold RT_STACK in *; lia | clear - Hx BILO HSTK WLO; unfold RT_STACK in *; lia].
    - intros x Hx. cbv beta in Hx. unfold bio_tail in Hx. cbn [cells_size csize Nat.add] in Hx. apply (AG47 (BI + 72) 56); [do 4 right; left; clear; lia| clear - Hx; lia]. }
  pose proof (proj2 (af_acc_live RT AF Σ2 m7 BI 128 ART7 INBI2)) as ACC7.
  pose proof (af_acc_stack RT AF Σ2 m7 W 8 ART7 ltac:(rewrite SP2, SP1; clear - WLO NUM; lia) ltac:(clear - WHI; lia)) as ACCW7.
  (* [comment removed for export] *)
  pose proof (bwi_s2_walk sp gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 w3 w4 w5 w6
                ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F6 fc6 m7 f lo pd BI IN n W meth hj j4 nr nw (Z_to_bv 64 0)
                HP F0 F64 FIMG ltac:(clear - FLO LOW; lia) ltac:(destruct FSH; [left | right]; lia) ltac:(fold usp; unfold RT_STACK in *; clear - HSTK; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; clear - NUM; lia)) as W5.
  fold usp usp1 in W5.
  specialize (W5 FR7 DL7 SH7 GAP7 ST7 HDR7 LW7 SB7 WC7 ACCW7 WLO WAL ltac:(clear - WHI; unfold USTACK_TOP in *; lia) BH7 BT7 ACC7 BI0 BIAL BIHI BILO ltac:(clear - PFB2; lia) ltac:(clear - HN; lia) HIN MI7).
  cl_lift W5 Hc7' c8 Hc8.
  destruct (ASTA_unpack RT Σ2 _ _ c8 Hc8) as (ms8 & (ra1 & y0 & y1 & y2 & g0 & g1 & g2 & g3 & g4 & g5 & g7 & y3 & y4 & y5 & y6 & m8 & -> & MU8 & WM8 & MI8 & FR8 & WC8 & BT8 & GAP8 & ST8) & Hc8'). clear Hc8.
  fold usp in MU8, FR8, GAP8, Hc8'. fold usp1 in GAP8, ST8, Hc8'.
  fold usp in ST8. fold usp1 in ST8.
  assert (ART8 : ART RT Σ2 m8).
  { apply (af_frame RT AF Σ2 m7 m8 usp1 ART7 ltac:(rewrite SP2, SP1; unfold usp1; lia)); [| exact WM8].
    intros a Ha. apply MU8. cbn [outside]. split; [| split; [| split; [| split; [| exact I]]]]; intros Hin; apply Ha.
    - apply (acl_live _ _ _ BI 128); [exact INBI2 | lia].
    - apply acl_stack. unfold usp1, USTACK_TOP in *. clear - Hin WLO WHI NUM HP. lia.
    - apply (acl_frame _ _ _ f 0%nat); [exact INF2 | change (fs_size 0) with 64; lia].
    - apply (acl_fshadow _ _ _ f 0%nat); [exact INF2 | change (fs_size 0) with 64; rewrite SHF; unfold shad, SHB; lia]. }
  (* [comment removed for export] *)
  destruct (af_frame_release RT AF Σ2 m8 f 0%nat (rt_frames RT Σ) ART8 ltac:(rewrite FRS2; exact FRS1)) as (Σ3 & flg & FLC & NAC & FL0 & FLW & FW & REL).
  change (fs_size 0) with 64 in FW. replace (f + 64 - 8) with (f + 56) in FW by lia. rewrite SP2, SP1 in FLW.
  (* [comment removed for export] *)
  pose proof (bwi_s3_walk ra1 ra sp gp (Z_to_bv 64 0xba3ef0) y0 y1 y2 g0 g1 g2 g3 g4 g5 g7 (Z_to_bv 64 W) (Z_to_bv 64 ((BI + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 IN) (Z_to_bv 64 BI) (Z_to_bv 64 (BI + 16)) (Z_to_bv 64 (f + 32))
                (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) y3 y4 y5 y6
                s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F6 fc6 m8 f flg lo pd j4
                HP ltac:(fold usp; unfold RT_STACK in *; clear - HSTK; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; clear - NUM; lia)
                F0 ltac:(clear - FLO LOW; lia) FL0 ltac:(clear - FLW LOW; lia) ST8 GAP8 FR8 FW FLC MI8) as W6.
  fold usp usp1 in W6.
  cl_lift W6 Hc8' c9 Hc9.
  destruct (ASTA_unpack RT Σ2 _ _ c9 Hc9) as (ms9 & (z0 & z1 & z2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & z3 & z4 & z5 & z6 & m9 & -> & MU9 & WM9 & MI9 & ST9 & FLC9) & Hc9'). clear Hc9.
  fold usp in ST9.
  destruct (REL m9 MU9 WM9 FLC9) as (ART9 & FRS3 & LV3 & SP3 & CR3 & AL3 & AM3 & CG3).
  (* [comment removed for export] *)
  assert (NFL2 : forall x, aclient (rt_live RT Σ2) (rt_frames RT Σ2) usp1 x -> x <> flg).
  { intros x Hx Ex. subst x. destruct Hx as [H|H]; [unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; clear - H FLW NUM HP; lia|].
    apply NAC. right. exact H. }
  assert (NFL5 : forall x, aclient (rt_live RT Σ2) (rt_frames RT Σ) usp x -> x <> flg).
  { intros x Hx. apply NFL2. apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | rewrite FRS2, FRS1; intros e' He'; right; exact He' | unfold usp1; clear - HP; lia]. }
  (* [comment removed for export] *)
  assert (A69 : forall x : word, aclient (rt_live RT Σ2) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (BI + 104 <= bv_unsigned x < BI + 112) -> ~ (W <= bv_unsigned x < W + 8) -> m9 x = m6 x).
  { intros x Hx HB HW.
    destruct (frame_apart RT AF Σ2 m6 f 0%nat (rt_frames RT Σ) usp _ ART6 ltac:(rewrite FRS2; exact FRS1) ltac:(rewrite SP2, SP1; lia) Hx) as (N1 & N2).
    change (fs_size 0) with 64 in N1, N2. rewrite SHF in N2. unfold shad, SHB in N2.
    rewrite (MU9 x ltac:(cbn [outside]; split; [pose proof (NFL5 _ Hx) as NE; clear - NE; lia | exact I])).
    rewrite (MU8 x ltac:(cbn [outside]; clear - N1 N2 HB HW; lia)).
    apply MU7. cbn [outside]. clear - N1. lia. }
  apply Hk. exists Σ2, Σ3, m6.
  split; [| split; [exact HPQ| split; [exact LV3 | split; [exact FRS3 | split; [rewrite SP3, SP2; exact SP1 | split; [exact CR3 | exact CG3]]]]]].
  eapply ASTA_conseq; [exact (ASTA_switch RT Σ2 Σ3 PMc _ c9 Hc9' AL3 AM3)|]. intros ms <-. exists m9.
  split; [exists z0, z1, z2, h1, h2, h3, h4, h5, h6, h7, z3, z4, z5, z6, F6, fc6; reflexivity|].
  split; [exact ART9|]. split; [exact MI9|]. split; [exact ST9|]. split; [exact (wmono_trans asegs _ _ _ WM7 (wmono_trans asegs _ _ _ WM8 WM9))|].
  assert (A09 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> outside FP (bv_unsigned x) ->
                 ~ (BI + 104 <= bv_unsigned x < BI + 112) -> ~ (W <= bv_unsigned x < W + 8) -> m9 x = m x).
  { intros x Hx Ho HB HW.
    assert (Hx2 : aclient (rt_live RT Σ2) (rt_frames RT Σ) usp (bv_unsigned x)).
    { apply (acl_keep _ _ _ _ FP _ LVK); [| exact Ho]. rewrite LV1. exact Hx. }
    rewrite (A69 x Hx2 HB HW).
    rewrite (PRES6 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [rewrite LV1; auto | rewrite FRS1; intros e' He'; right; exact He' | unfold usp1; clear - HP; lia]) Ho).
    apply A05; [exact Hx| | exact HW]. destruct (cl_split RT AF Σ m usp 208 _ ART0 ltac:(lia) ltac:(lia) Hx) as [Hi|Lo]; [right; exact Hi | left; exact Lo]. }
  split; [exact A09|]. split; [exact A69|].
  split.
  { apply (rw_cells_agree_nw asegs m m9 _ _ BH). intros x Hx. cbv beta in Hx. unfold bio_head in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply A09; [apply (acl_live _ _ _ BI 128); [exact INBI | clear - Hx; lia] | apply FPBI; left; clear - Hx; lia | clear - Hx; lia | clear - Hx WLO BILO HSTK; unfold RT_STACK in *; lia]. }
  split.
  { apply (rw_cells_agree_nw asegs m8 m9 _ _ BT8). intros x Hx. cbv beta in Hx. unfold bio_tail in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply MU9. cbn [outside]. split; [| exact I]. pose proof (NFL5 (bv_unsigned x) ltac:(apply (acl_live _ _ _ BI 128); [exact INBI2 | clear - Hx; lia])) as NE. clear - NE. lia. }
  apply (rw_cells_agree_nw asegs m8 m9 _ _ WC8). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
  apply MU9. cbn [outside]. split; [| exact I]. pose proof (NFL5 (bv_unsigned x) ltac:(apply acl_stack; unfold USTACK_TOP in *; clear - Hx WLO WHI; lia)) as NE. clear - NE. lia.
Qed.

(* [comment removed for export] *)
Definition mwrite_specB (Σ : rts RT) (PMc : Model -> Prop) (sp gp tp s0 ra : word) (usp lo BI IN n : Z) (m : mem)
    (FP : list (Z * Z)) (PQ : rts RT -> mem -> Prop) : Prop :=
  forall (Σ1 : rts RT) (f pd : Z) (m4 : mem) (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
  (pd = 0 \/ pd = 16) -> (usp + -32) mod 32 = pd ->
  rt_live RT Σ1 = rt_live RT Σ -> rt_frames RT Σ1 = (f, 0%nat) :: rt_frames RT Σ -> rt_sp0 RT Σ1 = rt_sp0 RT Σ -> rt_credit RT Σ1 = rt_credit RT Σ - 1 -> rt_cg RT Σ1 = rt_cg RT Σ ->
  0 < f -> f mod 64 = 0 ->
  ART RT Σ1 m4 -> mem_inv asegs m4 -> wmono asegs m m4 -> call_ok RT Σ1 m4 (Z_to_bv 64 (usp + -32 + -160 - pd + -32)) lo ->
  (forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> (bv_unsigned x < usp - 240 \/ usp <= bv_unsigned x) -> m4 x = m x) ->
  rw_cells asegs m4 (usp - 16) [C8 s0; C8 ra] -> rw_cells asegs m4 (usp + -32 - 16) [C8 sp; C8 (Z_to_bv 64 SITE_bw_intern)] ->
  rw_cells asegs m4 (usp + -32 + -160 - pd + -16) [C8 (Z_to_bv 64 (usp + -32)); C8 (Z_to_bv 64 SITE_bwi_bwc)] ->
  cps asegs (ASTA RT Σ1 PMc (eq (mwrite_entry gp tp (usp + -32 + -160 - pd) BI IN n (usp + -24) f t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc m4)))
    (fun c => exists (Σ2 : rts RT),
       ASTA RT Σ2 PMc (fun ms => exists m5, mwrite_ret gp tp (usp + -32 + -160 - pd) BI IN n (usp + -24) f (Z_to_bv 64 n) m5 ms
           /\ ART RT Σ2 m5 /\ mem_inv asegs m5 /\ stk asegs m5 lo (usp + -32 + -160 - pd + -32)
           /\ (forall x : word, aclient (rt_live RT Σ1) (rt_frames RT Σ1) (usp + -32 + -160 - pd + -32) (bv_unsigned x) -> outside FP (bv_unsigned x) -> m5 x = m4 x)
           /\ PQ Σ2 m5) c
       /\ rt_frames RT Σ2 = rt_frames RT Σ1 /\ rt_sp0 RT Σ2 = rt_sp0 RT Σ1 /\ In (BI, 128) (rt_live RT Σ2)
       /\ (forall p k, In (p, k) (rt_live RT Σ1) -> In (p, k) (rt_live RT Σ2) \/ (forall x, p <= x < p + k -> ~ outside FP x))).

(* [comment removed for export] *)
Definition bio_write_wrap_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BI IN n meth fl : Z) (shw rrw numw padw ptrw nr nw : word) (FP : list (Z * Z)) (PQ : rts RT -> mem -> Prop),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 IN -> a2 = Z_to_bv 64 n ->
  (meth = M_MEM_A \/ meth = M_SECMEM_A) -> In (BI, 128) (rt_live RT Σ) -> BI mod 16 = 0 ->
  rw_cells asegs m BI (bio_head meth) -> rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) shw fl rrw numw padw ptrw) -> rw_cells asegs m (BI + 72) (bio_tail nr nw) ->
  0 <= IN < 2^64 -> 1 <= n < 2^31 - 1 ->
  (forall x, ~ outside FP x -> aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) x) ->
  (forall x, BI <= x < BI + 40 \/ BI + 72 <= x < BI + 128 -> outside FP x) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 240 <= bv_unsigned sp ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  mwrite_specB Σ PMc sp gp tp s0 ra (bv_unsigned sp) lo BI IN n m FP PQ ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_BIO_write m)))
    (fun c => exists (Σ2 Σ3 : rts RT) (m5 : mem),
       ASTA RT Σ3 PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 n) m' ms
           /\ ART RT Σ3 m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ wmono asegs m5 m'
           /\ (forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (bv_unsigned x) -> outside FP (bv_unsigned x) ->
                 ~ (BI + 104 <= bv_unsigned x < BI + 112) -> m' x = m x)
           /\ (forall x : word, aclient (rt_live RT Σ2) (rt_frames RT Σ) (bv_unsigned sp) (bv_unsigned x) -> ~ (BI + 104 <= bv_unsigned x < BI + 112) -> m' x = m5 x)
           /\ rw_cells asegs m' BI (bio_head meth) /\ rw_cells asegs m' (BI + 72) (bio_tail nr (Z_to_bv 64 (bv_unsigned nw + n)))) c
       /\ PQ Σ2 m5
       /\ rt_live RT Σ3 = rt_live RT Σ2 /\ rt_frames RT Σ3 = rt_frames RT Σ /\ rt_sp0 RT Σ3 = rt_sp0 RT Σ /\ rt_credit RT Σ3 = rt_credit RT Σ2 /\ rt_cg RT Σ3 = rt_cg RT Σ2).

Theorem bio_write_wrap : bio_write_wrap_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI IN n meth fl shw rrw numw padw ptrw nr nw FP PQ
    FDO MST -> -> -> -> HM INBI BIAL BH BW BT HIN HN FPOK FPBI ART0 MI0 CALL HSTK Hfr Hcr MPB.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 240 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLOI : SEGTOP_A <= lo) by (unfold SEGTOP_A, STACK_WIN in *; lia).
  set (uspi := usp + -32).
  assert (EUI : bv_unsigned (Z_to_bv 64 uspi) = uspi) by (apply unsigned_lit; unfold uspi, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  pose proof (af_live_range RT AF Σ m BI 128 ART0 INBI) as (BI0 & BILO' & _). assert (BILO : BI + 128 <= lo) by (clear - BILO' LOW; lia). clear BILO'.
  (* [comment removed for export] *)
  pose proof (bw_s0_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI IN n
                ltac:(fold usp; unfold RT_STACK in *; clear - HSTK; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; clear - NUM; lia) ST ltac:(clear - HN; lia) MI0) as W0.
  fold usp in W0. fold uspi in W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (j0 & j8 & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold uspi in FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 32 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 32 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AGL : forall a k, a + k <= usp - 32 -> agree_on (fun x => a <= x < a + k) m m1) by (intros a' k H x Hx; cbv beta in Hx; apply MU1; cbn [outside]; clear - H Hx; lia).
  assert (BH1 : rw_cells asegs m1 BI (bio_head meth)) by (apply (rw_cells_agree asegs m m1 _ _ BH); [apply AGL; unfold bio_head; cbn [cells_size csize Nat.add]; clear - BILO HSTK; unfold RT_STACK in *; lia | exact WM1]).
  assert (BW1 : rw_cells asegs m1 (BI + 40) (bio_w1_cells (Z_to_bv 64 1) shw fl rrw numw padw ptrw))
    by (apply (rw_cells_agree asegs m m1 _ _ BW); [apply AGL; unfold bio_w1_cells; cbn [cells_size csize Nat.add]; clear - BILO HSTK; unfold RT_STACK in *; lia | exact WM1]).
  assert (BT1 : rw_cells asegs m1 (BI + 72) (bio_tail nr nw)) by (apply (rw_cells_agree asegs m m1 _ _ BT); [apply AGL; unfold bio_tail; cbn [cells_size csize Nat.add]; clear - BILO HSTK; unfold RT_STACK in *; lia | exact WM1]).
  destruct (proj1 (rw_cells_app m1 uspi [CB 8 j0] [CB 8 j8; C8 s0; C8 ra]) FR1) as [FRa X]. cbn [cells_size csize Nat.add app] in X.
  destruct (proj1 (rw_cells_app m1 _ [CB 8 j8] [C8 s0; C8 ra]) X) as [WC1 FRR1]. cbn [cells_size csize Nat.add app] in FRR1. clear X.
  replace (uspi + Z.of_nat 8) with (usp + -24) in WC1, FRR1 by (unfold uspi; clear; lia). replace (usp + -24 + Z.of_nat 8) with (usp - 16) in FRR1 by (clear; lia).
  assert (CO1 : call_ok RT Σ m1 (Z_to_bv 64 uspi) lo) by (fold usp in SPA; cl_call_ok EUI ST1 LOW SPA 2).
  (* [comment removed for export] *)
  apply (bwi_wrap Σ PMc (Z_to_bv 64 SITE_bw_intern) (Z_to_bv 64 uspi) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 (Z_to_bv 64 BI) (Z_to_bv 64 IN) (Z_to_bv 64 n) (Z_to_bv 64 (usp + -24)) a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo BI IN n (usp + -24) meth fl shw rrw numw padw ptrw nr nw j8 FP PQ
           FDO MST eq_refl eq_refl eq_refl eq_refl eq_refl HM INBI BIAL BH1 BW1 BT1 HIN HN WC1).
  { rewrite EUI. unfold uspi. clear. lia. }
  { fold usp in SPA. clear - SPA. Z.div_mod_to_equations. lia. }
  { clear - SPT. fold usp in SPT. lia. }
  { intros x Hx. rewrite EUI. apply (aclient_mono _ _ _ _ _ _ _ (FPOK x Hx)); [auto | auto | unfold uspi; clear; lia]. }
  { intros x [Hx|[Hx|Hx]]; [apply FPBI; left; exact Hx | apply FPBI; right; exact Hx |].
    destruct (outside_dec FP x) as [H|H]; [exact H| exfalso]. pose proof (FPOK x H) as AC. fold usp in AC.
    pose proof (cl_split RT AF Σ m usp 240 _ ART0 ltac:(lia) ltac:(lia) AC) as N3. clear - Hx N3. lia. }
  { exact ART1. }
  { exact MI1. }
  { exact CO1. }
  { rewrite EUI. unfold uspi, RT_STACK in *. clear - HSTK. lia. }
  { exact Hfr. }
  { exact Hcr. }
  { (* [comment removed for export] *)
    unfold mwrite_spec. rewrite EUI. intros Σ1 f pd m4 x0 x1 x2 y4 y5 y6 y7 x3 x4 x5 x6 F' fc' HP HPM LV1 FRS1 SP1 CR1 CG1 F0 F64 ART4 MI4 WM14 CO4 A14 FRR4 REC4.
    assert (A04 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> (bv_unsigned x < usp - 240 \/ usp <= bv_unsigned x) -> m4 x = m x).
    { intros x Hx Hlt. rewrite (A14 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold uspi; clear; lia]) ltac:(unfold uspi; clear - Hlt; lia) ltac:(clear - Hlt; lia)).
      apply MU1. cbn [outside]. clear - Hlt. lia. }
    assert (FRR4' : rw_cells asegs m4 (usp - 16) [C8 s0; C8 ra]).
    { apply (rw_cells_agree_nw asegs m1 m4 _ _ FRR1). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
      apply A14; [left; unfold uspi, USTACK_TOP in *; clear - Hx NUM; lia | unfold uspi; clear - Hx; lia | clear - Hx; lia]. }
    unfold uspi in CO4, REC4 |- *.
    replace (usp + -32 - 16) with (usp + -32 - 16) in FRR4 by reflexivity.
    exact (MPB Σ1 f pd m4 x0 x1 x2 y4 y5 y6 y7 x3 x4 x5 x6 F' fc' HP HPM LV1 FRS1 SP1 CR1 CG1 F0 F64 ART4 MI4 (wmono_trans asegs _ _ _ WM1 WM14) CO4 A04 FRR4' FRR4 REC4). }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ2 & Σ3 & m5 & Hc2 & HPQ & LV3 & FRS3 & SP3 & CR3 & CG3).
  destruct (ASTA_unpack RT Σ3 _ _ c2 Hc2) as (ms2 & (m6 & RS & ART6 & MI6 & ST6 & WM56 & PRm & PRm5 & BH6 & BT6 & WC6) & Hc2'). clear Hc2.
  destruct RS as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F6 & fc6 & ->).
  rewrite EUI in ST6, PRm, PRm5. rewrite (ret_pc_even SITE_bw_intern) in Hc2' by (unfold SITE_bw_intern; lia).
  (* [comment removed for export] *)
  assert (NST : forall x, usp - 240 <= x < usp -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x -> False).
  { intros x Hx AC. pose proof (cl_split RT AF Σ m usp 240 _ ART0 ltac:(lia) ltac:(lia) AC) as N3. clear - Hx N3. lia. }
  assert (NFP : forall x, usp - 240 <= x < usp -> outside FP x).
  { intros x Hx. destruct (outside_dec FP x) as [H|H]; [exact H| exfalso]. exact (NST x Hx (FPOK x H)). }
  assert (P16 : forall x : word, (uspi <= bv_unsigned x < usp + -24 \/ usp - 16 <= bv_unsigned x < usp) -> m6 x = m1 x).
  { intros x Hx. apply PRm; [left; unfold uspi, USTACK_TOP in *; clear - Hx NUM; lia | apply NFP; unfold uspi in Hx; clear - Hx; lia | unfold uspi in Hx; clear - Hx BILO HSTK; unfold RT_STACK in *; lia | unfold uspi in Hx; clear - Hx; lia]. }
  assert (FR6 : rw_cells asegs m6 uspi [CB 8 j0; C4 (Z_to_bv 64 n); C4 (Z_to_bv 64 0); C8 s0; C8 ra]).
  { apply (proj2 (rw_cells_app m6 uspi [CB 8 j0] [C4 (Z_to_bv 64 n); C4 (Z_to_bv 64 0); C8 s0; C8 ra])). split.
    - apply (rw_cells_agree_nw asegs m1 m6 _ _ FRa). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply P16. left. unfold uspi in Hx |- *. clear - Hx. lia.
    - cbn [cells_size csize Nat.add]. replace (uspi + Z.of_nat 8) with (usp + -24) by (unfold uspi; clear; lia).
      apply (proj2 (rw_cells_app m6 (usp + -24) [C4 (Z_to_bv 64 n); C4 (Z_to_bv 64 0)] [C8 s0; C8 ra])). split.
      + apply (proj2 (Fz_T_ekit.t_cells_halves asegs m6 (usp + -24) n 0 ltac:(clear - HN; lia) ltac:(clear; lia))). rewrite Z.mul_0_r, Z.add_0_r. exact WC6.
      + cbn [cells_size csize Nat.add]. replace (usp + -24 + Z.of_nat 8) with (usp - 16) by (clear; lia).
        apply (rw_cells_agree_nw asegs m1 m6 _ _ FRR1). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply P16. right. clear - Hx. lia. }
  (* [comment removed for export] *)
  pose proof (bw_s1_walk ra (Z_to_bv 64 SITE_bw_intern) sp gp (Z_to_bv 64 0xba3ef0) v0 v1 v2 s0 s1 d1 d2 d3 d4 d5 d6 d7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F6 fc6 m6 lo n j0
                ltac:(fold usp; unfold RT_STACK in *; clear - HSTK; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; clear - NUM; lia)) as W7.
  fold usp uspi in W7. specialize (W7 ST6 FR6 ltac:(clear - HN; lia) MI6).
  cl_lift W7 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ3 _ _ c3 Hc3) as (ms3 & (z0 & z1 & z2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & z3 & z4 & z5 & z6 & m7 & -> & MU7 & WM7 & MI7 & ST7) & Hc3'). clear Hc3.
  fold usp in ST7.
  assert (E7 : forall x : word, m7 x = m6 x) by (intros x; apply MU7; exact I).
  assert (ART7 : ART RT Σ3 m7) by (apply (af_frame RT AF Σ3 m6 m7 uspi ART6 ltac:(rewrite SP3; unfold uspi; lia)); [intros x _; apply E7 | exact WM7]).
  apply Hk. exists Σ2, Σ3, m5.
  split; [| split; [exact HPQ| split; [exact LV3 | split; [exact FRS3 | split; [exact SP3 | split; [exact CR3 | exact CG3]]]]]].
  eapply ASTA_conseq; [exact Hc3'|]. intros ms <-. exists m7.
  split; [exists z0, z1, z2, h1, h2, h3, h4, h5, h6, h7, z3, z4, z5, z6, F6, fc6; reflexivity|].
  split; [exact ART7|]. split; [exact MI7|]. split; [exact ST7|]. split; [exact (wmono_trans asegs _ _ _ WM56 WM7)|].
  split.
  { intros x Hx Ho HB. rewrite E7.
    rewrite (PRm x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold uspi; clear; lia]) Ho HB ltac:(intros HW; apply (NST (bv_unsigned x) ltac:(clear - HW; lia) Hx))).
    exact (PR1 x Hx I). }
  split.
  { intros x Hx HB. rewrite E7. apply PRm5; [apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold uspi; clear; lia] | exact HB |].
    intros HW. rewrite <- LV3, <- FRS3 in Hx. pose proof (cl_split RT AF Σ3 m6 usp 240 _ ART6 ltac:(rewrite SP3; lia) ltac:(lia) Hx) as N3. clear - HW N3. lia. }
  split; [apply (rw_cells_agree_nw asegs m6 m7 _ _ BH6); intros x _; apply E7|].
  apply (rw_cells_agree_nw asegs m6 m7 _ _ BT6); intros x _; apply E7.
Qed.
End CBwrite.
