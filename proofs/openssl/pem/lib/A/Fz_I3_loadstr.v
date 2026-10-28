(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Malloc Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import LhPure LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout PLayout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_mkit Fz_G_kit Fz_ckit Fz_env Fz_M_malloc Fz_W5_icb Th_errno Th_tsd Th_key Th_once Th_mutex Fz_T_once Fz_T_lock Fz_T_local Fz_T_master1 Fz_T_sa Fz_T_sa_set Fz_T_master Fz_T_slx Fz_I1_img Fz_I1_hash Fz_I1_defs Fz_I1_loadw Fz_I1_errload Fz_I1_efirst Fz_I1_crypto Fz_I3_shelve Fz_I3_loadstrw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation zeros n := (repeat (Z_to_bv 8 0) n) (only parsing).
Notation TP_A := (0xba3ef0)%Z (only parsing).
Notation ERRNO_A := (0xba3e4c)%Z (only parsing).
Notation MK_ONCE := (0xb9f500)%Z (only parsing).
Notation MK_KEY := (0xb9f520)%Z (only parsing).
Notation MK_INIT := (0xb9f540)%Z (only parsing).
Notation MK_CLEAN := (0x1f69dc)%Z (only parsing).

Section LoadStr.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis SM0 : stack_malloc_contract RT 0.
Hypothesis C_SHV : shelve_first_stmt RT.
Hypothesis C_CRS : crypto_strs_stmt RT GOBJ.
Hypothesis GO_mkey : GOBJ MK_KEY 4.
Hypothesis TSD : forall Σ m, ART RT Σ m -> rw_cells asegs m (TP_A + -88) [C8 (Z_to_bv 64 TSD_MAIN)].

Definition LS_SITES : list (Z * Z) := (SITE_ls_shv, e_loadstr) :: (SITE_ls_crs, e_loadstr) :: SHV_SITES ++ CR_SITES.
Definition LS_CALLS : list (Z * Z) := (SITE_ls_shv, e_shelve) :: (SITE_ls_crs, e_crypto_strs) :: SHV_CALLS ++ CR_CALLS.
(* [comment removed for export] *)
Definition LS_W (j : Z) : list (Z * Z) :=
  [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (ERRNO_A, ERRNO_A + 4); (MK_ONCE, MK_ONCE + 4); (MK_KEY, MK_KEY + 4); (MK_INIT, MK_INIT + 1); (NEXT_KEY, NEXT_KEY + 12);
   (KEYS + 8 * j, KEYS + 8 * j + 8); (TP_A + -96, TP_A + -88); (TSD_MAIN + 8 * j, TSD_MAIN + 8 * j + 8); (TP_A + -150, TP_A + -149);
   (G_ERR_ONCE, G_ERR_ONCE + 4); (G_ERR_LOCK, G_ERR_LOCK + 8); (G_ERR_HASH, G_ERR_HASH + 8); (G_ERR_FLAG, G_ERR_FLAG + 4); (G_LS_RET, G_LS_RET + 4)].

(* [comment removed for export] *)
Definition loadstr_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (nk j : Z) (e od sh kold w oldcb lk0 h0 f0 r0 : word) (ib u : byte),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x340 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_loadstr (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) LS_SITES LS_CALLS ->
  (length (rt_frames RT Σ) + 1 < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 4327 < LIVE_MAX -> 38 <= rt_credit RT Σ ->
  Forall (fun x => 0 < snd x) (rt_live RT Σ) -> cl_env m lb canary ->
  rw_cells asegs m G_IC_STOPPED [C1 (Z_to_bv 8 0)] -> rw_cells asegs m G_IC_OPTSDONE [C8 od] ->
  rw_cells asegs m G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)] -> rw_cells asegs m G_IC_BASE_RET [C4 (Z_to_bv 64 1)] ->
  rw_cells asegs m ERRNO_A [C4 e] ->
  rw_cells asegs m MK_ONCE [C4 z64] -> rw_cells asegs m MK_INIT [C1 ib] -> rw_cells asegs m MK_KEY [C4 kold] ->
  rw_cells asegs m NEXT_KEY [C4 (Z_to_bv 64 nk)] -> 0 <= nk < 128 -> rw_cells asegs m KEY_LOCK [C4 z64; C4 z64; C4 sh] ->
  rw_cells asegs m (KEYS + 8 * j) [C8 z64] -> ro_cells asegs m (KEYS + 8 * nk) [C8 w] -> ((j = nk /\ w = z64) \/ (j = (nk + 1) mod 128 /\ bv_unsigned w <> 0)) -> 1 <= j ->
  rw_cells asegs m (TSD_MAIN + 8 * j) [C8 z64] -> rw_cells asegs m (TP_A + -150) [C1 u] -> rw_cells asegs m (TP_A + -96) [C8 oldcb] ->
  rw_cells asegs m G_ERR_ONCE [C4 z64] -> rw_cells asegs m G_ERR_LOCK [C8 lk0] -> rw_cells asegs m G_ERR_HASH [C8 h0] -> rw_cells asegs m G_ERR_FLAG [C4 f0] ->
  rw_cells asegs m G_LS_RET [C4 r0] ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_loadstr m)))
    (fun c => exists (Σ' : rts RT) (MK SA P pk lh B : Z) (L' : list (Z * Z)) (g' : lh_geo) (bks' : list (list (bptr * Z))) (lb' u' : byte) (e' top' v : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
           /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (LS_W j) m m'
           /\ cl_env m' lb' canary
           /\ rw_cells asegs m' G_IC_STOPPED [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m' G_IC_OPTSDONE [C8 od]
           /\ rw_cells asegs m' G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m' G_IC_BASE_RET [C4 (Z_to_bv 64 1)]
           /\ rw_cells asegs m' ERRNO_A [C4 e']
           /\ rw_cells asegs m' MK_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m' MK_INIT [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m' MK_KEY [C4 (Z_to_bv 64 j)]
           /\ rw_cells asegs m' NEXT_KEY [C4 (Z_to_bv 64 j)] /\ rw_cells asegs m' KEY_LOCK [C4 z64; C4 z64; C4 sh] /\ rw_cells asegs m' (KEYS + 8 * j) [C8 (Z_to_bv 64 MK_CLEAN)]
           /\ rw_cells asegs m' (TP_A + -96) [C8 oldcb] /\ rw_cells asegs m' (TSD_MAIN + 8 * j) [C8 (Z_to_bv 64 MK)] /\ rw_cells asegs m' (TP_A + -150) [C1 u']
           /\ rw_cells asegs m' MK [CB 24 (zeros 24); C8 (Z_to_bv 64 SA); CB 40 (zeros 40)]
           /\ rw_cells asegs m' SA (sa_hdr (Z_to_bv 64 1) z64 top' (Z_to_bv 64 0) (Z_to_bv 64 P)) /\ bv_unsigned top' = 0
           /\ rw_cells asegs m' P [C8 z64; CB 120 (zeros 120)]
           /\ err_statics m' pk lh /\ rw_cells asegs m' pk (mutex_cells z64 z64) /\ lh_repE GOBJ m' L' lh B g' bks'
           /\ rw_cells asegs m' G_LS_RET [C4 (Z_to_bv 64 1)]) c
       /\ Permutation (rt_live RT Σ') (L' ++ (pk, 40) :: (P, 128) :: (SA, 32) :: (MK, 72) :: rt_live RT Σ) /\ Z.of_nat (length L') <= 4320 /\ 0 <= g_items g' <= 4318
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 38 <= rt_credit RT Σ' /\ rt_cg RT Σ' = rt_cg RT Σ
       /\ 0 < MK /\ MK mod 16 = 0 /\ MK + 72 < USTACK_TOP /\ 0 < SA /\ SA mod 16 = 0 /\ SA + 32 < USTACK_TOP /\ 0 < P /\ P mod 16 = 0 /\ P + 128 < USTACK_TOP
       /\ 0 < pk /\ pk mod 16 = 0 /\ pk + 40 < USTACK_TOP).
Theorem loadstr_cps : loadstr_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary nk j e od sh kold w oldcb lk0 h0 f0 r0 ib u
    FDO MST -> ART0 MI0 CALL HSTK CTX UWC CGH Hfr Hlen Hcr POS CLE STP OD ONCE BRET ERC OC IC KC NK HNK KL KJ PROBE CASE HJ1 SLOT UC CBC ONC LKC LHC FLC LSR.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  set (pad := usp mod 32).
  assert (HP : pad = 0 \/ pad = 16) by (unfold pad; clear - SPA; Z.div_mod_to_equations; lia).
  assert (HPM : usp mod 32 = pad) by reflexivity. clearbody pad.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 0x340 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP /\ SEGTOP_A <= lo) by (unfold RT_STACK, STACK_WIN, USTACK_TOP, SEGTOP_A in *; lia).
  set (usp1 := usp + -64 - pad).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (HLOS : 0x10007fff8000 <= lo) by exact (proj1 (proj2 NUM)).
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  assert (HJ : 0 <= j < 128) by (destruct CASE as [[-> _] | [-> _]]; [lia | apply Z.mod_pos_bound; lia]).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & UAR & UT).
  (* [comment removed for export] *)
  pose proof (ls_w0 ra sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pad
                HP HPM ST ltac:(fold usp; unfold RT_STACK in *; lia) HLOS SPH UT SHC UAR MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (a1' & m1 & -> & MU1 & WM1 & MI1 & FR1 & GAP1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, GAP1, ST1, Hc1'. fold usp1 in GAP1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 64 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 64 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  (* [comment removed for export] *)
  apply (SM0 Σ PMc (Z_to_bv 64 SITE_ls_sm) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 64) a1' a2 a3 a4 a5 a6 a7
           s2 s3 (Z_to_bv 64 0x7fff8000) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo FDO MST ltac:(left; reflexivity) eq_refl ltac:(lia) ltac:(lia) ART1 MI1).
  { unfold call_ok. rewrite EU1. split; [exact ST1|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|].
    fold usp in SPA. clear - SPA HP HPM. Z.div_mod_to_equations. lia. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & f & Hc2 & FRS1 & LV1 & SP1 & CR1 & F0 & F64 & FU & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WF2 & WS2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_ls_sm) in Hc2' by (unfold SITE_ls_sm; lia).
  assert (INF : In (f, 0%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  pose proof (af_frames_range RT AF Σ1 m2 f 0%nat ART2 INF) as (_ & FLO & _ & FAP).
  pose proof (af_frames_align RT AF Σ1 m2 f 0%nat ART2 INF) as (_ & FIMG).
  pose proof (af_frames_hi RT AF Σ1 m2 f 0%nat ART2 INF) as FSH.
  rewrite SP1 in FLO. change (fs_size 0) with 64 in FLO, FSH, FU, WF2, WS2, FAP. change (64 - 8) with 56 in WF2. change (64 / 8) with 8 in WS2.
  unfold shad, SHB in WS2. unfold SEGTOP_A in FIMG. rewrite LV1 in FAP.
  assert (AG2 : forall a k, usp1 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m1 m2).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES2. left. lia. }
  cl_keep FR1 AG2 WM2 FR2.
  assert (GAP2 : stk asegs m2 usp1 (usp + -64)).
  { apply (stk_agree_nw asegs m1 m2 _ _ GAP1). intros x Hx. cbv beta in Hx. apply PRES2. left. unfold USTACK_TOP in *. lia. }
  destruct (wr_at_rw_CB m2 f 56 WF2 ltac:(lia)) as (fj & FB2). destruct (wr_at_rw_CB m2 (f / 8 + 2147450880) 8 WS2 ltac:(lia)) as (sj & SB2).
  change (Z.to_nat 56) with 56%nat in FB2. change (Z.to_nat 8) with 8%nat in SB2.
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & SHC2 & _ & _ & UT2).
  assert (WM02 : wmono asegs m m2) by exact (wmono_trans asegs _ _ _ WM1 WM2).
  (* [comment removed for export] *)
  assert (PR2 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> m2 a = m a).
  { intros a Ha. rewrite (PRES2 a ltac:(apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros ? X; exact X| intros ? X; exact X| unfold usp1; lia])). exact (PR1 a Ha I). }
  assert (STAT2 : forall a cs, rw_cells asegs m a cs -> 0xb8f190 <= a -> a + Z.of_nat (cells_size cs) <= 0xbc57d0 ->
            (a + Z.of_nat (cells_size cs) <= 0xba3e98 \/ 0xbc41b8 <= a) -> (a + Z.of_nat (cells_size cs) <= 0xbc5298 \/ 0xbc52a0 <= a) -> rw_cells asegs m2 a cs).
  { intros a cs H H1 H2 H3 H4. apply (rw_cells_agree asegs m m2 _ _ H); [| exact WM02]. intros x Hx. cbv beta in Hx. apply PR2. right; left; apply client_static_intro; clear - H1 H2 H3 H4 Hx; lia. }
  (* [comment removed for export] *)
  pose proof (ls_w1 sp gp (Z_to_bv 64 TP_A) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s2 s3 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6
                ra s0 s1 s2 s3 s4 s5 F2 fc2 m2 f lo pad fj sj HP F0 F64 FIMG ltac:(lia) ltac:(destruct FSH; [left | right]; lia)
                ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia)
                UT2 FR2 GAP2 ST2 FB2 SB2 MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (j8 & fr & m3 & -> & MU3 & WM3 & MI3 & FR3 & FB3 & SB3 & GAP3 & ST3) & Hc3'). clear Hc3.
  fold usp in MU3, FR3, GAP3, Hc3'. fold usp1 in GAP3, ST3, Hc3'.
  assert (SHF : shad (f + 64) = shad f + 8) by (replace (f + 64) with (f + 64 * 1) by lia; rewrite (shad_add64 f 1 F64); lia).
  pose proof (div8_facts f) as Q1.
  (* [comment removed for export] *)
  assert (FKEEP : forall (ma mb : mem) W, ART RT Σ1 ma -> munch W ma mb -> wmono asegs ma mb ->
            (forall x, ~ outside W x -> (f <= x < f + 56) \/ (shad f <= x < shad f + 8) \/ (usp - 96 <= x < usp - 56)) ->
            ART RT Σ1 mb /\ (forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> mb a = ma a)).
  { intros ma mb W HAx MUx WMx HW. split.
    - apply (af_frame RT AF Σ1 ma mb (usp - 96) HAx ltac:(rewrite SP1; lia)); [| exact WMx].
      intros a Ha. apply MUx. destruct (outside_dec W (bv_unsigned a)) as [O|O]; [exact O|]. exfalso. apply Ha.
      destruct (HW _ O) as [X|[X|X]].
      + apply (acl_frame _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; lia].
      + apply (acl_fshadow _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; rewrite SHF; lia].
      + apply acl_stack. unfold USTACK_TOP in *. lia.
    - intros a Ha. apply MUx. destruct (outside_dec W (bv_unsigned a)) as [O|O]; [exact O|]. exfalso.
      destruct (newframe_apart RT AF Σ Σ1 m2 f 0%nat usp _ ART2 FRS1 LV1 SP1 ltac:(lia) Ha) as (N1 & N2). change (fs_size 0) with 64 in N1, N2. rewrite SHF in N2.
      pose proof (cl_split RT AF Σ m usp 96 _ ART0 ltac:(lia) ltac:(lia) Ha) as N4.
      destruct (HW _ O) as [X|[X|X]]; lia. }
  destruct (FKEEP m2 m3 _ ART2 MU3 WM3 ltac:(intros x Hx; cbn [outside] in Hx; unfold shad, SHB; lia)) as [ART3 PR3].
  assert (WM03 : wmono asegs m m3) by exact (wmono_trans asegs _ _ _ WM02 WM3).
  assert (PR03 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> m3 a = m a) by (intros a Ha; rewrite (PR3 a Ha); exact (PR2 a Ha)).
  assert (STAT3 : forall a cs, rw_cells asegs m a cs -> 0xb8f190 <= a -> a + Z.of_nat (cells_size cs) <= 0xbc57d0 ->
            (a + Z.of_nat (cells_size cs) <= 0xba3e98 \/ 0xbc41b8 <= a) -> (a + Z.of_nat (cells_size cs) <= 0xbc5298 \/ 0xbc52a0 <= a) -> rw_cells asegs m3 a cs).
  { intros a cs H H1 H2 H3 H4. apply (rw_cells_agree asegs m m3 _ _ H); [| exact WM03]. intros x Hx. cbv beta in Hx. apply PR03. right; left; apply client_static_intro; clear - H1 H2 H3 H4 Hx; lia. }
  assert (PROBE3 : ro_cells asegs m3 (KEYS + 8 * nk) [C8 w]).
  { apply (ro_cells_agree asegs m m3 _ _ PROBE). cbn [cells_size csize Nat.add]. intros x Hx. apply PR03. right; left; apply client_static_intro; lia. }
  pose proof (cl_env_pres _ _ _ m m3 lb canary CLE PR03) as CLE3.
  (* [comment removed for export] *)
  assert (AGS3 : agree_on (fun x => usp <= x < USTACK_TOP) m m3) by (intros a Ha; cbv beta in Ha; apply PR03; left; exact Ha).
  assert (FRR3 : rw_cells asegs m3 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp + -64 + Z.of_nat (cells_size [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia).
    exact (rw_cells_skip m3 (usp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR3). }
  rewrite <- CG1 in CGH, CTX.
  destruct (cl_chain_call (rt_cg RT Σ1) e_loadstr e_shelve SITE_ls_shv m m3 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH _ ltac:(left; reflexivity)) (proj2 CGH _ ltac:(left; reflexivity)) UWC AGS3 FRR3 ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTX3 & UWC3).
  (* [comment removed for export] *)
  pose proof FB3 as SLOT3. change [C8 (Z_to_bv 64 LS_MAGIC); C8 (Z_to_bv 64 LS_DESCR); C8 (Z_to_bv 64 e_loadstr); CB 32 fr] with ([C8 (Z_to_bv 64 LS_MAGIC); C8 (Z_to_bv 64 LS_DESCR); C8 (Z_to_bv 64 e_loadstr)] ++ [CB 32 fr]) in SLOT3.
  apply (proj1 (rw_cells_app m3 _ _ _)) in SLOT3. destruct SLOT3 as [_ SLOT3]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SLOT3.
  apply (rw_cells_split_CB asegs m3 _ [] 32 fr [] [8; 8; 8; 8]%nat) in SLOT3; [| reflexivity]. cbn [mk_CB_cells app firstn skipn] in SLOT3.
  pose proof (rw_cells_skip m3 (f + 24) [CB 8 (firstn 8 fr)] _ SLOT3) as RES3. cbn [cells_size csize Nat.add] in RES3. replace (f + 24 + 8) with (f + 32) in RES3 by lia.
  lazymatch type of RES3 with rw_cells _ _ _ (?c1 :: ?rest) => change (c1 :: rest) with ([c1] ++ rest) in RES3 end.
  apply (proj1 (rw_cells_app m3 _ _ _)) in RES3. destruct RES3 as [RES3 _].
  assert (SB34 : rw_cells asegs m3 (f / 8 + 2147450880 + 4) [C1 (Z_to_bv 8 0)])
    by exact (rw_cells_head m3 _ _ _ (rw_cells_skip m3 (f / 8 + 2147450880) [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15))] _ SB3)).
  assert (ACC3 : acc asegs m3 (f + 32) 8).
  { apply (acc_of_shadow0 m3 (f + 32)); [replace (shad (f + 32)) with (f / 8 + 2147450880 + 4) by (unfold shad, SHB; Z.div_mod_to_equations; lia); exact (rw_C1_bytes m3 _ _ SB34)
                                       | clear - F64; Z.div_mod_to_equations; lia | lia]. }
  assert (FRIN3 : In (f, 0%nat) (rt_frames RT Σ1)) by exact INF.
  pose proof (TSD Σ1 m3 ART3) as TSD3.
  (* [comment removed for export] *)
  apply (C_SHV Σ1 PMc (Z_to_bv 64 SITE_ls_shv) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) u0 u1 u2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 LS_DESCR) (Z_to_bv 64 e_loadstr) b3 b4 b5 b6 b7
           (Z_to_bv 64 f) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m3 lo (bv_unsigned ra :: outer) lb canary
           (f + 32) f nk j e od sh kold w oldcb ib u (firstn 8 (skipn 8 fr)) FDO MST eq_refl eq_refl FRIN3 ltac:(lia) ltac:(lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) RES3 ACC3 ART3 MI3).
  { assert (LOW1 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SP1; exact LOW).
    unfold call_ok. rewrite EU1. split; [exact ST3|]. split; [exact LOW1|]. split; [unfold usp1, RT_STACK in *; lia|]. split; [unfold usp1, USTACK_TOP in *; lia|].
    fold usp in SPA. clear - SPA HP. unfold usp1. Z.div_mod_to_equations. lia. }
  { rewrite EU1. unfold usp1, RT_STACK in *. clear - HSTK HP. lia. }
  { rewrite (unsigned_lit SITE_ls_shv) by (unfold SITE_ls_shv; lia). exact CTX3. }
  { exact UWC3. }
  { apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { rewrite FRS1. cbn [length]. lia. }
  { rewrite LV1. lia. }
  { rewrite CR1. lia. }
  { exact CLE3. }
  { exact (STAT3 _ _ STP ltac:(unfold G_IC_STOPPED; lia) ltac:(cbn; unfold G_IC_STOPPED; lia) ltac:(cbn; unfold G_IC_STOPPED; lia) ltac:(cbn; unfold G_IC_STOPPED; lia)). }
  { exact (STAT3 _ _ OD ltac:(unfold G_IC_OPTSDONE; lia) ltac:(cbn; unfold G_IC_OPTSDONE; lia) ltac:(cbn; unfold G_IC_OPTSDONE; lia) ltac:(cbn; unfold G_IC_OPTSDONE; lia)). }
  { exact (STAT3 _ _ ONCE ltac:(unfold G_IC_BASE_ONCE; lia) ltac:(cbn; unfold G_IC_BASE_ONCE; lia) ltac:(cbn; unfold G_IC_BASE_ONCE; lia) ltac:(cbn; unfold G_IC_BASE_ONCE; lia)). }
  { exact (STAT3 _ _ BRET ltac:(unfold G_IC_BASE_RET; lia) ltac:(cbn; unfold G_IC_BASE_RET; lia) ltac:(cbn; unfold G_IC_BASE_RET; lia) ltac:(cbn; unfold G_IC_BASE_RET; lia)). }
  { exact (STAT3 _ _ ERC ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)). }
  { exact (STAT3 _ _ OC ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)). }
  { exact (STAT3 _ _ IC ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)). }
  { exact (STAT3 _ _ KC ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)). }
  { exact (STAT3 _ _ NK ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)). }
  { exact HNK. }
  { exact (STAT3 _ _ KL ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)). }
  { exact (STAT3 _ _ KJ ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)). }
  { exact PROBE3. }
  { exact CASE. }
  { exact HJ1. }
  { exact (STAT3 _ _ SLOT ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)). }
  { exact (STAT3 _ _ UC ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)). }
  { exact (STAT3 _ _ CBC ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)). }
  { exact Hc3'. }
  clear Hc3'. intros c4 (Σ2 & MK & SA & P & u' & e' & Hc4 & LV2 & FRS2 & SP2 & CR2 & CG2 & MK0 & MK16 & MKU & SA0 & SA16 & SAU & P0 & P16 & PU).
  destruct (ASTA_unpack RT Σ2 _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & CLE4 & STP4 & OD4 & ONCE4 & BRET4 & ERC4 & OC4 & IC4 & KC4 & NK4 & KL4 & KJ4 & CBC4 & RES4 & SLOT4 & UC4 & MKC4 & SAC4 & PC4) & Hc4'). clear Hc4.
  destruct RS4 as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & F4 & fc4 & ->).
  rewrite EU1 in ST4, PRES4. rewrite (ret_pc_even SITE_ls_shv) in Hc4' by (unfold SITE_ls_shv; lia).

  (* [comment removed for export] *)
  assert (AG34 : forall Q : Z -> Prop, (forall x, Q x -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp1 x /\ outside (SHV_W j (f + 32)) x) -> agree_on Q m3 m4).
  { intros Q HQ a Ha. destruct (HQ _ Ha) as (X1 & X2). exact (PRES4 a X1 X2). }
  assert (STAT34 : forall a cs, rw_cells asegs m3 a cs -> 0xb9f7e0 <= a -> a + Z.of_nat (cells_size cs) <= 0xb9f860 -> rw_cells asegs m4 a cs).
  { intros a cs X H1 H2. apply (rw_cells_agree asegs m3 m4 _ _ X); [| exact WM4]. apply AG34. intros x Hx. cbv beta in Hx. clear - H1 H2 Hx FIMG HJ. split; [right; left; apply client_static_intro; lia|].
    unfold SHV_W, G_ALLOW_CUST. cbn [outside]. repeat split; try exact I; lia. }
  pose proof (STAT34 _ _ (STAT3 _ _ ONC ltac:(unfold G_ERR_ONCE; lia) ltac:(cbn; unfold G_ERR_ONCE; lia) ltac:(cbn; unfold G_ERR_ONCE; lia) ltac:(cbn; unfold G_ERR_ONCE; lia)) ltac:(unfold G_ERR_ONCE; lia) ltac:(cbn; unfold G_ERR_ONCE; lia)) as ONC4.
  pose proof (STAT34 _ _ (STAT3 _ _ LKC ltac:(unfold G_ERR_LOCK; lia) ltac:(cbn; unfold G_ERR_LOCK; lia) ltac:(cbn; unfold G_ERR_LOCK; lia) ltac:(cbn; unfold G_ERR_LOCK; lia)) ltac:(unfold G_ERR_LOCK; lia) ltac:(cbn; unfold G_ERR_LOCK; lia)) as LKC4.
  pose proof (STAT34 _ _ (STAT3 _ _ LHC ltac:(unfold G_ERR_HASH; lia) ltac:(cbn; unfold G_ERR_HASH; lia) ltac:(cbn; unfold G_ERR_HASH; lia) ltac:(cbn; unfold G_ERR_HASH; lia)) ltac:(unfold G_ERR_HASH; lia) ltac:(cbn; unfold G_ERR_HASH; lia)) as LHC4.
  pose proof (STAT34 _ _ (STAT3 _ _ FLC ltac:(unfold G_ERR_FLAG; lia) ltac:(cbn; unfold G_ERR_FLAG; lia) ltac:(cbn; unfold G_ERR_FLAG; lia) ltac:(cbn; unfold G_ERR_FLAG; lia)) ltac:(unfold G_ERR_FLAG; lia) ltac:(cbn; unfold G_ERR_FLAG; lia)) as FLC4.
  assert (LSR4 : rw_cells asegs m4 G_LS_RET [C4 r0]).
  { apply (rw_cells_agree asegs m3 m4 _ _ (STAT3 _ _ LSR ltac:(unfold G_LS_RET; lia) ltac:(cbn; unfold G_LS_RET; lia) ltac:(cbn; unfold G_LS_RET; lia) ltac:(cbn; unfold G_LS_RET; lia))); [| exact WM4].
    apply AG34. cbn [cells_size csize Nat.add]. intros x Hx. split; [right; left; apply client_static_intro; unfold G_LS_RET in *; lia|]. unfold SHV_W, G_ALLOW_CUST, G_LS_RET in *. cbn [outside]. repeat split; try exact I; lia. }
  eassert (FR4 : rw_cells asegs m4 (usp + -64) _).
  { apply (rw_cells_agree asegs m3 m4 _ _ FR3); [| exact WM4]. apply AG34. cbn [cells_size csize Nat.add]. intros x Hx. split; [left; unfold usp1, USTACK_TOP in *; lia|].
    unfold SHV_W, G_ALLOW_CUST. cbn [outside]. unfold usp in *. repeat split; try exact I; lia. }
  assert (UWC4 : uw_chain m4 (Z_to_bv 64 usp1) sp (bv_unsigned ra :: outer)).
  { apply (uw_chain_agree _ m3 m4 _ _ UWC3). rewrite EU1. apply AG34. intros x Hx. cbv beta in Hx. split; [left; exact Hx|]. unfold SHV_W, G_ALLOW_CUST. cbn [outside]. unfold usp1, usp in *. repeat split; try exact I; lia. }
  (* [comment removed for export] *)
  assert (FKEEP4 : forall a : word, (f <= bv_unsigned a < f + 32) \/ (shad f <= bv_unsigned a < shad f + 8) -> m4 a = m3 a).
  { intros a Ha. apply PRES4; [| unfold SHV_W, G_ALLOW_CUST; cbn [outside]; unfold shad, SHB in Ha; repeat split; try exact I; lia].
    destruct Ha as [Ha|Ha]; [apply (acl_frame _ _ _ f 0%nat); [exact INF| change (fs_size 0) with 64; lia] | apply (acl_fshadow _ _ _ f 0%nat); [exact INF| change (fs_size 0) with 64; rewrite SHF; lia]]. }
  assert (FB4 : rw_cells asegs m4 f [C8 (Z_to_bv 64 LS_MAGIC); C8 (Z_to_bv 64 LS_DESCR); C8 (Z_to_bv 64 e_loadstr)]).
  { pose proof FB3 as X. lazymatch type of X with rw_cells _ _ _ [?c1; ?c2; ?c3; ?c4] => change [c1; c2; c3; c4] with ([c1; c2; c3] ++ [c4]) in X end.
    apply (proj1 (rw_cells_app m3 _ _ _)) in X. destruct X as [X _].
    apply (rw_cells_agree asegs m3 m4 _ _ X); [| exact WM4]. cbn [cells_size csize Nat.add]. intros x Hx. apply FKEEP4. left. lia. }
  assert (SB4 : rw_cells asegs m4 (f / 8 + 2147450880) [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))]).
  { apply (rw_cells_agree asegs m3 m4 _ _ SB3); [| exact WM4]. cbn [cells_size csize Nat.add]. intros x Hx. apply FKEEP4. right. unfold shad, SHB. lia. }
  (* [comment removed for export] *)
  pose proof (ls_w2 (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) w0 w1 w2 sp (Z_to_bv 64 usp1) d1 d2 d3 d4 d5 d6 d7 (Z_to_bv 64 f) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
                s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F4 fc4 m4 lo ltac:(rewrite EU1; exact ST4) HLOS ltac:(rewrite EU1; unfold usp1, RT_STACK in *; lia) ltac:(rewrite EU1; unfold usp1; lia) MI4) as W2.
  cl_lift W2 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ2 _ _ c5 Hc5) as (ms5 & (rax & -> & RAX) & Hc5'). clear Hc5.
  assert (FRIN4 : In (f, 0%nat) (rt_frames RT Σ2)) by (rewrite FRS2; exact INF).
  pose proof CGH as CGH2. rewrite <- CG2 in CGH2.
  (* [comment removed for export] *)
  apply (C_CRS Σ2 PMc rax (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) w0 w1 w2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 1) d1 d2 d3 d4 d5 d6 d7 (Z_to_bv 64 f) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
           s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F4 fc4 m4 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary od lk0 h0 f0 oldcb FDO MST eq_refl ART4 MI4).
  { assert (LOW2 : rt_sp0 RT Σ2 - STACK_WIN <= lo) by (rewrite SP2, SP1; exact LOW).
    unfold call_ok. rewrite EU1. split; [exact ST4|]. split; [exact LOW2|]. split; [unfold usp1, RT_STACK in *; lia|]. split; [unfold usp1, USTACK_TOP in *; lia|].
    fold usp in SPA. clear - SPA HP. unfold usp1. Z.div_mod_to_equations. lia. }
  { rewrite EU1. unfold usp1, RT_STACK in *. clear - HSTK HP. lia. }
  { rewrite RAX, CG2. apply (cg_ctx_call _ _ _ _ _ CTX); [exact (proj1 CGH _ ltac:(right; left; reflexivity)) | exact (proj2 CGH _ ltac:(right; left; reflexivity))]. }
  { exact UWC4. }
  { apply (cg_has_weaken _ _ _ _ _ CGH2); vm_compute; reflexivity. }
  { rewrite FRS2, FRS1. cbn [length]. lia. }
  { rewrite LV2, LV1. cbn [length]. lia. }
  { rewrite CR2, CR1. lia. }
  { rewrite LV2, LV1. constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor; [cbn; lia|]. exact POS. }
  { exact CLE4. }
  { exact STP4. } { exact OD4. } { exact ONCE4. } { exact BRET4. }
  { exact ONC4. } { exact LKC4. } { exact LHC4. } { exact FLC4. }
  { unfold G_CANCELBUF. exact CBC4. }
  { exact Hc5'. }
  clear Hc5'. intros c6 (Σ3 & pk & lh & B & L' & g' & bks' & lb' & Hc6 & PERM3 & LL3 & IT3 & FRS3 & SP3 & CR3 & CG3 & PK0 & PK16 & PKU).
  destruct (ASTA_unpack RT Σ3 _ _ c6 Hc6) as (ms6 & (m6 & RS6 & (ART6 & MI6 & ST6) & PRES6 & CLE6 & STP6 & OD6 & ONCE6 & BRET6 & STC6 & CBC6 & MC6 & REPE6) & Hc6'). clear Hc6.
  destruct RS6 as (x0 & x1 & x2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & x3 & x4 & x5 & x6 & F6 & fc6 & ->).
  rewrite EU1 in ST6, PRES6. rewrite <- (Z_to_bv_bv_unsigned rax), RAX, (ret_pc_even SITE_ls_crs) in Hc6' by (unfold SITE_ls_crs; lia).

  (* [comment removed for export] *)
  assert (AG46 : forall Q : Z -> Prop, (forall x, Q x -> aclient (rt_live RT Σ2) (rt_frames RT Σ2) usp1 x /\ outside (EFIRST_W pk) x) -> agree_on Q m4 m6).
  { intros Q HQ a Ha. destruct (HQ _ Ha) as (X1 & X2). exact (PRES6 a X1 X2). }
  assert (STAT46 : forall a cs, rw_cells asegs m4 a cs -> 0xb8f190 <= a -> a + Z.of_nat (cells_size cs) <= 0xbc57d0 ->
            (a + Z.of_nat (cells_size cs) <= 0xba3e98 \/ 0xbc41b8 <= a) -> (a + Z.of_nat (cells_size cs) <= 0xbc5298 \/ 0xbc52a0 <= a) ->
            (a + Z.of_nat (cells_size cs) <= 0xb9f7c0 \/ 0xb9f848 <= a) -> (a + Z.of_nat (cells_size cs) <= 0xba3e90 \/ 0xba3e98 <= a) -> rw_cells asegs m6 a cs).
  { intros a cs X H1 H2 H3 H4 H5 H6. apply (rw_cells_agree_nw asegs m4 m6 _ _ X). apply AG46. intros x Hx. cbv beta in Hx. clear - H1 H2 H3 H4 H5 H6 Hx. split; [right; left; apply client_static_intro; lia|].
    unfold EFIRST_W, G_ALLOW_CUST, G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_CANCELBUF. cbn [outside]. repeat split; try exact I; lia. }
  pose proof (STAT46 _ _ ERC4 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as ERC6.
  pose proof (STAT46 _ _ OC4 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as OC6.
  pose proof (STAT46 _ _ IC4 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as IC6.
  pose proof (STAT46 _ _ KC4 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as KC6.
  pose proof (STAT46 _ _ NK4 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as NK6.
  pose proof (STAT46 _ _ KL4 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as KL6.
  pose proof (STAT46 _ _ KJ4 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as KJ6.
  pose proof (STAT46 _ _ SLOT4 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as SLOT6.
  pose proof (STAT46 _ _ UC4 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as UC6.
  assert (LSR6 : rw_cells asegs m6 G_LS_RET [C4 r0]).
  { unfold G_LS_RET in *. exact (STAT46 _ _ LSR4 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)). }
  (* [comment removed for export] *)
  assert (INMK2 : In (MK, 72) (rt_live RT Σ2)) by (rewrite LV2; right; right; left; reflexivity).
  assert (INSA2 : In (SA, 32) (rt_live RT Σ2)) by (rewrite LV2; right; left; reflexivity).
  assert (INP2 : In (P, 128) (rt_live RT Σ2)) by (rewrite LV2; left; reflexivity).
  assert (IN23 : forall x, In x (rt_live RT Σ2) -> In x (rt_live RT Σ3)) by (intros x Hx; eapply Permutation_in; [apply Permutation_sym; exact PERM3| apply in_or_app; right; right; exact Hx]).
  pose proof (afp_live_hi RT GOBJ AFP Σ2 m4 MK 72 ART4 INMK2 ltac:(lia)) as MKHI.
  pose proof (afp_live_hi RT GOBJ AFP Σ2 m4 SA 32 ART4 INSA2 ltac:(lia)) as SAHI.
  pose proof (afp_live_hi RT GOBJ AFP Σ2 m4 P 128 ART4 INP2 ltac:(lia)) as PHI.
  pose proof (af_live_range RT AF Σ3 m6 MK 72 ART6 (IN23 _ INMK2)) as (_ & MKLO & _).
  pose proof (af_live_range RT AF Σ3 m6 SA 32 ART6 (IN23 _ INSA2)) as (_ & SALO & _).
  pose proof (af_live_range RT AF Σ3 m6 P 128 ART6 (IN23 _ INP2)) as (_ & PLO & _). rewrite SP3, SP2, SP1 in MKLO, SALO, PLO.
  assert (SAP : SA + 32 <= P \/ P + 128 <= SA).
  { pose proof (af_live_disj RT AF Σ2 m4 P 128 SA 32 [] ((SA, 32) :: (MK, 72) :: rt_live RT Σ1) ART4 ltac:(rewrite LV2; reflexivity) ltac:(left; reflexivity)) as X. lia. }
  assert (BLK46 : forall p n cs, In (p, n) (rt_live RT Σ2) -> 0x10007fff8000 <= p -> rw_cells asegs m4 p cs -> Z.of_nat (cells_size cs) <= n -> rw_cells asegs m6 p cs).
  { intros p n cs Hin Hhi X Hsz. apply (rw_cells_agree_nw asegs m4 m6 _ _ X). apply AG46. intros x Hx. cbv beta in Hx. clear - Hin Hhi Hsz Hx. split; [right; right; left; exists p, n; split; [exact Hin| lia]|].
    unfold EFIRST_W, G_ALLOW_CUST, G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_CANCELBUF. cbn [outside]. repeat split; try exact I; lia. }
  pose proof (BLK46 MK 72 _ INMK2 MKHI MKC4 ltac:(cbn; lia)) as MKC6.
  pose proof (BLK46 SA 32 _ INSA2 SAHI SAC4 ltac:(cbn; lia)) as SAC6.
  pose proof (BLK46 P 128 _ INP2 PHI PC4 ltac:(cbn; lia)) as PC6.
  assert (FKEEP6 : forall a : word, (f <= bv_unsigned a < f + 56) \/ (shad f <= bv_unsigned a < shad f + 8) -> m6 a = m4 a).
  { intros a Ha. apply PRES6; [| unfold EFIRST_W, G_ALLOW_CUST, G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_CANCELBUF; cbn [outside]; unfold shad, SHB in Ha; clear - Ha F0 FIMG; repeat split; try exact I; lia].
    destruct Ha as [Ha|Ha]; [apply (acl_frame _ _ _ f 0%nat); [exact FRIN4| change (fs_size 0) with 64; lia] | apply (acl_fshadow _ _ _ f 0%nat); [exact FRIN4| change (fs_size 0) with 64; rewrite SHF; lia]]. }
  assert (RES6 : rw_cells asegs m6 (f + 32) [C8 z64]) by (apply (rw_cells_agree_nw asegs m4 m6 _ _ RES4); cbn [cells_size csize Nat.add]; intros x Hx; apply FKEEP6; left; lia).
  assert (FB6 : rw_cells asegs m6 f [C8 (Z_to_bv 64 LS_MAGIC); C8 (Z_to_bv 64 LS_DESCR); C8 (Z_to_bv 64 e_loadstr)]) by (apply (rw_cells_agree_nw asegs m4 m6 _ _ FB4); cbn [cells_size csize Nat.add]; intros x Hx; apply FKEEP6; left; lia).
  eassert (SB6 : rw_cells asegs m6 (f / 8 + 2147450880) _) by (apply (rw_cells_agree_nw asegs m4 m6 _ _ SB4); cbn [cells_size csize Nat.add]; intros x Hx; apply FKEEP6; right; unfold shad, SHB; lia).
  eassert (FR6 : rw_cells asegs m6 (usp + -64) _).
  { apply (rw_cells_agree_nw asegs m4 m6 _ _ FR4). apply AG46. cbn [cells_size csize Nat.add]. intros x Hx. split; [left; unfold usp1, USTACK_TOP in *; lia|].
    unfold EFIRST_W, G_ALLOW_CUST, G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_CANCELBUF. cbn [outside]. unfold usp in *. repeat split; try exact I; lia. }
  assert (GAP6 : stk asegs m6 usp1 (usp + -64)).
  { apply (stk_agree_nw asegs m3 m6 _ _ GAP3). intros x Hx. cbv beta in Hx. rewrite (PRES6 x). 2: left; clear - Hx NUM; unfold USTACK_TOP in *; lia.
    2: unfold EFIRST_W, G_ALLOW_CUST, G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_CANCELBUF; cbn [outside]; clear - Hx NUM HLOS HSTK HP; unfold usp1, RT_STACK, USTACK_TOP, STACK_WIN, SEGTOP_A in *; repeat split; try exact I; lia.
    apply PRES4; [left; clear - Hx NUM; unfold USTACK_TOP in *; lia|]. unfold SHV_W, G_ALLOW_CUST; cbn [outside]; clear - Hx NUM HLOS HSTK HP HJ FIMG FLO; unfold usp1, RT_STACK, USTACK_TOP, STACK_WIN, SEGTOP_A in *; repeat split; try exact I; lia. }
  destruct (af_client_consts RT AF Σ3 m6 ART6) as (_ & SHC6 & _ & _ & UT6).
  pose proof (afp_gsh_byte RT GOBJ AFP Σ3 m6 _ _ MK_KEY ART6 GO_mkey ltac:(lia) ltac:(lia) ltac:(reflexivity)) as KSB6. cbn [Z.ltb Z.sub Z.add Z.leb] in KSB6.
  (* [comment removed for export] *)
  pose proof (ls_w3 (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) x0 x1 x2 sp (Z_to_bv 64 usp1) g1 g2 g3 g4 g5 g6 g7 (Z_to_bv 64 f) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
                s6 s7 s8 s9 s10 s11 x3 x4 x5 x6 F6 fc6 m6 lo (f + 32) ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) RES6
                ltac:(rewrite EU1; exact ST6) HLOS ltac:(rewrite EU1; unfold usp1, RT_STACK in *; lia) ltac:(rewrite EU1; unfold usp1; lia) MI6) as W3.
  cl_lift W3 Hc6' c7 Hc7.
  destruct (ASTA_unpack RT Σ3 _ _ c7 Hc7) as (ms7 & <- & Hc7'). clear Hc7.
  (* [comment removed for export] *)
  pose proof (unshelve_proof (Z_to_bv 64 SITE_ls_ush) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) x0 x1 x2 sp (Z_to_bv 64 usp1) z64 z64 g2 g3 g4 g5 g6 g7 (Z_to_bv 64 f) (Z_to_bv 64 1) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
                s6 s7 s8 s9 s10 s11 x3 x4 x5 x6 F6 fc6 m6 lo j MK SA P z64 z64 (Z_to_bv 64 1) (Z_to_bv 64 (-1)) (zeros 24) (zeros 40) (zeros 120)
                eq_refl eq_refl (proj1 OC6) (proj1 KC6) ltac:(lia) KSB6 UT6 SHC6 (proj1 (TSD Σ3 m6 ART6)) (proj1 SLOT6)
                MKHI ltac:(clear - MK16; Z.div_mod_to_equations; lia) ltac:(lia) (proj2 (af_acc_live RT AF Σ3 m6 MK 72 ART6 (IN23 _ INMK2))) MKC6
                SAHI ltac:(clear - SA16; Z.div_mod_to_equations; lia) ltac:(lia) (proj2 (af_acc_live RT AF Σ3 m6 SA 32 ART6 (IN23 _ INSA2))) SAC6
                PHI ltac:(clear - P16; Z.div_mod_to_equations; lia) ltac:(lia) (proj2 (af_acc_live RT AF Σ3 m6 P 128 ART6 (IN23 _ INP2))) PC6 SAP
                ltac:(rewrite EU1; exact ST6) HLOS ltac:(rewrite EU1; unfold usp1, RT_STACK in *; lia) ltac:(rewrite EU1; unfold usp1, USTACK_TOP in *; lia) MI6) as WU.
  rewrite EU1 in WU.
  cl_lift WU Hc7' c8 Hc8.
  destruct (ASTA_unpack RT Σ3 _ _ c8 Hc8) as (ms8 & (y1 & z1 & z2 & z3 & top' & m7 & -> & MU7 & WM7 & MI7 & HT7 & ST7 & SAC7 & PC7) & Hc8'). clear Hc8.

  (* [comment removed for export] *)
  assert (OUT7 : forall Q : Z -> Prop, (forall x, Q x -> ~ (usp1 - 112 <= x < usp1) /\ ~ (SA + 8 <= x < SA + 24) /\ ~ (P <= x < P + 8)) -> agree_on Q m6 m7).
  { intros Q HQ a Ha. apply MU7. cbn [outside]. destruct (HQ _ Ha) as (X1 & X2 & X3). repeat split; try exact I; lia. }
  assert (ART7 : ART RT Σ3 m7).
  { apply (af_frame RT AF Σ3 m6 m7 (usp1 - 112) ART6 ltac:(rewrite SP3, SP2, SP1; unfold usp1; lia)); [| exact WM7].
    intros a Ha. apply MU7. cbn [outside]. repeat split; try exact I; intros Hin; apply Ha.
    - left. unfold usp1, USTACK_TOP in *. lia.
    - right; right; left. exists SA, 32. split; [exact (IN23 _ INSA2)| lia].
    - right; right; left. exists P, 128. split; [exact (IN23 _ INP2)| lia]. }
  assert (STAT7 : forall a cs, rw_cells asegs m6 a cs -> a + Z.of_nat (cells_size cs) <= 0x10007fff8000 -> rw_cells asegs m7 a cs).
  { intros a cs X H1. apply (rw_cells_agree asegs m6 m7 _ _ X); [| exact WM7]. apply OUT7. intros x Hx. unfold usp1 in *. lia. }
  assert (FB7 : rw_cells asegs m7 f [C8 (Z_to_bv 64 LS_MAGIC)]).
  { apply (rw_cells_agree asegs m6 m7 _ _ (rw_cells_head m6 _ _ _ FB6)); [| exact WM7]. apply OUT7. cbn [cells_size csize Nat.add]. intros x Hx.
    destruct (af_frames_range RT AF Σ2 m4 f 0%nat ART4 FRIN4) as (_ & _ & _ & FAP2). change (fs_size 0) with 64 in FAP2.
    pose proof (FAP2 _ _ INSA2) as X1. pose proof (FAP2 _ _ INP2) as X2. unfold usp1 in *. lia. }
  assert (SB7 : rw_cells asegs m7 (f / 8 + 2147450880) [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))]).
  { apply (rw_cells_agree asegs m6 m7 _ _ SB6); [| exact WM7]. apply OUT7. cbn [cells_size csize Nat.add]. intros x Hx.
    destruct (proj1 (af_fshadow_apart RT AF Σ2 m4 f 0%nat ART4 FRIN4) SA 32 INSA2) as [Y1|Y1]; destruct (proj1 (af_fshadow_apart RT AF Σ2 m4 f 0%nat ART4 FRIN4) P 128 INP2) as [Y2|Y2];
      change (fs_size 0) with 64 in *; rewrite ?SHF in *; unfold shad, SHB, usp1 in *; lia. }
  eassert (FR7 : rw_cells asegs m7 (usp + -64) _) by (apply (rw_cells_agree asegs m6 m7 _ _ FR6); [| exact WM7]; apply OUT7; cbn [cells_size csize Nat.add]; intros x Hx; unfold usp1, usp in *; lia).
  assert (GAP7 : stk asegs m7 usp1 (usp + -64)) by (apply (stk_agree_nw asegs m6 m7 _ _ GAP6); intros x Hx; cbv beta in Hx; apply MU7; cbn [outside]; unfold usp1, usp in *; repeat split; try exact I; lia).
  destruct (af_client_consts RT AF Σ3 m7 ART7) as (_ & _ & _ & _ & UT7).
  (* [comment removed for export] *)
  pose proof (ls_wxa sp gp (Z_to_bv 64 TP_A) x0 y1 x2 (Z_to_bv 64 1) z1 z2 z3 g4 g5 g6 g7 s6 s7 s8 s9 s10 s11 x3 x4 x5 x6 F6 fc6 m7 (Z_to_bv 64 SITE_ls_ush) f lo pad
                (Z_to_bv 64 LS_MAGIC) r0 _ _ _ _ _ _ _ _ F0 F64 FIMG ltac:(lia) ltac:(destruct FSH; [left | right]; lia) FB7 SB7 UT7 (STAT7 _ _ LSR6 ltac:(cbn; unfold G_LS_RET; lia))
                ST7 HLOS ltac:(fold usp; unfold RT_STACK in *; lia) SPH MI7) as WXA.
  fold usp usp1 in WXA.
  cl_lift WXA Hc8' c9 Hc9.
  destruct (ASTA_unpack RT Σ3 _ _ c9 Hc9) as (ms9 & (m8 & -> & MU8 & WM8 & MI8 & LSR8) & Hc9'). clear Hc9.
  assert (OUT8 : forall Q : Z -> Prop, (forall x, Q x -> ~ (f <= x < f + 8) /\ ~ (shad f <= x < shad f + 8) /\ ~ (G_LS_RET <= x < G_LS_RET + 4)) -> agree_on Q m7 m8).
  { intros Q HQ a Ha. apply MU8. cbn [outside]. destruct (HQ _ Ha) as (X1 & X2 & X3). unfold shad, SHB, G_LS_RET in *. repeat split; try exact I; lia. }
  assert (FRIN6 : In (f, 0%nat) (rt_frames RT Σ3)) by (rewrite FRS3; exact FRIN4).
  assert (ART8 : ART RT Σ3 m8).
  { apply (af_frame RT AF Σ3 m7 m8 (usp1 - 112) ART7 ltac:(rewrite SP3, SP2, SP1; unfold usp1; lia)); [| exact WM8].
    intros a Ha. apply MU8. cbn [outside]. repeat split; try exact I; intros Hin; apply Ha.
    - apply (acl_frame _ _ _ f 0%nat); [exact FRIN6| change (fs_size 0) with 64; lia].
    - apply (acl_fshadow _ _ _ f 0%nat); [exact FRIN6| change (fs_size 0) with 64; rewrite SHF; unfold shad, SHB in *; lia].
    - right; left. apply client_static_intro; unfold G_LS_RET in *; lia. }
  (* [comment removed for export] *)
  destruct (af_frame_release RT AF Σ3 m8 f 0%nat (rt_frames RT Σ) ART8 ltac:(rewrite FRS3, FRS2; exact FRS1)) as (Σ4 & fl & FLG & NAC & FL0 & FLW & FW & REL).
  change (fs_size 0) with 64 in FW. replace (f + 64 - 8) with (f + 56) in FW by lia. rewrite SP3, SP2, SP1 in FLW.
  assert (NFL : forall x, aclient (rt_live RT Σ3) (rt_frames RT Σ3) (usp1 - 112) x -> x <> fl).
  { intros x Hx E. subst x. destruct Hx as [H|H]; [unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia|]. apply NAC. right. exact H. }
  eassert (FR8 : rw_cells asegs m8 (usp + -64) _) by (apply (rw_cells_agree asegs m7 m8 _ _ FR7); [| exact WM8]; apply OUT8; cbn [cells_size csize Nat.add]; intros x Hx; unfold shad, SHB, G_LS_RET, usp in *; lia).
  assert (GAP8 : stk asegs m8 usp1 (usp + -64)) by (apply (stk_agree_nw asegs m7 m8 _ _ GAP7); intros x Hx; cbv beta in Hx; apply MU8; cbn [outside]; unfold shad, SHB, G_LS_RET, usp1, usp in *; repeat split; try exact I; lia).
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  assert (ST8 : stk asegs m8 lo usp1).
  { apply (stk_agree_nw asegs m7 m8 _ _ ST7). intros x Hx. cbv beta in Hx. apply MU8. cbn [outside]. unfold shad, SHB, G_LS_RET, usp1 in *. repeat split; try exact I; lia. }
  pose proof (ls_wxb sp gp (Z_to_bv 64 TP_A) x0 y1 x2 (Z_to_bv 64 (-11)) z1 z2 z3 g4 g5 g6 g7 (Z_to_bv 64 1) (Z_to_bv 64 (f / 8 + 2147450880)) s6 s7 s8 s9 s10 s11 x3 x4 x5 x6
                (Z_to_bv 64 SITE_ls_ush) ra s0 s1 s2 s3 s4 s5 F6 fc6 m8 f fl lo pad j8
                HP ltac:(fold usp; unfold RT_STACK in *; lia) HLOS SPH F0 ltac:(lia) FL0 ltac:(lia) ST8 GAP8 FR8 FW FLG MI8) as WXB.
  fold usp usp1 in WXB.
  cl_lift WXB Hc9' c10 Hc10.
  destruct (ASTA_unpack RT Σ3 _ _ c10 Hc10) as (ms10 & (q0 & q1 & q2 & q3 & q4 & q5 & q6 & m9 & -> & MU9 & WM9 & MI9 & ST9 & FL9) & Hc10'). clear Hc10.
  fold usp in ST9.
  destruct (REL m9 MU9 WM9 FL9) as (ART9 & FRS4 & LV4 & SP4 & CR4 & AL4 & AM4 & CG4).
  (* [comment removed for export] *)
  assert (INL3 : forall x, In x (rt_live RT Σ) -> In x (rt_live RT Σ3)) by (intros x Hx; apply IN23; rewrite LV2, LV1; right; right; right; exact Hx).
  assert (PERM3' : Permutation (rt_live RT Σ3) ((L' ++ [(pk, 40)]) ++ rt_live RT Σ2)) by (rewrite <- app_assoc; exact PERM3).
  assert (APART : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) usp a ->
            ~ (MK <= a < MK + 72) /\ ~ (SA <= a < SA + 32) /\ ~ (P <= a < P + 128) /\ ~ (pk <= a < pk + 40) /\ ~ (f <= a < f + 64) /\ ~ (shad f <= a < shad f + 8) /\ a <> fl
            /\ (usp <= a \/ a < usp - 0x340)).
  { intros a Ha.
    destruct (newframe_apart RT AF Σ Σ1 m2 f 0%nat usp _ ART2 FRS1 LV1 SP1 ltac:(lia) Ha) as (N1 & N2). change (fs_size 0) with 64 in N1, N2. rewrite SHF in N2.
    pose proof (cl_split RT AF Σ m usp 0x340 _ ART0 ltac:(lia) ltac:(lia) Ha) as N4.
    assert (NF : a <> fl).
    { intros E. subst a. destruct Ha as [H|H]; [unfold USTACK_TOP, RT_STACK, STACK_WIN in *; lia|]. apply NAC. right.
      destruct H as [H|[H|[H|H]]]; [left; exact H | right; left; destruct H as (p' & n' & Hin & R); exists p', n'; split; [exact (INL3 _ Hin)| exact R]
        | right; right; left; destruct H as (f' & k' & Hin & R); exists f', k'; split; [rewrite FRS3, FRS2, FRS1; right; exact Hin | exact R]
        | right; right; right; destruct H as (f' & k' & Hin & R); exists f', k'; split; [rewrite FRS3, FRS2, FRS1; right; exact Hin | exact R]]. }
    assert (BLK : forall p n, In (p, n) (rt_live RT Σ2) -> ~ In (p, n) (rt_live RT Σ) -> 0 < n -> 0x10007fff8000 <= p -> ~ (p <= a < p + n)).
    { intros p n Hin Hnot Hn Hhi R. destruct Ha as [H|[H|[H|[H|H]]]].
      - pose proof (af_live_range RT AF Σ2 m4 p n ART4 Hin) as (_ & X & _). rewrite SP2, SP1 in X. clear - X H R NUM. unfold USTACK_TOP, STACK_WIN, RT_STACK in *. lia.
      - pose proof (client_static_range _ H) as CR. clear - CR Hhi R. unfold SEGTOP_A in *. lia.
      - destruct H as (p' & n' & Hin' & R'). rewrite LV2, LV1 in Hin.
        assert (D : p + n <= p' \/ p' + n' <= p).
        { destruct Hin as [E|[E|[E|E]]]; [injection E; intros <- <- .. | exfalso; exact (Hnot E)].
          + exact (af_live_disj RT AF Σ2 m4 P 128 p' n' [] ((SA, 32) :: (MK, 72) :: rt_live RT Σ1) ART4 ltac:(rewrite LV2; reflexivity) ltac:(rewrite LV1; right; right; exact Hin')).
          + exact (af_live_disj RT AF Σ2 m4 SA 32 p' n' [(P, 128)] ((MK, 72) :: rt_live RT Σ1) ART4 ltac:(rewrite LV2; reflexivity) ltac:(rewrite LV1; right; right; exact Hin')).
          + exact (af_live_disj RT AF Σ2 m4 MK 72 p' n' [(P, 128); (SA, 32)] (rt_live RT Σ1) ART4 ltac:(rewrite LV2; reflexivity) ltac:(rewrite LV1; right; right; exact Hin')). }
        pose proof (proj1 (Forall_forall _ _) POS _ Hin') as Hn'. cbn in Hn'. clear - D Hn' Hn R R'. lia.
      - destruct H as (f' & k' & Hin' & R'). pose proof (af_frames_range RT AF Σ2 m4 f' k' ART4 ltac:(rewrite FRS2, FRS1; right; exact Hin')) as (_ & _ & _ & X).
        destruct (X p n Hin) as [Y|Y]; clear - Y R R'; lia.
      - destruct H as (f' & k' & Hin' & R'). pose proof (af_frames_range RT AF Σ m f' k' ART0 Hin') as (FRA & FRB & _). pose proof (af_frames_hi RT AF Σ m f' k' ART0 Hin') as FRC.
        unfold shad, SHB in R'. clear - R R' FRA FRB FRC Hhi SP0R. unfold USTACK_TOP, STACK_WIN in *. assert (f' + fs_size k' <= 2 ^ 47) by lia. Z.div_mod_to_equations. lia. }
    assert (NMK : ~ In (MK, 72) (rt_live RT Σ)) by (intros Hin; pose proof (af_live_disj RT AF Σ2 m4 MK 72 MK 72 [(P, 128); (SA, 32)] (rt_live RT Σ1) ART4 ltac:(rewrite LV2; reflexivity) ltac:(rewrite LV1; right; right; exact Hin)); lia).
    assert (NSA : ~ In (SA, 32) (rt_live RT Σ)) by (intros Hin; pose proof (af_live_disj RT AF Σ2 m4 SA 32 SA 32 [(P, 128)] ((MK, 72) :: rt_live RT Σ1) ART4 ltac:(rewrite LV2; reflexivity) ltac:(rewrite LV1; right; right; exact Hin)); lia).
    assert (NP : ~ In (P, 128) (rt_live RT Σ)) by (intros Hin; pose proof (af_live_disj RT AF Σ2 m4 P 128 P 128 [] ((SA, 32) :: (MK, 72) :: rt_live RT Σ1) ART4 ltac:(rewrite LV2; reflexivity) ltac:(rewrite LV1; right; right; exact Hin)); lia).
    assert (NPK : ~ (pk <= a < pk + 40)).
    { intros R. destruct Ha as [H|[H|[H|[H|H]]]].
      - pose proof (af_live_range RT AF Σ3 m6 pk 40 ART6 ltac:(eapply Permutation_in; [apply Permutation_sym; exact PERM3| apply in_or_app; right; left; reflexivity])) as (_ & X & _).
        rewrite SP3, SP2, SP1 in X. clear - X H R NUM. unfold USTACK_TOP, STACK_WIN, RT_STACK in *. lia.
      - pose proof (client_static_range _ H) as CR. pose proof (afp_live_hi RT GOBJ AFP Σ3 m6 pk 40 ART6 ltac:(eapply Permutation_in; [apply Permutation_sym; exact PERM3| apply in_or_app; right; left; reflexivity]) ltac:(lia)) as PKH. clear - CR PKH R. unfold SEGTOP_A in *. lia.
      - destruct H as (p' & n' & Hin' & R'). pose proof (proj1 (Forall_forall _ _) POS _ Hin') as Hn. cbn in Hn.
        pose proof (Fz_I1_insert.lrest_apart RT AF Σ3 m6 (L' ++ [(pk, 40)]) (rt_live RT Σ2) pk 40 p' n' ART6 PERM3' ltac:(apply in_or_app; right; left; reflexivity) ltac:(rewrite LV2, LV1; right; right; right; exact Hin') ltac:(lia) Hn) as XX. clear - XX R R' Hn. lia.
      - destruct H as (f' & k' & Hin' & R'). pose proof (af_frames_range RT AF Σ3 m6 f' k' ART6 ltac:(rewrite FRS3, FRS2, FRS1; right; exact Hin')) as (_ & _ & _ & X).
        destruct (X pk 40 ltac:(eapply Permutation_in; [apply Permutation_sym; exact PERM3| apply in_or_app; right; left; reflexivity])) as [Y|Y]; clear - Y R R'; lia.
      - destruct H as (f' & k' & Hin' & R'). pose proof (af_frames_range RT AF Σ m f' k' ART0 Hin') as (FRA & FRB & _). pose proof (af_frames_hi RT AF Σ m f' k' ART0 Hin') as FRC.
        pose proof (afp_live_hi RT GOBJ AFP Σ3 m6 pk 40 ART6 ltac:(eapply Permutation_in; [apply Permutation_sym; exact PERM3| apply in_or_app; right; left; reflexivity]) ltac:(lia)) as PKH.
        unfold shad, SHB in R'. clear - R R' FRA FRB FRC PKH SP0R. unfold USTACK_TOP, STACK_WIN in *. assert (f' + fs_size k' <= 2 ^ 47) by lia. Z.div_mod_to_equations. lia. }
    pose proof (BLK MK 72 INMK2 NMK ltac:(lia) MKHI). pose proof (BLK SA 32 INSA2 NSA ltac:(lia) SAHI). pose proof (BLK P 128 INP2 NP ltac:(lia) PHI).
    repeat split; try assumption. }

  (* [comment removed for export] *)
  assert (NFLs : forall x, client_static x -> x <> fl) by (intros x Hx E; subst x; apply NAC; right; left; exact Hx).
  assert (WM69 : wmono asegs m6 m9) by exact (wmono_trans asegs _ _ _ WM7 (wmono_trans asegs _ _ _ WM8 WM9)).
  assert (AG69 : forall Q : Z -> Prop, (forall x, Q x -> ~ (usp1 - 112 <= x < usp1) /\ ~ (SA + 8 <= x < SA + 24) /\ ~ (P <= x < P + 8) /\ ~ (f <= x < f + 8)
                                                  /\ ~ (shad f <= x < shad f + 8) /\ ~ (G_LS_RET <= x < G_LS_RET + 4) /\ x <> fl) -> agree_on Q m6 m9).
  { intros Q HQ a Ha. destruct (HQ _ Ha) as (X1 & X2 & X3 & X4 & X5 & X6 & X7). clear HQ Ha. unfold shad, SHB, G_LS_RET in X5, X6.
    rewrite (MU9 a). 2:{ cbn [outside]. clear - X7. split; [lia| exact I]. }
    rewrite (MU8 a). 2:{ cbn [outside]. unfold G_LS_RET. clear - X4 X5 X6. repeat split; try exact I; lia. }
    apply MU7. cbn [outside]. clear - X1 X2 X3. repeat split; try exact I; lia. }
  assert (STAT69 : forall a cs, rw_cells asegs m6 a cs -> 0xb8f190 <= a -> a + Z.of_nat (cells_size cs) <= 0xbc57d0 ->
            (a + Z.of_nat (cells_size cs) <= 0xba3e98 \/ 0xbc41b8 <= a) -> (a + Z.of_nat (cells_size cs) <= 0xbc5298 \/ 0xbc52a0 <= a) ->
            (a + Z.of_nat (cells_size cs) <= G_LS_RET \/ G_LS_RET + 4 <= a) -> rw_cells asegs m9 a cs).
  { intros a cs X H1 H2 H3 H4 H5. apply (rw_cells_agree asegs m6 m9 _ _ X); [| exact WM69]. apply AG69. intros x Hx. cbv beta in Hx.
    assert (CSx : client_static x) by (clear - H1 H2 H3 H4 Hx; apply client_static_intro; lia). pose proof (NFLs x CSx) as NX.
    clear - H1 H2 H3 H4 H5 Hx NX SAHI PHI FIMG F0 NUM HLOS HSTK HP. unfold shad, SHB, usp1, G_LS_RET, USTACK_TOP, RT_STACK, STACK_WIN in *. repeat split; lia. }
  assert (MKP : P + 128 <= MK \/ MK + 72 <= P) by exact (af_live_disj RT AF Σ2 m4 P 128 MK 72 [] ((SA, 32) :: (MK, 72) :: rt_live RT Σ1) ART4 ltac:(rewrite LV2; reflexivity) ltac:(right; left; reflexivity)).
  assert (MKS : SA + 32 <= MK \/ MK + 72 <= SA) by exact (af_live_disj RT AF Σ2 m4 SA 32 MK 72 [(P, 128)] ((MK, 72) :: rt_live RT Σ1) ART4 ltac:(rewrite LV2; reflexivity) ltac:(right; left; reflexivity)).
  destruct (af_frames_range RT AF Σ2 m4 f 0%nat ART4 FRIN4) as (_ & _ & _ & FAP2). change (fs_size 0) with 64 in FAP2.
  pose proof (FAP2 _ _ INMK2) as FMK. pose proof (FAP2 _ _ INSA2) as FSA. pose proof (FAP2 _ _ INP2) as FP.
  assert (INPK3 : In (pk, 40) (rt_live RT Σ3)) by (eapply Permutation_in; [apply Permutation_sym; exact PERM3| apply in_or_app; right; left; reflexivity]).
  destruct (af_frames_range RT AF Σ3 m6 f 0%nat ART6 FRIN6) as (_ & _ & _ & FAP3). change (fs_size 0) with 64 in FAP3.
  pose proof (FAP3 _ _ INPK3) as FPK. pose proof (afp_live_hi RT GOBJ AFP Σ3 m6 pk 40 ART6 INPK3 ltac:(clear; lia)) as PKHI.
  pose proof (af_live_range RT AF Σ3 m6 pk 40 ART6 INPK3) as (_ & PKLO & _). rewrite SP3, SP2, SP1 in PKLO.
  assert (PKS : SA + 32 <= pk \/ pk + 40 <= SA) by exact (Fz_I1_insert.lrest_apart RT AF Σ3 m6 (L' ++ [(pk, 40)]) (rt_live RT Σ2) pk 40 SA 32 ART6 PERM3' ltac:(apply in_or_app; right; left; reflexivity) INSA2 ltac:(clear; lia) ltac:(clear; lia)) || 
    (pose proof (Fz_I1_insert.lrest_apart RT AF Σ3 m6 (L' ++ [(pk, 40)]) (rt_live RT Σ2) pk 40 SA 32 ART6 PERM3' ltac:(apply in_or_app; right; left; reflexivity) INSA2 ltac:(clear; lia) ltac:(clear; lia)) as XX; lia).
  assert (PKP : P + 128 <= pk \/ pk + 40 <= P) by (pose proof (Fz_I1_insert.lrest_apart RT AF Σ3 m6 (L' ++ [(pk, 40)]) (rt_live RT Σ2) pk 40 P 128 ART6 PERM3' ltac:(apply in_or_app; right; left; reflexivity) INP2 ltac:(clear; lia) ltac:(clear; lia)) as XX; lia).
  assert (NFL3 : forall p n x, In (p, n) (rt_live RT Σ3) -> p <= x < p + n -> x <> fl) by (intros p n x Hin R E; subst x; apply NAC; right; right; left; exists p, n; split; [exact Hin| exact R]).
  assert (MKC9 : rw_cells asegs m9 MK [CB 24 (zeros 24); C8 (Z_to_bv 64 SA); CB 40 (zeros 40)]).
  { apply (rw_cells_agree asegs m6 m9 _ _ MKC6); [| exact WM69]. apply AG69. cbn [cells_size csize Nat.add]. intros x Hx.
    pose proof (NFL3 MK 72 x (IN23 _ INMK2) ltac:(clear - Hx; lia)) as NX. clear - Hx NX MKP MKS FMK MKHI MKLO NUM HLOS HSTK HP F0 FLO SP0R. unfold shad, SHB, usp1, G_LS_RET, USTACK_TOP, RT_STACK, STACK_WIN in *. repeat split; lia. }
  assert (MC9 : rw_cells asegs m9 pk (mutex_cells z64 z64)).
  { apply (rw_cells_agree asegs m6 m9 _ _ MC6); [| exact WM69]. apply AG69. cbn [cells_size csize Nat.add mutex_cells]. intros x Hx.
    pose proof (NFL3 pk 40 x INPK3 ltac:(clear - Hx; lia)) as NX. clear - Hx NX PKP PKS FPK PKHI PKLO NUM HLOS HSTK HP F0 FLO SP0R. unfold shad, SHB, usp1, G_LS_RET, USTACK_TOP, RT_STACK, STACK_WIN in *. repeat split; lia. }
  assert (AG79 : forall Q : Z -> Prop, (forall x, Q x -> ~ (f <= x < f + 8) /\ ~ (shad f <= x < shad f + 8) /\ ~ (G_LS_RET <= x < G_LS_RET + 4) /\ x <> fl) -> agree_on Q m7 m9).
  { intros Q HQ a Ha. destruct (HQ _ Ha) as (X4 & X5 & X6 & X7). clear HQ Ha. unfold shad, SHB, G_LS_RET in X5, X6.
    rewrite (MU9 a). 2:{ cbn [outside]. clear - X7. split; [lia| exact I]. }
    apply MU8. cbn [outside]. unfold G_LS_RET. clear - X4 X5 X6. repeat split; try exact I; lia. }
  assert (WM79 : wmono asegs m7 m9) by exact (wmono_trans asegs _ _ _ WM8 WM9).
  assert (SAC9 : rw_cells asegs m9 SA (sa_hdr (Z_to_bv 64 1) z64 top' (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 1) + sa_delta z64 (Z_to_bv 64 (-1)))) (Z_to_bv 64 P))).
  { apply (rw_cells_agree asegs m7 m9 _ _ SAC7); [| exact WM79]. apply AG79. unfold sa_hdr. cbn [cells_size csize Nat.add]. intros x Hx.
    pose proof (NFL3 SA 32 x (IN23 _ INSA2) ltac:(clear - Hx; lia)) as NX. clear - Hx NX FSA SAHI F0 FLO SP0R. unfold shad, SHB, G_LS_RET, USTACK_TOP, STACK_WIN in *. repeat split; lia. }
  change (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 1) + sa_delta z64 (Z_to_bv 64 (-1)))) with (Z_to_bv 64 0) in SAC9.
  assert (PC9 : rw_cells asegs m9 P [C8 z64; CB 120 (zeros 120)]).
  { apply (rw_cells_agree asegs m7 m9 _ _ PC7); [| exact WM79]. apply AG79. cbn [cells_size csize Nat.add]. intros x Hx.
    pose proof (NFL3 P 128 x (IN23 _ INP2) ltac:(clear - Hx; lia)) as NX. clear - Hx NX FP PHI F0 FLO SP0R. unfold shad, SHB, G_LS_RET, USTACK_TOP, STACK_WIN in *. repeat split; lia. }
  assert (LSR9 : rw_cells asegs m9 G_LS_RET [C4 (Z_to_bv 64 1)]).
  { apply (rw_cells_agree asegs m8 m9 _ _ LSR8); [| exact WM9]. cbn [cells_size csize Nat.add]. intros x Hx. apply MU9. cbn [outside]. split; [| exact I].
    assert (CSx : client_static (bv_unsigned x)) by (clear - Hx; apply client_static_intro; unfold G_LS_RET in *; lia). pose proof (NFLs _ CSx) as NX. clear - NX Hx. unfold G_LS_RET in *. lia. }
  assert (CLE9 : cl_env m9 lb' canary).
  { apply (cl_env_agree m6 m9 _ _ CLE6). intros a Ha. apply (AG69 cl_cell); [| exact Ha]. intros x Hx.
    pose proof (cl_cell_static _ Hx) as CS. pose proof (NFLs _ CS) as NX. pose proof (client_static_range _ CS) as CR.
    unfold cl_cell, in_ranges, CL_CELLS in Hx. destruct Hx as (lo' & hi' & Hin & R). cbn in Hin.
    clear - Hin R NX CR SAHI PHI FIMG F0 NUM HLOS HSTK HP. unfold G_MALLOC_IMPL, CL_REALLOC_IMPL, CL_FREE_IMPL, CL_MEMSET_FUNC, G_ALLOW_CUST, ssp_guard, shad, SHB, usp1, G_LS_RET, USTACK_TOP, RT_STACK, SEGTOP_A in *.
    decompose [or] Hin; try match goal with H : (_, _) = (_, _) |- _ => injection H; intros; subst end; try contradiction; repeat split; try lia. }
  assert (REPE9 : lh_repE GOBJ m9 L' lh B g' bks').
  { destruct REPE6 as (REP & PERML & ALN). split; [| exact (conj PERML ALN)]. pose proof (lh_geo_bounds g' (proj1 REP)) as GB.
    eapply lh_rep_agree; [exact REP| | intros ? ? ? ? _ X; exact X]. intros a Ra Ha.
    assert (INa : exists p n, In (p, n) L' /\ p <= a < p + n /\ n <= 64512).
    { destruct Ha as [X|[X|(q & A & Hq & X)]]; [exists lh, 104| exists B, (8 * g_na g')| exists A, 24]; (split; [| split; [lia | clear - GB; lia]]).
      - eapply Permutation_in; [apply Permutation_sym; exact PERML| left; reflexivity].
      - eapply Permutation_in; [apply Permutation_sym; exact PERML| right; left; reflexivity].
      - destruct (lh_rep_owned asegs LH_CEIL _ _ _ _ _ _ _ _ _ _ _ REP q A Hq) as [O _]. exact O. }
    destruct INa as (p & n & Hin & R & NSZ).
    assert (INp3 : In (p, n) (rt_live RT Σ3)) by (eapply Permutation_in; [apply Permutation_sym; exact PERM3| apply in_or_app; left; exact Hin]).
    pose proof (af_live_range RT AF Σ3 m6 p n ART6 INp3) as (_ & PLO' & _). rewrite SP3, SP2, SP1 in PLO'.
    assert (Hn1 : 0 < n) by (clear - R; lia). pose proof (afp_live_hi RT GOBJ AFP Σ3 m6 p n ART6 INp3 NSZ) as PHI'.
    pose proof (FAP3 _ _ INp3) as PF.
    pose proof (Fz_I1_insert.lrest_apart RT AF Σ3 m6 (L' ++ [(pk, 40)]) (rt_live RT Σ2) p n SA 32 ART6 PERM3' ltac:(apply in_or_app; left; exact Hin) INSA2 ltac:(clear - Hn1; lia) ltac:(clear; lia)) as PS.
    pose proof (Fz_I1_insert.lrest_apart RT AF Σ3 m6 (L' ++ [(pk, 40)]) (rt_live RT Σ2) p n P 128 ART6 PERM3' ltac:(apply in_or_app; left; exact Hin) INP2 ltac:(clear - Hn1; lia) ltac:(clear; lia)) as PP.
    pose proof (NFL3 p n a INp3 R) as NX.
    assert (E : m9 (wa a) = m6 (wa a)); [| split; [exact E| intros Hw; apply WM69; exact Hw]].
    apply (AG69 (fun x => x = a)); [| unfold wa; rewrite unsigned_lit by (clear - Ra; lia); reflexivity]. intros x ->. clear - R PLO' PHI' PF PS PP NX NUM HLOS HSTK HP F0 FLO SP0R. unfold shad, SHB, usp1, G_LS_RET, USTACK_TOP, RT_STACK, STACK_WIN in *. repeat split; lia. }
  assert (STC9 : err_statics m9 pk lh).
  { destruct STC6 as (Y1 & Y2 & Y3 & Y4). unfold err_statics, G_ERR_ONCE, G_ERR_FLAG, G_ERR_LOCK, G_ERR_HASH in *.
    pose proof (STAT69 _ _ Y1 ltac:(clear - HJ; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; unfold G_LS_RET; lia)) as W1'.
    pose proof (STAT69 _ _ Y2 ltac:(clear - HJ; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; unfold G_LS_RET; lia)) as W2'.
    pose proof (STAT69 _ _ Y3 ltac:(clear - HJ; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; unfold G_LS_RET; lia)) as W3'.
    pose proof (STAT69 _ _ Y4 ltac:(clear - HJ; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; unfold G_LS_RET; lia)) as W4'.
    exact (conj W1' (conj W2' (conj W3' W4'))). }
  (* [comment removed for export] *)
  apply Hk. exists Σ4, MK, SA, P, pk, lh, B, L', g', bks', lb', u', e', top', (Z_to_bv 64 fl).
  split.
  2:{ split; [rewrite LV4; eapply Permutation_trans; [exact PERM3| rewrite LV2, LV1; apply Permutation_refl]|].
      split; [exact LL3|]. split; [exact IT3|].
      split; [exact FRS4|]. split; [rewrite SP4, SP3, SP2; exact SP1|]. split; [rewrite CR4; lia|]. split; [rewrite CG4, CG3, CG2; exact CG1|].
      repeat split; assumption. }
  eapply ASTA_conseq; [exact (ASTA_switch RT Σ3 Σ4 PMc _ c10 Hc10' AL4 AM4)|]. intros ms <-. exists m9.
  split; [exists q0, q1, q2, z1, z2, z3, g4, g5, g6, g7, q3, q4, q5, q6, F6, fc6; reflexivity|].
  split; [exact (conj ART9 (conj MI9 ST9))|].
  split.
  { intros a Ha Ho. destruct (APART _ Ha) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). unfold LS_W in Ho. cbn [outside] in Ho.
    destruct Ho as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & O12 & O13 & O14 & O15 & _).
    rewrite (MU9 a). 2:{ cbn [outside]. clear - A7. split; [lia| exact I]. }
    rewrite (MU8 a). 2:{ cbn [outside]. unfold G_LS_RET in *. unfold shad, SHB in A6. clear - A5 A6 O15. repeat split; try exact I; lia. }
    rewrite (MU7 a). 2:{ cbn [outside]. clear - A2 A3 A8 HP. unfold usp1. repeat split; try exact I; lia. }
    assert (X1 : aclient (rt_live RT Σ2) (rt_frames RT Σ2) usp1 (bv_unsigned a)).
    { apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros y Hy; rewrite LV2, LV1; right; right; right; exact Hy | rewrite FRS2, FRS1; intros y Hy; right; exact Hy | clear - HP; unfold usp1; lia]. }
    assert (X2 : outside (EFIRST_W pk) (bv_unsigned a)) by (unfold EFIRST_W, G_CANCELBUF; cbn [outside]; clear - O1 O8 O11 O12 O13 O14; repeat split; try exact I; lia).
    rewrite (PRES6 a X1 X2).
    assert (X3 : aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp1 (bv_unsigned a)).
    { apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros y Hy; rewrite LV1; exact Hy | rewrite FRS1; intros y Hy; right; exact Hy | clear - HP; unfold usp1; lia]. }
    assert (X4 : outside (SHV_W j (f + 32)) (bv_unsigned a)) by (unfold SHV_W; cbn [outside]; clear - O1 O2 O3 O4 O5 O6 O7 O8 O9 O10 A5; repeat split; try exact I; lia).
    rewrite (PRES4 a X3 X4). rewrite (PR3 a Ha). exact (PR2 a Ha). }
  split; [exact CLE9|].
  unfold G_IC_STOPPED, G_IC_OPTSDONE, G_IC_BASE_ONCE, G_IC_BASE_RET, G_CANCELBUF in *.
  split; [exact (STAT69 _ _ STP6 ltac:(clear - HJ; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; unfold G_LS_RET; lia))|].
  split; [exact (STAT69 _ _ OD6 ltac:(clear - HJ; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; unfold G_LS_RET; lia))|].
  split; [exact (STAT69 _ _ ONCE6 ltac:(clear - HJ; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; unfold G_LS_RET; lia))|].
  split; [exact (STAT69 _ _ BRET6 ltac:(clear - HJ; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; unfold G_LS_RET; lia))|].
  split; [exact (STAT69 _ _ ERC6 ltac:(clear - HJ; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; unfold G_LS_RET; lia))|].
  split; [exact (STAT69 _ _ OC6 ltac:(clear - HJ; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; unfold G_LS_RET; lia))|].
  split; [exact (STAT69 _ _ IC6 ltac:(clear - HJ; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; unfold G_LS_RET; lia))|].
  split; [exact (STAT69 _ _ KC6 ltac:(clear - HJ; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; unfold G_LS_RET; lia))|].
  split; [exact (STAT69 _ _ NK6 ltac:(clear - HJ; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; unfold G_LS_RET; lia))|].
  split; [exact (STAT69 _ _ KL6 ltac:(clear - HJ; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; unfold G_LS_RET; lia))|].
  split; [exact (STAT69 _ _ KJ6 ltac:(clear - HJ; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; unfold G_LS_RET; lia))|].
  split; [exact (STAT69 _ _ CBC6 ltac:(clear - HJ; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; unfold G_LS_RET; lia))|].
  split; [exact (STAT69 _ _ SLOT6 ltac:(clear - HJ HJ1; lia) ltac:(clear - HJ HJ1; cbn; lia) ltac:(clear - HJ HJ1; cbn; lia) ltac:(clear - HJ HJ1; cbn; lia) ltac:(clear - HJ HJ1; cbn; unfold G_LS_RET; lia))|].
  split; [exact (STAT69 _ _ UC6 ltac:(clear - HJ; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; lia) ltac:(clear - HJ; cbn; unfold G_LS_RET; lia))|].
  split; [exact MKC9|]. split; [exact SAC9|]. split; [rewrite HT7; reflexivity|]. split; [exact PC9|].
  split; [exact STC9|]. split; [exact MC9|]. split; [exact REPE9|]. exact LSR9.
Qed.
End LoadStr.
