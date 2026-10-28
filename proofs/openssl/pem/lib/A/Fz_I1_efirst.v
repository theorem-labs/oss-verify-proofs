(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Malloc Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import LhPure LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs PLayout Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_mkit Fz_G_kit Th_mutex Th_once Fz_T_lock Fz_T_once Fz_I1_img Fz_I1_hash Fz_I1_defs Fz_env Fz_M_malloc Fz_M_zalloc Fz_M_locknew Fz_M_realloc Fz_M_realloc_array Fz_W5_icb Fz_I1_insw Fz_I1_insx Fz_I1_insert Fz_I1_loadw Fz_I1_load Fz_I1_errload Fz_G_CRYPTO_calloc Fz_G_OPENSSL_LH_set_thunks Fz_G_OPENSSL_LH_new Fz_I1_first.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).

Definition TPV : Z := 0xba3ef0.                (* [comment removed for export] *)
Definition G_CANCELBUF : Z := 0xba3e90.        (* [comment removed for export] *)

Section EFirst.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_DESI : do_esi_stmt RT GOBJ.
Hypothesis C_ELS : err_load_strings_stmt RT GOBJ.

Definition EFIRST_SITES : list (Z * Z) := OELS_SITES ++ DESI_SITES.
Definition EFIRST_CALLS : list (Z * Z) := (ONCE_RET_INIT, e_do_esi) :: OELS_CALLS ++ DESI_CALLS.
Definition EFIRST_W (pk : Z) : list (Z * Z) :=
  [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (G_ERR_ONCE, G_ERR_ONCE + 4); (G_ERR_LOCK, G_ERR_LOCK + 8); (G_ERR_HASH, G_ERR_HASH + 8); (G_ERR_FLAG, G_ERR_FLAG + 4);
   (G_CANCELBUF, G_CANCELBUF + 8)].

(* [comment removed for export] *)
Definition efirst_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary od lk0 h0 f0 oldcb : word) (n1 n2 : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TPV ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x200 + 176 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_err_strings (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) EFIRST_SITES EFIRST_CALLS ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 3 + n1 + n2 < LIVE_MAX -> 2 <= rt_credit RT Σ ->
  Forall (fun x => 0 < snd x) (rt_live RT Σ) ->
  cl_env m lb canary ->
  rw_cells asegs m G_IC_STOPPED [C1 (Z_to_bv 8 0)] -> rw_cells asegs m G_IC_OPTSDONE [C8 od] ->
  rw_cells asegs m G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)] -> rw_cells asegs m G_IC_BASE_RET [C4 (Z_to_bv 64 1)] ->
  rw_cells asegs m G_ERR_ONCE [C4 z64] -> rw_cells asegs m G_ERR_LOCK [C8 lk0] -> rw_cells asegs m G_ERR_HASH [C8 h0] -> rw_cells asegs m G_ERR_FLAG [C4 f0] ->
  rw_cells asegs m G_CANCELBUF [C8 oldcb] ->
  els_table GOBJ ERR_TAB1 n1 -> els_table GOBJ ERR_TAB2 n2 -> 0 <= n1 -> 0 <= n2 -> n1 + n2 < LH_KMAX ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_err_strings m)))
    (fun c => exists (Σ' : rts RT) (pk lh B : Z) (L' : list (Z * Z)) (g' : lh_geo) (bks' : list (list (bptr * Z))) (lb' : byte),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
           /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (EFIRST_W pk) m m'
           /\ cl_env m' lb' canary
           /\ rw_cells asegs m' G_IC_STOPPED [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m' G_IC_OPTSDONE [C8 od]
           /\ rw_cells asegs m' G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m' G_IC_BASE_RET [C4 (Z_to_bv 64 1)]
           /\ err_statics m' pk lh /\ rw_cells asegs m' G_CANCELBUF [C8 oldcb]
           /\ rw_cells asegs m' pk (mutex_cells z64 z64) /\ lh_repE GOBJ m' L' lh B g' bks') c
       /\ Permutation (rt_live RT Σ') (L' ++ (pk, 40) :: rt_live RT Σ) /\ Z.of_nat (length L') <= 2 + n1 + n2 /\ 0 <= g_items g' <= n1 + n2
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 2 <= rt_credit RT Σ' /\ rt_cg RT Σ' = rt_cg RT Σ
       /\ 0 < pk /\ pk mod 16 = 0 /\ pk + 40 < USTACK_TOP /\ 0x10007fff8000 <= pk
       /\ (forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) x -> ~ (pk <= x < pk + 40))).

Theorem efirst_cps : efirst_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary od lk0 h0 f0 oldcb n1 n2
    FDO MST -> ART0 MI0 CALL HSTK CTX UWC CGH Hfr Hlen Hcr POS ENV STP OD ONCE BRET ONC LKC LHC FLC CBC TAB1 TAB2 N1 N2 ITEMS.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 688 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP /\ SEGTOP_A <= lo) by (unfold RT_STACK, STACK_WIN, USTACK_TOP, SEGTOP_A in *; lia).
  cl_eu usp (-16) EU1. cl_eu usp (-144) EU2.
  assert (LO0 : 0x10007fff8000 <= lo) by lia. assert (HT1 : bv_unsigned sp <= 2 ^ 47) by (fold usp; unfold USTACK_TOP in *; lia).
  unfold G_IC_STOPPED, G_IC_OPTSDONE, G_IC_BASE_ONCE, G_IC_BASE_RET in STP, OD, ONCE, BRET. unfold G_ERR_ONCE in ONC. unfold G_ERR_LOCK in LKC. unfold G_ERR_HASH in LHC.
  unfold G_ERR_FLAG in FLC. unfold G_CANCELBUF in CBC. unfold TPV in *.
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  (* [comment removed for export] *)
  pose proof (oels_w0 ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                ST LO0 ltac:(fold usp; unfold RT_STACK in *; lia) HT1 MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1. fold usp in MU1, ST1, FR1, Hc1'.
  assert (MU1' : munch ([] ++ [(usp - 16, usp)]) m m1) by (eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside app]; intros; lia).
  pose proof (cl_seg_ART RT AF Σ m m1 usp 16 [] ART0 ltac:(lia) ltac:(lia) MU1' ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 16 [] ART0 ltac:(lia) ltac:(lia) MU1') as PR1.
  assert (STAT1 : forall a cs, rw_cells asegs m a cs -> 0x10000 <= a -> a + Z.of_nat (cells_size cs) <= SEGTOP_A -> rw_cells asegs m1 a cs).
  { intros a cs H H1 H2. apply (rw_cells_agree asegs m m1 _ _ H); [| exact WM1]. intros x Hx. cbv beta in Hx. apply MU1. cbn [outside]. unfold SEGTOP_A in *. split; [lia| exact I]. }
  pose proof (STAT1 _ _ ONC ltac:(lia) ltac:(cbn; unfold SEGTOP_A; lia)) as ONC1. pose proof (STAT1 _ _ CBC ltac:(lia) ltac:(cbn; unfold SEGTOP_A; lia)) as CBC1.
  assert (ENV1 : cl_env m1 lb canary).
  { apply (cl_env_agree m m1 lb canary ENV). intros a Ha. pose proof (client_static_range _ (cl_cell_static _ Ha)) as CR. unfold SEGTOP_A in *.
    apply MU1. cbn [outside]. split; [lia| exact I]. }
  destruct (af_client_consts RT AF Σ m1 ART1) as (_ & SHC1 & _ & _ & UT1).
  (* [comment removed for export] *)
  pose proof (T_run_once_enter_proof (Z_to_bv 64 OELS_ONCE_RET) (Z_to_bv 64 (usp + -16)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 (Z_to_bv 64 G_ERR_ONCE) (Z_to_bv 64 e_do_esi) a2 a3 a4 a5 a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo e_do_esi oldcb canary) as WE.
  rewrite (unsigned_lit G_ERR_ONCE), (unsigned_lit 0xba3ef0), EU1 in WE by (unfold G_ERR_ONCE; lia). unfold G_ERR_ONCE, got_ssp, ssp_guard in WE.
  specialize (WE ONC1 eq_refl eq_refl ltac:(unfold e_do_esi; lia) eq_refl (cl_env_ssp m1 lb canary UT1 ENV1) CBC1 ltac:(lia) ST1 ltac:(lia) ltac:(unfold RT_STACK in *; lia)).
  specialize (WE ltac:(left; lia) ltac:(left; lia) ltac:(left; lia) ltac:(left; lia) ltac:(left; lia) ltac:(left; lia) ltac:(right; lia) ltac:(left; lia) ltac:(right; lia) MI1).
  cl_lift WE Hc1' c2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (a0' & a1' & a2' & a3' & junk & m2 & -> & MU2 & WM2 & MI2 & ST2 & SSP2 & ONC2 & CBC2 & FULL2 & PO2 & FR2) & Hc2'). clear Hc2.
  rewrite (ret_pc_even e_do_esi) in Hc2' by (unfold e_do_esi; lia).
  replace (usp + -16 + -128) with (usp + -144) in * by lia. replace (usp + -16 + -32) with (usp + -48) in * by lia. replace (usp + -16 + -16) with (usp + -32) in * by lia.
  assert (MU2' : munch ([(0xb9f820, 0xb9f820 + 4); (0xba3e90, 0xba3e90 + 8)] ++ [(usp - 144, usp)]) m1 m2).
  { eapply munch_weaken; [| exact MU2]. unfold sub_fp. cbn [outside app]. intros; lia. }
  pose proof (cl_seg_ART RT AF Σ m1 m2 usp 144 _ ART1 ltac:(lia) ltac:(lia) MU2' ltac:(intros x Hx; apply client_static_intro; cbn [outside app] in Hx; lia) WM2) as ART2.
  assert (OFF12 : forall P : Z -> Prop, (forall x, P x -> ~ (usp - 144 <= x < usp - 16) /\ ~ (0xb9f820 <= x < 0xb9f824) /\ ~ (0xba3e90 <= x < 0xba3e98)) -> agree_on P m1 m2).
  { intros P HP a Ha. apply MU2. cbn [outside]. destruct (HP _ Ha) as (X1 & X2 & X3). repeat split; try exact I; lia. }
  assert (STAT2 : forall a cs, rw_cells asegs m a cs -> 0x10000 <= a -> a + Z.of_nat (cells_size cs) <= SEGTOP_A ->
                   (a + Z.of_nat (cells_size cs) <= 0xb9f820 \/ 0xb9f824 <= a) -> a + Z.of_nat (cells_size cs) <= 0xba3e90 -> rw_cells asegs m2 a cs).
  { intros a cs H H1 H2 H3 H4. apply (rw_cells_agree asegs m1 m2 _ _ (STAT1 a cs H H1 H2)); [| exact WM2]. apply OFF12. unfold SEGTOP_A, STACK_WIN in *. intros; lia. }
  pose proof (STAT2 _ _ STP ltac:(lia) ltac:(cbn; unfold SEGTOP_A; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as STP2.
  pose proof (STAT2 _ _ OD ltac:(lia) ltac:(cbn; unfold SEGTOP_A; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as OD2.
  pose proof (STAT2 _ _ ONCE ltac:(lia) ltac:(cbn; unfold SEGTOP_A; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as ONCE2.
  pose proof (STAT2 _ _ BRET ltac:(lia) ltac:(cbn; unfold SEGTOP_A; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as BRET2.
  pose proof (STAT2 _ _ LKC ltac:(lia) ltac:(cbn; unfold SEGTOP_A; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as LKC2.
  pose proof (STAT2 _ _ LHC ltac:(lia) ltac:(cbn; unfold SEGTOP_A; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as LHC2.
  pose proof (STAT2 _ _ FLC ltac:(lia) ltac:(cbn; unfold SEGTOP_A; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as FLC2.
  assert (ENV2 : cl_env m2 lb canary) by (apply (cl_env_seg _ m1 m2 _ canary ENV1 MU2); cl_fp_lia).
  (* [comment removed for export] *)
  apply (C_DESI Σ PMc (Z_to_bv 64 ONCE_RET_INIT) (Z_to_bv 64 (usp + -144)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 (Z_to_bv 64 12187680) (Z_to_bv 64 e_do_esi) a0' a1' a2' a3' a4 a5 a6 a7
           (Z_to_bv 64 0) (Z_to_bv 64 12336944) (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 2) s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 lo [] lb canary od lk0 h0 f0 FDO MST eq_refl ART2 MI2).
  { unfold call_ok. rewrite EU2. split; [exact ST2|]. split; [exact LOW|]. split; [unfold RT_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|].
    fold usp in SPA. clear - SPA. Z.div_mod_to_equations. lia. }
  { rewrite EU2. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit ONCE_RET_INIT) by (unfold ONCE_RET_INIT; lia). split; [| exact I]. apply (proj2 CGH). left. reflexivity. }
  { cbn [uw_chain]. left. rewrite (unsigned_lit 12187680), EU2 by lia. unfold RT_STACK in *. lia. }
  { clear - CGH. unfold EFIRST_SITES, EFIRST_CALLS in CGH. split; intros x Hx; [apply (proj1 CGH); apply in_or_app; right; exact Hx| apply (proj2 CGH); right; apply in_or_app; right; exact Hx]. }
  { exact Hfr. }
  { lia. }
  { exact Hcr. }
  { exact ENV2. }
  { exact STP2. }
  { exact OD2. }
  { exact ONCE2. }
  { exact BRET2. }
  { exact LKC2. }
  { exact LHC2. }
  { exact FLC2. }
  { exact Hc2'. }
  clear Hc2'. intros c3 (Σ1 & pk & lh & B & Hc3 & LV1 & FRS1 & SP1 & CR1 & CG1 & PK0 & PK16 & PKHI).
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (m3 & RS3 & (ART3 & MI3 & ST3) & PRES3 & ENV3 & STP3 & OD3 & ONCE3 & BRET3 & LKC3 & LHC3 & FLC3 & MC3 & REPE3) & Hc3'). clear Hc3.
  destruct RS3 as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F3 & fc3 & ->).
  rewrite EU2 in ST3, PRES3. rewrite (ret_pc_even ONCE_RET_INIT) in Hc3' by (unfold ONCE_RET_INIT; lia).
  assert (AG23 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) (usp - 144) x
                     /\ ~ (0xb9f7c0 <= x < 0xb9f7c1) /\ ~ (0xb9f7e0 <= x < 0xb9f7e8) /\ ~ (0xb9f800 <= x < 0xb9f808) /\ ~ (0xb9f840 <= x < 0xb9f844)) -> agree_on P m2 m3).
  { intros P HP a Ha. destruct (HP _ Ha) as (X1 & X2 & X3 & X4 & X5). apply PRES3; [exact X1|]. cbn [outside]. unfold G_ALLOW_CUST, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG. repeat split; try exact I; lia. }
  assert (ONC3 : rw_cells asegs m3 12187680 [C4 (Z_to_bv 64 1)]).
  { apply (rw_cells_agree_nw asegs m2 m3 _ _ ONC2). apply AG23. cbn [cells_size csize Nat.add]. intros x Hx. split; [right; left; apply client_static_intro; lia| repeat split; lia]. }
  assert (CBC3 : rw_cells asegs m3 12205712 [C8 (Z_to_bv 64 (usp + -144))]).
  { replace 12205712 with (12205808 + -96) by reflexivity. apply (rw_cells_agree_nw asegs m2 m3 _ _ CBC2). apply AG23. cbn [cells_size csize Nat.add]. intros x Hx. split; [right; left; apply client_static_intro; lia| repeat split; lia]. }
  eassert (FULL3 : rw_cells asegs m3 (usp + -144) _).
  { apply (rw_cells_agree_nw asegs m2 m3 _ _ FULL2). apply AG23. cbn [cells_size csize Nat.add once_full_cells]. intros x Hx. split; [left; unfold USTACK_TOP in *; lia| unfold STACK_WIN in *; repeat split; lia]. }
  eassert (PO3 : rw_cells asegs m3 (usp + -48) _).
  { apply (rw_cells_agree_nw asegs m2 m3 _ _ PO2). apply AG23. cbn [cells_size csize Nat.add]. intros x Hx. split; [left; unfold USTACK_TOP in *; lia| unfold STACK_WIN in *; repeat split; lia]. }
  eassert (FRO3 : rw_cells asegs m3 (usp + -32) _).
  { apply (rw_cells_agree_nw asegs m2 m3 _ _ FR2). apply AG23. cbn [cells_size csize Nat.add]. intros x Hx. split; [left; unfold USTACK_TOP in *; lia| unfold STACK_WIN in *; repeat split; lia]. }
  destruct (af_client_consts RT AF Σ1 m3 ART3) as (_ & _ & _ & _ & UT3).
  (* [comment removed for export] *)
  pose proof (T_run_once_leave_proof (Z_to_bv 64 ONCE_RET_INIT) gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 (Z_to_bv 64 e_do_esi) (Z_to_bv 64 1) e1 e2 e3 e4 e5 e6 e7 (Z_to_bv 64 0)
                (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 2) s7 s8 s9 s10 s11 w3 w4 w5 w6 F3 fc3 m3 lo (usp + -16) 12187680 (Z_to_bv 64 (usp + -144)) oldcb canary
                (Z_to_bv 64 OELS_ONCE_RET) sp s1 s2 s3 s4 s5 s6 junk) as WL.
  rewrite (unsigned_lit 0xba3ef0) in WL by lia. unfold got_ssp, ssp_guard in WL.
  replace (usp + -16 + -128) with (usp + -144) in WL by lia. replace (usp + -16 + -32) with (usp + -48) in WL by lia. replace (usp + -16 + -16) with (usp + -32) in WL by lia.
  specialize (WL ONC3 eq_refl (cl_env_ssp m3 _ canary UT3 ENV3) CBC3 ltac:(lia) FULL3 PO3 FRO3 ST3 ltac:(lia) ltac:(unfold RT_STACK in *; lia) ltac:(unfold USTACK_TOP in *; lia)).
  specialize (WL ltac:(left; lia) ltac:(left; lia) ltac:(left; lia) ltac:(left; lia) ltac:(left; lia) ltac:(left; lia) ltac:(right; lia) ltac:(left; lia) ltac:(right; lia) MI3).
  cl_lift WL Hc3' c4 Hc4.
  destruct (ASTA_unpack RT Σ1 _ _ c4 Hc4) as (ms4 & (b1 & b2 & b3 & m4 & -> & MU4 & WM4 & MI4 & ST4 & SSP4 & ONC4 & CBC4) & Hc4'). clear Hc4.
  rewrite (ret_pc_even OELS_ONCE_RET) in Hc4' by (unfold OELS_ONCE_RET; lia).
  replace (usp + -16 - 160) with (usp - 176) in MU4 by lia.
  assert (MU4' : munch ([(12187680, 12187680 + 4); (12205712, 12205712 + 8)] ++ [(usp - 16 - 160, usp - 16)]) m3 m4).
  { eapply munch_weaken; [| exact MU4]. unfold sub_fp. cbn [outside app]. intros; lia. }
  pose proof (cl_seg_ART RT AF Σ1 m3 m4 (usp - 16) 160 _ ART3 ltac:(rewrite SP1; lia) ltac:(lia) MU4' ltac:(intros x Hx; apply client_static_intro; cbn [outside app] in Hx; lia) WM4) as ART4.
  assert (OFF34 : forall P : Z -> Prop, (forall x, P x -> ~ (usp - 176 <= x < usp - 16) /\ ~ (12187680 <= x < 12187684) /\ ~ (12205712 <= x < 12205720)) -> agree_on P m3 m4).
  { intros P HP a Ha. apply MU4. cbn [outside]. destruct (HP _ Ha) as (X1 & X2 & X3). repeat split; try exact I; lia. }
  assert (STAT4 : forall a cs, rw_cells asegs m3 a cs -> 0x10000 <= a -> (a + Z.of_nat (cells_size cs) <= 12187680 \/ 12187684 <= a) -> a + Z.of_nat (cells_size cs) <= 12205712 -> rw_cells asegs m4 a cs).
  { intros a cs H H1 H2 H3. apply (rw_cells_agree asegs m3 m4 _ _ H); [| exact WM4]. apply OFF34. unfold STACK_WIN in *. intros; lia. }
  unfold G_IC_STOPPED in STP3. unfold G_IC_OPTSDONE in OD3. unfold G_IC_BASE_ONCE in ONCE3. unfold G_IC_BASE_RET in BRET3. unfold G_ERR_LOCK in LKC3. unfold G_ERR_HASH in LHC3. unfold G_ERR_FLAG in FLC3.
  pose proof (STAT4 _ _ STP3 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as STP4. pose proof (STAT4 _ _ OD3 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as OD4.
  pose proof (STAT4 _ _ ONCE3 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as ONCE4. pose proof (STAT4 _ _ BRET3 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as BRET4.
  pose proof (STAT4 _ _ LKC3 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as LKC4. pose proof (STAT4 _ _ LHC3 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as LHC4.
  pose proof (STAT4 _ _ FLC3 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as FLC4.
  pose proof (af_live_range RT AF Σ1 m3 pk 40 ART3 ltac:(rewrite LV1; right; right; left; reflexivity)) as (_ & PKLO & _).
  pose proof (afp_live_hi RT GOBJ AFP Σ1 m3 pk 40 ART3 ltac:(rewrite LV1; right; right; left; reflexivity) ltac:(lia)) as PKH.
  pose proof (af_live_range RT AF Σ1 m3 lh 104 ART3 ltac:(rewrite LV1; right; left; reflexivity)) as (LH0 & LHLO & _).
  pose proof (afp_live_hi RT GOBJ AFP Σ1 m3 lh 104 ART3 ltac:(rewrite LV1; right; left; reflexivity) ltac:(lia)) as LHH.
  pose proof (af_live_range RT AF Σ1 m3 B 128 ART3 ltac:(rewrite LV1; left; reflexivity)) as (B0 & BLO & _).
  pose proof (afp_live_hi RT GOBJ AFP Σ1 m3 B 128 ART3 ltac:(rewrite LV1; left; reflexivity) ltac:(lia)) as BH.
  rewrite SP1 in PKLO, LHLO, BLO.
  assert (MC4 : rw_cells asegs m4 pk (mutex_cells z64 z64)) by (apply (rw_cells_agree asegs m3 m4 _ _ MC3); [apply OFF34; cbn [cells_size csize Nat.add mutex_cells]; unfold STACK_WIN in *; intros; lia| exact WM4]).
  assert (ENV4 : cl_env m4 (Z_to_bv 8 1) canary) by (apply (cl_env_seg _ m3 m4 _ canary ENV3 MU4); cl_fp_lia).
  destruct REPE3 as (REP3 & PERML & ALN).
  assert (REPE4 : lh_repE GOBJ m4 [(lh, 104); (B, 128)] lh B LH_G0 (repeat [] 16)).
  { split; [| exact (conj PERML ALN)]. eapply lh_rep_agree; [exact REP3| | intros ? ? ? ? _ X; exact X].
    eapply LhRep.agree_on_mono; [exact (LhRep.agree_on_of_munch asegs _ _ _ MU4 WM4)|].
    intros a [Ha|[Ha|(q & A & Hq & Ha)]]; cbn [outside]; [unfold LH_G0 in *; cbn [g_na] in *; unfold STACK_WIN in *; repeat split; try exact I; lia| unfold LH_G0 in *; cbn [g_na] in *; unfold STACK_WIN in *; repeat split; try exact I; lia|].
    exfalso. rewrite concat_repeat_nil' in Hq. exact Hq. }
  (* [comment removed for export] *)
  assert (UWC4 : uw_chain m4 sp s0 outer).
  { apply (uw_chain_agree outer m m4 sp s0 UWC). intros a Ha. cbv beta in Ha.
    rewrite (MU4 a ltac:(cbn [outside]; unfold USTACK_TOP in *; repeat split; try exact I; lia)).
    rewrite (PRES3 a ltac:(left; lia) ltac:(cbn [outside]; unfold G_ALLOW_CUST, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, USTACK_TOP in *; repeat split; try exact I; lia)).
    rewrite (MU2 a ltac:(cbn [outside]; unfold USTACK_TOP in *; repeat split; try exact I; lia)). apply MU1. cbn [outside]. split; [lia| exact I]. }
  eassert (FR4 : rw_cells asegs m4 (usp + -16) _).
  { apply (rw_cells_agree asegs m3 m4 _ _ (rw_cells_agree_nw asegs m2 m3 _ _ (rw_cells_agree asegs m1 m2 _ _ FR1 ltac:(apply OFF12; cbn [cells_size csize Nat.add]; unfold STACK_WIN in *; intros; lia) WM2)
             ltac:(apply AG23; cbn [cells_size csize Nat.add]; intros x Hx; split; [left; unfold USTACK_TOP in *; lia| unfold STACK_WIN in *; repeat split; lia]))); [| exact WM4].
    apply OFF34. cbn [cells_size csize Nat.add]. unfold STACK_WIN in *. intros; lia. }
  (* [comment removed for export] *)
  assert (PRES_4 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp (EFIRST_W pk) m m4).
  { intros a Ha Ho. cbn [outside] in Ho. destruct Ho as (O1 & O2 & O3 & O4 & O5 & O6 & _). unfold G_ALLOW_CUST, G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_CANCELBUF in O1, O2, O3, O4, O5, O6.
    pose proof (cl_split RT AF Σ m usp 688 _ ART0 ltac:(lia) ltac:(lia) Ha) as OFFa.
    rewrite (MU4 a ltac:(cbn [outside]; repeat split; try exact I; lia)).
    rewrite (PRES3 a ltac:(apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros ? X; exact X| intros ? X; exact X| lia]) ltac:(cbn [outside]; unfold G_ALLOW_CUST, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG; repeat split; try exact I; lia)).
    rewrite (MU2 a ltac:(cbn [outside]; repeat split; try exact I; lia)). apply MU1. cbn [outside]. split; [lia| exact I]. }
  assert (PERM1 : Permutation (rt_live RT Σ1) ([(lh, 104); (B, 128)] ++ (pk, 40) :: rt_live RT Σ)) by (rewrite LV1; apply perm_swap).
  assert (RPOS : Forall (fun x => 0 < snd x) ((pk, 40) :: rt_live RT Σ)) by (constructor; [cbn; lia| exact POS]).
  assert (INPK : In (pk, 40) ((pk, 40) :: rt_live RT Σ)) by (left; reflexivity).
  assert (PK4 : pk mod 4 = 0) by (clear - PK16; Z.div_mod_to_equations; lia).
  assert (PKR : 0 <= pk < 2^64) by (unfold USTACK_TOP in *; lia). assert (LHR : 0 <= lh < 2^64) by (unfold STACK_WIN, USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ1 m4 ART4) as (_ & SHC4 & _ & _ & UT4).
  assert (STATR : forall a, G_ERR_LOCK <= a < G_ERR_FLAG + 4 -> aclient ((pk, 40) :: rt_live RT Σ) (rt_frames RT Σ1) (usp - 16) a) by (intros a Ha; right; left; apply client_static_intro; unfold G_ERR_LOCK, G_ERR_FLAG in Ha; lia).
  assert (LOW1 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SP1; exact LOW).
  (* [comment removed for export] *)
  pose proof (oels_w1 sp gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 sp s1 b1 b2 b3 e4 e5 e6 e7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F3 fc3 m4 lo
                FLC4 UT4 ST4 LO0 ltac:(fold usp; unfold RT_STACK in *; lia) HT1 MI4) as W1.
  cl_lift W1 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ1 _ _ c5 Hc5) as (ms5 & -> & Hc5'). clear Hc5.
  rewrite <- CG1 in CTX, CGH.
  destruct (cl_chain_call (rt_cg RT Σ1) e_err_strings e_err_load_strings SITE_oels_1 m4 m4 ra s0 sp (Z_to_bv 64 (usp + -16)) outer CTX
              (proj1 CGH (SITE_oels_1, e_err_strings) ltac:(left; reflexivity)) (proj2 CGH (SITE_oels_1, e_err_load_strings) ltac:(right; left; reflexivity)) UWC4 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -16) by lia; exact FR4) ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc & UWCc).
  apply (C_ELS Σ1 PMc (Z_to_bv 64 SITE_oels_1) (Z_to_bv 64 (usp + -16)) gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 sp s1 (Z_to_bv 64 ERR_TAB1) b1 b2 b3 e4 e5 e6 e7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F3 fc3 m4 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary [(lh, 104); (B, 128)] ((pk, 40) :: rt_live RT Σ) lh B LH_G0 (repeat [] 16) pk ERR_TAB1 n1
           FDO MST eq_refl eq_refl ART4 MI4).
  { fold usp in SPA. cl_call_ok EU1 ST4 LOW1 SPA 1. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_oels_1) by (unfold SITE_oels_1; lia). exact CTXc. }
  { exact UWCc. }
  { clear - CGH. unfold EFIRST_SITES, EFIRST_CALLS, OELS_SITES, OELS_CALLS, ELS_SITES, ELS_CALLS in *.
    split; intros x Hx; [apply (proj1 CGH); apply in_or_app; left| apply (proj2 CGH); right; apply in_or_app; left]; cbn [In app] in Hx |- *; tauto. }
  { rewrite LV1. cbn [length]. lia. }
  { lia. }
  { exact ENV4. }
  { exact LKC4. }
  { exact LHC4. }
  { exact INPK. }
  { exact PK4. }
  { exact MC4. }
  { exact REPE4. }
  { exact PERM1. }
  { exact RPOS. }
  { exact TAB1. }
  { lia. }
  { unfold LH_G0. cbn [g_items]. lia. }
  { exact Hc5'. }
  clear Hc5'. intros c6 (Σ6 & L6 & B6 & g6 & bks6 & lb6 & Hc6 & PERM6 & LL6 & IT6 & FRS6 & SP6 & CR6 & CG6).
  destruct (ASTA_unpack RT Σ6 _ _ c6 Hc6) as (ms6 & (m6 & RS6 & (ART6 & MI6 & ST6) & PRES6 & ENV6 & REPE6 & MC6 & LKC6 & LHC6) & Hc6'). clear Hc6.
  destruct RS6 as (x0 & x1 & x2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & x3 & x4 & x5 & x6 & F6 & fc6 & ->).
  rewrite EU1 in ST6, PRES6. fold usp in ST6, PRES6. rewrite (ret_pc_even SITE_oels_1) in Hc6' by (unfold SITE_oels_1; lia).
  cbn [length] in LL6. unfold LH_G0 in IT6. cbn [g_items] in IT6.
  (* [comment removed for export] *)
  assert (MONO : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) usp x -> aclient ((pk, 40) :: rt_live RT Σ) (rt_frames RT Σ1) (usp - 16) x).
  { intros x Hx. apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e He; right; exact He| rewrite FRS1; intros e He; exact He| lia]. }
  assert (NPK : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) usp x -> ~ (pk <= x < pk + 40)).
  { intros x Hx. exact (newchunk_apart_gen RT AF Σ Σ1 m3 [(B, 128); (lh, 104)] pk 40 usp x ART3 LV1 FRS1 SP1 ltac:(lia) ltac:(lia) Hx). }
  assert (AG6 : forall P : Z -> Prop, (forall x, P x -> aclient ((pk, 40) :: rt_live RT Σ) (rt_frames RT Σ1) (usp - 16) x /\ x <> G_ALLOW_CUST /\ ~ (pk + 4 <= x < pk + 8)) -> agree_on P m4 m6).
  { intros P HP a Ha. destruct (HP _ Ha) as (X1 & X2 & X3). apply PRES6; [exact X1| cbn [outside]; repeat split; try exact I; lia]. }
  eassert (FR6 : rw_cells asegs m6 (usp + -16) _).
  { apply (rw_cells_agree_nw asegs m4 m6 _ _ FR4). apply AG6. cbn [cells_size csize Nat.add]. intros x Hx. split; [left; unfold USTACK_TOP in *; lia|]. unfold G_ALLOW_CUST, STACK_WIN in *. lia. }
  assert (STAT6 : forall a cs, rw_cells asegs m4 a cs -> 0xb8f190 <= a -> a + Z.of_nat (cells_size cs) <= 0xba3e98 -> (a + Z.of_nat (cells_size cs) <= G_ALLOW_CUST \/ G_ALLOW_CUST + 1 <= a) -> rw_cells asegs m6 a cs).
  { intros a cs H H1 H2 H3. apply (rw_cells_agree_nw asegs m4 m6 _ _ H). apply AG6. intros x Hx. split; [right; left; apply client_static_intro; lia|]. unfold G_ALLOW_CUST, STACK_WIN in *. lia. }
  unfold G_ALLOW_CUST in STAT6.
  pose proof (STAT6 _ _ ONC4 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as ONC6. pose proof (STAT6 _ _ CBC4 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as CBC6.
  pose proof (STAT6 _ _ FLC4 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as FLC6.
  pose proof (STAT6 _ _ STP4 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as STP6. pose proof (STAT6 _ _ OD4 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as OD6.
  pose proof (STAT6 _ _ ONCE4 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as ONCE6. pose proof (STAT6 _ _ BRET4 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as BRET6.
  pose proof (uw_chain_agree outer m4 m6 sp s0 UWC4 ltac:(apply AG6; intros x Hx; split; [left; lia|]; unfold G_ALLOW_CUST, USTACK_TOP, STACK_WIN in *; lia)) as UWC6.
  (* [comment removed for export] *)
  pose proof (oels_w2 sp gp (Z_to_bv 64 0xba3ef0) x0 x1 x2 sp s1 (Z_to_bv 64 1) d1 d2 d3 d4 d5 d6 d7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x5 x6 F6 fc6 m6 lo
                ST6 LO0 ltac:(fold usp; unfold RT_STACK in *; lia) HT1 MI6) as W2.
  cl_lift W2 Hc6' c7 Hc7.
  destruct (ASTA_unpack RT Σ6 _ _ c7 Hc7) as (ms7 & -> & Hc7'). clear Hc7.
  rewrite <- CG6 in CTX, CGH.
  destruct (cl_chain_call (rt_cg RT Σ6) e_err_strings e_err_load_strings SITE_oels_2 m6 m6 ra s0 sp (Z_to_bv 64 (usp + -16)) outer CTX
              (proj1 CGH (SITE_oels_2, e_err_strings) ltac:(right; left; reflexivity)) (proj2 CGH (SITE_oels_2, e_err_load_strings) ltac:(right; right; left; reflexivity)) UWC6 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -16) by lia; exact FR6) ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXd & UWCd).
  assert (LOW6 : rt_sp0 RT Σ6 - STACK_WIN <= lo) by (rewrite SP6; exact LOW1).
  pose proof (Permutation_length PERM6) as PL6. rewrite length_app in PL6. cbn [length] in PL6.
  apply (C_ELS Σ6 PMc (Z_to_bv 64 SITE_oels_2) (Z_to_bv 64 (usp + -16)) gp (Z_to_bv 64 0xba3ef0) x0 x1 x2 sp s1 (Z_to_bv 64 ERR_TAB2) d1 d2 d3 d4 d5 d6 d7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x5 x6 F6 fc6 m6 lo (bv_unsigned ra :: outer) lb6 canary L6 ((pk, 40) :: rt_live RT Σ) lh B6 g6 bks6 pk ERR_TAB2 n2 FDO MST eq_refl eq_refl ART6 MI6).
  { fold usp in SPA. cl_call_ok EU1 ST6 LOW6 SPA 1. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_oels_2) by (unfold SITE_oels_2; lia). exact CTXd. }
  { exact UWCd. }
  { clear - CGH. unfold EFIRST_SITES, EFIRST_CALLS, OELS_SITES, OELS_CALLS, ELS_SITES, ELS_CALLS in *.
    split; intros x Hx; [apply (proj1 CGH); apply in_or_app; left| apply (proj2 CGH); right; apply in_or_app; left]; cbn [In app] in Hx |- *; tauto. }
  { lia. }
  { rewrite CR6. lia. }
  { exact ENV6. }
  { exact LKC6. }
  { exact LHC6. }
  { exact INPK. }
  { exact PK4. }
  { exact MC6. }
  { exact REPE6. }
  { exact PERM6. }
  { exact RPOS. }
  { exact TAB2. }
  { lia. }
  { lia. }
  { exact Hc7'. }
  clear Hc7'. intros c8 (Σ8 & L8 & B8 & g8 & bks8 & lb8 & Hc8 & PERM8 & LL8 & IT8 & FRS8 & SP8 & CR8 & CG8).
  destruct (ASTA_unpack RT Σ8 _ _ c8 Hc8) as (ms8 & (m8 & RS8 & (ART8 & MI8 & ST8) & PRES8 & ENV8 & REPE8 & MC8 & LKC8 & LHC8) & Hc8'). clear Hc8.
  destruct RS8 as (v0 & v1 & v2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & v3 & v4 & v5 & v6 & F8 & fc8 & ->).
  rewrite EU1 in ST8, PRES8. fold usp in ST8, PRES8. rewrite (ret_pc_even SITE_oels_2) in Hc8' by (unfold SITE_oels_2; lia).
  rewrite FRS6 in PRES8.
  assert (AG8 : forall P : Z -> Prop, (forall x, P x -> aclient ((pk, 40) :: rt_live RT Σ) (rt_frames RT Σ1) (usp - 16) x /\ x <> G_ALLOW_CUST /\ ~ (pk + 4 <= x < pk + 8)) -> agree_on P m6 m8).
  { intros P HP a Ha. destruct (HP _ Ha) as (X1 & X2 & X3). apply PRES8; [exact X1| cbn [outside]; repeat split; try exact I; lia]. }
  eassert (FR8 : rw_cells asegs m8 (usp + -16) _).
  { apply (rw_cells_agree_nw asegs m6 m8 _ _ FR6). apply AG8. cbn [cells_size csize Nat.add]. intros x Hx. split; [left; unfold USTACK_TOP in *; lia|]. unfold G_ALLOW_CUST, STACK_WIN in *. lia. }
  assert (STAT8 : forall a cs, rw_cells asegs m6 a cs -> 0xb8f190 <= a -> a + Z.of_nat (cells_size cs) <= 0xba3e98 -> (a + Z.of_nat (cells_size cs) <= G_ALLOW_CUST \/ G_ALLOW_CUST + 1 <= a) -> rw_cells asegs m8 a cs).
  { intros a cs H H1 H2 H3. apply (rw_cells_agree_nw asegs m6 m8 _ _ H). apply AG8. intros x Hx. split; [right; left; apply client_static_intro; lia|]. unfold G_ALLOW_CUST, STACK_WIN in *. lia. }
  unfold G_ALLOW_CUST in STAT8.
  pose proof (STAT8 _ _ ONC6 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as ONC8. pose proof (STAT8 _ _ CBC6 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as CBC8.
  pose proof (STAT8 _ _ FLC6 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as FLC8.
  pose proof (STAT8 _ _ STP6 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as STP8. pose proof (STAT8 _ _ OD6 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as OD8.
  pose proof (STAT8 _ _ ONCE6 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as ONCE8. pose proof (STAT8 _ _ BRET6 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as BRET8.
  (* [comment removed for export] *)
  pose proof (oels_w3 (Z_to_bv 64 SITE_oels_2) sp gp (Z_to_bv 64 0xba3ef0) v0 v1 v2 sp s1 (Z_to_bv 64 1) h1 h2 h3 h4 h5 h6 h7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F8 fc8 m8 lo ra s0
                FR8 ST8 LO0 ltac:(fold usp; unfold RT_STACK in *; lia) HT1 MI8) as W3.
  cl_lift W3 Hc8' c9 Hc9.
  destruct (ASTA_unpack RT Σ8 _ _ c9 Hc9) as (ms9 & (-> & ST9) & Hc9'). clear Hc9.
  apply Hk. exists Σ8, pk, lh, B8, L8, g8, bks8, lb8.
  split.
  - apply (ASTA_conseq RT Σ8 PMc _ _ c9 Hc9'). intros ms9 <-. exists m8. fold usp in ST9.
    split; [exists v0, v1, v2, h1, h2, h3, h4, h5, h6, h7, v3, v4, v5, v6, F8, fc8; reflexivity|].
    split; [exact (conj ART8 (conj MI8 ST9))|].
    split. { intros a Ha Ho. pose proof (MONO _ Ha) as Ha'. pose proof (NPK _ Ha) as Na. pose proof Ho as Ho'. cbn [outside] in Ho'. destruct Ho' as (O1 & _).
             rewrite (PRES8 a Ha' ltac:(cbn [outside]; repeat split; try exact I; lia)). rewrite (PRES6 a Ha' ltac:(cbn [outside]; repeat split; try exact I; lia)).
             exact (PRES_4 a Ha Ho). }
    split; [exact ENV8|]. split; [exact STP8|]. split; [exact OD8|]. split; [exact ONCE8|]. split; [exact BRET8|].
    split; [exact (conj ONC8 (conj FLC8 (conj LKC8 LHC8)))|]. split; [exact CBC8|]. exact (conj MC8 REPE8).
  - split; [exact PERM8|]. split; [lia|]. split; [unfold LH_G0 in *; cbn [g_items] in *; pose proof (proj1 (proj1 REPE8)) as GOK; unfold lh_geo_ok, LH_KMAX in GOK; lia|].
    split; [rewrite FRS8, FRS6; exact FRS1|]. split; [rewrite SP8, SP6; exact SP1|]. split; [rewrite CR8, CR6; lia|]. split; [rewrite CG8, CG6; exact CG1|].
    split; [lia|]. split; [exact PK16|]. split; [exact PKHI|]. split; [exact PKH| exact NPK].
Qed.
End EFirst.
