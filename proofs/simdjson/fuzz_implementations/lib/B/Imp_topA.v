(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import PropExec ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP Frame.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_rlkit D_libiface D_auxv I_lkit X_aexdefs X_ixdefs X_atcxa Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_num_akit Sj_num_iface Sj_h_alloc Sj_stage2_iface Atp_hkit4A Atp_hkit5A Atp_fzwA Atp_setcapA Atp_defsA Atp_activewA Atp_pid1A Atp_pidiA Pj_rtkA Pj_cpsA Pj_defsA Pj_hdefsA Imp_hdefsA Imp_ifaceA Imp_libifaceA Imp_ios_defsA Imp_gsidefsA Imp_lftoi1A Imp_lftoi2A Imp_lftoi3A Imp_lftoi4A Imp_segdefsA Imp_segA3a Imp_segA3 Imp_segA2 Imp_segA1b Imp_segA1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma imp_cost_bound : forall n, 0 <= n < 2^26 -> 1 + imp_setup_costA n <= FUZZ_COST_IMP.
Proof.
  intros n N. change (2^26) with 67108864 in N.
  assert (C : 32 <= Z.max n 32 <= 2^26) by (change (2^26) with 67108864; lia).
  pose proof (al_sbuf_bounds _ C) as B1. pose proof (al_tape_bounds _ C) as B2. pose proof (sc_idx_bounds (Z.max n 32) ltac:(change (2^26) with 67108864; lia)) as B3.
  assert (SB : al_sbuf (Z.max n 32) <= 2 * Z.max n 32 + 128) by (unfold al_sbuf, roundup64; Z.div_mod_to_equations; lia).
  assert (TP : al_tape (Z.max n 32) <= 8 * Z.max n 32 + 536) by (unfold al_tape, roundup64; Z.div_mod_to_equations; lia).
  assert (SC : sc_idx (Z.max n 32) <= 4 * Z.max n 32 + 288) by (unfold sc_idx, roundup64; Z.div_mod_to_equations; lia).
  pose proof (mcost_le (al_sbuf (Z.max n 32)) ltac:(lia)) as M1. pose proof (mcost_le (al_tape (Z.max n 32)) ltac:(lia)) as M2.
  pose proof (mcost_le (sc_idx (Z.max n 32)) ltac:(lia)) as M3.
  pose proof (mcost_small 96 ltac:(lia)) as M4. pose proof (mcost_small 8192 ltac:(lia)) as M5. pose proof (mcost_small 1024 ltac:(lia)) as M6. pose proof (mcost_small 8 ltac:(lia)) as M8.
  pose proof (mcost_le (n + 64) ltac:(lia)) as M7.
  unfold imp_setup_costA, imp_body_costA, GRSI_COST_A, pj_pid_costA, pid_cost6, S2A_COST, Sj_num_iface.NUMA_CREDIT, imp_okarm_costA, IMP_PUT_COST_A, FUZZ_COST_IMP, DCOST in *.
  change (2^30) with 1073741824 in *. change (3 * 2^31) with 6442450944. lia.
Qed.

Section Top.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PDONE : rts RT -> mem -> Z -> list (Z * Z) -> Prop.
Hypothesis PDT : pdtor_cps RT PDONE.
Hypothesis PDFP : pdone_fpA RT PDONE.
Hypothesis PID : pj_pid_cpsA RT (pj_libA sj_lib) PDONE.
Hypothesis OKARM : forall PMc, imp_okarm_cpsA RT PMc.
Hypothesis GRSI : grsi_icontractA RT.
Hypothesis ATCXA : atcxa_icontract RT.
Local Ltac ul := unfold FUZZ_STACK_IMP, FUZZ_STACK, PID_STACK, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.

Theorem fuzz_one_impA : fuzz_one_cps_imp RT imp_libA.
Proof using AF RC PDT PDFP PID OKARM GRSI ATCXA.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo v
    FDO MST EA0 EA1 ETP D0 BSL BS INLV FRS0 LVPOS LVB CR0 S0C LIBv AXv VIN IOS NL0 XD0 AUX0 SPG ART0 MI0 ST0 LOW LOR SPT SPA SPLE FRM.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_client_consts RT AF Σ m ART0) as CC0.
  set (usp := bv_unsigned sp) in *. set (n := Z.of_nat (length bs)) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (N0 : 0 <= n < 2^26) by (subst n; lia).
  assert (DR : 0 <= d < 2^64).
  { destruct INLV as [(p & k & Hin & P1 & P2)|(E & DL)]; [| clear - D0 DL; ul].
    pose proof (af_live_range RT AF Σ m p k ART0 Hin) as (R0 & R1 & R2). clear - D0 P1 P2 R1 SP0R N0. ul. }
  match goal with |- cps bsegs _ ?K0 => set (K := K0) end.

  assert (KFIN : imp_fin_k RT PMc K Σ v usp lo ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m (rt_credit RT Σ - FUZZ_COST_IMP)).
  { unfold imp_fin_k. intros Σ' A8 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' FRM' ART' MI' ST' PR' LIB' AX' VA LV' FRS' SP' CR'.
    apply (aevt_done RT PMc). intros c Hc. subst K. cbv beta. split.
    - exists Σ', A8. split; [| split; [exact VA| split; [exact LV'| split; [exact FRS'| split; [exact SP'| exact CR']]]]].
      eapply ASTA_conseq; [exact Hc|]. intros ms <-. exists m'.
      split; [rewrite ESP; do 16 eexists; reflexivity|]. split; [split; [exact ART'| split; [exact MI'| exact ST']]|].
      split; [rewrite FRS0; exact PR'| split; [exact LIB'| exact AX']].
    - rewrite (asta_eq_fcsr RT Σ' PMc _ c Hc). exact FRM'. }
  eapply cps_conseq; [| intros c [Hc _]; exact Hc| intros c Hc; exact Hc].
  apply (cps_of_aevt RT PMc). subst a0 a1 tp. rewrite ESP. unfold entry_st.

  destruct (imp_prologue usp lo d n ra gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m
              ST0 ltac:(ul) ltac:(ul) ltac:(ul) SPA ltac:(lia) CC0 MI0) as (sp' & SPR & SPA' & W0).
  apply (aevt_evt RT AF PMc MST). change (Z_to_bv 64 TP_A) with (Z_to_bv 64 TPV_A). eapply evt_cut; [exact W0|]. cbv beta.
  intros ms1 (m1 & a1' & a3' & j0 & j8 & j120 & -> & MU1 & WM1 & MI1 & ST1 & L0 & STp1 & SV1). apply evt_done. clear W0.
  assert (AG01 : forall P : Z -> Prop, (forall x, P x -> ~ (sp' <= x < usp)) -> agree_on P m m1).
  { intros P HP a Ha. apply MU1. cbn [outside]. split; [exact (HP _ Ha)| exact I]. }
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 sp' ART0 ltac:(ul)); [| exact WM1]. intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. ul. }
  assert (NST : forall x, client_static x \/ in_live (rt_live RT Σ) x -> ~ (sp' <= x < usp)).
  { intros x [Hx|Hx]; [pose proof (client_static_range _ Hx); clear - H SPR LOW LOR SP0R; ul|].
    destruct Hx as (p & k & Hin & R). pose proof (af_live_range RT AF Σ m p k ART0 Hin) as (_ & Y & _). clear - R Y SPR LOW LOR. ul. }
  assert (LIB1 : imp_libA v m1).
  { apply (imp_libA_agree v m m1 LIBv). apply AG01. intros x Hx. apply NST. destruct (imp_lib_rng_cases v x Hx) as [[CS _]|(B & EB & R)]; [left; exact CS|].
    right. exists B, 8. split; [exact (VIN B EB)| lia]. }
  assert (AX1 : aexvA v m1).
  { destruct v as [B|]; cbn [aexvA] in AXv |- *.
    - apply (aex6A_agree m m1 AXv). apply AG01. intros x (l & h & Hin & R). apply NST. left. unfold IMP_AEX_W in Hin. revert R. aex_lits. cbn [In] in Hin. intros R.
      destruct Hin as [E|[E|[]]]; injection E as <- <-; apply client_static_intro; lia.
    - destruct AXv as [(p1 & p2 & f4 & f5 & T4) (b4 & b5 & A4)]. split; [exists p1, p2, f4, f5| exists b4, b5];
        [apply (rw_cells_agree_nw bsegs m m1 _ _ T4)| apply (rw_cells_agree_nw bsegs m m1 _ _ A4)]; apply AG01; intros x Hx;
        [unfold aex_tbl in Hx| unfold aex_args in Hx]; cbn [cells_size csize Nat.add] in Hx; apply NST; left; apply client_static_intro; aex_lits; lia. }
  assert (BS1 : bytes_at bsegs m1 d bs).
  { apply (bytes_at_agree bsegs m m1 _ _ BS). apply AG01. intros x Hx. cbv beta in Hx. apply NST. right.
    destruct INLV as [(p & k & Hin & P1 & P2)| (E & DL)]; [| subst n; rewrite E in Hx; cbn [length] in Hx; lia]. exists p, k. split; [exact Hin| subst n; lia]. }
  assert (PRES1 : forall a : word, aclient (rt_live RT Σ) [] usp (bv_unsigned a) -> outside IMP_XFP_A (bv_unsigned a) -> m1 a = m a).
  { intros a Ha _. apply MU1. cbn [outside]. split; [| exact I]. rewrite <- FRS0 in Ha. destruct (aclient_split_c RT AF Σ m usp _ ART0 Ha); [lia| ul]. }
  assert (EU1 : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; ul).
  clear MU1 WM1 ST0 MI0.

  unfold entry_st.
  eapply (aevt_icall RT PMc).
  { exact (rc_stack_malloc_5 RT RC Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 lo FDO MST ltac:(right; right; reflexivity) eq_refl
             ltac:(rewrite FRS0; cbn; unfold FRAMES_MAX; lia) ltac:(unfold FUZZ_COST_IMP in CR0; lia) ART1 MI1
             ltac:(unfold call_ok; rewrite EU1; split; [exact ST1|]; split; [ul|]; split; [ul|]; split; [ul| clear - SPA'; Z.div_mod_to_equations; lia])
             ltac:(intros _; rewrite EU1; clear - SPLE SPR; lia)). }
  intros c (Σ1 & f & HQ & FRS1 & LV1 & SP1 & CR1 & FPOS & F64 & FTOP). eexists Σ1, _. split; [exact HQ|].
  intros ms' (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WRF & WRS).
  apply (ret_stF_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 ms' (fun ms => aevt RT PMc Σ1 K ms) RS2).
  intros v0 v1 v2 e1 e2 e3 e4 e5 e6 e7 v3 v4 v5 v6 F1. rewrite EU1 in ST2, PRES2.
  rewrite (ret_pc_even IMP_SMRET_A) by (unfold IMP_SMRET_A; lia). rewrite FRS0 in FRS1.
  change (fs_size 5) with 2048 in *. change (2048 / 8) with 256 in WRS. replace (2048 - 8) with 2040 in WRF by reflexivity.
  assert (INF1 : In (f, 5%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  pose proof (fframe_ranges RT AF Σ1 m2 f 5 ART2 INF1) as (_ & FR1' & _ & SHB0 & SHT).
  pose proof (af_fshadow_apart RT AF Σ1 m2 f 5 ART2 INF1) as (FSL & FSF). pose proof (FSF f 5%nat INF1) as FSELF.
  pose proof (af_frames_align RT AF Σ1 m2 f 5 ART2 INF1) as (_ & FSEG).
  change (fs_size 5) with 2048 in *. rewrite SP1 in FR1', SHT.
  assert (SHF : shad (f + 2048) = shad f + 256) by (unfold shad; Z.div_mod_to_equations; lia). rewrite SHF in *.

  assert (G : impG (rt_sp0 RT Σ) usp sp' f lo).
  { unfold impG. split; [exact FSEG|]. split; [exact F64|]. split; [exact FR1'|]. split; [exact SHB0|]. split; [exact SHT|]. split; [exact FSELF|].
    split; [exact LOW|]. split; [unfold FUZZ_STACK_IMP in LOR; exact LOR|]. split; [exact SPT|]. split; [exact SPR|]. split; [exact SPA'|]. split; [exact SP0W| lia]. }

  assert (AG12 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) [] sp' x) -> agree_on P m1 m2).
  { intros P HP a Ha. apply PRES2. rewrite FRS0. exact (HP _ Ha). }
  apply (imp_setupA RT AF RC PDONE PDT PDFP PID OKARM GRSI ATCXA PMc FDO MST Σ Σ1 K v usp sp' f lo d bs gp v0 v1 v2 e1 e2 e3 e4 e5 e6 e7 s3 s4 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6
           ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F1 fc m m2 (rt_credit RT Σ - FUZZ_COST_IMP) j0 j8 j120 G ART2 MI2 ST2 FRS1 LV1 SP1);
    [| unfold FUZZ_COST_IMP in CR0 |- *; lia| exact VIN| rewrite LV1; exact LVPOS| rewrite LV1; unfold FUZZ_LIVE_IMP in LVB; lia| exact D0| exact BSL| | exact INLV| | | | exact WRF| exact WRS| | | exact NL0| exact IOS| | exact FRM| exact KFIN].
  - pose proof (imp_cost_bound n N0) as CB. subst n. lia.
  - apply (bytes_at_agree bsegs m1 m2 _ _ BS1). apply AG12. intros x Hx. cbv beta in Hx.
    destruct INLV as [(p & k & Hin & P1 & P2)| (E & DL)]; [| subst n; rewrite E in Hx; cbn [length] in Hx; lia]. right; right; left. exists p, k. split; [exact Hin| subst n; lia].
  - apply (rw_cells_agree_nw bsegs m1 m2 _ _ L0). apply AG12. intros x Hx. unfold imp_locals0 in Hx. cbn [cells_size csize Nat.add] in Hx. left. ul.
  - apply (stk_agree_nw bsegs m1 m2 _ _ STp1). apply AG12. intros x Hx. cbv beta in Hx. left. ul.
  - apply (rw_cells_agree_nw bsegs m1 m2 _ _ SV1). apply AG12. intros x Hx. rewrite imp_savedA_size in Hx. left. ul.
  - apply (imp_libA_agree v m1 m2 LIB1). apply AG12. intros x Hx. destruct (imp_lib_rng_cases v x Hx) as [[CS _]|(B & EB & R)]; [right; left; exact CS|].
    right; right; left. exists B, 8. split; [exact (VIN B EB)| lia].
  - destruct v as [B|]; cbn [aexvA] in AX1 |- *.
    + apply (aex6A_agree m1 m2 AX1). apply AG12. intros x (l & h & Hin & R). right; left. unfold IMP_AEX_W in Hin. revert R. aex_lits. cbn [In] in Hin. intros R.
      destruct Hin as [E|[E|[]]]; injection E as <- <-; apply client_static_intro; lia.
    + destruct AX1 as [(p1 & p2 & f4 & f5 & T4) (b4 & b5 & A4)]. split; [exists p1, p2, f4, f5| exists b4, b5];
        [apply (rw_cells_agree_nw bsegs m1 m2 _ _ T4)| apply (rw_cells_agree_nw bsegs m1 m2 _ _ A4)]; apply AG12; intros x Hx;
        [unfold aex_tbl in Hx| unfold aex_args in Hx]; cbn [cells_size csize Nat.add] in Hx; right; left; apply client_static_intro; aex_lits; lia.
  - intros a Ha Ho. rewrite <- (PRES1 a Ha Ho). apply PRES2. rewrite FRS0. apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e []| lia].
Qed.

End Top.
