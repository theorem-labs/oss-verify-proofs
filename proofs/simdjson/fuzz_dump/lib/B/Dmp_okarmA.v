(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim SjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2 Sj_num_akit Sj_h_alloc Sj_stage2_iface Atp_fzwA Atp_defsA Atp_kitA Atp_pidiA Pj_rtkA Pj_defsA Pj_os_defsA El_os_defsA El_ins_ifaceA El_defsA Dmp_hdefsA Dmp_pj_ifaceA Dmp_lftoi1A Dmp_lftoi4A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Section Okarm.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable PMc : Model -> Prop.

Hypothesis ROA : forall Σ m, ART RT Σ m -> pj_os_roA m.
Hypothesis CTOR : ctor_cpsA RT PMc OSFRESHA.
Hypothesis PJ : pj_root_cpsA RT PMc.
Hypothesis LOCD : locdtor_evtA.
Hypothesis IOSD : iosdtor_cpsA RT PMc OSIOSA.

Lemma DMP_OKARM_STACK_eq : DMP_OKARM_STACK_A = 275456 + RT_STACK.
Proof. reflexivity. Qed.
Lemma pj_needA_root : pj_needA TAPE_MAX_DEPTH = 275200 + RT_STACK.
Proof. reflexivity. Qed.
Local Ltac ul := rewrite ?DMP_OKARM_STACK_eq, ?pj_needA_root in *; unfold PJ_OS_CTOR_STACK_A, PJ_LOC_STACK_A, PJ_IOS_DTOR_STACK_A, FUZZ_STACK in *;
                 unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.

Theorem dmp_okarm_okA : dmp_okarm_cpsA RT PMc.
Proof using AF ROA CTOR PJ LOCD IOSD.
  intros Σ K X E ra gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s8 s11 t3 t4 t5 t6 F fc m j20 j112 jos j432
    FDO MST LK OKE LE P1N WFS AL FRS AI LIB NL IOS RC FT FS ARTg MIg STg NEED FRM CRB HK.
  pose proof LK as [(SPR & SPA') (SPT & SPA) (LLO & LOR) (FPOS & F64 & FSEG & FLO) (FSELF & SHB0 & SHT)].
  destruct X as [usp sp' f lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  pose proof LE as (EDOC & EFD & EKD & ELO & EHI). cbn [lf_usp lf_S1 lf_F lf_lo] in EDOC, EFD, EKD, ELO, EHI.
  pose proof (af_sp0_range RT AF Σ m ARTg) as SP0R. pose proof AL as (ALT & ALS & ALP & ALF & WLO).
  unfold lf_regs in *.
  assert (INF : In (f, 3%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  assert (STAT : forall x, client_static x -> x < sp') by (intros x Hx; pose proof (client_static_range _ Hx); clear - H LLO LOR SPR; ul).
  pose proof (af_frames_range RT AF Σ m f 3%nat ARTg INF) as (_ & _ & _ & FLV). change (fs_size 3) with 512 in FLV.
  pose proof (af_fshadow_apart RT AF Σ m f 3%nat ARTg INF) as (FSL & _). change (fs_size 3) with 512 in FSL.
  assert (SHF0 : shad f = f / 8 + SHB) by reflexivity.
  pose proof OKE as OK'. destruct OK' as [_ _ _ _ (T16 & NT8 & TN & TS & TL) (S16 & NS8 & SN & SS & SL) PTRR PTR0 (D8 & DF & DL & DS & DT) LOW' [HL HT]].
  set (W := dmp_okarm_W (mkLF usp sp' f lo)) in HK.

  assert (OWA : forall a, outside W a ->
            ~ (shad f + 18 <= a < shad f + 54) /\ outside [(PJ_LOC_LO_A, PJ_LOC_HI_A); (f + 144, f + 144 + 288)] a
            /\ outside [(f + 144, f + 144 + 288); (EL_TPLOC_A, EL_TPLOC_A + 8)] a /\ ~ (f + 144 <= a < f + 152) /\ outside [(f + 144 + 136, f + 144 + 144)] a).
  { intros a Ho. subst W. unfold dmp_okarm_W, EL_LIB_FP, LIB_FP, EL_UNW_A, EL_EHG_A, EL_TPLOC_A, TPV_A, PJ_LOC_LO_A, PJ_LOC_HI_A in *. cbn [lf_usp lf_S1 lf_F lf_lo outside app] in Ho |- *.
    clear - Ho. repeat split; try exact I; lia. }
  assert (OWL : forall a q k, In (q, k) (rt_live RT Σ) -> q <= a < q + k -> outside W a).
  { intros a q k Hin Ha. pose proof (af_live_range RT AF Σ m q k ARTg Hin) as (Y0 & Y1 & Y2). pose proof (FLV q k Hin) as Y3. pose proof (FSL q k Hin) as Y4.
    rewrite SHF0 in Y4. subst W. unfold dmp_okarm_W, EL_LIB_FP, LIB_FP, EL_UNW_A, EL_EHG_A, EL_TPLOC_A, TPV_A. cbn [lf_usp lf_S1 lf_F lf_lo outside app].
    unfold shad, SHB, SEGTOP_A, FUZZ_STACK, STACK_WIN, USTACK_TOP in *.
    replace ((f + 512) / 8 + 2147450880) with (f / 8 + 2147450880 + 64) in Y4 by (Z.div_mod_to_equations; lia).
    clear - Ha Y0 Y1 Y2 Y3 Y4 SPR LOR LLO WLO ELO. repeat split; try exact I; lia. }
  assert (OWD : forall a, (f <= a < f + 144 \/ f + 432 <= a < f + 512 \/ shad f <= a < shad f + 18 \/ shad f + 54 <= a < shad f + 64 \/ sp' <= a < usp) -> outside W a).
  { intros a Ha. subst W. unfold dmp_okarm_W, EL_LIB_FP, LIB_FP, EL_UNW_A, EL_EHG_A, EL_TPLOC_A, TPV_A. cbn [lf_usp lf_S1 lf_F lf_lo outside app].
    unfold shad, SHB, SEGTOP_A, FUZZ_STACK, STACK_WIN, USTACK_TOP in *. clear - Ha FSEG FLO FSELF SHB0 SHT SPR LOR LLO.
    repeat split; try exact I; lia. }
  assert (AIN : forall x, ainv_rng E x -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x /\ outside W x).
  { intros x Hx. split; [exact (ainv_rng_aclient RT Σ E sp' x AL OKE Hx)|].
    unfold ainv_rng in Hx. rewrite EDOC, P1N in Hx. destruct Hx as [Hx|[Hx|[Hx|[Hx|Hx]]]].
    - apply (OWL x _ _ ALT). lia.
    - apply (OWL x _ _ ALS). lia.
    - unfold zlength in Hx. cbn [length] in Hx. lia.
    - apply OWD. lia.
    - apply OWD. right; right; left. unfold shad, SHB in *. clear - Hx F64. Z.div_mod_to_equations. lia. }
  assert (INS : forall x, sp' <= x < usp -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x) by (intros x Hx; left; clear - Hx SPT; ul).
  assert (INFR : forall x, f <= x < f + 504 -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x).
  { intros x Hx. right; right; right; left. exists f, 3%nat. split; [exact INF| change (fs_size 3) with 512; lia]. }
  assert (INSH : forall x, shad f <= x < shad f + 64 -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x).
  { intros x Hx. right; right; right; right. exists f, 3%nat. split; [exact INF| change (fs_size 3) with 512; unfold shad in *; Z.div_mod_to_equations; lia]. }
  assert (INST : forall x, client_static x -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x) by (intros x Hx; right; left; exact Hx).

  set (REL := fun mk : mem => forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) sp' (bv_unsigned a) -> outside W (bv_unsigned a) -> mk a = m a).
  assert (RELAG : forall mk, REL mk -> forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x /\ outside W x) -> agree_on P m mk).
  { intros mk R P HP a Ha. destruct (HP _ Ha) as [H1 H2]. exact (R a H1 H2). }

  pose proof FT as FT'. unfold dmp_ftail in FT'.
  change ([CB 32 j112; CB 288 jos; CB 72 j432]) with ([CB 32 j112] ++ [CB 288 jos] ++ [CB 72 j432]) in FT'.
  apply Sj_stage1_kit.rw_cells_app in FT'. destruct FT' as [C112 FT']. apply Sj_stage1_kit.rw_cells_app in FT'. destruct FT' as [CO C432].
  cbn [cells_size csize Nat.add] in CO, C432. replace (f + 112 + Z.of_nat 32) with (f + 144) in CO by lia. replace (f + 112 + Z.of_nat 32 + Z.of_nat 288) with (f + 432) in C432 by lia.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (dmp_walkO1 usp sp' f ra gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s8 s11 t3 t4 t5 t6 j20 F fc m);
                   [exact FPOS| clear - FLO LOR SPT; ul| clear - SHB0; unfold SHB in *; lia| clear - SHT LOR SPT; ul| clear - LLO LOR SPR; ul| clear - SPR SPT; ul
                   | right; clear - SHT LOR SPR; ul| exact FS| exact RC| exact MIg]|].
  cbv beta. intros ms1 (m1 & -> & MU1 & WM1 & MI1 & FS1). apply evt_done. unfold lf_regs.
  assert (REL1 : REL m1) by (intros a Ha Ho; apply MU1; cbn [outside]; split; [exact (proj1 (OWA _ Ho))| exact I]).
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 sp' ARTg ltac:(clear - WLO ELO LOR SPR; ul)); [| exact WM1]. intros a Ha. apply MU1. cbn [outside]. split; [| exact I].
    intros Hin. apply Ha. apply INSH. clear - Hin. lia. }
  assert (ST1 : stk bsegs m1 lo sp') by (apply (stk_agree bsegs m m1 _ _ STg); [| exact WM1]; intros a Ha; apply MU1; cbn [outside]; cbv beta in Ha; split; [clear - Ha SHT; lia| exact I]).
  pose proof (RELAG m1 REL1) as AG1.
  assert (HULL1 : os_hullA m1 (f + 144)).
  { split; [exists jos; eapply rw_cells_agree_nw; [exact CO|]; apply (agree_of_munch _ _ _ _ MU1); intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; split; [clear - Hx FSELF; lia| exact I]|].
    exact (dmp_sh_os m1 f 0 ltac:(clear - F64; Z.div_mod_to_equations; lia) FS1). }

  assert (LIBX : forall ma mb, el_libA ma -> LOCBA mb ->
            agree_on (fun a => sj_lib_rng a \/ PJ_LOCKW_A <= a < PJ_LOCKW_A + 4 \/ EL_EHG_A <= a < EL_EHG_A + 12 \/ EL_UNW_A <= a < EL_UNW_A + 8 \/ EL_TPLOC_A <= a < EL_TPLOC_A + 8) ma mb ->
            el_libA mb).
  { intros ma mb [(S & L & LW) (Eh & U & T)] LB AG. split; [split; [| split]| split; [| split]].
    - eapply sj_lib_agree; [exact S|]. intros a Ha. apply AG. left; exact Ha.
    - right. exact LB.
    - eapply lockwA_agree; [exact LW|]. intros a Ha. apply AG. right; left; exact Ha.
    - eapply rw_cells_agree_nw; [exact Eh|]. intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. right; right; left. lia.
    - destruct U as [uw U]. exists uw. eapply rw_cells_agree_nw; [exact U|]. intros a Ha. apply AG. rewrite uw_cellsA_size in Ha. right; right; right; left. lia.
    - eapply rw_cells_agree_nw; [exact T|]. intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. do 4 right. lia. }
  assert (LIBRNG : forall a, (sj_lib_rng a \/ PJ_LOCKW_A <= a < PJ_LOCKW_A + 4 \/ EL_EHG_A <= a < EL_EHG_A + 12 \/ EL_UNW_A <= a < EL_UNW_A + 8 \/ EL_TPLOC_A <= a < EL_TPLOC_A + 8) ->
            client_static a /\ outside [(PJ_LOC_LO_A, PJ_LOC_HI_A); (f + 144, f + 144 + 288)] a /\ ~ (shad f + 18 <= a < shad f + 54)
            /\ ~ (f + 144 <= a < f + 152) /\ outside [(f + 144 + 136, f + 144 + 144)] a).
  { intros a Ha. unfold sj_lib_rng, PJ_LOCKW_A, EL_EHG_A, EL_UNW_A, EL_TPLOC_A, TPV_A, PJ_LOC_LO_A, PJ_LOC_HI_A in *. cbn [outside].
    rewrite SHF0. unfold SHB. split; [apply client_static_intro; clear - Ha; lia|]. clear - Ha FSEG. unfold SEGTOP_A in FSEG. repeat split; try exact I; try lia.
    all: Z.div_mod_to_equations; lia. }
  assert (LIB1 : el_libA m1).
  { apply (el_libA_agree m m1 LIB). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. pose proof (el_lib_rng_static x Hx) as [_ R]. cbn [outside].
    rewrite SHF0. unfold SHB. clear - R FPOS. split; [| exact I]. Z.div_mod_to_equations; lia. }
  assert (OWST : forall a, (LIBC_NL <= a < LIBC_NL + 1 \/ 0x6cb3a8 <= a < 0x6cb3a8 + 8) -> outside W a).
  { intros a Ha. subst W. unfold dmp_okarm_W, EL_LIB_FP, LIB_FP, EL_UNW_A, EL_EHG_A, EL_TPLOC_A, TPV_A, LIBC_NL in *. cbn [lf_usp lf_S1 lf_F lf_lo outside app].
    rewrite SHF0. unfold SHB, SEGTOP_A, FUZZ_STACK, STACK_WIN, USTACK_TOP in *. clear - Ha FSEG FLO LLO LOR SPR. repeat split; try exact I; try lia. all: Z.div_mod_to_equations; lia. }
  assert (NLX : forall mk, REL mk -> libc_nl mk).
  { intros mk R. apply (libc_nl_agree m mk NL). apply (RELAG mk R). intros x Hx. split; [exact (INST _ (libc_nl_static _ Hx))| apply OWST; left; exact Hx]. }
  assert (IOSX : forall (Σx : rts RT) mk, REL mk -> ART RT Σx mk -> io_ssp mk).
  { intros Σx mk R A'. destruct IOS as (g & G1 & G2). exists g. split; [exact (proj1 (af_got_lib RT AF Σx mk A'))|]. apply (ro_cells_agree bsegs m mk _ _ G2). apply (RELAG mk R).
    intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [apply INST; apply client_static_intro; clear - Hx; lia| apply OWST; right; exact Hx]. }
  pose proof LIB1 as [(_ & LOC1 & LW1) _].

  eapply (CTOR Σ K (f + 144) sp' lo f 3%nat (wz DMP_CTORRET_A) gp t0 t1 t2 (wz usp) (wz sp') a1 a2 a3 a4 a5 a6 a7
            (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 144)) (wz (f + 56)) (wz 1) s8 (wz f) (wz DMP_MAGIC1) s11 t3 t4 t5 t6 F fc m1 FDO MST INF);
    [clear; lia| change (fs_size 3) with 512; clear; lia| clear - F64; Z.div_mod_to_equations; lia| exact HULL1| exact LOC1| exact (NLX m1 REL1)| exact LW1| exact (IOSX Σ m1 REL1 ART1)
    | exact ART1| exact MI1| exact ST1| rewrite <- ELO; exact WLO| clear - NEED; ul| clear - SPR SPT; ul| clear - SPA'; Z.div_mod_to_equations; lia|].
  intros u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 m2 ART2 MI2 ST2 FRESH2 HULL2 LOCB2 PRES2.
  assert (REL2 : REL m2).
  { intros a Ha Ho. rewrite (PRES2 a Ha (proj1 (proj2 (OWA _ Ho)))). exact (REL1 a Ha Ho). }
  pose proof (RELAG m2 REL2) as AG2.
  assert (LIB2 : el_libA m2).
  { apply (LIBX m1 m2 LIB1 LOCB2). intros a Ha. destruct (LIBRNG _ Ha) as (CSa & Oa & _). exact (PRES2 a (INST _ CSa) Oa). }
  assert (AI2 : AINV_A E m2) by (apply (AINV_A_agree E m m2 AI); apply AG2; exact AIN).

  assert (SHOUT : forall a, shad f <= a < shad f + 64 ->
            outside [(PJ_LOC_LO_A, PJ_LOC_HI_A); (f + 144, f + 144 + 288)] a /\ outside [(f + 144, f + 144 + 288); (EL_TPLOC_A, EL_TPLOC_A + 8)] a
            /\ ~ (f + 144 <= a < f + 152) /\ outside [(f + 144 + 136, f + 144 + 144)] a).
  { intros a Ha. unfold EL_LIB_FP, LIB_FP, EL_UNW_A, EL_EHG_A, EL_TPLOC_A, TPV_A, PJ_LOC_LO_A, PJ_LOC_HI_A. cbn [outside app]. rewrite SHF0 in Ha. unfold SHB in Ha.
    clear - Ha FSELF FSEG SHF0. unfold SEGTOP_A in FSEG. rewrite SHF0 in FSELF. unfold SHB in FSELF. repeat split; try exact I; Z.div_mod_to_equations; lia. }
  assert (FS2 : rw_cells bsegs m2 (shad f) (map C1 dmp_sh_ok)).
  { eapply rw_cells_agree_nw; [exact FS1|]. intros a Ha. rewrite cells_size_map_C1 in Ha; unfold dmp_sh_ok, dmp_sh_pro, dmp_sh_x in Ha; rewrite dmp_sh_length in Ha. apply PRES2; [apply INSH; lia| exact (proj1 (SHOUT _ Ha))]. }

  rewrite (ret_pc_even DMP_CTORRET_A) by (unfold DMP_CTORRET_A; lia). apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (dmp_walkO2 usp sp' f gp u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s8 s11 u3 u4 u5 u6 F2 fc m2 FPOS ltac:(clear - FLO LOR SPT; ul) MI2)|].
  cbv beta. intros ms2 <-. apply evt_done. unfold lf_regs. rewrite <- EDOC.

  assert (TPL2 : el_tploc m2) by (destruct LIB2 as [_ (_ & _ & T)]; exact T).
  eapply (PJ Σ K E (f + 144) sp' f 3%nat (wz DMP_PJRET_A) gp u0 u1 u2 (wz usp) (wz sp') b3 b4 b5 b6 b7
            (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 144)) (wz (ae_DOC E)) (wz 1) (wz (f + 272)) (wz f) (wz DMP_MAGIC1) s11 u3 u4 u5 u6 F2 fc m2
            FDO MST OKE AL AI2 INF);
    [clear; lia| change (fs_size 3) with 512; clear; lia| clear - F64; Z.div_mod_to_equations; lia| rewrite EDOC; left; clear; lia
    | exact FRESH2| exact (dmp_sh_os m2 f 0 ltac:(clear - F64; Z.div_mod_to_equations; lia) FS2)| exact LOCB2| exact TPL2| exact (IOSX Σ m2 REL2 ART2)| exact FRM
    | exact ART2| exact MI2| rewrite ELO; exact ST2| rewrite ELO; clear - NEED; ul| clear - SPR SPT; ul| exact SPA'
    | rewrite FRS; cbn [length]; unfold FRAMES_TOT; clear; lia| clear - CRB; unfold dmp_okarm_cost in CRB; lia|].
  intros Σ3 v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F3 fc3 m3 ART3 MI3 ST3 OX3 HULL3 LOCB3 TPL3 FRM3 AI3 LV3 FRS3 SP3 CR3 PRES3.
  rewrite ELO in ST3. rewrite (ret_pc_even DMP_PJRET_A) by (unfold DMP_PJRET_A; lia).

  assert (LIBX' : forall ma mb, el_libA ma -> LOCBA mb -> el_tploc mb ->
            agree_on (fun a => sj_lib_rng a \/ PJ_LOCKW_A <= a < PJ_LOCKW_A + 4 \/ EL_EHG_A <= a < EL_EHG_A + 12 \/ EL_UNW_A <= a < EL_UNW_A + 8) ma mb -> el_libA mb).
  { intros ma mb [(S & L & LW) (Eh & U & T)] LB TP AG. split; [split; [| split]| split; [| split]].
    - eapply sj_lib_agree; [exact S|]. intros a Ha. apply AG. left; exact Ha.
    - right. exact LB.
    - eapply lockwA_agree; [exact LW|]. intros a Ha. apply AG. right; left; exact Ha.
    - eapply rw_cells_agree_nw; [exact Eh|]. intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. right; right; left. lia.
    - destruct U as [uw U]. exists uw. eapply rw_cells_agree_nw; [exact U|]. intros a Ha. apply AG. rewrite uw_cellsA_size in Ha. right; right; right. lia.
    - exact TP. }
  assert (LIBRNG3 : forall a, (sj_lib_rng a \/ PJ_LOCKW_A <= a < PJ_LOCKW_A + 4 \/ EL_EHG_A <= a < EL_EHG_A + 12 \/ EL_UNW_A <= a < EL_UNW_A + 8) ->
            client_static a /\ outside [(f + 144, f + 144 + 288); (EL_TPLOC_A, EL_TPLOC_A + 8)] a).
  { intros a Ha. unfold sj_lib_rng, PJ_LOCKW_A, EL_EHG_A, EL_UNW_A, EL_TPLOC_A, TPV_A in *. cbn [outside].
    split; [apply client_static_intro; clear - Ha; lia|]. clear - Ha FSEG. unfold SEGTOP_A in FSEG. repeat split; try exact I; lia. }
  assert (LIB3 : el_libA m3).
  { apply (LIBX' m2 m3 LIB2 LOCB3 TPL3). intros a Ha. destruct (LIBRNG3 _ Ha) as [CSa Oa]. exact (PRES3 a (INST _ CSa) Oa). }
  rewrite EDOC.
  assert (REL3 : REL m3).
  { intros a Ha Ho. rewrite (PRES3 a Ha (proj1 (proj2 (proj2 (OWA _ Ho))))). exact (REL2 a Ha Ho). }
  assert (FS3 : rw_cells bsegs m3 (shad f) (map C1 dmp_sh_ok)).
  { eapply rw_cells_agree_nw; [exact FS2|]. intros a Ha. rewrite cells_size_map_C1 in Ha; unfold dmp_sh_ok, dmp_sh_pro, dmp_sh_x in Ha; rewrite dmp_sh_length in Ha. apply PRES3; [apply INSH; lia| exact (proj1 (proj2 (SHOUT _ Ha)))]. }
  pose proof LIB3 as [(_ & LOC3 & LW3) _].
  pose proof (ROA Σ3 m3 ART3) as (_ & GVT & _ & _).
  destruct OX3 as (fill & (pb & pp & ep & dum & j148 & j284 & OSC & _) & _). rewrite <- os_cellsA_X in OSC.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (dmp_walkR1 usp sp' f gp v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 s11 v3 v4 v5 v6 pb (wz pp) (wz ep) fill dum j148 j284 F3 fc3 m3 FPOS ltac:(clear - FLO LOR SPT; ul) OSC GVT MI3)|].
  cbv beta. intros ms4 (m4 & a1x & -> & MU4 & WM4 & MI4 & OSC4). apply evt_done. unfold lf_regs.
  unfold os_cellsA, sb_cellsA, ios_cellsA in OSC4. cbn [app tl] in OSC4.
  assert (REL4 : REL m4).
  { intros a Ha Ho. rewrite (MU4 a); [exact (REL3 a Ha Ho)|]. cbn [outside]. split; [exact (proj1 (proj2 (proj2 (proj2 (OWA _ Ho)))))| exact I]. }
  assert (FPC4 : fp_client RT Σ3 lo [(f + 144, f + 152)]).
  { constructor; [| constructor]. right; right. exists f, 3%nat. cbn [fst snd]. rewrite FRS3, FRS. split; [left; reflexivity| change (fs_size 3) with 512; clear; lia]. }
  assert (ART4 : ART RT Σ3 m4) by (exact (art_fp_client RT AF Σ3 m3 m4 lo _ ART3 ltac:(rewrite SP3, <- ELO; exact WLO) FPC4 MU4 WM4)).
  assert (ST4 : stk bsegs m4 lo sp') by (apply (stk_agree bsegs m3 m4 _ _ ST3); [| exact WM4]; intros a Ha; apply MU4; cbn [outside]; cbv beta in Ha; split; [clear - Ha FLO; lia| exact I]).
  assert (FS4 : rw_cells bsegs m4 (shad f) (map C1 dmp_sh_ok)).
  { eapply rw_cells_agree_nw; [exact FS3|]. intros a Ha. rewrite cells_size_map_C1 in Ha; unfold dmp_sh_ok, dmp_sh_pro, dmp_sh_x in Ha; rewrite dmp_sh_length in Ha. apply MU4. cbn [outside]. split; [exact (proj1 (proj2 (proj2 (SHOUT _ Ha))))| exact I]. }
  assert (LOCB4 : LOCBA m4).
  { apply (LOCBA_agree m3 m4 LOCB3). apply (agree_of_munch _ _ _ _ MU4). intros x Hx. cbv beta in Hx. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx. cbn [outside].
    split; [clear - Hx FSEG; unfold SEGTOP_A in FSEG; lia| exact I]. }
  assert (IMP4 : rw_cells bsegs m4 (f + 144 + 8) [C8 (wz PJ_LOC_IMP_A)]).
  { lazymatch type of OSC4 with rw_cells _ _ _ (?d0 :: ?d1 :: ?rest) =>
      pose proof OSC4 as X4; change (d0 :: d1 :: rest) with ([d0] ++ [d1] ++ rest) in X4 end.
    apply Sj_stage1_kit.rw_cells_app in X4. destruct X4 as [_ X4]. apply Sj_stage1_kit.rw_cells_app in X4. destruct X4 as [X4 _].
    cbn [cells_size csize Nat.add] in X4. replace (f + 144 + Z.of_nat 8) with (f + 144 + 8) in X4 by lia. exact X4. }

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (LOCD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (f + 144 + 8)); [exact IMP4| exact LOCB4| exact MI4]|].
  cbv beta. intros ms5 (y0 & y1 & y2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & ->). apply evt_done.
  rewrite (ret_pc_even DMP_LOCRET_A) by (unfold DMP_LOCRET_A; lia).

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (dmp_walkR2 usp sp' f (wz DMP_LOCRET_A) gp y0 y1 y2 e0 e1 e2 e3 e4 e5 e6 e7 s11 y3 y4 y5 y6 F3 fc3 m4 FPOS ltac:(clear - FLO LOR SPT; ul) MI4)|].
  cbv beta. intros ms6 <-. apply evt_done. unfold lf_regs.

  lazymatch type of OSC4 with rw_cells _ _ _ (?d0 :: ?d1 :: ?d2 :: ?d3 :: ?d4 :: ?d5 :: ?d6 :: ?d7 :: ?d8 :: ?d9 :: ?rest) =>
    pose proof OSC4 as IOS4; change (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: d6 :: d7 :: d8 :: d9 :: rest) with ([d0; d1; d2; d3; d4; d5; d6; d7; d8; d9] ++ rest) in IOS4 end.
  apply Sj_stage1_kit.rw_cells_app in IOS4. destruct IOS4 as [_ IOS4]. cbn [cells_size csize Nat.add] in IOS4. replace (f + 144 + Z.of_nat 136) with (f + 144 + 136) in IOS4 by lia.
  destruct (rw_cells_forget bsegs m4 _ _ OSC4) as [bo HULL4]. cbn [cells_size csize Nat.add] in HULL4.

  eapply (IOSD Σ3 K (f + 144) sp' lo f 3%nat (wz DMP_IOSRET_A) gp _ _ _ (wz usp) (wz sp') _ _ _ _ _ _ _
            (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 144)) (wz (f + 56)) (wz 1) (wz (f + 272)) (wz f) (wz DMP_MAGIC1) s11 _ _ _ _ F3 fc3 m4 FDO MST);
    [rewrite FRS3; exact INF| clear; lia| change (fs_size 3) with 512; clear; lia| clear - F64; Z.div_mod_to_equations; lia
    | exists PJ_IOS_VPTR_A, fill, j148, j284; exact IOS4
    | split; [exists bo; exact HULL4| exact (dmp_sh_os m4 f 0 ltac:(clear - F64; Z.div_mod_to_equations; lia) FS4)]
    | exact LOCB4
    | unfold unwind_ok; rewrite !unsigned_lit by (clear - SPR SPT LLO LOR; ul); right; right; clear - SPR; lia
    | exact ART4| exact MI4| exact ST4| rewrite SP3, <- ELO; exact WLO| clear - NEED; ul| clear - SPR SPT; ul| clear - SPA'; Z.div_mod_to_equations; lia|].
  intros w0 w1 w2 d0 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 F5 m5 ART5 MI5 ST5 [[jos5 HULL5] SHO5] PRES5. rewrite LV3, FRS3 in PRES5.
  assert (REL5 : REL m5).
  { intros a Ha Ho. rewrite (PRES5 a); [exact (REL4 a Ha Ho)| exact Ha| exact (proj2 (proj2 (proj2 (proj2 (OWA _ Ho)))))]. }
  assert (FS5 : rw_cells bsegs m5 (shad f) (map C1 dmp_sh_ok)).
  { eapply rw_cells_agree_nw; [exact FS4|]. intros a Ha. rewrite cells_size_map_C1 in Ha; unfold dmp_sh_ok, dmp_sh_pro, dmp_sh_x in Ha; rewrite dmp_sh_length in Ha. apply PRES5; [apply INSH; lia| exact (proj2 (proj2 (proj2 (SHOUT _ Ha))))]. }

  rewrite (ret_pc_even DMP_IOSRET_A) by (unfold DMP_IOSRET_A; lia). apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (dmp_walkR3 usp sp' f lo (wz DMP_IOSRET_A) gp w0 w1 w2 d0 d1 d2 d3 d4 d5 d6 d7 s11 w3 w4 w5 w6 F5 fc3 m5
                             FPOS FLO ltac:(clear - SHT; lia) ltac:(clear - SHB0; unfold SHB in *; lia) FSELF ltac:(clear - LOR SPT; ul) FS5 MI5)|].
  cbv beta. intros ms7 (m6 & -> & MU6 & WM6 & MI6 & FS6). apply evt_done. unfold lf_regs.
  assert (REL6 : REL m6).
  { intros a Ha Ho. rewrite (MU6 a); [exact (REL5 a Ha Ho)|]. cbn [outside]. split; [exact (proj1 (OWA _ Ho))| exact I]. }
  pose proof (RELAG m6 REL6) as AG6.
  assert (ART6 : ART RT Σ3 m6).
  { apply (art_client_write RT AF Σ3 m5 m6 sp' ART5 ltac:(rewrite SP3; clear - WLO ELO LOR SPR; ul)); [| exact WM6]. intros a Ha. apply MU6. cbn [outside]. split; [| exact I].
    intros Hin. apply Ha. rewrite LV3, FRS3. apply INSH. clear - Hin. lia. }
  assert (ST6 : stk bsegs m6 lo sp') by (apply (stk_agree bsegs m5 m6 _ _ ST5); [| exact WM6]; intros a Ha; apply MU6; cbn [outside]; cbv beta in Ha; split; [clear - Ha SHT; lia| exact I]).
  apply (HK Σ3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F5 fc3 m6 j112 jos5 j432 FRM3 ART6 MI6 ST6 LV3 FRS3 SP3).
  - clear - CR3. unfold dmp_okarm_cost. lia.
  - intros a Ha Ho. exact (REL6 a Ha Ho).
  - apply (AINV_A_agree E m3 m6 AI3). intros a Ha. destruct (AIN _ Ha) as [CA OA].
    rewrite (MU6 a); [| cbn [outside]; split; [exact (proj1 (OWA _ OA))| exact I]].
    rewrite (PRES5 a); [| exact CA| exact (proj2 (proj2 (proj2 (proj2 (OWA _ OA)))))].
    apply MU4. cbn [outside]. split; [exact (proj1 (proj2 (proj2 (proj2 (OWA _ OA)))))| exact I].
  - apply (el_libA_agree m3 m6 LIB3). intros a Ha. pose proof (el_lib_rng_static _ Ha) as [CSa R].
    rewrite (MU6 a); [| cbn [outside]; rewrite SHF0; unfold SHB; split; [clear - R FPOS; Z.div_mod_to_equations; lia| exact I]].
    rewrite (PRES5 a); [| exact (INST _ CSa)| cbn [outside]; split; [clear - R FSEG; unfold SEGTOP_A in FSEG; lia| exact I]].
    apply MU4. cbn [outside]. split; [clear - R FSEG; unfold SEGTOP_A in FSEG; lia| exact I].
  - apply (LOCBA_agree m4 m6 LOCB4). intros a Ha. cbv beta in Ha. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Ha.
    rewrite (MU6 a); [| cbn [outside]; rewrite SHF0; unfold SHB; split; [clear - Ha FPOS; Z.div_mod_to_equations; lia| exact I]].
    apply PRES5; [apply INST; apply client_static_intro; clear - Ha; lia| cbn [outside]; split; [clear - Ha FSEG; unfold SEGTOP_A in FSEG; lia| exact I]].
  - unfold dmp_ftail. change ([CB 32 j112; CB 288 jos5; CB 72 j432]) with ([CB 32 j112] ++ [CB 288 jos5] ++ [CB 72 j432]).
    apply Sj_stage1_kit.rw_cells_app. split.
    { eapply rw_cells_agree_nw; [exact C112|]. apply AG6. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [apply INFR; lia| apply OWD; lia]. }
    cbn [cells_size csize Nat.add]. replace (f + 112 + Z.of_nat 32) with (f + 144) by lia. apply Sj_stage1_kit.rw_cells_app. split.
    { eapply rw_cells_agree_nw; [exact HULL5|]. apply (agree_of_munch _ _ _ _ MU6). intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbn [outside]. split; [clear - Hx FSELF; lia| exact I]. }
    cbn [cells_size csize Nat.add]. replace (f + 144 + Z.of_nat 288) with (f + 432) by lia.
    eapply rw_cells_agree_nw; [exact C432|]. apply AG6. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [apply INFR; lia| apply OWD; lia].
  - exact FS6.
Qed.
End Okarm.
