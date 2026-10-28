(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep ZBridge.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Startup_glue Pj_loc_kit Pj_os_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_rlkit D_libiface Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_new Sj_num_akit Sj_num_amem Atp_fzwA Pj_rtkA Pj_defsA Pj_cpsA Pj_os_defsA Pj_mciA Pj_loc_akitA Pj_loc_getA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import StoreFast.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Section Ctor.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis ROA : forall Σ m, ART RT Σ m -> pj_os_roA m.
Hypothesis LOCGET : loc_get_cpsA RT PMc.

Local Ltac ul := unfold PJ_OS_CTOR_STACK_A, PJ_LOC_STACK_A, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Local Ltac chk SHZ a := lstep; rewrite shr3_div; lstep; shz_pose SHZ a; lstep; shz_norm; lstep; if_false.

Theorem ctor_okA : ctor_cpsA RT PMc OSFRESHA.
Proof using AF RC FDO MST ROA LOCGET.
  unfold ctor_cpsA. intros until m. intros FDO' MST' INF FLO FHI AL16 HULL LOC NL LK IOS ART0 MI ST LOW LOR SPT SP16 HK.
  pose proof (af_frames_range RT AF Σ m fO kO ART0 INF) as (F0 & FTOP & _ & FLIVE).
  pose proof (af_frames_align RT AF Σ m fO kO ART0 INF) as (_ & FSEG).
  pose proof (proj2 (af_fshadow_apart RT AF Σ m fO kO ART0 INF) fO kO INF) as FSELF.
  pose proof (fframe_ranges RT AF Σ m fO kO ART0 INF) as (_ & _ & _ & _ & SHT).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _). pose proof (ROA Σ m ART0) as (_ & GOTV & _).
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, PJ_GOT_VT_A, PJ_SB_BVT_A, PJ_IOS_BVT_A, SHB in *.
  unfold PJ_OS_CTOR_STACK_A, PJ_LOC_STACK_A in *. unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *. remember (fs_size kO) as FSZ eqn:EFSZ.
  assert (Q0 : 0 <= q - 160) by (destruct ST; lia).
  assert (UQ : bv_unsigned (wz q) = q) by (apply unsigned_lit; lia).
  assert (UQ112 : bv_unsigned (wz (q + -112)) = q + -112) by (apply unsigned_lit; lia).
  assert (EO : bv_unsigned (wz OS) = OS) by (apply unsigned_lit; lia).
  destruct HULL as [(bo & OSR) SHBY].
  apply (rw_cells_split_CB bsegs _ _ [] 288 bo [] [8; 8; 48; 64; 8; 8; 4; 4; 8; 8; 4; 4; 8; 8; 80; 8; 4; 4]%nat) in OSR; [| reflexivity].
  cbn [mk_CB_cells app] in OSR. forget_junk OSR.
  change (id (bytes_at bsegs m (shad OS) (repeat z8 36))) in SHBY. change (id (lockwA m)) in LK. change (id (libc_nl m)) in NL.
  pose proof (munch_refl [(q - 112, q); (OS, OS + 288)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.

  assert (CL : forall sp' x, (q + -112 <= x < q /\ sp' <= q + -112) \/ (fO <= x < fO + FSZ - 8) \/ (fO / 8 + 2147450880 <= x < (fO + FSZ) / 8 + 2147450880)
            \/ (PJ_LOC_LO_A <= x < PJ_LOC_HI_A) \/ (PJ_LOCKW_A <= x < PJ_LOCKW_A + 4) \/ (LIBC_NL <= x < LIBC_NL + 1) \/ (0x6cb3a8 <= x < 0x6cb3a8 + 8) ->
            aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x).
  { intros sp' x [[H1 H2]|[H|[H|[H|[H|[H|H]]]]]]; [left; ul| right; right; right; left| do 4 right| right; left| right; left| right; left| right; left];
      [exists fO, kO; rewrite <- EFSZ; split; [exact INF| exact H]| exists fO, kO; rewrite <- EFSZ; split; [exact INF| unfold shad, SHB; exact H]
      | apply client_static_intro; unfold PJ_LOC_LO_A, PJ_LOC_HI_A in H; lia| apply client_static_intro; unfold PJ_LOCKW_A in H; lia
      | apply client_static_intro; unfold LIBC_NL in H; lia| apply client_static_intro; lia]. }

  assert (SHZ0 : forall mx, agree_on (fun x => OS / 8 + 2147450880 <= x < OS / 8 + 2147450880 + 36) m mx -> shz mx OS 288).
  { intros mx AG. change 288 with (8 * Z.of_nat 36). apply (shz_of_zero_run mx OS 36); [Z.div_mod_to_equations; lia| lia|].
    unfold id in SHBY. eapply bytes_at_agree; [exact SHBY|]. intros a Ha. rewrite repeat_length in Ha. apply AG. unfold shad, SHB in Ha. lia. }
  assert (SHZ : forall m', munch [(q - 112, q); (OS, OS + 288)] m m' -> wmono bsegs m m' -> shz m' OS 288).
  { intros m' MU' _. apply SHZ0. apply (agree_of_munch _ _ _ _ MU'). intros x Hx. cbn [outside]. unfold shad, SHB in *. clear - Hx FLO FHI FSELF F0 SHT LOW LOR.
    split; [| split; [| exact I]]; Z.div_mod_to_equations; lia. }
  apply (aevt_evt RT AF PMc MST).
  carve_frame 112%nat ST.
  do 14 lstep.
  do 3 lstep.
  do 2 lstep.
  chk SHZ (OS + 184).
  lstep.
  lstep.
  chk SHZ (OS + 136).
  do 2 lstep.
  lstep.    rewrite shr3_div.
  do 2 lstep.
  lstep.    shz_pose SHZ OS. lstep. shz_norm. lstep. if_false.
  do 2 lstep.
  do 2 lstep.
  do 2 lstep.
  lstep.
  apply evt_done.

  assert (MI3 : mem_inv bsegs m3) by assumption.
  assert (AG03 : forall P : Z -> Prop, (forall x, P x -> ~ (q + -112 <= x < q) /\ ~ (OS <= x < OS + 288)) -> agree_on P m m3).
  { intros P HP a Ha. apply MU. cbn [outside]. destruct (HP _ Ha) as [H1 H2]. split; [exact H1| split; [exact H2| exact I]]. }
  assert (ART3 : ART RT Σ m3).
  { apply (art_client_write RT AF Σ m m3 (q + -112) ART0 ltac:(ul)); [| exact WM]. intros a Ha. apply MU. cbn [outside].
    split; [intros Hin; apply Ha; apply (CL (q + -112)); left; lia|]. split; [| exact I]. intros Hin. apply Ha. apply (CL (q + -112)). right; left. lia. }
  assert (PRES3 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> outside [(PJ_LOC_LO_A, PJ_LOC_HI_A); (OS, OS + 288)] (bv_unsigned a) -> m3 a = m a).
  { intros a Ha Ho. apply MU. pose proof (aclient_split_c RT AF Σ m q (bv_unsigned a) ART0 Ha) as SPL. unfold STACK_WIN in SPL. cbn [outside] in Ho |- *.
    clear - Ho SPL LOW LOR. repeat split; try exact I; lia. }
  assert (STAT3 : agree_on (fun x => PJ_LOC_LO_A <= x < PJ_LOC_HI_A \/ PJ_LOCKW_A <= x < PJ_LOCKW_A + 4 \/ LIBC_NL <= x < LIBC_NL + 1 \/ 0x6cb3a8 <= x < 0x6cb3a8 + 8 \/ 0x16ef68 <= x < 0x16ef68 + 8) m m3).
  { apply AG03. intros x Hx. unfold PJ_LOC_LO_A, PJ_LOC_HI_A, PJ_LOCKW_A, LIBC_NL in Hx. clear - Hx FSEG FLO LOW LOR SP0R. lia. }
  assert (LOC3 : pj_locA m3) by (apply (pj_locA_agree m m3 LOC); intros a Ha; apply STAT3; left; exact Ha).
  assert (NL3 : libc_nl m3) by (unfold id in NL; apply (libc_nl_agree m m3 NL); intros a Ha; apply STAT3; right; right; left; exact Ha).
  assert (LK3 : lockwA m3) by (unfold id in LK; apply (lockwA_agree m m3 LK); intros a Ha; apply STAT3; right; left; exact Ha).
  assert (IOS3 : io_ssp m3).
  { destruct IOS as (g & I1 & I2). exists g. split; [apply (ro_cells_agree bsegs m m3 _ _ I1)| apply (ro_cells_agree bsegs m m3 _ _ I2)]; intros a Ha; apply STAT3;
      cbn [cells_size csize Nat.add] in Ha; [do 4 right| do 3 right; left]; lia. }
  clear NL LK IOS LOC STAT3.
  takeZ OSR 1%nat (OS + 8)%Z P0. takeZ OSR 1%nat (OS + 16)%Z LOCC.
  eapply (LOCGET Σ K (OS + 8) (q + -112) lo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 _ FDO MST LOC3 NL3 LK3 IOS3 LOCC
            ltac:(clear - AL16; Z.div_mod_to_equations; lia) ltac:(intros i Hi; apply (CL (q + -112)); right; left; lia) ltac:(right; unfold PJ_LOC_LO_A in *; lia)
            ART3 MI3 ST LOW ltac:(ul) ltac:(ul) ltac:(clear - SP16; Z.div_mod_to_equations; lia)).
  intros u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F4 m4 ART4 MI4 ST4 LOCB4 IMP4 PRES4. rewrite (ret_pc_even 0xaec68) by lia.
  assert (PRES4' : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> outside [(PJ_LOC_LO_A, PJ_LOC_HI_A); (OS, OS + 288)] (bv_unsigned a) -> m4 a = m a).
  { intros a Ha Ho. rewrite <- (PRES3 a Ha Ho). apply PRES4; [apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia]|]. cbn [outside] in Ho |- *. lia. }
  assert (AG34 : forall P : Z -> Prop, (forall x, P x -> ((q + -112 <= x < q) \/ (fO <= x < fO + FSZ - 8) \/ (fO / 8 + 2147450880 <= x < (fO + FSZ) / 8 + 2147450880))
                                                     /\ ~ (PJ_LOC_LO_A <= x < PJ_LOC_HI_A) /\ ~ (OS + 8 <= x < OS + 8 + 8)) -> agree_on P m3 m4).
  { intros P HP a Ha. destruct (HP _ Ha) as (H1 & H2 & H3). apply PRES4; [| cbn [outside]; split; [exact H2| split; [exact H3| exact I]]].
    apply (CL (q + -112)). destruct H1 as [H|[H|H]]; [left; split; [exact H| lia]| right; left; exact H| right; right; left; exact H]. }
  lazymatch type of OSR with rw_cells _ _ _ ?cs0 => assert (OSR4 : rw_cells bsegs m4 (OS + 16) cs0)
      by (eapply rw_cells_agree_nw; [exact OSR|]; apply AG34; intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold PJ_LOC_LO_A, PJ_LOC_HI_A; clear - Hx FLO FHI FSEG; split; [right; left; lia| lia]) end.
  lazymatch type of P0 with rw_cells _ _ _ ?cs0 => assert (VP4 : rw_cells bsegs m4 OS cs0)
      by (eapply rw_cells_agree_nw; [exact P0|]; apply AG34; intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold PJ_LOC_LO_A, PJ_LOC_HI_A; clear - Hx FLO FHI FSEG; split; [right; left; lia| lia]) end.
  lazymatch type of FR with rw_cells _ _ _ ?cs0 => assert (FR4 : rw_cells bsegs m4 (q + -112) cs0)
      by (eapply rw_cells_agree_nw; [exact FR|]; apply AG34; intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold PJ_LOC_LO_A, PJ_LOC_HI_A; clear - Hx FLO FHI FSEG FTOP LOW LOR; split; [left; lia| lia]) end.
  assert (SHB4 : bytes_at bsegs m4 (shad OS) (repeat z8 36)).
  { unfold id in SHBY. eapply bytes_at_agree; [exact SHBY|]. intros a Ha. rewrite repeat_length in Ha. apply PRES4'; unfold shad, SHB in *.
    - apply (CL q). right; right; left. clear - Ha FLO FHI. Z.div_mod_to_equations. lia.
    - cbn [outside]. unfold PJ_LOC_LO_A, PJ_LOC_HI_A. clear - Ha FLO FHI FSELF F0 FSEG. repeat split; try exact I; Z.div_mod_to_equations; lia. }
  clear AG03 AG34 MU WM ART3 MI3 ST PRES3 PRES4 OSR P0 LOCC FR SHBY LOC3 NL3 LK3 IOS3 ART0 MI.
  pose proof VP4 as OSR. glueZ OSR IMP4. glueZ OSR OSR4. clear VP4.

  apply (aevt_evt RT AF PMc MST).
  do 3 lstep.
  lstep.
  apply evt_done.
  assert (CD4 : checked_dst RT Σ m4 (Z_to_bv 64 (q + -112)) (OS + 16) 48).
  { unfold checked_dst. rewrite UQ112. split; [| split].
    - intros _. split; [| right; left; exists fO, kO; rewrite <- EFSZ; split; [exact INF| lia]].
      apply (acc_sub bsegs m4 OS 288); [| lia| lia]. change 288 with (8 * Z.of_nat 36). apply (acc_zero_run bsegs m4 OS 36); [clear - AL16; Z.div_mod_to_equations; lia| lia| exact SHB4].
    - intros i Hi. apply (CL (q + -112)). right; left. lia.
    - apply (wr_at_sub m4 OS 288); [exact (rw_cells_wr_at bsegs m4 _ _ 288 OSR ltac:(cbn; lia))| lia| lia| lia]. }
  assert (COK4 : call_ok RT Σ m4 (Z_to_bv 64 (q + -112)) lo).
  { unfold call_ok. rewrite UQ112. split; [exact ST4|]. split; [exact LOW|]. split; [ul|]. split; [ul| clear - SP16; Z.div_mod_to_equations; lia]. }
  eapply (aevt_memsetP RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F4 fc m4 (OS + 16) 48 z8 lo eq_refl eq_refl eq_refl
            ltac:(lia) ltac:(lia) CD4 ART4 MI4 COK4).
  intros v0 v1 v2 e1 e2 e3 e4 e5 e6 e7 v3 v4 v5 v6 F5 m5 (ART5 & MI5 & WM5 & ST5) PRES5 BY5. rewrite UQ112 in ST5, PRES5.
  rewrite (ret_pc_even 0xaec78) by lia. change (Z.to_nat 48) with 48%nat in BY5.
  assert (AG45 : forall P : Z -> Prop, (forall x, P x -> ((q + -112 <= x < q) \/ (fO <= x < fO + FSZ - 8) \/ (fO / 8 + 2147450880 <= x < (fO + FSZ) / 8 + 2147450880) \/ (PJ_LOC_LO_A <= x < PJ_LOC_HI_A))
                                                     /\ ~ (OS + 16 <= x < OS + 16 + 48)) -> agree_on P m4 m5).
  { intros P HP a Ha. destruct (HP _ Ha) as (H1 & H2). apply PRES5; [| exact H2].
    apply (CL (q + -112)). destruct H1 as [H|[H|[H|H]]]; [left; split; [exact H| lia]| right; left; exact H| right; right; left; exact H| right; right; right; left; exact H]. }
  lazymatch type of OSR with rw_cells _ _ _ (?c0 :: ?c1 :: CB 48 ?jj :: ?rest) =>
    assert (OSR5 : rw_cells bsegs m5 OS ([c0; c1] ++ [CB 48 (repeat z8 48)] ++ rest));
    [ apply (cells_mid_update m4 m5 OS [c0; c1] 48 jj (repeat z8 48) rest); [exact OSR| | exact WM5| cbn [cells_size csize Nat.add]; replace (OS + Z.of_nat 16) with (OS + 16) by lia; exact BY5| apply repeat_length];
      apply AG45; intros x (Hx & Hn); cbn [app cells_size csize Nat.add] in Hx, Hn; clear - Hx Hn FLO FHI; split; [right; left; lia| lia] |]
  end.
  cbn [app] in OSR5.
  takeZ OSR5 2%nat (OS + 16)%Z P0. takeZ OSR5 1%nat (OS + 64)%Z MS1.
  retype MS1 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
  glueZ MS1 OSR5. glueZ P0 MS1. clear OSR. rename P0 into OSR.
  lazymatch type of FR4 with rw_cells _ _ _ ?cs0 => assert (FR5 : rw_cells bsegs m5 (q + -112) cs0)
      by (eapply rw_cells_agree_nw; [exact FR4|]; apply AG45; intros x Hx; cbn [cells_size csize Nat.add] in Hx; clear - Hx FLO FHI FSEG FTOP LOW LOR; split; [left; lia| lia]) end.
  assert (SHB5 : bytes_at bsegs m5 (shad OS) (repeat z8 36)).
  { eapply bytes_at_agree; [exact SHB4|]. apply AG45. intros x Hx. rewrite repeat_length in Hx. unfold shad, SHB in *. clear - Hx FLO FHI FSELF F0. split; [right; right; left|]; Z.div_mod_to_equations; lia. }
  assert (LOCB5 : LOCBA m5) by (apply (LOCBA_agree m4 m5 LOCB4); apply AG45; intros x Hx; unfold PJ_LOC_LO_A, PJ_LOC_HI_A in *; clear - Hx FLO FSEG; split; [right; right; right; lia| lia]).
  assert (PRES5' : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> outside [(PJ_LOC_LO_A, PJ_LOC_HI_A); (OS, OS + 288)] (bv_unsigned a) -> m5 a = m a).
  { intros a Ha Ho. rewrite <- (PRES4' a Ha Ho). apply PRES5; [apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia]|]. cbn [outside] in Ho |- *. lia. }
  clear AG45 PRES5 BY5 CD4 COK4 ART4 MI4 ST4 FR4 SHB4 LOCB4 PRES4' WM5.
  pose proof (munch_refl [(q - 128, q); (OS, OS + 288)]%Z m5) as MU. pose proof (wmono_refl bsegs m5) as WM.
  assert (SHZ5 : forall m', munch [(q - 128, q); (OS, OS + 288)] m5 m' -> wmono bsegs m5 m' -> shz m' OS 288).
  { intros m' MU' _. change 288 with (8 * Z.of_nat 36). apply (shz_of_zero_run m' OS 36); [clear - AL16; Z.div_mod_to_equations; lia| lia|].
    eapply bytes_at_agree; [exact SHB5|]. apply (agree_of_munch _ _ _ _ MU'). intros x Hx. rewrite repeat_length in Hx. cbn [outside]. unfold shad, SHB in *.
    clear - Hx FLO FHI FSELF F0 SHT LOW LOR. split; [| split; [| exact I]]; Z.div_mod_to_equations; lia. }
  change (id (bytes_at bsegs m5 (shad OS) (repeat z8 36))) in SHB5.

  apply (aevt_evt RT AF PMc MST).
  shz_pose SHZ5 OS. lstep. shz_norm. lstep. if_false.
  do 3 lstep.
  lstep.    rewrite shr3_div.
  do 2 lstep.
  lstep.    shz_pose SHZ5 (OS + 128). lstep. shz_norm. lstep. if_false.
  do 2 lstep.
  shz_pose SHZ5 (OS + 136). lstep. shz_norm. lstep. if_false.
  do 2 lstep.
  do 2 lstep.
  do 2 lstep.
  do 2 lstep.
  lstep.
  carve_frame 16%nat ST5.
  do 3 lstep.
  do 2 lstep.
  do 4 lstep.
  do 4 lstep.
  do 5 lstep.
  lstep.
  apply evt_done.
  assert (UQ128 : bv_unsigned (wz (q + -128)) = q + -128) by (apply unsigned_lit; lia).
  assert (ART8 : ART RT Σ m9).
  { apply (art_client_write RT AF Σ m5 m9 (q + -128) ART5 ltac:(ul)); [| exact WM]. intros a Ha. apply MU. cbn [outside].
    split; [intros Hin; apply Ha; left; ul|]. split; [| exact I]. intros Hin. apply Ha. apply (CL (q + -128)). right; left. lia. }
  assert (SHB8 : bytes_at bsegs m9 (shad OS) (repeat z8 36)).
  { unfold id in SHB5. eapply bytes_at_agree; [exact SHB5|]. apply (agree_of_munch _ _ _ _ MU). intros x Hx. rewrite repeat_length in Hx. cbn [outside]. unfold shad, SHB in *.
    clear - Hx FLO FHI FSELF F0 SHT LOW LOR. split; [| split; [| exact I]]; Z.div_mod_to_equations; lia. }
  assert (LOCB8 : LOCBA m9).
  { apply (LOCBA_agree m5 m9 LOCB5). apply (agree_of_munch _ _ _ _ MU). intros x Hx. cbn [outside]. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx.
    clear - Hx FLO FHI FSEG LOW LOR SP0R. split; [| split; [| exact I]]; lia. }
  takeZ OSR 19%nat (OS + 192)%Z P0. takeZ OSR 1%nat (OS + 272)%Z MS2.
  assert (CHK8 : 0 < 80 -> acc bsegs m9 (OS + 192) 80 /\ rng_class RT Σ (OS + 192) 80).
  { intros _. split; [| right; left; exists fO, kO; rewrite <- EFSZ; split; [exact INF| lia]].
    apply (acc_sub bsegs m9 OS 288); [| lia| lia]. change 288 with (8 * Z.of_nat 36). apply (acc_zero_run bsegs m9 OS 36); [clear - AL16; Z.div_mod_to_equations; lia| lia| exact SHB8]. }
  assert (COK8 : call_ok RT Σ m9 (wz (q + -128)) lo).
  { unfold call_ok. rewrite UQ128. split; [exact ST5|]. split; [exact LOW|]. split; [ul|]. split; [ul| clear - SP16; Z.div_mod_to_equations; lia]. }
  eapply (memsetA_spec RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fc m9 (OS + 192) 0 80 _ lo MS2
            ltac:(lia) ltac:(ul) ltac:(lia) ltac:(lia) CHK8 ltac:(intros i Hi; rewrite UQ128; apply (CL (q + -128)); right; left; lia) ART8 MI5 COK8).
  intros ms' (w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & F6 & m10 & -> & PRES9 & WM9 & MI9 & ART9 & ST9 & BY9).
  rewrite UQ128 in PRES9, ST9. rewrite (ret_pc_even 0x11055c) by lia.
  change (Z.to_nat 80) with 80%nat in BY9. change (0 mod 256) with 0 in BY9.
  retype BY9 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
              C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
  assert (AG89 : forall P : Z -> Prop, (forall x, P x -> ((q + -128 <= x < q) \/ (fO <= x < fO + FSZ - 8) \/ (fO / 8 + 2147450880 <= x < (fO + FSZ) / 8 + 2147450880) \/ (PJ_LOC_LO_A <= x < PJ_LOC_HI_A))
                                                     /\ ~ (OS + 192 <= x < OS + 192 + 80)) -> agree_on P m9 m10).
  { intros P HP a Ha. destruct (HP _ Ha) as (H1 & H2). apply PRES9; [| cbn [outside]; split; [exact H2| exact I]].
    destruct H1 as [H|[H|[H|H]]]; [left; ul| apply (CL (q + -128)); right; left; exact H| apply (CL (q + -128)); right; right; left; exact H| apply (CL (q + -128)); right; right; right; left; exact H]. }
  lazymatch type of P0 with rw_cells _ _ _ ?cs0 => assert (P09 : rw_cells bsegs m10 OS cs0)
      by (eapply rw_cells_agree_nw; [exact P0|]; apply AG89; intros x Hx; cbn [cells_size csize Nat.add] in Hx; clear - Hx FLO FHI; split; [right; left; lia| lia]) end.
  lazymatch type of OSR with rw_cells _ _ _ ?cs0 => assert (OSR9 : rw_cells bsegs m10 (OS + 272) cs0)
      by (eapply rw_cells_agree_nw; [exact OSR|]; apply AG89; intros x Hx; cbn [cells_size csize Nat.add] in Hx; clear - Hx FLO FHI; split; [right; left; lia| lia]) end.
  lazymatch type of FR5 with rw_cells _ _ _ ?cs0 => assert (FRc9 : rw_cells bsegs m10 (q + -112) cs0)
      by (eapply rw_cells_agree_nw; [exact FR5|]; apply AG89; intros x Hx; cbn [cells_size csize Nat.add] in Hx; clear - Hx FLO FHI FSEG FTOP LOW LOR; split; [left; lia| lia]) end.
  lazymatch type of FR with rw_cells _ _ _ ?cs0 => assert (FRi9 : rw_cells bsegs m10 (q + -128) cs0)
      by (eapply rw_cells_agree_nw; [exact FR|]; apply AG89; intros x Hx; cbn [cells_size csize Nat.add] in Hx; clear - Hx FLO FHI FSEG FTOP LOW LOR; split; [left; lia| lia]) end.
  assert (SHB9 : bytes_at bsegs m10 (shad OS) (repeat z8 36)).
  { eapply bytes_at_agree; [exact SHB8|]. apply AG89. intros x Hx. rewrite repeat_length in Hx. unfold shad, SHB in *. clear - Hx FLO FHI FSELF F0. split; [right; right; left|]; Z.div_mod_to_equations; lia. }
  assert (LOCB9 : LOCBA m10) by (apply (LOCBA_agree m9 m10 LOCB8); apply AG89; intros x Hx; unfold PJ_LOC_LO_A, PJ_LOC_HI_A in *; clear - Hx FLO FSEG; split; [right; right; right; lia| lia]).
  assert (PRES9' : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> outside [(PJ_LOC_LO_A, PJ_LOC_HI_A); (OS, OS + 288)] (bv_unsigned a) -> m10 a = m a).
  { intros a Ha Ho. rewrite <- (PRES5' a Ha Ho). transitivity (m9 a).
    - apply PRES9; [apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia]|]. cbn [outside] in Ho |- *. lia.
    - apply MU. pose proof (aclient_split_c RT AF Σ m5 q (bv_unsigned a) ART5 Ha) as SPL. unfold STACK_WIN in SPL. cbn [outside] in Ho |- *. clear - Ho SPL LOW LOR. repeat split; try exact I; lia. }
  clear AG89 PRES9 P0 OSR MS2 FR FR5 SHB8 LOCB5 LOCB8 CHK8 COK8 ART8 MI5 ST5 MU WM SHZ5 SHB5 PRES5' ART5.
  glueZ BY9 OSR9. glueZ P09 BY9. rename P09 into OSR.
  pose proof (munch_refl [(q - 128, q); (OS, OS + 288)]%Z m10) as MU. pose proof (wmono_refl bsegs m10) as WM.
  change (id (bytes_at bsegs m10 (shad OS) (repeat z8 36))) in SHB9.

  apply (aevt_evt RT AF PMc MST).
  do 4 lstep.
  release_frame FRi9 ST9 (q + -112).
  lstep.
  takeZ OSR 18%nat (OS + 184)%Z P0. takeZ OSR 1%nat (OS + 192)%Z LOC2. merge_at LOC2 0%nat 1%nat.
  assert (MI9' : mem_inv bsegs m10) by assumption.
  eapply evt_cut.
  { eapply (locale_ctor_specB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fc m10 lo (OS + 184) _); rewrite ?UQ112;
      [exact ST9| ul| clear - LOW SP0R; lia| exact LOCB9| exact LOC2| lia| ul| left; clear - FHI FTOP LOW LOR; lia| right; clear - FLO FSEG; lia| exact MI9']. }
  cbv beta. intros ms1 (x0 & x1 & x2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & x3 & x4 & x5 & x6 & m11 & -> & MU10 & WM10 & MI10 & ST10 & LOC10 & LOCB10).
  rewrite UQ112 in MU10, ST10. rewrite (ret_pc_even 0xaecd8) by lia.
  assert (AG910 : forall P : Z -> Prop, (forall x, P x -> ~ (q + -112 - 32 <= x < q + -112) /\ ~ (OS + 184 <= x < OS + 184 + 8)) -> agree_on P m10 m11).
  { intros P HP a Ha. apply MU10. cbn [outside]. destruct (HP _ Ha) as [H1 H2]. split; [exact H1| split; [exact H2| exact I]]. }
  assert (ART10 : ART RT Σ m11).
  { apply (art_client_write RT AF Σ m10 m11 (q + -112 - 32) ART9 ltac:(ul)); [| exact WM10]. intros a Ha. apply MU10. cbn [outside].
    split; [intros Hin; apply Ha; left; ul|]. split; [| exact I]. intros Hin. apply Ha. apply (CL (q + -112 - 32)). right; left. lia. }
  lazymatch type of P0 with rw_cells _ _ _ ?cs0 => assert (P010 : rw_cells bsegs m11 OS cs0)
      by (eapply rw_cells_agree_nw; [exact P0|]; apply AG910; intros x Hx; cbn [cells_size csize Nat.add] in Hx; clear - Hx FLO FHI FSEG FTOP LOW LOR; lia) end.
  lazymatch type of OSR with rw_cells _ _ _ ?cs0 => assert (OSR10 : rw_cells bsegs m11 (OS + 192) cs0)
      by (eapply rw_cells_agree_nw; [exact OSR|]; apply AG910; intros x Hx; cbn [cells_size csize Nat.add] in Hx; clear - Hx FLO FHI FSEG FTOP LOW LOR; lia) end.
  lazymatch type of FRc9 with rw_cells _ _ _ ?cs0 => assert (FR10 : rw_cells bsegs m11 (q + -112) cs0)
      by (eapply rw_cells_agree_nw; [exact FRc9|]; apply AG910; intros x Hx; cbn [cells_size csize Nat.add] in Hx; clear - Hx FLO FHI FSEG FTOP LOW LOR; lia) end.
  assert (SHB10 : bytes_at bsegs m11 (shad OS) (repeat z8 36)).
  { unfold id in SHB9. eapply bytes_at_agree; [exact SHB9|]. apply AG910. intros x Hx. rewrite repeat_length in Hx. unfold shad, SHB in *.
    clear - Hx FLO FHI FSELF F0 SHT LOW LOR. split; Z.div_mod_to_equations; lia. }
  assert (PRES10 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> outside [(PJ_LOC_LO_A, PJ_LOC_HI_A); (OS, OS + 288)] (bv_unsigned a) -> m11 a = m a).
  { intros a Ha Ho. rewrite <- (PRES9' a Ha Ho). apply MU10. pose proof (aclient_split_c RT AF Σ m10 q (bv_unsigned a) ART9 Ha) as SPL. unfold STACK_WIN in SPL.
    cbn [outside] in Ho |- *. clear - Ho SPL LOW LOR. repeat split; try exact I; lia. }
  clear AG910 MU10 WM10 P0 OSR FRc9 SHB9 LOCB9 PRES9' ART9 MI9' MU WM LOC2.
  glueZ LOC10 OSR10. glueZ P010 LOC10. rename P010 into OSR.
  pose proof (munch_refl [(q - 112, q); (OS, OS + 288)]%Z m11) as MU. pose proof (wmono_refl bsegs m11) as WM.
  assert (SHZ10 : forall m', munch [(q - 112, q); (OS, OS + 288)] m11 m' -> wmono bsegs m11 m' -> shz m' OS 288).
  { intros m' MU' _. change 288 with (8 * Z.of_nat 36). apply (shz_of_zero_run m' OS 36); [clear - AL16; Z.div_mod_to_equations; lia| lia|].
    eapply bytes_at_agree; [exact SHB10|]. apply (agree_of_munch _ _ _ _ MU'). intros x Hx. rewrite repeat_length in Hx. cbn [outside]. unfold shad, SHB in *.
    clear - Hx FLO FHI FSELF F0 SHT LOW LOR. split; [| split; [| exact I]]; Z.div_mod_to_equations; lia. }
  change (id (bytes_at bsegs m11 (shad OS) (repeat z8 36))) in SHB10.

  lstep.
  chk SHZ10 (OS + 272).
  lstep.
  lstep.
  chk SHZ10 (OS + 280).
  do 2 lstep.
  shz_pose SHZ10 OS. lstep. shz_norm. lstep. if_false.
  lstep.
  shz_pose SHZ10 (OS + 128). lstep. shz_norm. lstep. if_false.
  lstep.
  shz_pose SHZ10 (OS + 136). lstep. shz_norm. lstep. if_false.
  do 2 lstep.
  do 13 lstep.
  release_frame FR10 ST10 q.
  do 2 lstep.
  apply evt_done.
  replace (OS <? 1) with false in OSR by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z] in OSR.
  retype_at OSR 30%nat 1%nat [C4 (Z_to_bv 64 0xffffffff)].
  assert (AGF : forall P : Z -> Prop, (forall x, P x -> ~ (q - 112 <= x < q) /\ ~ (OS <= x < OS + 288)) -> agree_on P m11 m15).
  { intros P HP a Ha. apply MU. cbn [outside]. destruct (HP _ Ha) as [H1 H2]. split; [exact H1| split; [exact H2| exact I]]. }
  assert (ARTF : ART RT Σ m15).
  { apply (art_client_write RT AF Σ m11 m15 (q + -112) ART10 ltac:(ul)); [| exact WM]. intros a Ha. apply MU. cbn [outside].
    split; [intros Hin; apply Ha; left; ul|]. split; [| exact I]. intros Hin. apply Ha. apply (CL (q + -112)). right; left. lia. }
  assert (OSF : OSFRESHA m15 OS) by (unfold OSFRESHA, os_cellsA, sb_cellsA, ios_cellsA; cbn [app]; do 3 eexists; exact OSR).
  eapply HK; [exact ARTF| assumption| exact ST10| exact OSF| | |].
  - split; [exact (OSFRESHA_hull _ _ OSF)|]. unfold id in SHB10. eapply bytes_at_agree; [exact SHB10|]. apply AGF. intros x Hx. rewrite repeat_length in Hx. unfold shad, SHB in *.
    clear - Hx FLO FHI FSELF F0 SHT LOW LOR. split; Z.div_mod_to_equations; lia.
  - apply (LOCBA_agree m11 m15 LOCB10). apply AGF. intros x Hx. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx. clear - Hx FLO FHI FSEG LOW LOR SP0R. lia.
  - intros a Ha Ho. rewrite <- (PRES10 a Ha Ho). apply MU. pose proof (aclient_split_c RT AF Σ m11 q (bv_unsigned a) ART10 Ha) as SPL. unfold STACK_WIN in SPL.
    cbn [outside] in Ho |- *. clear - Ho SPL LOW LOR. repeat split; try exact I; lia.
Qed.
End Ctor.
