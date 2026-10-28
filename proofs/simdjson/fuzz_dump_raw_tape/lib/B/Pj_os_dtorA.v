(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_new Sj_num_akit Sj_num_amem Pj_rtkA Pj_defsA Pj_cpsA Pj_os_defsA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Pj_os_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma locdtor_evtA_proof : locdtor_evtA.
Proof.
  unfold locdtor_evtA. intros until P. intros LOC LB MI.
  do 4 lstep.
  if_true.
  lstep.
  apply evt_done. do 15 eexists. cbv delta [mkR]. reflexivity.
Qed.

Section Dtor.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.

Local Ltac ul := unfold PJ_IOS_DTOR_STACK_A, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Theorem iosdtor_cpsA_proof : iosdtor_cpsA RT PMc OSIOSA.
Proof using AF RC FDO MST.
  unfold iosdtor_cpsA. intros until m. intros FDO' MST' INF FLO FHI AL16 OSI HULL LB UNW ART0 MI ST LOW LOR SPT SP16 HK.
  pose proof (af_frames_range RT AF Σ m fO kO ART0 INF) as (F0 & FTOP & FSEG & FLIVE).
  pose proof (proj2 (af_fshadow_apart RT AF Σ m fO kO ART0 INF) fO kO INF) as FSELF.
  pose proof (fframe_ranges RT AF Σ m fO kO ART0 INF) as (_ & _ & FSZ0 & SHB0 & SHT).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, PJ_IOS_DTOR_STACK_A in *. remember (fs_size kO) as FSZ eqn:EFSZ.
  assert (LO48 : lo <= q - 48) by ul. assert (Q0 : 0 <= q - 48) by (destruct ST; ul).
  assert (UQ : bv_unsigned (wz q) = q) by (apply unsigned_lit; ul).
  assert (UQ48 : bv_unsigned (wz (q + -48)) = q + -48) by (apply unsigned_lit; ul).
  destruct OSI as (vp & fill & j148 & j284 & IOSF). unfold ios_cellsA in IOSF.
  destruct HULL as [(bo & FO) SHZ].
  destruct LB as (l1 & l2 & l3 & l4 & l5 & l6 & l7 & l8 & l9 & l10 & l11 & l12 & l13 & l14 & l15 & LBC).
  pose proof (munch_refl [(q - 48, q); (OS + 136, OS + 144)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.

  apply (rw_cells_split_CB bsegs _ _ [] 288 _ [] [136; 152]%nat) in FO; [| reflexivity]. cbn [mk_CB_cells app] in FO.
  lazymatch type of FO with rw_cells _ _ _ (?c0 :: ?rest) => change (c0 :: rest) with ([c0] ++ rest) in FO end.
  apply Sj_stage1_kit.rw_cells_app in FO. destruct FO as [FO _].
  lazymatch type of FO with rw_cells _ _ _ [CB 136 ?t] => set (bo1 := t) in FO; clearbody bo1 end.
  change (id (rw_cells bsegs m OS [CB 136 bo1])) in FO.
  change (id (bytes_at bsegs m (shad OS) (repeat z8 36))) in SHZ.
  change (id (rw_cells bsegs m PJ_LOC_LO_A (locb_cellsA l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15))) in LBC.
  apply (aevt_evt RT AF PMc MST).
  lstep.
  carve_frame 48%nat ST.
  do 12 lstep.
  if_false.
  do 2 lstep.
  if_true.
  lstep.
  lstep.
  takeZ IOSF 8%nat (OS + 184)%Z P0. takeZ IOSF 1%nat (OS + 192)%Z LOCM.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (LBC1 : rw_cells bsegs m1 PJ_LOC_LO_A (locb_cellsA l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15)).
  { unfold id in LBC. apply (rw_cells_transport bsegs _ m m1 _ _ LBC MU WM). rewrite locb_cellsA_size. unfold PJ_LOC_LO_A. cbn [disjoint_from]. lia. }
  clear LBC.
  eapply evt_cut.
  { eapply (locdtor_evtA_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (OS + 184)%Z); [exact LOCM | exists l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15; exact LBC1 | assumption]. }
  intros ms' (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & ->).
  rewrite (ret_pc_even 0x110738) by lia.
  glueZ LOCM IOSF. glueZ P0 LOCM. rename P0 into IOSF.
  lstep.
  lstep.
  apply evt_done.

  assert (CL : forall x, (q + -48 <= x < q) \/ (fO <= x < fO + FSZ - 8) \/ (shad fO <= x < shad (fO + FSZ)) -> aclient (rt_live RT Σ) (rt_frames RT Σ) (q + -48) x).
  { intros x [H|[H|H]]; [left; ul| right; right; right; left| do 4 right]; (exists fO, kO; rewrite <- EFSZ; split; [exact INF| exact H]). }
  assert (CLq : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) q a -> aclient (rt_live RT Σ) (rt_frames RT Σ) (q + -48) a).
  { intros a Ha. apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia]. }
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 (q + -48) ART0 ltac:(ul)); [| exact WM].
    intros a Ha. apply MU. cbn [outside]. split; [intros Hin; apply Ha; apply CL; left; exact Hin|]. split; [intros Hin; apply Ha; apply CL; right; left; lia| exact I]. }
  assert (PRES1 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> outside [(OS + 136, OS + 144)] (bv_unsigned a) -> m1 a = m a).
  { intros a Ha Ho. apply MU. cbn [outside] in Ho |- *. pose proof (aclient_split_c RT AF Σ m q (bv_unsigned a) ART0 Ha) as SPL.
    split; [clear - SPL LOW LOR; ul| exact Ho]. }
  assert (COK : forall mx, stk bsegs mx lo (q + -48) -> call_ok RT Σ mx (Z_to_bv 64 (q + -48)) lo).
  { intros mx STx. unfold call_ok. rewrite UQ48. split; [exact STx|]. split; [exact LOW|]. split; [ul|]. split; [ul| clear - SP16; Z.div_mod_to_equations; lia]. }
  assert (UNW1 : forall r : word, unwind_ok r (Z_to_bv 64 (OS + 136)) (Z_to_bv 64 (q + -48))).
  { intros r. unfold unwind_ok. rewrite UQ48, unsigned_lit by ul. left. ul. }
  clear MU WM.

  eapply (aevt_free0 RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 lo eq_refl ART1 MI (COK m1 ST) (UNW1 _)).
  intros v1 w0 w1 w2 b1 b2 b3 b4 b5 b6 b7 w3 w4 w5 w6 F2 m2 (ART2 & MI2 & WM2 & ST2) PRES2. rewrite UQ48 in ST2, PRES2. rewrite (ret_pc_even 0x110740) by lia.
  assert (AG12 : forall P : Z -> Prop, (forall x, P x -> (q + -48 <= x < q) \/ (fO <= x < fO + FSZ - 8) \/ (shad fO <= x < shad (fO + FSZ))) -> agree_on P m1 m2).
  { intros P HP a Ha. apply PRES2; [exact (CL _ (HP _ Ha))| lia]. }
  lazymatch type of IOSF with rw_cells _ _ _ ?cs => assert (IOSF2 : rw_cells bsegs m2 (OS + 136) cs)
      by (eapply rw_cells_agree_nw; [exact IOSF|]; apply AG12; intros x Hx; cbn [cells_size csize Nat.add] in Hx; right; left; lia) end.
  lazymatch type of FR with rw_cells _ _ _ ?cs => assert (FR2 : rw_cells bsegs m2 (q + -48) cs)
      by (eapply rw_cells_agree_nw; [exact FR|]; apply AG12; intros x Hx; cbn [cells_size csize Nat.add] in Hx; left; lia) end.
  assert (PRES2' : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> outside [(OS + 136, OS + 144)] (bv_unsigned a) -> m2 a = m a).
  { intros a Ha Ho. rewrite <- (PRES1 a Ha Ho). apply PRES2; [exact (CLq _ Ha)| lia]. }
  clear AG12 IOSF FR PRES1 PRES2 ART1 MI ST WM2.
  apply (aevt_evt RT AF PMc MST).
  lstep.
  lstep.
  apply evt_done.

  eapply (aevt_free0 RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc m2 lo eq_refl ART2 MI2 (COK m2 ST2) (UNW1 _)).
  intros v2 x0 x1 x2 c1 c2 c3 c4 c5 c6 c7 x3 x4 x5 x6 F3 m3 (ART3 & MI3 & WM3 & ST3) PRES3. rewrite UQ48 in ST3, PRES3. rewrite (ret_pc_even 0x110748) by lia.
  assert (AG23 : forall P : Z -> Prop, (forall x, P x -> (q + -48 <= x < q) \/ (fO <= x < fO + FSZ - 8) \/ (shad fO <= x < shad (fO + FSZ))) -> agree_on P m2 m3).
  { intros P HP a Ha. apply PRES3; [exact (CL _ (HP _ Ha))| lia]. }
  lazymatch type of IOSF2 with rw_cells _ _ _ ?cs => assert (IOSF3 : rw_cells bsegs m3 (OS + 136) cs)
      by (eapply rw_cells_agree_nw; [exact IOSF2|]; apply AG23; intros x Hx; cbn [cells_size csize Nat.add] in Hx; right; left; lia) end.
  lazymatch type of FR2 with rw_cells _ _ _ ?cs => assert (FR3 : rw_cells bsegs m3 (q + -48) cs)
      by (eapply rw_cells_agree_nw; [exact FR2|]; apply AG23; intros x Hx; cbn [cells_size csize Nat.add] in Hx; left; lia) end.
  assert (PRES3' : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> outside [(OS + 136, OS + 144)] (bv_unsigned a) -> m3 a = m a).
  { intros a Ha Ho. rewrite <- (PRES2' a Ha Ho). apply PRES3; [exact (CLq _ Ha)| lia]. }
  clear AG23 IOSF2 FR2 PRES2' PRES3 ART2 MI2 ST2 WM3.
  apply (aevt_evt RT AF PMc MST).
  lstep.
  lstep.
  apply evt_done.

  eapply (aevt_free0 RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc m3 lo eq_refl ART3 MI3 (COK m3 ST3) (UNW1 _)).
  intros v3 y0 y1 y2 d1 d2 d3 d4 d5 d6 d7 y3 y4 y5 y6 F4 m4 (ART4 & MI4 & WM4 & ST4) PRES4. rewrite UQ48 in ST4, PRES4. rewrite (ret_pc_even 0x110750) by lia.
  assert (AG34 : forall P : Z -> Prop, (forall x, P x -> (q + -48 <= x < q) \/ (fO <= x < fO + FSZ - 8) \/ (shad fO <= x < shad (fO + FSZ))) -> agree_on P m3 m4).
  { intros P HP a Ha. apply PRES4; [exact (CL _ (HP _ Ha))| lia]. }
  lazymatch type of IOSF3 with rw_cells _ _ _ ?cs => assert (IOSF4 : rw_cells bsegs m4 (OS + 136) cs)
      by (eapply rw_cells_agree_nw; [exact IOSF3|]; apply AG34; intros x Hx; cbn [cells_size csize Nat.add] in Hx; right; left; lia) end.
  lazymatch type of FR3 with rw_cells _ _ _ ?cs => assert (FR4 : rw_cells bsegs m4 (q + -48) cs)
      by (eapply rw_cells_agree_nw; [exact FR3|]; apply AG34; intros x Hx; cbn [cells_size csize Nat.add] in Hx; left; lia) end.
  assert (PRES4' : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> outside [(OS + 136, OS + 144)] (bv_unsigned a) -> m4 a = m a).
  { intros a Ha Ho. rewrite <- (PRES3' a Ha Ho). apply PRES4; [exact (CLq _ Ha)| lia]. }
  clear AG34 IOSF3 FR3 PRES3' PRES4 ART3 MI3 ST3 WM4.

  apply (aevt_evt RT AF PMc MST).
  do 7 lstep.
  release_frame FR4 ST4 q.
  lstep.
  apply evt_done.
  assert (COK4 : call_ok RT Σ m4 (Z_to_bv 64 q) lo).
  { unfold call_ok. rewrite UQ. split; [exact ST4|]. split; [exact LOW|]. split; [ul|]. split; [ul| exact SP16]. }
  eapply (aevt_free0 RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F4 fc m4 lo eq_refl ART4 MI4 COK4 UNW).
  intros v4 z0 z1 z2 e1 e2 e3 e4 e5 e6 e7 z3 z4 z5 z6 F5 m5 (ART5 & MI5 & WM5 & ST5) PRES5. rewrite UQ in ST5, PRES5.
  assert (PRES5' : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> outside [(OS + 136, OS + 144)] (bv_unsigned a) -> m5 a = m a).
  { intros a Ha Ho. rewrite <- (PRES4' a Ha Ho). apply PRES5; [exact Ha| lia]. }
  eapply HK; [exact ART5| exact MI5| exact ST5| | exact PRES5'].

  unfold id in FO, SHZ.
  assert (FO5 : rw_cells bsegs m5 OS [CB 136 bo1]).
  { eapply rw_cells_agree_nw; [exact FO|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply PRES5'; [| cbn [outside]; lia].
    right; right; right; left. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia]. }
  lazymatch type of IOSF4 with rw_cells _ _ _ ?cs => assert (IOSF5 : rw_cells bsegs m5 (OS + 136) cs)
      by (eapply rw_cells_agree_nw; [exact IOSF4|]; intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply PRES5; [right; right; right; left; exists fO, kO; rewrite <- EFSZ; split; [exact INF| lia]| lia]) end.
  split.
  - lazymatch type of IOSF5 with rw_cells _ _ _ ?cs =>
      destruct (rw_cells_forget bsegs m5 OS ([CB 136 bo1] ++ cs)) as (bo5 & H5);
        [apply Sj_stage1_kit.rw_cells_app; split; [exact FO5|]; cbn [cells_size csize Nat.add]; replace (OS + Z.of_nat 136) with (OS + 136) by lia; exact IOSF5| exists bo5; exact H5] end.
  - apply (bytes_at_agree bsegs m m5 _ _ SHZ). intros a Ha. rewrite repeat_length in Ha. apply PRES5'.
    + do 4 right. exists fO, kO. rewrite <- EFSZ. split; [exact INF|]. unfold shad in *. clear - Ha FLO FHI. Z.div_mod_to_equations. lia.
    + cbn [outside]. unfold shad in *. clear - Ha FLO FHI FSELF F0. split; [| exact I]. Z.div_mod_to_equations. lia.
Qed.

End Dtor.
