(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd SjAlloc.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec Require Import Prelim Stdio SjModel AtpModel OdModel.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_stage1_kit Sj_num_kit Atp_h_defs.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Layout RT_iface RT_iface2 RT_anndefs D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps
  Sj_hkit Sj_hkit2 Sj_new Sj_num_akit Sj_num_amem Od_hbaseA Atp_h_defsA Od_defsB Od_cpsB Od_lkitB Od_bodyB Od_beginB Od_top_defsB
  Od_proB Od_splitintoB Od_setup_defsB Od_setupkB Od_setupw1B Od_setupw2B Od_setupcB Od_exitB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section PhaseA.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis AF : art_facts RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis RTF : rt_contracts_f RT.
Hypothesis SPL : splitinto_cps0A RT.
Hypothesis EMPS : empls_cpsA RT.

Notation aevt := (aevt RT PMc).
Local Ltac ul := unfold FUZZ_STACK, ATPA_SPLITINTO_STACK, ATPA_SPLIT_STACK, ATPA_PUSH_STACK, OD_NEED in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.
Local Notation LIB_agree' := (Od_setupcB.LIB_agree' LIB LIB_loc).
Local Notation aevt_splitinto := (Od_setupcB.aevt_splitinto RT PMc FDO MST SPL).
Local Notation aevt_empls := (Od_setupcB.aevt_empls RT PMc FDO MST EMPS).

Lemma od_cutA_intro : forall (Σ0 Σx : rts RT) (m0 mx : mem) (usp S1 f lo D act A cap size : Z) (bs : list byte) (d' : list Z) (els : list (Z * Z))
    (cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word) (x408 x416 : word) (z424 : byte)
    (j0 j136 j176 j264 j288 j336 j376 j425 j432 h3 jd jp tS : list byte) (h0 h1 h2 : word),
  usp mod 16 = 0 -> usp + 16 <= USTACK_TOP -> S1 mod 32 = 0 -> usp - 560 <= S1 <= usp - 544 ->
  rt_sp0 RT Σ0 - STACK_WIN <= lo -> lo + FUZZ_STACK <= usp -> f mod 64 = 0 -> 0 < f ->
  rt_frames RT Σ0 = [] -> (forall p n, In (p, n) (rt_live RT Σ0) -> 0 < n) ->
  Z.of_nat (length (rt_live RT Σ0)) + FUZZ_LIVE <= LIVE_MAX -> FUZZ_COST <= rt_credit RT Σ0 ->
  ART RT Σx mx -> mem_inv bsegs mx -> stk bsegs mx lo S1 -> rt_frames RT Σx = [(f, 3%nat)] -> rt_sp0 RT Σx = rt_sp0 RT Σ0 ->
  rw_cells bsegs mx (S1 + 376) [CB 24 j376; C8 (Z_to_bv 64 f)] -> rw_cells bsegs mx (S1 + 408) [C8 x408; C8 x416] ->
  rw_cells bsegs mx (S1 + 424) [C1 z424; CB 7 j425; CB 8 j432] ->
  stk bsegs mx (S1 + 440) (usp - 104) -> rw_cells bsegs mx (usp - 104) (fa_saved cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11) ->
  rw_cells bsegs mx f [C8 h0; C8 h1; C8 h2; CB 8 h3] ->
  vrepA mx (f + 32) A cap size els -> 1 <= size -> wr_at bsegs mx (f / 8 + 2147450880) 64 ->
  rw_cells bsegs mx (f + 192) [CB 64 jd] -> LIB mx ->
  (forall a : word, aclient (rt_live RT Σ0) [] usp (bv_unsigned a) -> mx a = m0 a) ->
  d' = tl (od_chars bs) -> act = od_action (od_chars bs) -> Z.of_nat (length bs) < 2^26 ->
  rt_live RT Σx = vblockA A cap size ++ rt_live RT Σ0 -> rt_credit RT Σ0 - OD_VEC_COST <= rt_credit RT Σx ->
  rw_cells bsegs mx S1 [CB 120 j0; C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f); CB 32 j136; C8 (Z_to_bv 64 (f + 96)); CB 72 j176;
                        C8 (Z_to_bv 64 (f / 8 + 2147450880)); C8 (Z_to_bv 64 act); CB 16 j264; C8 (Z_to_bv 64 (f + 224)); CB 40 j288;
                        C8 (Z_to_bv 64 (f + 208)); CB 32 j336; C8 (Z_to_bv 64 (f + 200))] ->
  rw_cells bsegs mx (f + 96) [CB 56 jp] ->
  rw_cells bsegs mx (f / 8 + 2147450880) (oa_shadow2 tS) ->
  els = oa_els D d' -> bytes_at bsegs mx D (zbytes d') -> 0 <= D ->
  ((exists p k, In (p, k) (rt_live RT Σ0) /\ p <= D /\ D + zlength d' <= p + k) \/ (d' = [] /\ D < SEGTOP_A)) ->
  exists p0, od_cutA RT LIB Σ0 Σx m0 mx usp S1 f lo (od_chars bs) A cap size p0 els cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11.
Proof using.
  intros until h2.
  intros U16 UT S32 S1R LOW LOR F64 FPOS FRS0 LVPOS LVB CR0 ARTx MIx STx FRSx SPx HA FD TL STp FRs FH VR SZ1 WRS FDoc LIBx CPx ED EACT BSL LVx CRx
    LOWx FP FS EELS BYD D0 INLVD.
  destruct (oa_els_shape D d') as (P0 & rest & SHAPE & PCASE & PREF).
  assert (ES0 : od_s0 (od_chars bs) = nth 0 (atp_parts d') []) by (unfold od_s0, od_parts, od_rest; rewrite ED; reflexivity).

  apply (rw_cells_split_CB bsegs _ _ [] 24 _ [C8 (Z_to_bv 64 f)] [8; 16]%nat) in HA; [| reflexivity]. cbn [mk_CB_cells app] in HA.
  lazymatch type of HA with rw_cells _ _ _ (?c0 :: ?rest) => change (c0 :: rest) with ([c0] ++ rest) in HA end.
  apply Sj_stage1_kit.rw_cells_app in HA. destruct HA as [HA0 HA]. cbn [cells_size csize Nat.add] in HA.
  replace (S1 + 376 + Z.of_nat 8) with (S1 + 384) in HA by lia.
  exists P0. constructor.
  - constructor; try assumption.
    + split; assumption.
    + split; assumption.
    + split; assumption.
    + split; assumption.
    +
      pose proof (rw_cells_wr_at bsegs mx _ _ 24 HA ltac:(cbn; lia)) as W1.
      pose proof (rw_cells_wr_at bsegs mx _ _ 16 FD ltac:(cbn; lia)) as W2.
      pose proof (rw_cells_wr_at bsegs mx _ _ 16 TL ltac:(cbn; lia)) as W3.
      replace (S1 + 408) with (S1 + 384 + 24) in W2 by lia.
      pose proof (wr_at_join bsegs mx _ _ _ W1 W2 ltac:(lia) ltac:(lia)) as W12.
      replace (S1 + 424) with (S1 + 384 + (24 + 16)) in W3 by lia.
      pose proof (wr_at_join bsegs mx _ _ _ W12 W3 ltac:(lia) ltac:(lia)) as W. change (24 + 16 + 16) with 56 in W.
      destruct (wr_at_rw_CB mx _ _ W ltac:(lia)) as (jj & X). change (Z.to_nat 56) with 56%nat in X.
      apply (rw_cells_split_CB bsegs _ _ [] 56 _ [] [48; 8]%nat) in X; [| reflexivity]. cbn [mk_CB_cells app] in X.
      eexists _, _. exact X.
    +
      apply (rw_cells_merge bsegs mx f [] [C8 h0]) in FH. cbn [app cells_size csize] in FH.
      apply (rw_cells_merge bsegs mx f [CB 8 (cells_bytes [C8 h0])] [C8 h1; C8 h2; CB 8 h3] []) in FH. cbn [app cells_size csize Nat.add] in FH.
      eexists _, _. exact FH.
    + eexists. exact FDoc.
    + intros a Ha _. exact (CPx a Ha).
  - split; [apply od_chars_range| rewrite od_chars_length; exact BSL].
  - exact LVx.
  - exact CRx.
  - lazymatch type of HA0 with rw_cells _ _ _ [CB 8 ?jj] => exists j0, j136, j176, j264, j288, j336, jj end.
    unfold od_lowA, wz. rewrite <- EACT.
    replace (S1 + 376) with (S1 + Z.of_nat 376) in HA0 by lia.
    exact (proj2 (Sj_stage1_kit.rw_cells_app bsegs mx S1 _ _) (conj LOWx HA0)).
  - eexists. exact FP.
  - unfold oa_shadow2 in FS. cbn [map app repeat] in FS.
    lazymatch type of FS with rw_cells _ _ _ ?l =>
      lazymatch l with context C [[CB 28 tS]] => let l1 := context C [@nil cell] in change l with (l1 ++ [CB 28 tS]) in FS end end.
    apply Sj_stage1_kit.rw_cells_app in FS. destruct FS as [FS _].
    assert (E15 : Z_to_bv 8 (-15) = Z_to_bv 8 0xf1) by (apply bv_eq; reflexivity).
    assert (E14 : Z_to_bv 8 (-14) = Z_to_bv 8 0xf2) by (apply bv_eq; reflexivity).
    assert (E13 : Z_to_bv 8 (-13) = Z_to_bv 8 0xf3) by (apply bv_eq; reflexivity).
    assert (E8 : Z_to_bv 8 (-8) = Z_to_bv 8 0xf8) by (apply bv_eq; reflexivity).
    rewrite E15, E14, E13, E8 in FS. exact FS.
  - exists rest. rewrite EELS, ES0. exact SHAPE.
  - destruct PCASE as [(E & _)|(E & _)]; lia.
  - rewrite ES0. destruct PCASE as [(E & E0 & _)|(E & NE)].
    + rewrite E0. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
    + subst P0. rewrite PREF. rewrite <- (firstn_skipn (length (nth 0 (atp_parts d') [])) d') in BYD.
      unfold zbytes in *. rewrite map_app in BYD. apply bytes_at_app in BYD. exact (proj1 BYD).
  - rewrite ES0. destruct PCASE as [(E & E0 & _)|(E & NE)]; [left; exact E0| right].
    destruct INLVD as [(p & k & Hin & P1 & P2)|(E' & _)]; [| contradiction].
    exists p, k. split; [exact Hin|]. subst P0. split; [exact P1|].
    assert (zlength (nth 0 (atp_parts d') []) <= zlength d'); [| lia].
    rewrite PREF at 1. unfold zlength. rewrite firstn_length. lia.
Qed.

Lemma od_loop_exit : forall (K : config -> Prop) (Σ0 : rts RT) (m0 : mem) (usp lo : Z) (dz : list Z)
    (gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word),
  od_cutA_k RT LIB PMc K Σ0 m0 usp lo dz gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 ->
  forall (ΣA : rts RT) (S1 F A cap size p0 : Z) (els : list (Z * Z))
         (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s9 t3 t4 t5 t6 : word) FR fc (mA : mem),
  frm0 fc ->
  od_cutA RT LIB Σ0 ΣA m0 mA usp S1 F lo dz A cap size p0 els cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 ->
  aevt ΣA K (lh_regs 0x96b70 ra S1 gp (Z_to_bv 64 0x656e70) t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 F s9 t3 t4 t5 t6 FR fc mA).
Proof using AF MST.
  intros K Σ0 m0 usp lo dz gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 KA.
  intros ΣA S1 F A cap size p0 els ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s9 t3 t4 t5 t6 FR fc mA FRM CA.
  pose proof (c0_vec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ca_0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CA)) as VR.
  pose proof (c0_size _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ca_0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CA)) as SZ1.
  pose proof (c0_F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ca_0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CA)) as (_ & FPOS).
  pose proof (c0_art _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ca_0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CA)) as ARTA.
  pose proof (c0_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ca_0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CA)) as MIA.
  pose proof (c0_frames _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ca_0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CA)) as FRSA.
  assert (INF : In (F, 3%nat) (rt_frames RT ΣA)) by (rewrite FRSA; left; reflexivity).
  pose proof (fframe_ranges RT AF ΣA mA F 3 ARTA INF) as (_ & FR1 & _). change (fs_size 3) with 512 in FR1.
  pose proof (af_sp0_range RT AF ΣA mA ARTA) as SP0R.
  destruct VR as (VSZ & VSC & VCAP & VA0 & VAT & VS & VB).
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { exact (od_walkLHx ra usp S1 F A cap size gp (Z_to_bv 64 0x656e70) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s9 t3 t4 t5 t6 FR fc mA
             FPOS ltac:(clear - FR1 SP0R; ul) VA0 VAT ltac:(lia) VS MIA). }
  cbv beta. intros ms <-. apply evt_done. unfold lh_regs.
  exact (KA ΣA S1 F A cap size p0 els _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR fc mA FRM CA).
Qed.

Theorem od_phaseA : od_phaseA_stmt RT LIB PMc.
Proof using LIB_loc AF FDO MST RTF SPL EMPS.
  intros Σ K ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo
    _ _ -> -> -> D0 BSL BS INLV FRS0 LVPOS LVB CR0 LIB0 ART0 MI0 ST0 LOW LOR SPT SPA FRM KA.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_client_consts RT AF Σ m ART0) as CC0.
  set (usp := bv_unsigned sp) in *. set (n := Z.of_nat (length bs)) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (N0 : 0 <= n < 2^64) by (subst n; lia).
  assert (DR : 0 <= d < 2^64 /\ d + n <= lo).
  { destruct INLV as [(p & k & Hin & P1 & P2)|(E & DL)]; [| subst n; rewrite E; cbn [length]; clear - D0 DL LOW SP0R; ul].
    pose proof (af_live_range RT AF Σ m p k ART0 Hin) as (R0 & R1 & R2). clear - D0 P1 P2 R1 SP0R N0 LOW. ul. }
  destruct DR as (DR & DLO).

  destruct (od_prologue usp lo d n ra gp (Z_to_bv 64 0x656e70) t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m
              ST0 ltac:(ul) ltac:(ul) ltac:(ul) SPA CC0 MI0) as (S1 & S1R & S32 & W0).
  rewrite <- ESP in W0.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [exact W0|]. clear W0.
  cbv beta. intros ms1 (m1 & a1' & a2' & j0 & j8 & j16 & j24 & j120 & j128 & j136 & j168 & j176 & j248 & j256 & j264 & j280 & j288 & j328 & j336
                          & j368 & j376 & j400 & j408 & j416 & j424 & j425 & j432 & -> & MU1 & WM1 & MI1 & ST1 & FRl1 & STp1 & FRs1).
  apply evt_done.
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 S1 ART0 ltac:(ul)); [| exact WM1].
    intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. ul. }
  assert (LIB1 : LIB m1).
  { apply (LIB_agree' m m1 LIB0). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. pose proof (proj2 (oa_lib_fp_static x Hx)).
    cbn [outside]. split; [ul| exact I]. }
  assert (BS1 : bytes_at bsegs m1 d bs).
  { apply (bytes_at_agree bsegs m m1 _ _ BS). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbv beta in Hx. cbn [outside]. split; [| exact I].
    clear - Hx DLO S1R LOW LOR. subst n. ul. }
  assert (CP1 : forall a : word, aclient (rt_live RT Σ) [] usp (bv_unsigned a) -> m1 a = m a).
  { intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. intros Hin.
    destruct Ha as [H|[H|[H|[H|H]]]].
    - lia.
    - pose proof (client_static_range _ H) as CR. clear - CR Hin S1R LOW LOR SP0R. ul.
    - destruct H as (p & k & Hp & HR). pose proof (af_live_range RT AF Σ m p k ART0 Hp) as (_ & R1 & _). clear - R1 HR Hin S1R LOW LOR. ul.
    - destruct H as (f & k & [] & _).
    - destruct H as (f & k & [] & _). }
  assert (EU1 : bv_unsigned (Z_to_bv 64 S1) = S1) by (apply unsigned_lit; ul).

  unfold entry_st.
  eapply (aevt_stack_malloc RT RTF PMc FDO MST Σ K 3%nat) with (lo := lo);
    [ left; reflexivity | reflexivity | rewrite FRS0; cbn; unfold FRAMES_MAX; lia | unfold FUZZ_COST in CR0; lia | exact ART1 | exact MI1
    | unfold call_ok; rewrite EU1; split; [exact ST1|]; split; [ul|]; split; [ul|]; split; [ul| clear - S32; Z.div_mod_to_equations; lia]
    | exact FRM | ].
  intros Σ1 f v0 v1 v2 e1 e2 e3 e4 e5 e6 e7 v3 v4 v5 v6 F2 fc2 m2 FRM2 (ART2 & MI2 & WM2 & ST2) PRES2 WRF WRS FRS1 LV1 SP1 CR1 FPOS F64 FTOP.
  rewrite EU1 in ST2, PRES2. rewrite FRS0 in FRS1, PRES2.
  rewrite (ret_pc_even 0x969b4) by lia.
  change (fs_size 3) with 512 in *. change (512 / 8) with 64 in WRS. change (512 - 8) with 504 in WRF.
  assert (INF1 : In (f, 3%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  pose proof (fframe_ranges RT AF Σ1 m2 f 3 ART2 INF1) as (_ & FR1' & _ & SHB0 & SHT).
  pose proof (af_fshadow_apart RT AF Σ1 m2 f 3 ART2 INF1) as (FSL & FSF). pose proof (FSF f 3%nat INF1) as FSELF.
  pose proof (af_frames_align RT AF Σ1 m2 f 3 ART2 INF1) as (_ & FSEG).
  pose proof (af_frames_range RT AF Σ1 m2 f 3%nat ART2 INF1) as (_ & _ & _ & FLV).
  change (fs_size 3) with 512 in *. rewrite SP1 in FR1', SHT.
  assert (SHF : shad (f + 512) = shad f + 64) by (unfold shad; clear - F64; Z.div_mod_to_equations; lia).
  rewrite SHF in *. unfold shad, SHB in SHB0, SHT, FSELF, FSL, WRS.
  assert (FD0 : 0 <= f / 8) by (apply Z.div_pos; lia).
  set (S := f / 8 + 2147450880) in *.
  assert (GF : f + 512 <= lo /\ S + 64 <= lo /\ (f + 512 <= S \/ S + 64 <= f) /\ SEGTOP_A <= f) by (clear - FR1' SHT LOW FSELF FSEG; ul).
  destruct GF as (FLO & SLO & FSEP & FSG).

  assert (AG12 : agree_on (fun x => aclient (rt_live RT Σ) [] S1 x) m1 m2) by (intros a Ha; exact (PRES2 a Ha)).
  assert (STp2 : stk bsegs m2 (S1 + 440) (usp - 104)).
  { apply (stk_agree bsegs m1 m2 _ _ STp1); [| exact WM2]. eapply agree_sub; [exact AG12|]. intros x Hx. left. ul. }
  assert (LIB2 : LIB m2).
  { apply (LIB_agree' m1 m2 LIB1). eapply agree_sub; [exact AG12|]. intros x Hx. right; left. exact (proj1 (oa_lib_fp_static x Hx)). }
  assert (BS2 : bytes_at bsegs m2 d bs).
  { apply (bytes_at_agree bsegs m1 m2 _ _ BS1). eapply agree_sub; [exact AG12|]. intros x Hx. cbv beta in Hx.
    destruct INLV as [(p & k & Hin & P1 & P2)| (E & DL)]; [| rewrite E in Hx; cbn [length] in Hx; lia].
    right; right; left. exists p, k. split; [exact Hin| subst n; lia]. }
  assert (CP2 : forall a : word, aclient (rt_live RT Σ) [] usp (bv_unsigned a) -> m2 a = m a).
  { intros a Ha. rewrite <- (CP1 a Ha). apply PRES2. apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia]. }
  clear STp1 LIB1 BS1 CP1.
  unfold od_locals0, fa_saved in *.
  rt_transport_with m1 m2 AG12 WM2 ltac:(intros x Hx; cbn [cells_size csize Nat.add] in Hx; left; clear - Hx S1R SPT; unfold USTACK_TOP in *; lia).
  clear AG12 PRES2 MU1 WM1 ST1 MI1 ART1.

  destruct (wr_at_rw_CB m2 f 32 (wr_at_sub m2 f 504 f 32 WRF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jH & FH2).
  change (Z.to_nat 32) with 32%nat in FH2.
  apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FH2; [| reflexivity]. cbn [mk_CB_cells app] in FH2.
  destruct (wr_at_rw_CB m2 (f + 32) 24 (wr_at_sub m2 f 504 (f + 32) 24 WRF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jV & FV2).
  change (Z.to_nat 24) with 24%nat in FV2.
  destruct (wr_at_rw_CB m2 (f + 96) 56 (wr_at_sub m2 f 504 (f + 96) 56 WRF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jP & FP2).
  change (Z.to_nat 56) with 56%nat in FP2.
  destruct (wr_at_rw_CB m2 (f + 192) 64 (wr_at_sub m2 f 504 (f + 192) 64 WRF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jD & FDoc2).
  change (Z.to_nat 64) with 64%nat in FDoc2.
  destruct (wr_at_rw_CB m2 S 64 WRS ltac:(lia)) as (jS & FS2).
  change (Z.to_nat 64) with 64%nat in FS2.
  apply (rw_cells_split_CB bsegs _ _ [] 64 _ [] [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 28]%nat) in FS2; [| reflexivity].
  cbn [mk_CB_cells app] in FS2.
  lazymatch type of FS2 with rw_cells _ _ _ [CB 1 ?l0; CB 1 ?l1; CB 1 ?l2; CB 1 ?l3; CB 1 ?l4; CB 1 ?l5; CB 1 ?l6; CB 1 ?l7; CB 1 ?l8; CB 1 ?l9;
                                             CB 1 ?l10; CB 1 ?l11; CB 1 ?l12; CB 1 ?l13; CB 1 ?l14; CB 1 ?l15; CB 1 ?l16; CB 1 ?l17; CB 1 ?l18; CB 1 ?l19;
                                             CB 1 ?l20; CB 1 ?l21; CB 1 ?l22; CB 1 ?l23; CB 1 ?l24; CB 1 ?l25; CB 1 ?l26; CB 1 ?l27; CB 1 ?l28; CB 1 ?l29;
                                             CB 1 ?l30; CB 1 ?l31; CB 1 ?l32; CB 1 ?l33; CB 1 ?l34; CB 1 ?l35; CB 28 ?t] =>
    change (rw_cells bsegs m2 S
              (oa_shadow0 [l0; l1; l2; l3; l4; l5; l6; l7; l8; l9; l10; l11; l12; l13; l14; l15; l16; l17; l18; l19; l20; l21; l22; l23; l24; l25; l26; l27;
                           l28; l29; l30; l31; l32; l33; l34; l35] t)) in FS2;
    set (tS := t) in FS2; clearbody tS
  end.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { lazymatch type of FH2 with rw_cells _ _ _ [CB 8 ?h0; CB 8 ?h1; CB 8 ?h2; CB 8 ?h3] =>
    lazymatch type of FS2 with rw_cells _ _ _ (oa_shadow0 ?LS _) =>
      exact (od_walk1h usp S1 f lo d n gp (Z_to_bv 64 0x656e70) v0 v1 v2 e1 e2 e3 e4 e5 e6 e7 s4 s5 s6 s8 s9 s10 s11 v3 v4 v5 v6
               j0 j8 j16 j24 j120 j128 j136 j168 j176 j248 j256 j264 j280 j288 j328 j336 j368 j376 j400 j408 j416 j424 j425 j432 h0 h1 h2 h3 tS LS F2 fc2 m2
               eq_refl FPOS FLO SLO FD0 FSEP ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) DR N0 FRl1 FH2 FS2 MI2)
    end end. }
  cbv beta. intros ms3 (m3 & b1 & b2 & b3 & b4 & b5 & b6 & -> & MU3 & WM3 & MI3 & FRl3 & FH3 & FS3).
  apply evt_done. unfold oa_W1h in MU3. fold S in MU3, FS3.
  assert (LOW1 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SP1; exact LOW).
  assert (FPW : fp_ok RT Σ1 lo [(S1, S1 + 440); (f, f + 24); (S, S + 36)]).
  { repeat apply Forall_cons; [| | | apply Forall_nil]; cbn [fst snd].
    - left. ul.
    - right; right; left. exists f, 3%nat. split; [exact INF1|]. change (fs_size 3) with 512. lia.
    - right; right; right. exists f, 3%nat. split; [exact INF1|]. change (fs_size 3) with 512. rewrite SHF. unfold shad, SHB. fold S. lia. }
  pose proof (art_of_munch RT AF Σ1 m2 m3 lo _ ART2 LOW1 FPW MU3 WM3) as ART3.
  assert (AG23 : agree_on (fun x => ~ (S1 <= x < S1 + 440) /\ ~ (f <= x < f + 24) /\ ~ (S <= x < S + 36)) m2 m3).
  { apply (agree_of_munch _ _ _ _ MU3). intros x (H1 & H2 & H3'). cbn [outside]. repeat split; assumption. }
  assert (ST3 : stk bsegs m3 lo S1).
  { apply (stk_agree bsegs m2 m3 _ _ ST2); [| exact WM3]. eapply agree_sub; [exact AG23|]. intros x Hx. cbv beta in *. ul. }
  assert (STp3 : stk bsegs m3 (S1 + 440) (usp - 104)).
  { apply (stk_agree bsegs m2 m3 _ _ STp2); [| exact WM3]. eapply agree_sub; [exact AG23|]. intros x Hx. cbv beta in *. ul. }
  assert (LIB3 : LIB m3).
  { apply (LIB_agree' m2 m3 LIB2). eapply agree_sub; [exact AG23|]. intros x Hx. pose proof (proj2 (oa_lib_fp_static x Hx)). cbv beta. ul. }
  assert (PAY : bs = [] \/ exists p k, In (p, k) (rt_live RT Σ1) /\ p <= d /\ d + n <= p + k /\ (f + 512 <= p \/ p + k <= f) /\ (p + k <= S \/ S + 64 <= p) /\ p + k <= lo).
  { destruct INLV as [(p & k & Hin & P1 & P2)| (E & DL)]; [right| left; exact E]. exists p, k. rewrite LV1.
    split; [exact Hin|]. split; [exact P1|]. split; [exact P2|]. rewrite <- LV1 in Hin.
    pose proof (af_live_range RT AF Σ1 m2 p k ART2 Hin) as (_ & R1 & _).
    split; [exact (FLV p k Hin)|]. split; [exact (FSL p k Hin)|]. clear - R1 LOW1. lia. }
  assert (CP3 : forall a : word, aclient (rt_live RT Σ) [] usp (bv_unsigned a) -> m3 a = m a).
  { intros a Ha. rewrite <- (CP2 a Ha). apply MU3. cbn [outside].
    destruct Ha as [H|[H|[H|[H|H]]]].
    - split; [lia|]. split; [clear - H FLO LOR; ul|]. split; [clear - H SLO LOR; ul| exact I].
    - pose proof (client_static_range _ H) as CR. split; [clear - CR S1R LOW LOR SP0R; ul|]. split; [clear - CR FSG; lia|]. split; [clear - CR SHB0; unfold SEGTOP_A, SHB in *; lia| exact I].
    - destruct H as (p & k & Hp & HR). rewrite <- LV1 in Hp. pose proof (af_live_range RT AF Σ1 m2 p k ART2 Hp) as (_ & R1 & _).
      pose proof (FLV p k Hp) as X1. pose proof (FSL p k Hp) as X2.
      split; [clear - R1 HR LOW1 S1R LOR; ul|]. split; [clear - HR X1; lia|]. split; [clear - HR X2; lia| exact I].
    - destruct H as (f0 & k0 & [] & _).
    - destruct H as (f0 & k0 & [] & _). }
  clear ST2 STp2 LIB2 CP2 ART2 MI2 FRl1 FH2 FS2 WRF FPW.
  rt_transport_with m2 m3 AG23 WM3 ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; cbv beta;
      first [ clear - Hx FLO SLO FSEP S1R LOR FPOS; ul
            | destruct PAY as [E|(p & k & _ & P1 & P2 & P3 & P4 & P5)]; [rewrite E in Hx; cbn [length] in Hx; clear - Hx; lia| clear - Hx P1 P2 P3 P4 P5 S1R LOR; subst n; ul] ]).
  clear AG23 MU3 WM2.

  assert (REST : forall (D act : Z) (d' : list Z) (xa1 xa2 xs3 : word) (m4 : mem),
            act = od_action (od_chars bs) -> d' = tl (od_chars bs) -> 0 <= D -> 0 <= act <= 12 ->
            bytes_at bsegs m3 D (zbytes d') -> D + zlength d' <= lo ->
            ((exists p k, In (p, k) (rt_live RT Σ1) /\ p <= D /\ D + zlength d' <= p + k) \/ (d' = [] /\ D < SEGTOP_A)) ->
            munch [(S1, S1 + 440)] m3 m4 -> wmono bsegs m3 m4 -> mem_inv bsegs m4 ->
            rw_cells bsegs m4 S1 (oa_locals2 f D j0 j8 j16 j24 j120 j136 j168 j176 j256 j264 j280 j288 j328 j336 j368 j376 j416 j425 j432) ->
            aevt Σ1 K (oa_st1 0x96b14 usp S1 f gp (Z_to_bv 64 0x656e70) v0 v1 v2 (Z_to_bv 64 act) xa1 xa2 b3 b4 b5 b6 (Z_to_bv 64 (zlength d')) xs3
                         s4 s5 s6 s8 s9 s10 s11 v3 v4 v5 v6 F2 fc2 m4)).
  2:{ destruct bs as [|b0 bs'].
      -
        subst n. cbn [length Z.of_nat] in *.
        apply (aevt_evt RT AF PMc MST).
        eapply evt_cut.
        { exact (od_walk1e usp S1 f d gp (Z_to_bv 64 0x656e70) v0 v1 v2 b1 b2 b3 b4 b5 b6 s4 s5 s6 s8 s9 s10 s11 v3 v4 v5 v6
                   j0 j8 j16 j24 j120 j136 j168 j176 j256 j264 j280 j288 j328 j336 j368 j376 j408 j416 j425 j432 F2 fc2 m3
                   ltac:(ul) ltac:(ul) ltac:(ul) FRl3 MI3). }
        cbv beta. intros ms4 (m4 & -> & MU4 & WM4 & MI4 & FRl4). apply evt_done.
        apply (REST 0 0 [] _ _ _ m4 eq_refl eq_refl ltac:(lia) ltac:(lia)); [| unfold zlength; cbn [length Z.of_nat]; clear - LOW SP0R; ul| right; split; [reflexivity| ul]| exact MU4| exact WM4| exact MI4| exact FRl4].
        split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
      -
        destruct PAY as [E|(p & k & Hin & P1 & P2 & P3 & P4 & P5)]; [discriminate E|].
        assert (NL : n = Z.of_nat (length bs') + 1) by (subst n; cbn [length]; lia).
        pose proof (af_acc_live RT AF Σ1 m3 p k ART3 Hin) as (_ & ACC).
        destruct (ACC (d - p) ltac:(lia)) as (b & SB & SOK). replace (p + (d - p)) with d in SB, SOK by lia. unfold shad, SHB in SB.
        change (b0 :: bs') with ([b0] ++ bs') in BS2. apply bytes_at_app in BS2. destruct BS2 as [BY0 BY1]. cbn [length Z.of_nat Pos.of_succ_nat] in BY1.
        pose proof (af_live_range RT AF Σ1 m3 p k ART3 Hin) as (PP0 & _ & _).
        assert (DD0 : 0 <= d / 8) by (apply Z.div_pos; lia).
        assert (DSH : d / 8 + 2147450880 + 1 <= S1).
        { clear - DD0 DLO LOR S1R SP0R SP0W LOW D0 N0. unfold FUZZ_STACK, STACK_WIN, USTACK_TOP in *. Z.div_mod_to_equations. lia. }
        apply (aevt_evt RT AF PMc MST).
        eapply evt_cut.
        { exact (od_walk1b usp S1 f d n b0 b gp (Z_to_bv 64 0x656e70) v0 v1 v2 b1 b2 b3 b4 b5 b6 s4 s5 s6 s8 s9 s10 s11 v3 v4 v5 v6
                   j0 j8 j16 j24 j120 j136 j168 j176 j256 j264 j280 j288 j328 j336 j368 j376 j408 j416 j425 j432 F2 fc2 m3
                   ltac:(ul) ltac:(ul) ltac:(ul) D0 ltac:(ul) ltac:(lia) DD0 DSH FRl3 BY0 SB SOK MI3). }
        cbv beta. intros ms4 (m4 & a1x & a2x & -> & MU4 & WM4 & MI4 & FRl4). apply evt_done.
        pose proof (bv_unsigned_in_range 8 b0) as B0R. unfold bv_modulus in B0R. change (2 ^ Z.of_N 8) with 256 in B0R.
        pose proof (Z.mod_pos_bound (bv_unsigned b0) 13 ltac:(lia)) as AR.
        assert (ZL : zlength (tl (od_chars (b0 :: bs'))) = n - 1) by (cbn [od_chars map tl]; unfold zlength; rewrite length_map; lia).
        rewrite <- ZL.
        apply (REST (d + 1) (bv_unsigned b0 mod 13) (tl (od_chars (b0 :: bs'))) _ _ _ m4 eq_refl eq_refl ltac:(lia) ltac:(lia));
          [| rewrite ZL; lia| left; exists p, k; split; [exact Hin| rewrite ZL; lia]| exact MU4| exact WM4| exact MI4| exact FRl4].
        cbn [od_chars map tl]. fold (od_chars bs'). rewrite od_zbytes_chars. exact BY1. }
  intros D act d' xa1 xa2 xs3 m4 EACT ED' D0' ACTR BYD DLO' INLVD MU4 WM4 MI4 FRl4.

  assert (FP4 : fp_ok RT Σ1 lo [(S1, S1 + 440)]) by (apply Forall_cons; [| apply Forall_nil]; cbn [fst snd]; left; ul).
  pose proof (art_of_munch RT AF Σ1 m3 m4 lo _ ART3 LOW1 FP4 MU4 WM4) as ART4.
  assert (AG34 : agree_on (fun x => ~ (S1 <= x < S1 + 440)) m3 m4)
    by (apply (agree_of_munch _ _ _ _ MU4); intros x Hx; cbn [outside]; split; [exact Hx| exact I]).
  assert (ST4 : stk bsegs m4 lo S1).
  { apply (stk_agree bsegs m3 m4 _ _ ST3); [| exact WM4]. eapply agree_sub; [exact AG34|]. intros x Hx. cbv beta in *. ul. }
  assert (STp4 : stk bsegs m4 (S1 + 440) (usp - 104)).
  { apply (stk_agree bsegs m3 m4 _ _ STp3); [| exact WM4]. eapply agree_sub; [exact AG34|]. intros x Hx. cbv beta in *. ul. }
  assert (LIB4 : LIB m4).
  { apply (LIB_agree' m3 m4 LIB3). eapply agree_sub; [exact AG34|]. intros x Hx. pose proof (proj2 (oa_lib_fp_static x Hx)). cbv beta. ul. }
  assert (CP4 : forall a : word, aclient (rt_live RT Σ) [] usp (bv_unsigned a) -> m4 a = m a).
  { intros a Ha. rewrite <- (CP3 a Ha). apply MU4. cbn [outside]. split; [| exact I].
    pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 ltac:(rewrite FRS0; exact Ha)) as SPL0. clear - SPL0 S1R LOW LOR. ul. }
  clear ST3 STp3 LIB3 CP3 ART3 MI3 FRl3 BS2 PAY.
  assert (ZLD : 0 <= zlength d') by (unfold zlength; lia).
  unfold oa_shadow1 in FS3. cbn [map app repeat] in FS3.
  rt_transport_with m3 m4 AG34 WM4 ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; cbv beta;
      first [ clear - Hx FLO SLO FSEP S1R LOR FPOS; ul
            | unfold zbytes in Hx; rewrite length_map in Hx; unfold zlength in DLO'; clear - Hx DLO' S1R LOR; ul ]).
  clear AG34 MU4 WM3 FP4.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { exact (od_walk1t usp S1 f lo D (zlength d') act gp (Z_to_bv 64 0x656e70) v0 v1 v2 xa1 xa2 b3 b4 b5 b6 xs3 s4 s5 s6 s8 s9 s10 s11 v3 v4 v5 v6
             j0 j8 j16 j24 j120 j136 j168 j176 j256 j264 j280 j288 j328 j336 j368 j376 j416 j425 j432 tS F2 fc2 m4
             FPOS FLO SLO FD0 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) FRl4 FS3 MI4). }
  unfold oa_shadow2. cbn [map app repeat].
  cbv beta. intros ms5 (m5 & -> & MU5 & WM5 & MI5 & FRl5 & FS5).
  apply evt_done. unfold oa_W1t in MU5. fold S in MU5, FS5.
  assert (FP5 : fp_ok RT Σ1 lo [(S1, S1 + 440); (S, S + 36)]).
  { repeat apply Forall_cons; [| | apply Forall_nil]; cbn [fst snd].
    - left. ul.
    - right; right; right. exists f, 3%nat. split; [exact INF1|]. change (fs_size 3) with 512. rewrite SHF. unfold shad, SHB. fold S. lia. }
  pose proof (art_of_munch RT AF Σ1 m4 m5 lo _ ART4 LOW1 FP5 MU5 WM5) as ART5.
  assert (AG45 : agree_on (fun x => ~ (S1 <= x < S1 + 440) /\ ~ (S <= x < S + 36)) m4 m5).
  { apply (agree_of_munch _ _ _ _ MU5). intros x (H1 & H2). cbn [outside]. repeat split; assumption. }
  assert (ST5 : stk bsegs m5 lo S1).
  { apply (stk_agree bsegs m4 m5 _ _ ST4); [| exact WM5]. eapply agree_sub; [exact AG45|]. intros x Hx. cbv beta in *. ul. }
  assert (STp5 : stk bsegs m5 (S1 + 440) (usp - 104)).
  { apply (stk_agree bsegs m4 m5 _ _ STp4); [| exact WM5]. eapply agree_sub; [exact AG45|]. intros x Hx. cbv beta in *. ul. }
  assert (LIB5 : LIB m5).
  { apply (LIB_agree' m4 m5 LIB4). eapply agree_sub; [exact AG45|]. intros x Hx. pose proof (proj2 (oa_lib_fp_static x Hx)). cbv beta. ul. }
  assert (INLVD' : d' = [] \/ exists p k, In (p, k) (rt_live RT Σ1) /\ p <= D /\ D + zlength d' <= p + k /\ (p + k <= S \/ S + 64 <= p)).
  { destruct INLVD as [(p & k & Hin & P1 & P2)|(E & _)]; [right| left; exact E]. exists p, k. repeat split; try assumption. exact (FSL p k Hin). }
  assert (CP5 : forall a : word, aclient (rt_live RT Σ) [] usp (bv_unsigned a) -> m5 a = m a).
  { intros a Ha. rewrite <- (CP4 a Ha). apply MU5. cbn [outside].
    pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 ltac:(rewrite FRS0; exact Ha)) as SPL0.
    split; [clear - SPL0 S1R LOW LOR; ul|]. split; [| exact I].
    destruct Ha as [H|[H|[H|[H|H]]]].
    - clear - H SLO LOR; ul.
    - pose proof (client_static_range _ H) as CR. clear - CR SHB0; unfold SEGTOP_A, SHB in *; lia.
    - destruct H as (p & k & Hp & HR). rewrite <- LV1 in Hp. pose proof (FSL p k Hp) as X2. clear - HR X2; lia.
    - destruct H as (f0 & k0 & [] & _).
    - destruct H as (f0 & k0 & [] & _). }
  clear ST4 STp4 LIB4 CP4 ART4 MI4 FRl4 FS3.
  rt_transport_with m4 m5 AG45 WM5 ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; cbv beta;
      first [ clear - Hx FLO SLO FSEP S1R LOR FPOS; ul
            | unfold zbytes in Hx; rewrite length_map in Hx; unfold zlength in DLO', INLVD';
              destruct INLVD' as [E|(p & k & _ & P1 & P2 & P3)]; [rewrite E in Hx; cbn [length] in Hx; clear - Hx; lia| clear - Hx DLO' P1 P2 P3 S1R LOR; ul] ]).
  clear AG45 MU5 WM4 FP5.

  unfold oa_locals3 in FRl5.
  apply (rw_cells_merge bsegs m5 S1 [] [CB 8 j0; CB 8 j8; CB 8 j16; CB 96 j24]) in FRl5.
  cbn [app cells_size csize Nat.add] in FRl5.
  set (J0 := cells_bytes _) in FRl5. clearbody J0.
  lazymatch type of FRl5 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15
                                             :: ?c16 :: ?c17 :: ?c18 :: ?c19 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: c15 :: c16 :: c17 :: c18 :: c19 :: rest)
      with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13] ++ [c14; c15] ++ [c16; c17] ++ [c18; c19] ++ rest) in FRl5 end.
  apply Sj_stage1_kit.rw_cells_app in FRl5. destruct FRl5 as [LOW5 X]. apply Sj_stage1_kit.rw_cells_app in X. destruct X as [HA5 X].
  apply Sj_stage1_kit.rw_cells_app in X. destruct X as [FD5 TL5].
  cbn [cells_size csize Nat.add app] in HA5, FD5, TL5.
  replace (S1 + Z.of_nat 376) with (S1 + 376) in * by lia.
  replace (S1 + 376 + Z.of_nat 32) with (S1 + 408) in * by lia.
  replace (S1 + 408 + Z.of_nat 16) with (S1 + 424) in * by lia.

  assert (FOBJV : fobj RT Σ1 m5 (f + 32) 24).
  { split; [clear - F64; Z.div_mod_to_equations; lia|]. split; [lia|]. change ((24 + 7) / 8) with 3.
    split; [exists f, 3%nat; change (fs_size 3) with 512; split; [exact INF1| lia]|].
    replace (shad (f + 32)) with (S + 4) by (subst S; unfold shad, SHB; clear - F64; Z.div_mod_to_equations; lia).
    pose proof FS5 as X.
    lazymatch type of X with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?d0 :: ?d1 :: ?d2 :: ?rest) =>
      change (c0 :: c1 :: c2 :: c3 :: d0 :: d1 :: d2 :: rest) with ([c0; c1; c2; c3] ++ [d0; d1; d2] ++ rest) in X end.
    apply Sj_stage1_kit.rw_cells_app in X. destruct X as [_ X]. apply Sj_stage1_kit.rw_cells_app in X. destruct X as [X _].
    cbn [cells_size csize Nat.add] in X. destruct X as [[_ HB] _]. exact HB. }

  assert (CHL : zlength (od_chars bs) = n) by (subst n; apply od_chars_length).
  assert (LENd : zlength d' < 2^26).
  { subst d'. unfold zlength in *. destruct (od_chars bs) as [|c0 l0]; cbn [tl length] in *; lia. }
  assert (RNGd : Forall (fun c => 0 <= c < 256) d').
  { subst d'. pose proof (od_chars_range bs) as X. destruct (od_chars bs) as [|c0 l0]; cbn [tl]; [exact X| inversion X; assumption]. }
  pose proof (od_vcb_ok d' LENd) as VCB0. pose proof (od_vcost_le d') as VCM.
  pose proof (vcost_pushes_nonneg (length (poffs d')) 0 0 ltac:(lia)) as VC0.

  unfold entry_st.
  eapply (aevt_splitinto Σ1 K) with (RV := f + 32) (FD := S1 + 408) (D := D) (d := d') (jv := jV) (lo := lo);
    rewrite ?EU1;
    [ reflexivity | reflexivity | reflexivity | exact BYD | exact RNGd | exact LENd | exact D0' | exact INLVD
    | rewrite LV1; exact LVPOS | exact FOBJV | exact FV2 | lia | ul | clear - S32; Z.div_mod_to_equations; lia | exact FD5
    | rewrite LV1; unfold FUZZ_LIVE in LVB; lia | rewrite CR1; unfold FUZZ_COST, OD_VEC_COST in *; lia
    | rewrite FRS1; cbn; unfold FRAMES_MAX2; lia | exact ART5 | exact MI5 | exact ST5 | exact LOW1 | ul | ul
    | clear - S32; Z.div_mod_to_equations; lia | exact FRM2 | ].
  intros Σ2 A rv w0 w1 w2 g1 g2 g3 g4 g5 g6 g7 w3 w4 w5 w6 F6 fc6 m6 FRM6 (ART6 & MI6 & ST6) PRES6 VR6 FD6 VL6 FRS6 SP6 CR6.
  rewrite (ret_pc_even 0x96b68) by lia.
  set (P0 := length (poffs d')) in *.
  assert (EP0 : zlength (poffs d') = Z.of_nat P0) by reflexivity. rewrite EP0 in *.
  rewrite FRS1 in PRES6, FRS6.
  assert (ACL : forall x, (S1 <= x < S1 + 408) \/ (S1 + 424 <= x < usp) \/ (f <= x < f + 32) \/ (f + 96 <= x < f + 256) \/ (S <= x < S + 64) ->
                  aclient (rt_live RT Σ1) [(f, 3%nat)] S1 x /\ outside [(f + 32, f + 32 + 24); (S1 + 408, S1 + 408 + 16)] x).
  { intros x Hx. assert (OUT : outside [(f + 32, f + 32 + 24); (S1 + 408, S1 + 408 + 16)] x).
    { cbn [outside]. destruct Hx as [H|[H|[H|[H|H]]]]; (split; [| split; [| exact I]]); clear - H FLO SLO S1R LOR FSEP FPOS; ul. }
    split; [| exact OUT]. destruct Hx as [H|[H|[H|[H|H]]]].
    - left. ul. - left. ul.
    - right; right; right; left. exists f, 3%nat. change (fs_size 3) with 512. split; [left; reflexivity| lia].
    - right; right; right; left. exists f, 3%nat. change (fs_size 3) with 512. split; [left; reflexivity| lia].
    - right; right; right; right. exists f, 3%nat. change (fs_size 3) with 512. rewrite SHF. unfold shad, SHB. fold S. split; [left; reflexivity| lia]. }
  assert (AG56 : agree_on (fun x => (S1 <= x < S1 + 408) \/ (S1 + 424 <= x < usp) \/ (f <= x < f + 32) \/ (f + 96 <= x < f + 256) \/ (S <= x < S + 64)) m5 m6).
  { intros a Ha. destruct (ACL _ Ha) as [H1 H2]. exact (PRES6 a H1 H2). }
  assert (STp6 : stk bsegs m6 (S1 + 440) (usp - 104)).
  { apply (stk_agree_nw bsegs m5 m6 _ _ STp5). eapply agree_sub; [exact AG56|]. intros x Hx. cbv beta in *. ul. }
  assert (LIB6 : LIB m6).
  { apply (LIB_agree' m5 m6 LIB5). intros a Ha. destruct (oa_lib_fp_static _ Ha) as [CS R]. apply PRES6; [right; left; exact CS|].
    cbn [outside]. clear - R FSG S1R LOW LOR SP0R. unfold SEGTOP_A in *. split; [lia|]. split; [ul| exact I]. }
  assert (BYD6 : bytes_at bsegs m6 D (zbytes d')).
  { apply (bytes_at_agree bsegs m5 m6 _ _ BYD). intros a Ha. cbv beta in Ha. unfold zbytes in Ha. rewrite length_map in Ha. unfold zlength in DLO', INLVD.
    destruct INLVD as [(p & k & Hin & P1 & P2)| (E & DL)]; [| rewrite E in Ha; cbn [length] in Ha; lia].
    apply PRES6.
    - right; right; left. exists p, k. split; [exact Hin| lia].
    - pose proof (FLV p k Hin) as X1. cbn [outside].
      split; [clear - Ha P1 P2 X1; lia|]. split; [| exact I]. clear - Ha DLO' LOR S1R. ul. }
  assert (CP6 : forall a : word, aclient (rt_live RT Σ) [] usp (bv_unsigned a) -> m6 a = m a).
  { intros a Ha. rewrite <- (CP5 a Ha).
    pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 ltac:(rewrite FRS0; exact Ha)) as SPL0.
    apply PRES6.
    - apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; rewrite LV1; exact He| intros e []| lia].
    - cbn [outside]. split; [| split; [| exact I]]; [| clear - SPL0 S1R LOW LOR; ul].
      destruct Ha as [H|[H|[H|[H|H]]]].
      + clear - H FLO LOR; ul.
      + pose proof (client_static_range _ H) as CR. clear - CR FSG; lia.
      + destruct H as (p & k & Hp & HR). rewrite <- LV1 in Hp. pose proof (FLV p k Hp) as X1. clear - HR X1; lia.
      + destruct H as (f0 & k0 & [] & _).
      + destruct H as (f0 & k0 & [] & _). }
  clear STp5 LIB5 BYD CP5 ST5 ART5 MI5 FD5 FV2 FOBJV.
  rt_transport_nw m5 m6 AG56 ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; cbv beta; clear - Hx S1R; lia).
  clear AG56 ACL.

  assert (LOW2 : rt_sp0 RT Σ2 - STACK_WIN <= lo) by (rewrite SP6; exact LOW1).
  assert (INF2 : In (f, 3%nat) (rt_frames RT Σ2)) by (rewrite FRS6; left; reflexivity).
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { exact (od_walkLH0 (Z_to_bv 64 0x96b68) usp S1 f gp (Z_to_bv 64 0x656e70) w0 w1 w2 rv g1 g2 g3 g4 g5 g6 g7 (Z_to_bv 64 (zlength d')) xs3 s4 s5 s6 s9
             w3 w4 w5 w6 F6 fc6 m6). }
  cbv beta. intros ms7 <-.
  apply evt_done.
  pose proof VR6 as (VSZ & VSC & VCAP & VA0 & VAT & VS & VB).
  assert (INLV0 : (exists p k, In (p, k) (rt_live RT Σ) /\ p <= D /\ D + zlength d' <= p + k) \/ (d' = [] /\ D < SEGTOP_A))
    by (rewrite <- LV1; exact INLVD).
  assert (FOBJ7 : forall Σx mx, rt_frames RT Σx = [(f, 3%nat)] -> rw_cells bsegs mx S (oa_shadow2 tS) -> fobj RT Σx mx (f + 32) 24).
  { intros Σx mx FRSx FSx.
    split; [clear - F64; Z.div_mod_to_equations; lia|]. split; [lia|]. change ((24 + 7) / 8) with 3.
    split; [exists f, 3%nat; change (fs_size 3) with 512; split; [rewrite FRSx; left; reflexivity| lia]|].
    replace (shad (f + 32)) with (S + 4) by (subst S; unfold shad, SHB; clear - F64; Z.div_mod_to_equations; lia).
    pose proof FSx as X. unfold oa_shadow2 in X. cbn [map app repeat] in X.
    lazymatch type of X with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?d0 :: ?d1 :: ?d2 :: ?rest) =>
      change (c0 :: c1 :: c2 :: c3 :: d0 :: d1 :: d2 :: rest) with ([c0; c1; c2; c3] ++ [d0; d1; d2] ++ rest) in X end.
    apply Sj_stage1_kit.rw_cells_app in X. destruct X as [_ X]. apply Sj_stage1_kit.rw_cells_app in X. destruct X as [X _].
    cbn [cells_size csize Nat.add] in X. destruct X as [[_ HB] _]. exact HB. }
  destruct (Nat.eq_dec P0 0) as [PZ|PNZ].
  -
    assert (EOP : oa_P d' = 1%nat) by (unfold oa_P; fold P0; lia).
    rewrite PZ in *. cbn [vcap_iter Z.of_nat] in *.
    destruct (poffs d') as [|e0 l0] eqn:EPO; [| subst P0; discriminate PZ]. cbn [map] in VR6.
    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut.
    { exact (od_walkLHs (Z_to_bv 64 0x96b68) usp S1 f A gp (Z_to_bv 64 0x656e70) w0 w1 w2 rv g1 g2 g3 g4 g5 g6 g7 (Z_to_bv 64 (-16)) (Z_to_bv 64 16) s4 s5 s6 s9
               w3 w4 w5 w6 F6 fc6 m6 FPOS ltac:(clear - FLO LOR SPT; ul) ltac:(clear - VA0 VAT; lia) VS MI6). }
    cbv beta. intros ms8 <-. apply evt_done. unfold lh_regs.
    assert (CRE : vcost_push 0 0 <= rt_credit RT Σ2).
    { rewrite EOP in VCB0. rewrite vcost_pushes_S in VCB0. cbn [vcost_pushes] in VCB0, CR6. unfold FUZZ_COST, OD_VEC_COST in *. rewrite CR1 in CR6.
      clear - VCB0 CR6 CR0. lia. }
    eapply (aevt_empls Σ2 K) with (V := f + 32) (A := A) (cap := 0) (size := 0) (els := []) (L0 := rt_live RT Σ1) (lo := lo);
      rewrite ?EU1;
      [ reflexivity | reflexivity | exact VR6 | exact VL6 | rewrite LV1; exact LVPOS | reflexivity | lia | exact (FOBJ7 Σ2 m6 FRS6 FS5)
      | rewrite LV1; unfold FUZZ_LIVE in LVB; lia | exact CRE | exact ART6 | exact MI6 | exact ST6 | exact LOW2 | ul | ul
      | clear - S32; Z.div_mod_to_equations; lia | exact FRM6 | ].
    intros Σ3 A3 y0 y1 y2 k1 k2 k3 k4 k5 k6 k7 y3 y4 y5 y6 F8 fc8 m8 FRM8 (ART8 & MI8 & ST8) PRES8 VR8 VL8 FRS8 SP8 CR8.
    rewrite (ret_pc_even 0x96ba4) by lia. rewrite FRS6 in PRES8, FRS8.
    assert (ACL : forall x, (S1 <= x < usp) \/ (f <= x < f + 32) \/ (f + 96 <= x < f + 256) \/ (S <= x < S + 64) ->
                    aclient (rt_live RT Σ1) [(f, 3%nat)] S1 x /\ outside [(f + 32, f + 32 + 24)] x).
    { intros x Hx. assert (OUT : outside [(f + 32, f + 32 + 24)] x).
      { cbn [outside]. destruct Hx as [H|[H|[H|H]]]; (split; [| exact I]); clear - H FLO SLO S1R LOR FSEP FPOS; ul. }
      split; [| exact OUT]. destruct Hx as [H|[H|[H|H]]].
      - left. ul.
      - right; right; right; left. exists f, 3%nat. change (fs_size 3) with 512. split; [left; reflexivity| lia].
      - right; right; right; left. exists f, 3%nat. change (fs_size 3) with 512. split; [left; reflexivity| lia].
      - right; right; right; right. exists f, 3%nat. change (fs_size 3) with 512. rewrite SHF. unfold shad, SHB. fold S. split; [left; reflexivity| lia]. }
    assert (AG78 : agree_on (fun x => (S1 <= x < usp) \/ (f <= x < f + 32) \/ (f + 96 <= x < f + 256) \/ (S <= x < S + 64)) m6 m8).
    { intros a Ha. destruct (ACL _ Ha) as [H1 H2]. exact (PRES8 a H1 H2). }
    assert (STp8 : stk bsegs m8 (S1 + 440) (usp - 104)).
    { apply (stk_agree_nw bsegs m6 m8 _ _ STp6). eapply agree_sub; [exact AG78|]. intros x Hx. cbv beta in *. ul. }
    assert (LIB8 : LIB m8).
    { apply (LIB_agree' m6 m8 LIB6). intros a Ha. destruct (oa_lib_fp_static _ Ha) as [CS R]. apply PRES8; [right; left; exact CS|].
      cbn [outside]. clear - R FSG. unfold SEGTOP_A in *. split; [lia| exact I]. }
    assert (BYD8 : bytes_at bsegs m8 D (zbytes d')).
    { apply (bytes_at_agree bsegs m6 m8 _ _ BYD6). intros a Ha. cbv beta in Ha. unfold zbytes in Ha. rewrite length_map in Ha. unfold zlength in INLVD.
      destruct INLVD as [(p & k & Hin & P1 & P2)| (E & DL)]; [| rewrite E in Ha; cbn [length] in Ha; lia].
      apply PRES8.
      - right; right; left. exists p, k. split; [exact Hin| lia].
      - pose proof (FLV p k Hin) as X1. cbn [outside]. split; [clear - Ha P1 P2 X1; lia| exact I]. }
    assert (CP8 : forall a : word, aclient (rt_live RT Σ) [] usp (bv_unsigned a) -> m8 a = m a).
    { intros a Ha. rewrite <- (CP6 a Ha).
      apply PRES8.
      - apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; rewrite LV1; exact He| intros e []| lia].
      - cbn [outside]. split; [| exact I].
        destruct Ha as [H|[H|[H|[H|H]]]].
        + clear - H FLO LOR; ul.
        + pose proof (client_static_range _ H) as CR. clear - CR FSG; lia.
        + destruct H as (p & k & Hp & HR). rewrite <- LV1 in Hp. pose proof (FLV p k Hp) as X1. clear - HR X1; lia.
        + destruct H as (f0 & k0 & [] & _).
        + destruct H as (f0 & k0 & [] & _). }
    clear STp6 LIB6 BYD6 CP6 ST6 ART6 MI6 VR6 VS VB.
    rt_transport_nw m6 m8 AG78 ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; cbv beta; clear - Hx S1R; lia).
    clear AG78 ACL.

    assert (LOW3 : rt_sp0 RT Σ3 - STACK_WIN <= lo) by (rewrite SP8; exact LOW2).
    assert (INF3 : In (f, 3%nat) (rt_frames RT Σ3)) by (rewrite FRS8; left; reflexivity).
    pose proof VR8 as (VSZ8 & VSC8 & VCAP8 & VA08 & VAT8 & VS8 & VB8).
    assert (VC1 : vcap_after 0 0 = 1) by reflexivity.
    destruct VB8 as [(C0 & _)|(C1 & A16 & APOS & VE8)]; [exfalso; clear - C0 VC1; lia|].
    assert (INA3 : In (A3, 16 * (0 + 1)) (rt_live RT Σ3)).
    { rewrite VL8. apply in_or_app. left. unfold vblockA. rewrite VC1. cbn [Z.eqb]. apply ann_block_vis. }
    pose proof (af_live_range RT AF Σ3 m8 _ _ ART8 INA3) as (_ & A3R & _).
    pose proof (af_frames_range RT AF Σ3 m8 f 3%nat ART8 INF3) as (_ & _ & _ & FLV3). pose proof (FLV3 _ _ INA3) as A3F. change (fs_size 3) with 512 in A3F.
    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut.
    { exact (od_walkLHr (Z_to_bv 64 0x96ba4) usp S1 f A3 (A3 + 16 * (0 + 1)) (A3 + 16 * vcap_after 0 0) gp (Z_to_bv 64 0x656e70) y0 y1 y2 k1 k2 k3 k4 k5 k6 k7
               (Z_to_bv 64 (A + 16 * 0)) (Z_to_bv 64 A) s6 s9 y3 y4 y5 y6 F8 fc8 m8
               FPOS ltac:(clear - FLO LOR SPT; ul) ltac:(clear - APOS VAT8 VC1; lia) ltac:(clear - A16; Z.div_mod_to_equations; lia) VS8 MI8). }
    cbv beta. intros ms9 (m9 & a0x & -> & MU9 & WM9 & MI9 & VS9).
    apply evt_done.
    assert (FP9 : fp_ok RT Σ3 lo [(f + 40, f + 48)]).
    { apply Forall_cons; [| apply Forall_nil]; cbn [fst snd]. right; right; left. exists f, 3%nat. split; [exact INF3|]. change (fs_size 3) with 512. lia. }
    pose proof (art_of_munch RT AF Σ3 m8 m9 lo _ ART8 LOW3 FP9 MU9 WM9) as ART9.
    assert (AG89 : agree_on (fun x => ~ (f + 40 <= x < f + 48)) m8 m9)
      by (apply (agree_of_munch _ _ _ _ MU9); intros x Hx; cbn [outside]; split; [exact Hx| exact I]).
    assert (ST9 : stk bsegs m9 lo S1).
    { apply (stk_agree bsegs m8 m9 _ _ ST8); [| exact WM9]. eapply agree_sub; [exact AG89|]. intros x Hx. cbv beta in *. clear - Hx FLO S1R LOR. ul. }
    assert (STp9 : stk bsegs m9 (S1 + 440) (usp - 104)).
    { apply (stk_agree bsegs m8 m9 _ _ STp8); [| exact WM9]. eapply agree_sub; [exact AG89|]. intros x Hx. cbv beta in *. clear - Hx FLO S1R LOR. ul. }
    assert (LIB9 : LIB m9).
    { apply (LIB_agree' m8 m9 LIB8). eapply agree_sub; [exact AG89|]. intros x Hx. pose proof (proj2 (oa_lib_fp_static x Hx)). cbv beta. clear - H FSG. ul. }
    assert (CP9 : forall a : word, aclient (rt_live RT Σ) [] usp (bv_unsigned a) -> m9 a = m a).
    { intros a Ha. rewrite <- (CP8 a Ha). apply MU9. cbn [outside]. split; [| exact I].
      destruct Ha as [H|[H|[H|[H|H]]]].
      - clear - H FLO LOR; ul.
      - pose proof (client_static_range _ H) as CR. clear - CR FSG; lia.
      - destruct H as (p & k & Hp & HR). rewrite <- LV1 in Hp. pose proof (FLV p k Hp) as X1. clear - HR X1; lia.
      - destruct H as (f0 & k0 & [] & _).
      - destruct H as (f0 & k0 & [] & _). }
    clear ST8 STp8 LIB8 CP8 ART8 MI8 VR8 VS8.
    rt_transport_with m8 m9 AG89 WM9 ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; cbv beta;
        first [ clear - Hx FLO SLO FSEP S1R LOR FPOS; ul
              | rewrite ?velts_size in Hx; cbn [length app Z.of_nat] in Hx; clear - Hx A3F; lia
              | unfold zbytes in Hx; rewrite length_map in Hx; unfold zlength in INLVD;
                destruct INLVD as [(p & k & Hin & P1 & P2)|(E & _)]; [pose proof (FLV p k Hin) as X1; clear - Hx P1 P2 X1; lia| rewrite E in Hx; cbn [length] in Hx; clear - Hx; lia] ]).
    clear AG89 MU9 FP9.
    assert (VR9 : vrepA m9 (f + 32) A3 (vcap_after 0 0) (0 + 1) ([] ++ [(0, 0)])).
    { split; [exact VSZ8|]. split; [exact VSC8|]. split; [exact VCAP8|]. split; [exact VA08|]. split; [exact VAT8|]. split; [exact VS9|].
      right. split; [exact C1|]. split; [exact A16|]. split; [exact APOS| exact VE8]. }
    destruct (od_cutA_intro Σ Σ3 m m9 usp S1 f lo D act A3 (vcap_after 0 0) (0 + 1) bs d' ([] ++ [(0, 0)])
                ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ J0 j136 j176 j264 j288 j336 j376 j425 j432 _ jD jP tS _ _ _
                SPA SPT S32 S1R LOW LOR F64 FPOS FRS0 LVPOS LVB CR0 ART9 MI9 ST9 FRS8 ltac:(rewrite SP8, SP6; exact SP1)
                HA5 FD6 TL5 STp9 FRs1 FH3 VR9 ltac:(lia) WRS FDoc2 LIB9 CP9 ED' EACT BSL ltac:(rewrite <- LV1; exact VL8)
                ltac:(rewrite EOP in VCB0; rewrite vcost_pushes_S in VCB0; cbn [vcost_pushes] in VCB0, CR6; unfold FUZZ_COST, OD_VEC_COST in *; rewrite CR1 in CR6;
                      clear - VCB0 CR6 CR8 CR0; lia)
                LOW5 FP2 FS5 ltac:(unfold oa_els; rewrite EOP, EPO; reflexivity) BYD8 D0' INLV0) as (p0 & CA).
    exact (od_loop_exit K Σ m usp lo (od_chars bs) gp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 KA Σ3 S1 f A3 (vcap_after 0 0) (0 + 1) p0 ([] ++ [(0, 0)])
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F8 fc8 m9 FRM8 CA).
  -
    assert (EOP : oa_P d' = P0) by (unfold oa_P; fold P0; lia).
    destruct (od_cutA_intro Σ Σ2 m m6 usp S1 f lo D act A (vcap_iter P0 0 0) (Z.of_nat P0) bs d' (map (pview D) (poffs d'))
                ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ J0 j136 j176 j264 j288 j336 j376 j425 j432 _ jD jP tS _ _ _
                SPA SPT S32 S1R LOW LOR F64 FPOS FRS0 LVPOS LVB CR0 ART6 MI6 ST6 FRS6 ltac:(rewrite SP6; exact SP1)
                HA5 FD6 TL5 STp6 FRs1 FH3 VR6 ltac:(lia) WRS FDoc2 LIB6 CP6 ED' EACT BSL ltac:(rewrite <- LV1; exact VL6)
                ltac:(rewrite EOP in VCB0; unfold FUZZ_COST, OD_VEC_COST in *; rewrite CR1 in CR6; clear - VCB0 CR6 CR0; lia)
                LOW5 FP2 FS5 ltac:(unfold oa_els; rewrite EOP; fold P0; rewrite Nat.sub_diag; cbn [repeat]; rewrite app_nil_r; reflexivity) BYD6 D0' INLV0) as (p0 & CA).
    exact (od_loop_exit K Σ m usp lo (od_chars bs) gp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 KA Σ2 S1 f A (vcap_iter P0 0 0) (Z.of_nat P0) p0 (map (pview D) (poffs d'))
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F6 fc6 m6 FRM6 CA).
Qed.
End PhaseA.
