(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun Stdio AtpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_stage1_kit Atp_h_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_hkit2 Sj_new Sj_h_dtor. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Sj_hkitB Atp_fzwA Atp_h_defsA Atp_h_vkitA Atp_h_vkit2A Pj_lftoi1A Atp_h_pushA Atp_h_pushcA Atp_h_findA Atp_h_splitA Atp_h_splitintowA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma shadow16_split : forall (m : mem) a (js : list byte), rw_cells asegs m a [CB 16 js] ->
  exists ls t, length ls = 12%nat /\ length t = 4%nat /\ rw_cells asegs m a (si_shadow0 (ls ++ t)).
Proof.
  intros m a js H.
  apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1]%nat) in H; [| reflexivity]. cbn [mk_CB_cells app] in H.
  lazymatch type of H with rw_cells _ _ _ [CB 1 ?x0; CB 1 ?x1; CB 1 ?x2; CB 1 ?x3; CB 1 ?x4; CB 1 ?x5; CB 1 ?x6; CB 1 ?x7; CB 1 ?x8; CB 1 ?x9; CB 1 ?x10; CB 1 ?x11;
                                         CB 1 ?x12; CB 1 ?x13; CB 1 ?x14; CB 1 ?x15] =>
    exists [x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11], [x12; x13; x14; x15] end.
  split; [reflexivity|]. split; [reflexivity|]. exact H.
Qed.

Lemma frame120_split : forall (m : mem) f (js : list byte), rw_cells asegs m f [CB 120 js] ->
  exists h0 h1 h2 h3 jv jr, rw_cells asegs m f [CB 8 h0; CB 8 h1; CB 8 h2; CB 8 h3; CB 24 jv; CB 64 jr].
Proof.
  intros m f js H.
  apply (rw_cells_split_CB asegs _ _ [] 120 _ [] [8; 8; 8; 8; 24; 64]%nat) in H; [| reflexivity]. cbn [mk_CB_cells app] in H.
  lazymatch type of H with rw_cells _ _ _ [CB 8 ?x0; CB 8 ?x1; CB 8 ?x2; CB 8 ?x3; CB 24 ?x4; CB 64 ?x5] => exists x0, x1, x2, x3, x4, x5 end. exact H.
Qed.

Section SplitInto.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTF : rt_contracts_f RT.
Hypothesis SM1 : stack_malloc1_contract RT.
Hypothesis SPLIT : split_cpsA RT.

Local Ltac ul := unfold ATPA_SPLITINTO_STACK, ATPA_SPLIT_STACK, ATPA_PUSH_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Theorem splitinto_ok : splitinto_cpsA RT.
Proof using AF RTF SM1 SPLIT.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m RV FD D d jv lo
    FDO MST -> -> -> PB LBYT LL D0 DPOS INLV LPOS FOBJ0 VJ UFD FDT FD8 FDC LVB CRB FRB ART0 MI0 ST0 LOW LOR SPT SPA FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_client_consts RT AF Σ m ART0) as CC.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP in Hk.
  pose proof FOBJ0 as (V8 & _ & (f0 & kf0 & INF0 & FLO0 & FHI0) & SHB0). change ((24 + 7) / 8) with 3 in FHI0, SHB0.
  pose proof (fframe_ranges RT AF Σ m f0 kf0 ART0 INF0) as (F00 & F01 & FSZ0 & SH00 & SH01).
  set (L := zlength d) in *. unfold zlength in L.
  assert (LBL : length (to_bytes d) = length d) by (unfold to_bytes; apply length_map).

  destruct (si_prologue usp lo RV FD ra gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m
              ST0 ltac:(ul) ltac:(ul) ltac:(ul) SPA ltac:(ul) ltac:(ul) CC MI0) as (sp' & SPR & SPA' & W0).
  rewrite <- ESP in W0.
  lazymatch type of W0 with evt asegs _ ?X0 => assert (W0' : forall ms, eq X0 ms -> evt asegs _ ms) by (intros ms <-; exact W0) end. clear W0.
  apply (cps_realizes asegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W0') Hc). clear W0'. intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & a1' & a2' & j0 & j1 & j2 & -> & MU1 & WM1 & MI1 & ST1 & FRl1 & STp1 & FRs1) & Hc1'). clear Hc1.
  assert (FPS : fp_client RT Σ lo [(sp', usp)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).
  pose proof (art_fp_client RT AF Σ m m1 lo _ ART0 LOW FPS MU1 WM1) as ART1.
  pose proof (fobj_munch RT AF Σ m m1 lo _ RV 24 ART0 LOW FPS MU1 FOBJ0) as FOBJ1.
  assert (EU1 : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; ul).
  assert (COK : forall Σx m', rt_sp0 RT Σx = rt_sp0 RT Σ -> stk asegs m' lo sp' -> call_ok RT Σx m' (Z_to_bv 64 sp') lo).
  { intros Σx m' SPx STx. unfold call_ok. rewrite EU1, SPx. split; [exact STx|]. split; [ul|]. split; [ul|]. split; [ul|]. clear - SPA'. Z.div_mod_to_equations. lia. }

  apply (SM1 Σ PMc (Z_to_bv 64 0xb201c) (Z_to_bv 64 sp') gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') (Z_to_bv 64 96) a1' a2' a3 a4 a5 a6 a7
           s2 (Z_to_bv 64 FD) (Z_to_bv 64 RV) s5 s6 s7 s8 (Z_to_bv 64 SHB) s10 s11 t3 t4 t5 t6 F fc m1 lo FDO MST eq_refl ltac:(lia) ltac:(pose proof (vcost_pushes_nonneg (length (poffs d)) 0 0 ltac:(lia)); lia) ART1 MI1 (COK Σ m1 eq_refl ST1) ltac:(intros Efr0; exfalso; rewrite Efr0 in INF0; exact INF0) _ _ Hc1').
  intros c2 (Σ1 & f & Hc2 & FRS1 & LV1 & SP1 & CR1 & F0 & F64 & FTOP).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WRF & WRS) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even 0xb201c) in Hc2' by lia.
  change (fs_size 1 - 8) with 120 in WRF. change (fs_size 1 / 8) with 16 in WRS. change (fs_size 1) with 128 in FTOP.

  assert (INF : In (f, 1%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  pose proof (fframe_ranges RT AF Σ1 m2 f 1%nat ART2 INF) as (_ & F1 & _ & SHF0 & SHF1). change (fs_size 1) with 128 in F1, SHF1. rewrite SP1 in F1, SHF1.
  pose proof (af_frames_range RT AF Σ1 m2 f 1%nat ART2 INF) as (_ & _ & FSEG & FLV). change (fs_size 1) with 128 in FSEG, FLV.
  pose proof (af_fshadow_apart RT AF Σ1 m2 f 1%nat ART2 INF) as [FSL FSF]. change (fs_size 1) with 128 in FSL, FSF.
  assert (NEWF : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) usp a -> ~ (f <= a < f + 128) /\ ~ (shad f <= a < shad (f + 128))).
  { intros a Ha. exact (newframe_apart RT AF Σ Σ1 m2 f 1%nat usp a ART2 FRS1 LV1 SP1 ltac:(ul) Ha). }
  assert (INF01 : In (f0, kf0) (rt_frames RT Σ1)) by (rewrite FRS1; right; exact INF0).
  pose proof (af_frames_disj RT AF Σ1 m2 f 1%nat f0 kf0 [] (rt_frames RT Σ) ART2 FRS1 INF0) as FDJ. change (fs_size 1) with 128 in FDJ.
  pose proof (FSF f0 kf0 INF01) as FSDJ. pose proof (FSF f 1%nat INF) as FSELF. change (fs_size 1) with 128 in FSELF.
  assert (SHF16 : shad (f + 128) = shad f + 16) by (unfold shad; Z.div_mod_to_equations; lia). rewrite SHF16 in SHF1, FSELF, FSL, FSF.
  pose proof (af_fshadow_apart RT AF Σ1 m2 f0 kf0 ART2 INF01) as [F0SL F0SF]. pose proof (F0SF f 1%nat INF) as F0S_F. change (fs_size 1) with 128 in F0S_F.
  assert (SHAPART : shad (f0 + fs_size kf0) <= shad f \/ shad (f + 128) <= shad f0).
  { unfold shad. destruct FDJ as [X|X]; [pose proof (Z.div_le_mono _ _ 8 ltac:(lia) X) | pose proof (Z.div_le_mono _ _ 8 ltac:(lia) X)]; lia. }

  destruct (wr_at_rw_CB m2 f 120 WRF ltac:(lia)) as (jf & JF). change (Z.to_nat 120) with 120%nat in JF.
  destruct (frame120_split m2 f jf JF) as (h0 & h1 & h2 & h3 & jv0 & jr & FH2). clear JF jf.
  destruct (wr_at_rw_CB m2 (shad f) 16 WRS ltac:(lia)) as (js & JS). change (Z.to_nat 16) with 16%nat in JS.
  destruct (shadow16_split m2 (shad f) js JS) as (ls & tt & LS & LT & FS2). clear JS js.
  assert (FRl2 : rw_cells asegs m2 sp' [CB 8 j0; CB 8 j1; CB 8 j2]).
  { apply (rw_cells_agree asegs m1 m2 _ _ FRl1); [| exact WM2]. apply (agree_of_pres _ _ _ _ _ _ PRES2). intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. ul. }

  pose proof (si_walk1 usp sp' f lo RV FD gp (Z_to_bv 64 0x6a7e68) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s2 s5 s6 s7 s8 s10 s11 u3 u4 u5 u6 j0 j1 j2 h0 h1 h2 h3 jv0 jr ls tt F2 fc m2
                LS LT F0 ltac:(ul) ltac:(ul) SHF0 FSELF ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) FRl2 FH2 FS2 MI2) as W1.
  lazymatch type of W1 with evt asegs _ ?X0 => assert (W1' : forall ms, eq X0 ms -> evt asegs _ ms) by (intros ms <-; exact W1) end. clear W1.
  apply (cps_realizes asegs _ _ _ c2 (asta_evt_c RT AF Σ1 PMc _ _ MST W1') Hc2'). clear W1'. intros c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (m3 & -> & MU3 & WM3 & MI3 & FRl3 & FH3 & FS3) & Hc3'). clear Hc3.

  assert (ARTW : forall (Σx : rts RT) mA mB W, ART RT Σx mA -> munch W mA mB -> wmono asegs mA mB -> rt_sp0 RT Σx = rt_sp0 RT Σ -> In (f, 1%nat) (rt_frames RT Σx) ->
            In (f0, kf0) (rt_frames RT Σx) ->
            (forall x, (lo <= x < USTACK_TOP) \/ (f <= x < f + 120) \/ (shad f <= x < shad f + 16) \/ (RV <= x < RV + 24) \/ outside W x) -> ART RT Σx mB).
  { intros Σx mA mB W HA MU WM SPx INFx INF0x HW. apply (art_client_write RT AF Σx mA mB lo HA ltac:(rewrite SPx; exact LOW)); [| exact WM].
    intros a Ha. destruct (HW (bv_unsigned a)) as [X|[X|[X|[X|O]]]]; [exfalso; apply Ha| exfalso; apply Ha| exfalso; apply Ha| exfalso; apply Ha| apply MU; exact O].
    - left. exact X.
    - right; right; right; left. exists f, 1%nat. change (fs_size 1) with 128. split; [exact INFx| lia].
    - right; right; right; right. exists f, 1%nat. rewrite SHF16. split; [exact INFx| lia].
    - right; right; right; left. exists f0, kf0. split; [exact INF0x| lia]. }
  assert (ART3 : ART RT Σ1 m3).
  { apply (ARTW Σ1 m2 m3 _ ART2 MU3 WM3 SP1 INF INF01). intros x. unfold si_W1. cbn [outside]. clear - SPR LOR SPT. ul. }

  assert (CLV : forall (Σx : rts RT) sp0 x, In (f0, kf0) (rt_frames RT Σx) -> RV <= x < RV + 24 -> aclient (rt_live RT Σx) (rt_frames RT Σx) sp0 x).
  { intros Σx sp0 x INx Hx. right; right; right; left. exists f0, kf0. split; [exact INx| lia]. }
  assert (CLVS : forall (Σx : rts RT) sp0 x, In (f0, kf0) (rt_frames RT Σx) -> shad RV <= x < shad RV + 3 -> aclient (rt_live RT Σx) (rt_frames RT Σx) sp0 x).
  { intros Σx sp0 x INx Hx. right; right; right; right. exists f0, kf0. split; [exact INx|].
    pose proof (fobj_shadow_range RT AF Σ m RV 24 ART0 FOBJ0) as (f9 & c9 & IN9 & S1 & S2 & _). change ((24 + 7) / 8) with 3 in S2.
    unfold shad in *. pose proof (Z.div_le_mono f0 RV 8 ltac:(lia) ltac:(lia)).
    assert ((RV + 24) / 8 <= (f0 + fs_size kf0) / 8) by (apply Z.div_le_mono; lia). Z.div_mod_to_equations. lia. }
  assert (RVSH : shad f0 <= shad RV /\ shad RV + 3 <= shad (f0 + fs_size kf0)).
  { unfold shad. pose proof (Z.div_le_mono f0 RV 8 ltac:(lia) ltac:(lia)). assert ((RV + 24) / 8 <= (f0 + fs_size kf0) / 8) by (apply Z.div_le_mono; lia). Z.div_mod_to_equations. lia. }
  assert (FOBJ3 : fobj RT Σ1 m3 RV 24).
  { destruct FOBJ1 as (A8 & N0 & _ & HB). split; [exact A8|]. split; [exact N0|]. split; [exists f0, kf0; split; [exact INF01| split; [exact FLO0| exact FHI0]]|].
    apply (bytes_at_agree asegs m1 m3 _ _ HB). intros a Ha. rewrite repeat_length in Ha. change (Z.of_nat (Z.to_nat ((24 + 7) / 8))) with 3 in Ha.
    rewrite (MU3 a). 2:{ unfold si_W1. cbn [outside]. split; [ul|]. split; [destruct F0S_F; lia|]. split; [| exact I]. rewrite SHF16 in SHAPART. destruct SHAPART; lia. }
    apply PRES2. apply (CLVS Σ sp'); [exact INF0| exact Ha]. }
  assert (VJ3 : rw_cells asegs m3 RV [CB 24 jv]).
  { apply (rw_cells_agree asegs m1 m3 _ _); [apply (rw_cells_agree asegs m m1 _ _ VJ); [| exact WM1]| | exact (wmono_trans _ _ _ _ WM2 WM3)].
    - apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbn [outside]. split; [ul| exact I].
    - intros a Ha. cbv beta in Ha. cbn [cells_size csize Nat.add] in Ha. rewrite (MU3 a). 2:{ unfold si_W1. cbn [outside]. split; [ul|]. split; [destruct FDJ; lia|]. split; [| exact I]. destruct FSDJ; lia. }
      apply PRES2. apply (CLV Σ sp'); [exact INF0| lia]. }
  assert (ST3 : stk asegs m3 lo sp').
  { apply (stk_agree asegs m2 m3 _ _ ST2); [| exact WM3]. apply (agree_of_munch _ _ _ _ MU3). intros x Hx. unfold si_W1. cbn [outside]. split; [lia|]. split; [ul|]. split; [ul| exact I]. }

  pose proof FOBJ3 as (_ & _ & _ & SHB3). change ((24 + 7) / 8) with 3 in SHB3.
  apply ((rf_asan_memset RT RTF) Σ1 PMc (Z_to_bv 64 0xb20c8) (Z_to_bv 64 sp') gp (Z_to_bv 64 0x6a7e68) u0 u1 u2 (Z_to_bv 64 usp) (Z_to_bv 64 sp')
           (Z_to_bv 64 RV) (Z_to_bv 64 0) (Z_to_bv 64 24) (Z_to_bv 64 (-13)) (Z_to_bv 64 (-8)) b5 b6 b7 (Z_to_bv 64 f) (Z_to_bv 64 FD) (Z_to_bv 64 RV) s5 s6
           (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) s10 s11 u3 u4 u5 u6
           F2 fc m3 RV 24 (Z_to_bv 8 0) lo FDO MST eq_refl eq_refl eq_refl ltac:(ul) ltac:(lia));
    [| exact ART3| exact MI3| exact (COK Σ1 m3 SP1 ST3)| split; [exact Hc3'| apply (cfrm0_of_asta RT Σ1 PMc (eq _) c3 Hc3'); intros ms0 <-; exact FRM] |].
  { unfold checked_dst. rewrite EU1. split; [| split; [| exact (rw_cells_wr_at asegs m3 RV _ 24 VJ3 ltac:(cbn; lia))]].
    - intros _. split; [exact (acc_zero_run asegs m3 RV 3 V8 ltac:(lia) SHB3)|]. right; left. exists f0, kf0. split; [exact INF01| lia].
    - intros i Hi. apply (CLV Σ1 sp'); [exact INF01| lia]. }
  intros c4 (Hc4 & FC4).
  destruct (ASTA_unpack_f RT Σ1 _ _ c4 Hc4 FC4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & BY4) & FRM4 & Hc4'). clear Hc4.
  destruct RS4 as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F4 & fc4 & ->).
  cbn [ms_fcsr] in FRM4. rewrite EU1 in ST4, PRES4. rewrite (ret_pc_even 0xb20c8) in Hc4' by lia.
  assert (VR4 : vrepA m4 RV 0 0 0 []).
  { unfold vrepA. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [| left; split; reflexivity].
    change (0 + 16 * 0) with 0. apply rw_cells_of_bytes; [cbn; repeat split; exact I| exact BY4|].
    cbn [cells_size csize Nat.add]. apply (wr_at_transport asegs m3 m4 RV 24 (rw_cells_wr_at asegs m3 RV _ 24 VJ3 ltac:(cbn; lia)) WM4). }

  assert (AGS4 : forall a : word, sp' <= bv_unsigned a < usp -> m4 a = m3 a) by (intros a Ha; apply PRES4; [left; ul| ul]).
  assert (FRl4 : rw_cells asegs m4 sp' [CB 8 j0; C8 (Z_to_bv 64 f); CB 8 j2]).
  { apply (rw_cells_agree_nw asegs m3 m4 _ _ FRl3). intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply AGS4. lia. }
  assert (AGF4 : forall a : word, f <= bv_unsigned a < f + 120 -> m4 a = m3 a).
  { intros a Ha. apply PRES4; [| destruct FDJ; lia]. right; right; right; left. exists f, 1%nat. change (fs_size 1) with 128. split; [exact INF| lia]. }
  assert (AGH4 : forall a : word, shad f <= bv_unsigned a < shad f + 16 -> m4 a = m3 a).
  { intros a Ha. apply PRES4; [| destruct FSDJ; lia]. right; right; right; right. exists f, 1%nat. rewrite SHF16. split; [exact INF| lia]. }
  assert (FH4 : rw_cells asegs m4 f (si_hdr h3 jv0 jr)).
  { apply (rw_cells_agree_nw asegs m3 m4 _ _ FH3). intros a Ha. unfold si_hdr in Ha. cbn [cells_size csize Nat.add] in Ha. apply AGF4. lia. }
  assert (FS4 : rw_cells asegs m4 (shad f) (si_shadow (-8) (-8) (-8) tt)).
  { apply (rw_cells_agree_nw asegs m3 m4 _ _ FS3). intros a Ha. unfold si_shadow in Ha. rewrite <- (app_nil_r tt) in Ha.
    do 4 (destruct tt as [|? tt]; [discriminate LT|]). destruct tt; [| discriminate LT]. cbn [map app repeat cells_size csize Nat.add] in Ha. apply AGH4. lia. }
  rewrite app_nil_r in FS4 || idtac.
  assert (STp4 : stk asegs m4 (sp' + 24) (usp - 104)).
  { apply (stk_agree_nw asegs m1 m4 _ _ STp1). intros a Ha. cbv beta in Ha. rewrite (AGS4 a) by lia. rewrite (MU3 a). 2:{ unfold si_W1. cbn [outside]. split; [lia|]. split; [ul|]. split; [ul| exact I]. }
    apply PRES2. left. lia. }
  assert (FRs4 : rw_cells asegs m4 (usp - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { apply (rw_cells_agree_nw asegs m1 m4 _ _ FRs1). intros a Ha. unfold fa_saved in Ha. cbn [cells_size csize Nat.add] in Ha. rewrite (AGS4 a) by lia.
    rewrite (MU3 a). 2:{ unfold si_W1. cbn [outside]. split; [lia|]. split; [ul|]. split; [ul| exact I]. } apply PRES2. left. lia. }
  assert (FDC4 : rw_cells asegs m4 FD [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 L)]).
  { unfold L. apply (rw_cells_agree_nw asegs m m4 _ _ FDC). intros a Ha. cbn [cells_size csize Nat.add] in Ha. rewrite (PRES4 a); [| left; ul| ul].
    rewrite (MU3 a). 2:{ unfold si_W1. cbn [outside]. split; [ul|]. split; [ul|]. split; [ul| exact I]. } rewrite (PRES2 a) by (left; ul). apply MU1. cbn [outside]. split; [ul| exact I]. }
  assert (BLO : rt_sp0 RT Σ - STACK_WIN + 16 <= sp') by (clear - LOW LOR SPR; ul).
  assert (PB4 : bytes_at asegs m4 D (to_bytes d)).
  { apply (bytes_at_agree asegs m m4 _ _ PB). intros a Ha. rewrite LBL in Ha.
    destruct INLV as [(pk & nk & INK & PK1 & PK2)|(DN & DLO)]; [| rewrite DN in Ha; cbn in Ha; lia]. unfold zlength in PK2.
    pose proof (af_live_range RT AF Σ m pk nk ART0 INK) as (K0 & K1 & _).
    assert (INK1 : In (pk, nk) (rt_live RT Σ1)) by (rewrite LV1; exact INK).
    pose proof (FLV pk nk INK1) as X1. pose proof (FSL pk nk INK1) as X2.
    pose proof (proj2 (proj2 (proj2 (af_frames_range RT AF Σ m f0 kf0 ART0 INF0))) pk nk INK) as X3.
    rewrite (PRES4 a); [| right; right; left; exists pk, nk; split; [exact INK1| lia]| clear - X3 FLO0 FHI0 PK1 PK2 Ha; lia].
    rewrite (MU3 a). 2:{ clear - X1 X2 PK1 PK2 Ha K1 BLO. unfold si_W1. cbn [outside]. lia. }
    rewrite (PRES2 a); [| right; right; left; exists pk, nk; split; [exact INK| lia]]. apply MU1. clear - PK1 PK2 Ha K1 BLO. cbn [outside]. lia. }

  assert (CAL4 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> outside [(RV, RV + 24); (FD, FD + 16)] (bv_unsigned a) -> m4 a = m a).
  { intros a Ha Hout. cbn [outside] in Hout. destruct Hout as (HO1 & HO2 & _). destruct (NEWF _ Ha) as [NF1 NF2]. rewrite SHF16 in NF2.
    pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha) as SPL.
    rewrite (PRES4 a); [| rewrite LV1, FRS1; apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| intros e He; right; exact He| clear - SPR; lia]| clear - HO1; lia].
    rewrite (MU3 a). 2:{ clear - SPL NF1 NF2 BLO SPR. unfold si_W1. cbn [outside]. lia. }
    rewrite (PRES2 a); [| apply (aclient_mono _ _ _ _ _ _ _ Ha); auto; clear - SPR; lia]. apply MU1. clear - SPL BLO SPR. cbn [outside]. lia. }
  assert (FOBJ4 : fobj RT Σ1 m4 RV 24).
  { apply (fobj_agree RT AF Σ1 Σ1 m3 m4 RV 24 ART3 FOBJ3 eq_refl). intros a Ha. cbv beta in Ha. change ((24 + 7) / 8) with 3 in Ha.
    pose proof (F0SF f0 kf0 INF01) as F0SELF. apply PRES4; [exact (CLVS Σ1 sp' _ INF01 Ha)| clear - Ha RVSH F0SELF FLO0 FHI0; lia]. }
  assert (FHm : rw_cells asegs m4 f [C8 (Z_to_bv 64 0x41b58ab3)]).
  { pose proof FH4 as X. unfold si_hdr in X.
    lazymatch type of X with rw_cells _ _ _ (?c0 :: ?rest) => change (c0 :: rest) with ([c0] ++ rest) in X end.
    apply Sj_stage1_kit.rw_cells_app in X. exact (proj1 X). }
  clear FRl1 FRl2 FRl3 FH2 FH3 FS2 FS3 VJ3 FOBJ3 SHB3 WRF WRS Hc1' Hc2' Hc3'.

  assert (DHI : D + L <= USTACK_TOP).
  { destruct INLV as [(pk & nk & INK & PK1 & PK2)|(DN & DLO)].
    - pose proof (af_live_range RT AF Σ m pk nk ART0 INK) as (_ & K1 & _). clear - K1 PK2 SP0R. ul.
    - subst d. clear - DLO. cbn in L. subst L. unfold SEGTOP_A, USTACK_TOP in *. lia. }
  assert (L0 : 0 <= L) by (subst L; lia). assert (EUU : bv_unsigned (Z_to_bv 64 usp) = usp) by (rewrite <- ESP; reflexivity).
  assert (FLO : f + 128 <= lo) by (clear - F1 LOW; lia). assert (SLO : shad f + 16 <= lo) by (clear - SHF1 LOW; lia).

  assert (TAIL : forall (Σs : rts RT) (ms : mem) (A' : Z) (rax x0 x1 x2 a0x a1x a2x a3x a4x a5x a6x a7x s5x s6x s10x s11x x3 x4 x5 x6 : word) Fx fcx cT,
    frm0 fcx -> ART RT Σs ms -> mem_inv asegs ms -> stk asegs ms lo sp' -> rt_frames RT Σs = rt_frames RT Σ1 -> rt_sp0 RT Σs = rt_sp0 RT Σ ->
    vliveA (rt_live RT Σs) A' (vcap_iter (length (poffs d)) 0 0) (zlength (poffs d)) (rt_live RT Σ) ->
    rt_credit RT Σ - 1 - vcost_pushes (length (poffs d)) 0 0 <= rt_credit RT Σs ->
    rw_cells asegs ms sp' [CB 8 j0; C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 (f + 32))] \/ rw_cells asegs ms sp' [CB 8 j0; C8 (Z_to_bv 64 f); CB 8 j2] ->
    stk asegs ms (sp' + 24) (usp - 104) -> rw_cells asegs ms (usp - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells asegs ms f [C8 (Z_to_bv 64 0x41b58ab3)] -> rw_cells asegs ms (shad f) (si_shadow (-8) (-8) (-8) tt) ->
    (forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> outside [(RV, RV + 24); (FD, FD + 16)] (bv_unsigned a) -> ms a = m a) ->
    vrepA ms RV A' (vcap_iter (length (poffs d)) 0 0) (zlength (poffs d)) (map (pview D) (poffs d)) ->
    rw_cells asegs ms FD [C8 (Z_to_bv 64 (D + L)); C8 (Z_to_bv 64 0)] ->
    ASTA RT Σs PMc (eq (si_regs 0xb21b8 rax sp' gp (Z_to_bv 64 0x6a7e68) x0 x1 x2 usp a0x a1x a2x a3x a4x a5x a6x a7x f FD RV s5x s6x
                          s10x s11x x3 x4 x5 x6 Fx fcx ms)) cT ->
    realizes asegs cT T).
  { intros Σs ms A' rax x0 x1 x2 a0x a1x a2x a3x a4x a5x a6x a7x s5x s6x s10x s11x x3 x4 x5 x6 Fx fcx cT
           FRMx ARTs MIs STs FRSs SPs VLs CRs FRls STps FRss FHs FSs CALs VRs FDCs HcT.
    assert (INFs : In (f, 1%nat) (rt_frames RT Σs)) by (rewrite FRSs; exact INF).
    assert (INF0s : In (f0, kf0) (rt_frames RT Σs)) by (rewrite FRSs; exact INF01).
    pose proof (si_rel1 usp sp' f FD RV rax gp (Z_to_bv 64 0x6a7e68) x0 x1 x2 a0x a1x a2x a3x a4x a5x a6x a7x s5x s6x s10x s11x x3 x4 x5 x6
                  (-8) (-8) (-8) tt [] Fx fcx ms LT F0 ltac:(clear - F1 SP0R; ul) SHF0 FSELF FHs FSs MIs) as W5.
    lazymatch type of W5 with evt asegs _ ?X0 => assert (W5' : forall q, eq X0 q -> evt asegs _ q) by (intros q <-; exact W5) end. clear W5.
    apply (cps_realizes asegs _ _ _ cT (asta_evt_c RT AF Σs PMc _ _ MST W5') HcT). clear W5'. intros c6 Hc6.
    destruct (ASTA_unpack RT Σs _ _ c6 Hc6) as (ms6 & (m6 & -> & MU6 & WM6 & MI6) & Hc6'). clear Hc6.
    assert (ART6 : ART RT Σs m6).
    { apply (ARTW Σs ms m6 _ ARTs MU6 WM6 SPs INFs INF0s). intros x. cbn [outside]. clear. lia. }

    destruct (af_frame_release RT AF Σs m6 f 1%nat (rt_frames RT Σ) ART6 ltac:(rewrite FRSs; exact FRS1)) as (Σ4 & fl & FLC & NAC & FL0 & FLW & FW & REL).
    change (fs_size 1) with 128 in FW. replace (f + 128 - 8) with (f + 120) in FW by lia. rewrite SPs in FLW.
    assert (AG6 : forall a : word, lo <= bv_unsigned a -> m6 a = ms a). { intros a Ha. apply MU6. cbn [outside]. clear - Ha FLO SLO. lia. }
    assert (FRl6 : exists loc, Z.of_nat (cells_size loc) = 24 /\ rw_cells asegs m6 sp' loc).
    { destruct FRls as [X|X]; [exists [CB 8 j0; C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 (f + 32))]| exists [CB 8 j0; C8 (Z_to_bv 64 f); CB 8 j2]]; (split; [reflexivity|]); apply (rw_cells_agree_nw asegs ms m6 _ _ X); intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply AG6; clear - Ha SPR LOR; ul. }
    destruct FRl6 as (loc & LOC & FRl6).
    assert (STp6 : stk asegs m6 (sp' + 24) (usp - 104)). { apply (stk_agree_nw asegs ms m6 _ _ STps). intros a Ha. cbv beta in Ha. apply AG6. clear - Ha SPR LOR; ul. }
    assert (ST6 : stk asegs m6 lo sp'). { apply (stk_agree_nw asegs ms m6 _ _ STs). intros a Ha. cbv beta in Ha. apply AG6. clear - Ha; lia. }
    assert (FRs6 : rw_cells asegs m6 (usp - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
    { apply (rw_cells_agree_nw asegs ms m6 _ _ FRss). intros a Ha. unfold fa_saved in Ha. cbn [cells_size csize Nat.add] in Ha. apply AG6. clear - Ha SPR LOR; ul. }
    pose proof (si_rel2 usp sp' f fl lo FD RV rax gp (Z_to_bv 64 0x6a7e68) x0 x1 x2 (Z_to_bv 64 (-11)) a1x a2x a3x a4x a5x a6x a7x s5x s6x s10x s11x x3 x4 x5 x6
                  ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 loc Fx fcx m6
                  LOC ST6 ltac:(clear - SPR LOR; ul) ltac:(clear - SPR; lia) ltac:(clear - SPT; ul) ltac:(clear - LOW SP0R; ul) F0 FLO FL0 ltac:(clear - FLW LOW; lia)
                  FRl6 STp6 FRs6 FW FLC MI6) as W6.
    lazymatch type of W6 with evt asegs _ ?X0 => assert (W6' : forall q, eq X0 q -> evt asegs _ q) by (intros q <-; exact W6) end. clear W6.
    apply (cps_realizes asegs _ _ _ c6 (asta_evt_c RT AF Σs PMc _ _ MST W6') Hc6'). clear W6'. intros c7 Hc7.
    destruct (ASTA_unpack RT Σs _ _ c7 Hc7) as (ms7 & (m7 & -> & MU7 & WM7 & MI7 & ST7 & FL7) & Hc7'). clear Hc7.
    destruct (REL m7 MU7 WM7 FL7) as (ART7 & FRS4 & LV4 & SP4 & CR4 & AL4 & AM4).
    assert (NFL : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) usp x -> x <> fl).
    { intros x Hx E. subst x. destruct Hx as [H|[H|[H|[H|H]]]].
      - clear - H FLW LOW LOR SPR. ul.
      - apply NAC. right; left. exact H.
      - apply NAC. right; right; left. rewrite VLs. apply (proj2 (in_live_app _ _ _)). right. exact H.
      - apply NAC. right; right; right; left. destruct H as (f9 & k9 & Hin & R). exists f9, k9. split; [rewrite FRSs, FRS1; right; exact Hin| exact R].
      - apply NAC. right; right; right; right. destruct H as (f9 & k9 & Hin & R). exists f9, k9. split; [rewrite FRSs, FRS1; right; exact Hin| exact R]. }
    apply Hk. split; [| apply (cfrm0_of_asta RT Σs PMc (eq _) c7 Hc7'); intros ms0 <-; exact FRMx].
    exists Σ4, A'. rewrite !EUU.
    split; [| split; [rewrite LV4; exact VLs| split; [exact FRS4| split; [rewrite SP4; exact SPs| rewrite CR4; exact CRs]]]].
    eapply ASTA_conseq; [exact (ASTA_switch RT Σs Σ4 PMc _ c7 Hc7' AL4 AM4)|]. intros q <-. exists (Z_to_bv 64 fl), m7.
    split; [unfold ret_st; do 16 eexists; reflexivity|].
    split; [split; [exact ART7| split; [exact MI7| exact ST7]]|].
    assert (AG7 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> m7 a = ms a).
    { intros a Ha. destruct (NEWF _ Ha) as [NF1 NF2]. rewrite SHF16 in NF2. rewrite (MU7 a); [apply MU6| cbn [outside]; split; [| exact I]; intros E; exact (NFL _ Ha ltac:(clear - E; lia))].
      cbn [outside]. clear - NF1 NF2. lia. }
    split; [| split].
    - intros a Ha Hout. rewrite (AG7 a Ha). exact (CALs a Ha Hout).
    - apply (vrepA_agree_nw ms m7 _ _ _ _ _ VRs). intros a [Ha|Ha]; [apply AG7; apply (CLV Σ usp); [exact INF0| exact Ha]|].
      pose proof VRs as (Es & Rs & _ & _ & _ & _ & BLK). destruct BLK as [(C0 & _)|(C1 & _ & _ & _)]; [exfalso; clear - Ha C0 Rs; lia|].
      assert (INA : In (A', 16 * zlength (poffs d)) (rt_live RT Σs)).
      { rewrite VLs. apply in_or_app. left. unfold vblockA. destruct (Z.eqb_spec (vcap_iter (length (poffs d)) 0 0) 0); [exfalso; clear - C1 e; lia|]. apply ann_block_vis. }
      pose proof (proj2 (proj2 (proj2 (af_frames_range RT AF Σs ms f 1%nat ARTs INFs))) _ _ INA) as Y1. change (fs_size 1) with 128 in Y1.
      pose proof (proj1 (af_fshadow_apart RT AF Σs ms f 1%nat ARTs INFs) _ _ INA) as Y2. rewrite SHF16 in Y2.
      rewrite (MU7 a); [apply MU6; cbn [outside]; clear - Ha Y1 Y2; lia|].
      cbn [outside]. split; [| exact I]. intros E. apply NAC. right; right; left. exists A', (16 * zlength (poffs d)). split; [exact INA| clear - E Ha; lia].
    - apply (rw_cells_agree_nw asegs ms m7 _ _ FDCs). intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply AG7. left. clear - Ha UFD FDT. lia. }
  destruct (list_eq_dec Z.eq_dec d []) as [DZ|DZ].
  -
    subst d. assert (L00 : L = 0) by reflexivity. clearbody L. subst L.
    assert (SHZFD : shz m4 FD 16) by (apply (shz_stackv RT AF Σ1 m4 FD 16 ART4); [rewrite SP1; clear - UFD LOW LOR; ul| lia| clear - FDT; lia]).
    pose proof (si_walk2e usp sp' f RV FD D gp (Z_to_bv 64 0x6a7e68) v0 v1 v2 (Z_to_bv 64 RV) d1 d2 d3 d4 d5 d6 d7 s5 s6 s10 s11 v3 v4 v5 v6 F4 fc4 m4
                  ltac:(clear - UFD LOR LOW SP0R; ul) ltac:(clear - FDT; ul) ltac:(clear - F0 FTOP; ul) ltac:(clear - D0 DHI L0; ul) SHZFD FDC4 MI4) as W2.
    lazymatch type of W2 with evt asegs _ ?X0 => assert (W2' : forall ms, eq X0 ms -> evt asegs _ ms) by (intros ms <-; exact W2) end. clear W2.
    apply (cps_realizes asegs _ _ _ c4 (asta_evt_c RT AF Σ1 PMc _ _ MST W2') Hc4'). clear W2'. intros c5 Hc5.
    destruct (ASTA_unpack RT Σ1 _ _ c5 Hc5) as (ms5 & <- & Hc5'). clear Hc5.
    apply (TAIL Σ1 m4 0 (Z_to_bv 64 0xb20c8) v0 v1 v2 (Z_to_bv 64 0) d1 (Z_to_bv 64 0) d3 d4 d5 d6 d7 (Z_to_bv 64 (FD + 8)) s6 (Z_to_bv 64 (shad (FD + 8))) s11 v3 v4 v5 v6 F4 fc4 c5
             FRM4 ART4 MI4 ST4 eq_refl SP1);
      [unfold vliveA; cbn; exact LV1| cbn [length poffs vcost_pushes]; rewrite CR1; lia| right; exact FRl4| exact STp4| exact FRs4| exact FHm| exact FS4| exact CAL4
      | cbn [length poffs vcap_iter zlength Z.of_nat map]; exact VR4| rewrite Z.add_0_r; exact FDC4| exact Hc5'].
  -
    assert (DP : 0 < D) by (destruct DPOS as [DZ'|DP]; [exfalso; exact (DZ DZ')| exact DP]). clear D0. rename DP into D0.
    assert (LP : 0 < L) by (destruct d; [exfalso; exact (DZ eq_refl)| subst L; cbn [length]; lia]).
    destruct INLV as [(pk & nk & INK & PK1 & PK2)|(DN & _)]; [| exfalso; exact (DZ DN)].
    pose proof (af_live_range RT AF Σ m pk nk ART0 INK) as (K0 & K1 & _).
    assert (INK1 : In (pk, nk) (rt_live RT Σ1)) by (rewrite LV1; exact INK).

    assert (XSH : x_shz [(shad f + 4, shad f + 7)] m4 FD 16).
    { intros m' MU WM. apply (shz_stackv RT AF Σ1 m' FD 16); [| rewrite SP1; clear - UFD LOW LOR; ul| lia| clear - FDT; lia].
      apply (ARTW Σ1 m4 m' _ ART4 MU WM SP1 INF INF01). intros x. cbn [outside]. clear. lia. }
    pose proof (si_walk2n usp sp' f lo RV FD D L gp (Z_to_bv 64 0x6a7e68) v0 v1 v2 (Z_to_bv 64 RV) d1 d2 d3 d4 d5 d6 d7 s5 s6 s10 s11 v3 v4 v5 v6 tt F4 fc4 m4
                  ltac:(clear - UFD LOR LOW SP0R; ul) ltac:(clear - FDT; ul) F0 FLO SLO SHF0 FSELF ltac:(clear - UFD LOR; ul)
                  ltac:(clear - D0 DHI L0; ul) ltac:(clear - LP DHI D0; ul) XSH FDC4 FS4 MI4) as W2.
    lazymatch type of W2 with evt asegs _ ?X0 => assert (W2' : forall ms, eq X0 ms -> evt asegs _ ms) by (intros ms <-; exact W2) end. clear W2.
    apply (cps_realizes asegs _ _ _ c4 (asta_evt_c RT AF Σ1 PMc _ _ MST W2') Hc4'). clear W2'. intros c5 Hc5.
    destruct (ASTA_unpack RT Σ1 _ _ c5 Hc5) as (ms5 & (m5 & -> & MU5 & WM5 & MI5 & FS5) & Hc5'). clear Hc5.
    assert (ART5 : ART RT Σ1 m5). { apply (ARTW Σ1 m4 m5 _ ART4 MU5 WM5 SP1 INF INF01). intros x. cbn [outside]. clear. lia. }
    assert (AG5 : forall a : word, ~ (shad f + 4 <= bv_unsigned a < shad f + 7) -> m5 a = m4 a) by (intros a Ha; apply MU5; cbn [outside]; split; [exact Ha| exact I]).

    assert (SH32 : shad (f + 32) = shad f + 4) by (unfold shad; clear - F64; Z.div_mod_to_equations; lia).
    assert (FOBJP : fobj RT Σ1 m5 (f + 32) 24).
    { split; [clear - F64; Z.div_mod_to_equations; lia|]. split; [lia|]. change ((24 + 7) / 8) with 3.
      split; [exists f, 1%nat; change (fs_size 1) with 128; split; [exact INF| lia]|]. rewrite SH32.
      pose proof FS5 as X. unfold si_shadow in X. cbn [map app repeat] in X.
      lazymatch type of X with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?e0 :: ?e1 :: ?e2 :: ?rest) =>
        change (c0 :: c1 :: c2 :: c3 :: e0 :: e1 :: e2 :: rest) with ([c0; c1; c2; c3] ++ [e0; e1; e2] ++ rest) in X end.
      apply Sj_stage1_kit.rw_cells_app in X. destruct X as [_ X]. apply Sj_stage1_kit.rw_cells_app in X. destruct X as [X _].
      cbn [cells_size csize Nat.add] in X. destruct X as [[_ HB] _]. exact HB. }
    assert (VJP : rw_cells asegs m5 (f + 32) [CB 24 jv0]).
    { pose proof FH4 as X. unfold si_hdr in X.
      lazymatch type of X with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?e0 :: ?rest) => change (c0 :: c1 :: c2 :: c3 :: e0 :: rest) with ([c0; c1; c2; c3] ++ [e0] ++ rest) in X end.
      apply Sj_stage1_kit.rw_cells_app in X. destruct X as [_ X]. apply Sj_stage1_kit.rw_cells_app in X. destruct X as [X _]. cbn [cells_size csize Nat.add] in X.
      apply (rw_cells_agree_nw asegs m4 m5 _ _ X). intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply AG5. clear - Ha FSELF. lia. }
    assert (ST5 : stk asegs m5 lo sp'). { apply (stk_agree_nw asegs m4 m5 _ _ ST4). intros a Ha. cbv beta in Ha. apply AG5. clear - Ha SLO. lia. }
    assert (PB5 : bytes_at asegs m5 D (to_bytes d)).
    { apply (bytes_at_agree asegs m4 m5 _ _ PB4). intros a Ha. rewrite LBL in Ha. apply AG5. pose proof (FSL pk nk INK1) as X2. clear - Ha X2 PK1 PK2. lia. }
    assert (LVB1 : Z.of_nat (length (rt_live RT Σ1)) + 4 <= LIVE_MAX) by (rewrite LV1; exact LVB).
    assert (LPOS1 : forall p n, In (p, n) (rt_live RT Σ1) -> 0 < n) by (rewrite LV1; exact LPOS).
    pose proof (af_client_consts RT AF Σ1 m5 ART5) as CC5.
    apply (SPLIT Σ1 PMc (Z_to_bv 64 0xb2110) (Z_to_bv 64 sp') gp (Z_to_bv 64 0x6a7e68) v0 v1 v2 (Z_to_bv 64 usp) (Z_to_bv 64 sp')
             (Z_to_bv 64 (f + 32)) (Z_to_bv 64 D) (Z_to_bv 64 L) d3 d4 d5 d6 d7
             (Z_to_bv 64 f) (Z_to_bv 64 FD) (Z_to_bv 64 RV) (Z_to_bv 64 (FD + 8)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB)
             (Z_to_bv 64 (shad (FD + 8))) (Z_to_bv 64 (shad FD)) v3 v4 v5 v6 F4 fc4 m5 (f + 32) D d jv0 lo
             FDO MST eq_refl eq_refl eq_refl eq_refl DZ PB5 LBYT LL (ex_intro _ pk (ex_intro _ nk (conj INK1 (conj PK1 PK2)))) LPOS1 FOBJP VJP LVB1
             ltac:(rewrite CR1; clear - CRB; lia) ART5 MI5 ltac:(rewrite EU1; exact ST5) ltac:(rewrite SP1; exact LOW) ltac:(rewrite EU1; clear - SPR LOR; ul)
             ltac:(rewrite EU1; clear - SPR SPT; lia) ltac:(rewrite EU1; clear - SPA'; Z.div_mod_to_equations; lia) FRM4 _ _ (conj Hc5' ltac:(apply (cfrm0_of_asta RT Σ1 PMc (eq _) c5 Hc5'); intros ms0 <-; exact FRM4))).
    intros c6 ((Σ2 & A2 & Hc6 & VL2 & FRS2 & SP2 & CR2) & FC6).
    destruct (ASTA_unpack_f RT Σ2 _ _ c6 Hc6 FC6) as (ms6 & ((r6 & m6 & RS6 & (ART6 & MI6 & ST6) & PRES6 & VR6) & FRM6 & Hc6')). clear Hc6.
    destruct RS6 as (y0 & y1 & y2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & F6 & fc6 & ->).
    cbn [ms_fcsr] in FRM6. rewrite EU1 in ST6, PRES6. rewrite (ret_pc_even 0xb2110) in Hc6' by lia. rewrite SP1 in SP2. rewrite CR1 in CR2.

    pose proof VL2 as LV2. unfold vliveA in LV2.
    assert (INF2 : In (f, 1%nat) (rt_frames RT Σ2)) by (rewrite FRS2; exact INF).
    assert (INF02 : In (f0, kf0) (rt_frames RT Σ2)) by (rewrite FRS2; exact INF01).
    assert (ACL1 : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) usp a -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) sp' a).
    { intros a Ha. rewrite LV1, FRS1. apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| intros e He; right; exact He| clear - SPR; lia]. }
    assert (ACL2 : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) usp a -> aclient (rt_live RT Σ2) (rt_frames RT Σ2) sp' a).
    { intros a Ha. rewrite LV2, FRS2, LV1, FRS1. apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; apply in_or_app; right; exact He| intros e He; right; exact He| clear - SPR; lia]. }
    assert (SPL' : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) usp a -> usp <= a \/ a < lo).
    { intros a Ha. pose proof (aclient_split_c RT AF Σ m usp a ART0 Ha). clear - H LOW. lia. }

    assert (AG6 : forall a : word, aclient (rt_live RT Σ1) (rt_frames RT Σ1) sp' (bv_unsigned a) -> ~ (f + 32 <= bv_unsigned a < f + 56) ->
                    ~ (shad f + 4 <= bv_unsigned a < shad f + 7) -> m6 a = m4 a).
    { intros a H1 H2 H3. rewrite (PRES6 a H1); [exact (AG5 a H3)| cbn [outside]; split; [clear - H2; lia| exact I]]. }
    assert (STK1 : forall a, sp' <= a < usp -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) sp' a) by (intros a Ha; left; clear - Ha SPT; ul).
    assert (STK2 : forall a, sp' <= a < USTACK_TOP -> aclient (rt_live RT Σ2) (rt_frames RT Σ2) sp' a) by (intros a Ha; left; exact Ha).
    assert (VC6 : rw_cells asegs m6 RV (vcells 0 0 0)).
    { pose proof VR4 as (_ & _ & _ & _ & _ & X & _). change (0 + 16 * 0) with 0 in X. unfold vcells.
      apply (rw_cells_agree_nw asegs m4 m6 _ _ X). intros a Ha. cbn [cells_size csize Nat.add] in Ha.
      apply AG6; [exact (CLV Σ1 sp' _ INF01 Ha)| clear - Ha FDJ FLO0 FHI0; lia| clear - Ha FSDJ SHF16 FLO0 FHI0; lia]. }
    assert (FOBJ6 : fobj RT Σ2 m6 RV 24).
    { apply (fobj_agree RT AF Σ1 Σ2 m4 m6 RV 24 ART4 FOBJ4 FRS2). intros a Ha. cbv beta in Ha. change ((24 + 7) / 8) with 3 in Ha.
      apply AG6; [exact (CLVS Σ1 sp' _ INF01 Ha)| clear - Ha RVSH F0S_F; lia| clear - Ha RVSH SHAPART SHF16; lia]. }
    assert (VSHZ : v_shz [(sp' - 32, sp'); (RV, RV + 24)] m6 RV).
    { apply (v_shz_of_fp RT AF Σ2 m6 lo _ RV ART6 ltac:(rewrite SP2; exact LOW)); [| exact FOBJ6].
      constructor; [left; cbn [fst snd]; clear - SPR LOR SPT; ul| constructor; [right; right; exists f0, kf0; cbn [fst snd]; split; [exact INF02| clear - FLO0 FHI0; lia]| constructor]]. }
    pose proof VR6 as (Es & Rs & Cs & A0s & AHs & SV6 & BLK6).
    pose proof (af_client_consts RT AF Σ2 m6 ART6) as (G1 & G2 & _).

    pose proof (si_walk3 usp sp' f lo RV FD A2 (A2 + 16 * zlength (poffs d)) (A2 + 16 * vcap_iter (length (poffs d)) 0 0)
                  gp (Z_to_bv 64 0x6a7e68) y0 y1 y2 r6 e1 e2 e3 e4 e5 e6 e7 y3 y4 y5 y6 F6 fc6 m6
                  ST6 ltac:(clear - SPR LOR; ul) ltac:(clear - LOW SP0R; ul) ltac:(clear - SPR SPT; ul) ltac:(clear - UFD FDT LOR LOW SP0R; ul)
                  F0 FLO SLO SHF0 FSELF ltac:(clear - F00 FLO0; lia) ltac:(clear - FHI0 F01 LOW; lia) ltac:(clear - FDJ FLO0 FHI0; lia) ltac:(clear - FSDJ SHF16 FLO0 FHI0; lia)
                  ltac:(clear - Rs Cs A0s AHs; lia) ltac:(clear - Rs Cs A0s AHs; lia) ltac:(clear - Rs Cs A0s AHs; lia) (conj G1 G2) VSHZ VC6 SV6 MI6) as W3.
    lazymatch type of W3 with evt asegs _ ?X0 => assert (W3' : forall ms, eq X0 ms -> evt asegs _ ms) by (intros ms <-; exact W3) end. clear W3.
    apply (cps_realizes asegs _ _ _ c6 (asta_evt_c RT AF Σ2 PMc _ _ MST W3') Hc6'). clear W3'. intros c7 Hc7.
    destruct (ASTA_unpack RT Σ2 _ _ c7 Hc7) as (ms7 & (m7 & -> & MU7 & WM7 & MI7 & ST7 & VC7 & PC7) & Hc7'). clear Hc7.
    assert (ART7 : ART RT Σ2 m7). { apply (ARTW Σ2 m6 m7 _ ART6 MU7 WM7 SP2 INF2 INF02). intros x. cbn [outside]. clear - SPR LOR SPT. ul. }
    assert (AG7 : forall a : word, ~ (sp' - 32 <= bv_unsigned a < sp') -> ~ (RV <= bv_unsigned a < RV + 24) -> m7 a = m6 a).
    { intros a H1 H2. apply MU7. cbn [outside]. split; [exact H1| split; [exact H2| exact I]]. }
    assert (FS7 : rw_cells asegs m7 (shad f) (si_shadow 0 0 0 tt)).
    { apply (rw_cells_agree_nw asegs m5 m7 _ _ FS5). intros a Ha. unfold si_shadow in Ha. rewrite <- (app_nil_r tt) in Ha.
      do 4 (destruct tt as [|? tt]; [discriminate LT|]). destruct tt; [| discriminate LT]. cbn [map app repeat cells_size csize Nat.add] in Ha.
      rewrite (AG7 a); [| clear - Ha SLO SPR LOR; ul| clear - Ha FSDJ SHF16 FLO0 FHI0; lia].
      apply PRES6; [right; right; right; right; exists f, 1%nat; rewrite SHF16; split; [exact INF| clear - Ha; lia]| cbn [outside]; split; [clear - Ha FSELF; lia| exact I]]. }
    rewrite app_nil_r in FS7 || idtac.
    assert (SHBP : bytes_at asegs m7 (shad (f + 32)) (repeat z8 3)).
    { rewrite SH32. pose proof FS7 as X. unfold si_shadow in X. cbn [map app repeat] in X.
      lazymatch type of X with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?e0 :: ?e1' :: ?e2' :: ?rest) =>
        change (c0 :: c1 :: c2 :: c3 :: e0 :: e1' :: e2' :: rest) with ([c0; c1; c2; c3] ++ [e0; e1'; e2'] ++ rest) in X end.
      apply Sj_stage1_kit.rw_cells_app in X. destruct X as [_ X]. apply Sj_stage1_kit.rw_cells_app in X. destruct X as [X _].
      cbn [cells_size csize Nat.add] in X. destruct X as [[_ HB] _]. exact HB. }

    apply ((rf_asan_memset RT RTF) Σ2 PMc (Z_to_bv 64 0xb2178) (Z_to_bv 64 sp') gp (Z_to_bv 64 0x6a7e68) y0 y1 y2 (Z_to_bv 64 usp) (Z_to_bv 64 sp')
             (Z_to_bv 64 (f + 32)) (Z_to_bv 64 0) (Z_to_bv 64 24) e3 e4 e5 e6 e7 (Z_to_bv 64 f) (Z_to_bv 64 FD) (Z_to_bv 64 RV) (Z_to_bv 64 (FD + 8)) (Z_to_bv 64 (f + 32))
             (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) (Z_to_bv 64 (shad (FD + 8))) (Z_to_bv 64 (shad FD)) y3 y4 y5 y6
             F6 fc6 m7 (f + 32) 24 (Z_to_bv 8 0) lo FDO MST eq_refl eq_refl eq_refl ltac:(clear - F0 F1 SP0R; ul) ltac:(lia));
      [| exact ART7| exact MI7| exact (COK Σ2 m7 SP2 ST7)| split; [exact Hc7'| apply (cfrm0_of_asta RT Σ2 PMc (eq _) c7 Hc7'); intros ms0 <-; exact FRM6] |].
    { unfold checked_dst. rewrite EU1. split; [| split; [| exact (rw_cells_wr_at asegs m7 (f + 32) _ 24 PC7 ltac:(cbn; lia))]].
      - intros _. split; [exact (acc_zero_run asegs m7 (f + 32) 3 ltac:(clear - F64; Z.div_mod_to_equations; lia) ltac:(lia) SHBP)|]. right; left. exists f, 1%nat. split; [exact INF2| change (fs_size 1) with 128; lia].
      - intros i Hi. right; right; right; left. exists f, 1%nat. split; [exact INF2| change (fs_size 1) with 128; lia]. }
    intros c8 (Hc8 & FC8).
    destruct (ASTA_unpack_f RT Σ2 _ _ c8 Hc8 FC8) as (ms8 & (m8 & RS8 & (ART8 & MI8 & WM8 & ST8) & PRES8 & BY8) & FRM8 & Hc8'). clear Hc8.
    destruct RS8 as (z0 & z1 & z2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & z3 & z4 & z5 & z6 & F8 & fc8 & ->).
    cbn [ms_fcsr] in FRM8. rewrite EU1 in ST8, PRES8. rewrite (ret_pc_even 0xb2178) in Hc8' by lia.

    assert (AG8 : forall a : word, aclient (rt_live RT Σ2) (rt_frames RT Σ2) sp' (bv_unsigned a) -> ~ (f + 32 <= bv_unsigned a < f + 56) -> m8 a = m7 a).
    { intros a H1 H2. apply (PRES8 a H1). clear - H2. lia. }
    assert (FRl8 : rw_cells asegs m8 sp' [CB 8 j0; C8 (Z_to_bv 64 f); CB 8 j2]).
    { apply (rw_cells_agree_nw asegs m4 m8 _ _ FRl4). intros a Ha. cbn [cells_size csize Nat.add] in Ha.
      rewrite (AG8 a); [| apply STK2; clear - Ha SPT SPR; ul| clear - Ha FLO SPR LOR; ul]. rewrite (AG7 a); [| clear - Ha; lia| clear - Ha FHI0 F01 LOW SPR LOR; ul].
      apply AG6; [apply STK1; clear - Ha SPR; lia| clear - Ha FLO SPR LOR; ul| clear - Ha SLO SPR LOR; ul]. }
    assert (PC8 : rw_cells asegs m8 (f + 32) (vcells 0 0 0)).
    { unfold vcells. apply rw_cells_of_bytes; [cbn; repeat split; exact I| exact BY8|].
      cbn [cells_size csize Nat.add]. apply (wr_at_transport asegs m7 m8 (f + 32) 24 (rw_cells_wr_at asegs m7 (f + 32) _ 24 PC7 ltac:(cbn; lia)) WM8). }
    assert (FS8 : rw_cells asegs m8 (shad f) (si_shadow 0 0 0 tt)).
    { apply (rw_cells_agree_nw asegs m7 m8 _ _ FS7). intros a Ha. unfold si_shadow in Ha. rewrite <- (app_nil_r tt) in Ha.
      do 4 (destruct tt as [|? tt]; [discriminate LT|]). destruct tt; [| discriminate LT]. cbn [map app repeat cells_size csize Nat.add] in Ha.
      apply AG8; [right; right; right; right; exists f, 1%nat; rewrite SHF16; split; [exact INF2| clear - Ha; lia]| clear - Ha FSELF; lia]. }
    rewrite app_nil_r in FS8 || idtac.
    assert (FDC8 : rw_cells asegs m8 FD [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 L)]).
    { apply (rw_cells_agree_nw asegs m4 m8 _ _ FDC4). intros a Ha. cbn [cells_size csize Nat.add] in Ha.
      rewrite (AG8 a); [| apply STK2; clear - Ha UFD FDT SPR; lia| clear - Ha FLO UFD LOR; ul]. rewrite (AG7 a); [| clear - Ha UFD SPR; lia| clear - Ha FHI0 F01 LOW UFD LOR; ul].
      apply AG6; [left; clear - Ha UFD FDT SPR; ul| clear - Ha FLO UFD LOR; ul| clear - Ha SLO UFD LOR; ul]. }
    pose proof (af_client_consts RT AF Σ2 m8 ART8) as (G1' & G2' & _).
    assert (XSH8 : forall X n, rt_sp0 RT Σ - STACK_WIN + 8 <= X -> 0 <= n -> X + n <= USTACK_TOP ->
                    x_shz [(sp' - 32, sp'); (sp' + 16, sp' + 24); (shad f + 4, shad f + 7); (FD, FD + 16)] m8 X n).
    { intros X n X0 N0 XT m' MU WM. apply (shz_stackv RT AF Σ2 m' X n); [| rewrite SP2; exact X0| exact N0| exact XT].
      apply (ARTW Σ2 m8 m' _ ART8 MU WM SP2 INF2 INF02). intros x. cbn [outside]. clear - SPR LOR SPT UFD FDT. ul. }

    pose proof (si_walk4 usp sp' f lo RV FD D L gp (Z_to_bv 64 0x6a7e68) z0 z1 z2 (Z_to_bv 64 (f + 32)) g1 g2 g3 g4 g5 g6 g7 z3 z4 z5 z6 j0 j2 tt F8 fc8 m8
                  LT ST8 ltac:(clear - SPR LOR; ul) ltac:(clear - LOW SP0R; ul) ltac:(clear - UFD SPR; lia) ltac:(clear - FDT; ul)
                  F0 FLO SLO SHF0 FSELF ltac:(clear - D0; lia) L0 ltac:(clear - DHI D0; ul) (conj G1' G2')
                  (XSH8 (sp' + 16) 8 ltac:(clear - SPR LOR LOW; ul) ltac:(lia) ltac:(clear - SPR SPT; lia)) (XSH8 FD 16 ltac:(clear - UFD LOR LOW; ul) ltac:(lia) ltac:(clear - FDT; lia))
                  FRl8 PC8 FS8 FDC8 MI8) as W4.
    lazymatch type of W4 with evt asegs _ ?X0 => assert (W4' : forall ms, eq X0 ms -> evt asegs _ ms) by (intros ms <-; exact W4) end. clear W4.
    apply (cps_realizes asegs _ _ _ c8 (asta_evt_c RT AF Σ2 PMc _ _ MST W4') Hc8'). clear W4'. intros c9 Hc9.
    destruct (ASTA_unpack RT Σ2 _ _ c9 Hc9) as (ms9 & (m9 & a2y & -> & MU9 & WM9 & MI9 & ST9 & FRl9 & FS9 & FDC9) & Hc9'). clear Hc9.
    assert (ART9 : ART RT Σ2 m9). { apply (ARTW Σ2 m8 m9 _ ART8 MU9 WM9 SP2 INF2 INF02). intros x. cbn [outside]. clear - SPR LOR SPT UFD FDT. ul. }
    assert (AG9 : forall a : word, ~ (sp' - 32 <= bv_unsigned a < sp') -> ~ (sp' + 16 <= bv_unsigned a < sp' + 24) -> ~ (shad f + 4 <= bv_unsigned a < shad f + 7) ->
                    ~ (FD <= bv_unsigned a < FD + 16) -> m9 a = m8 a).
    { intros a H1 H2 H3 H4. apply MU9. cbn [outside]. clear - H1 H2 H3 H4. tauto. }
    assert (ACL12 : forall a, aclient (rt_live RT Σ1) (rt_frames RT Σ1) sp' a -> aclient (rt_live RT Σ2) (rt_frames RT Σ2) sp' a).
    { intros a Ha. rewrite LV2, FRS2. apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; apply in_or_app; right; exact He| auto| lia]. }
    assert (AG49 : forall a : word, aclient (rt_live RT Σ1) (rt_frames RT Σ1) sp' (bv_unsigned a) -> ~ (f + 32 <= bv_unsigned a < f + 56) ->
                    ~ (shad f + 4 <= bv_unsigned a < shad f + 7) -> ~ (sp' - 32 <= bv_unsigned a < sp') -> ~ (RV <= bv_unsigned a < RV + 24) ->
                    ~ (sp' + 16 <= bv_unsigned a < sp' + 24) -> ~ (FD <= bv_unsigned a < FD + 16) -> m9 a = m4 a).
    { intros a H1 H2 H3 H4 H5 H6 H7. rewrite (AG9 a H4 H6 H3 H7). rewrite (AG8 a (ACL12 _ H1) H2). rewrite (AG7 a H4 H5). exact (AG6 a H1 H2 H3). }
    assert (STp9 : stk asegs m9 (sp' + 24) (usp - 104)).
    { apply (stk_agree_nw asegs m4 m9 _ _ STp4). intros a Ha. cbv beta in Ha.
      apply AG49; [apply STK1; clear - Ha SPR; lia| clear - Ha FLO SPR LOR; ul| clear - Ha SLO SPR LOR; ul| clear - Ha; lia| clear - Ha FHI0 F01 LOW SPR LOR; ul| clear - Ha; lia| clear - Ha UFD; lia]. }
    assert (FRs9 : rw_cells asegs m9 (usp - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
    { apply (rw_cells_agree_nw asegs m4 m9 _ _ FRs4). intros a Ha. unfold fa_saved in Ha. cbn [cells_size csize Nat.add] in Ha.
      apply AG49; [apply STK1; clear - Ha SPR; lia| clear - Ha FLO SPR LOR; ul| clear - Ha SLO SPR LOR; ul| clear - Ha SPR; lia| clear - Ha FHI0 F01 LOW SPR LOR; ul| clear - Ha SPR; lia| clear - Ha UFD; lia]. }
    assert (FHm9 : rw_cells asegs m9 f [C8 (Z_to_bv 64 0x41b58ab3)]).
    { apply (rw_cells_agree_nw asegs m4 m9 _ _ FHm). intros a Ha. cbn [cells_size csize Nat.add] in Ha.
      apply AG49; [right; right; right; left; exists f, 1%nat; change (fs_size 1) with 128; split; [exact INF| clear - Ha; lia]| clear - Ha; lia| clear - Ha FSELF; lia
                  | clear - Ha FLO SPR LOR; ul| clear - Ha FDJ FLO0 FHI0; lia| clear - Ha FLO SPR LOR; ul| clear - Ha FLO UFD LOR; ul]. }
    assert (CAL9 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> outside [(RV, RV + 24); (FD, FD + 16)] (bv_unsigned a) -> m9 a = m a).
    { intros a Ha Hout. rewrite <- (CAL4 a Ha Hout). pose proof Hout as (HO1 & HO2 & _). destruct (NEWF _ Ha) as [NF1 NF2]. rewrite SHF16 in NF2. pose proof (SPL' _ Ha) as SL.
      apply AG49; [exact (ACL1 _ Ha)| clear - NF1; lia| clear - NF2; lia| clear - SL SPR LOR; ul| exact HO1| clear - SL SPR LOR; ul| exact HO2]. }
    assert (VR9 : vrepA m9 RV A2 (vcap_iter (length (poffs d)) 0 0) (zlength (poffs d)) (map (pview D) (poffs d))).
    { unfold vrepA. split; [exact Es|]. split; [exact Rs|]. split; [exact Cs|]. split; [exact A0s|]. split; [exact AHs|]. split.
      - apply (rw_cells_agree_nw asegs m7 m9 _ _ VC7). intros a Ha. unfold vcells in Ha. cbn [cells_size csize Nat.add] in Ha.
        rewrite (AG9 a); [| clear - Ha FHI0 F01 LOW SPR LOR; ul| clear - Ha FHI0 F01 LOW SPR LOR; ul| clear - Ha FSDJ SHF16 FLO0 FHI0; lia| clear - Ha F01 FHI0 LOW LOR UFD; ul].
        apply AG8; [exact (CLV Σ2 sp' _ INF02 Ha)| clear - Ha FDJ FLO0 FHI0; lia].
      - destruct BLK6 as [Lz|(C1 & A16 & AP & BE6)]; [left; exact Lz| right]. split; [exact C1|]. split; [exact A16|]. split; [exact AP|].
        assert (INA2 : In (A2, 16 * zlength (poffs d)) (rt_live RT Σ2)).
        { rewrite LV2. apply in_or_app. left. unfold vblockA. destruct (Z.eqb_spec (vcap_iter (length (poffs d)) 0 0) 0); [exfalso; clear - C1 e; lia|]. apply ann_block_vis. }
        pose proof (af_live_range RT AF Σ2 m6 _ _ ART6 INA2) as (_ & Y3 & _). rewrite SP2 in Y3.
        pose proof (proj1 (af_fshadow_apart RT AF Σ2 m6 f 1%nat ART6 INF2) _ _ INA2) as Y2. rewrite SHF16 in Y2.
        pose proof (proj2 (proj2 (proj2 (af_frames_range RT AF Σ2 m6 f 1%nat ART6 INF2))) _ _ INA2) as Y1. change (fs_size 1) with 128 in Y1.
        pose proof (proj2 (proj2 (proj2 (af_frames_range RT AF Σ2 m6 f0 kf0 ART6 INF02))) _ _ INA2) as Y0.
        apply (rw_cells_agree_nw asegs m6 m9 _ _ BE6). intros a Ha. rewrite velts_size, length_map in Ha. unfold zlength in Y0, Y1, Y2, Y3, INA2.
        rewrite (AG9 a); [| clear - Ha Y3 LOW SPR LOR; ul| clear - Ha Y3 LOW SPR LOR; ul| clear - Ha Y2; lia| clear - Ha Y3 LOW LOR UFD; ul].
        rewrite (AG8 a); [| right; right; left; exists A2, (16 * Z.of_nat (length (poffs d))); split; [exact INA2| clear - Ha; lia]| clear - Ha Y1; lia].
        apply AG7; [clear - Ha Y3 LOW SPR LOR; ul| clear - Ha Y0 FLO0 FHI0; lia]. }
    apply (TAIL Σ2 m9 A2 (Z_to_bv 64 0xb2184) z0 z1 z2 (Z_to_bv 64 (D + L)) (Z_to_bv 64 L) a2y g3 g4 g5 g6 g7 (Z_to_bv 64 (FD + 8)) (Z_to_bv 64 (f + 32))
             (Z_to_bv 64 (shad (FD + 8))) (Z_to_bv 64 (shad FD)) z3 z4 z5 z6 F8 fc8 c9 FRM8 ART9 MI9 ST9 FRS2 SP2);
      [unfold vliveA; rewrite LV2, LV1; reflexivity| exact CR2| left; exact FRl9| exact STp9| exact FRs9| exact FHm9| exact FS9| exact CAL9| exact VR9| exact FDC9| exact Hc9'].
Qed.
End SplitInto.

Corollary splitinto_closed : forall RT, art_facts RT -> rt_contracts_f RT -> rt_contracts2 RT -> splitinto_cpsA RT.
Proof.
  intros RT AF RTF RC2.
  exact (splitinto_ok RT AF RTF (rc2_stack_malloc_1 RT RC2)
           (split_ok RT AF RTF (find_ok RT AF RTF (rc_memchr RT (rc2_rt RT RC2))) (pushr_ok RT AF RTF (rc2_annotate RT RC2)) (pushc_ok RT AF RTF (rc2_annotate RT RC2)))).
Qed.
