(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun Stdio SjModel AtpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_stage1_kit Atp_h_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_iface3 RT_iface5. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_hkit2 Sj_new. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_num_akit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_h_alloc Sj_stage2_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA Atp_setcapA Atp_activewA Atp_activeA Atp_defsA Atp_kitA Atp_h_defsA Atp_h_vkitA Atp_hkit6A Atp_pidwA Atp_pidiA Atp_pid0A Atp_pdtorA RT_rtf Pj_rtkA Pj_lftoi1A Pj_defsA Pj_os_defsA Pj_cpsA El_defsA El_lf1A El_lf2A El_lf2bA El_costA El_phasesA El_frontA El_parsewA El_parsekA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Parse1.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC2 : rt_contracts2 RT.
Variable PMc : Model -> Prop.

Local Ltac ul := unfold FUZZ_STACK, PID_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Theorem el_parse_p1 : forall (Σ0 : rts RT) (m0 : mem) (X : lfA) (d : Z) (bs : list byte) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (K : config -> Prop),
    fdfs_only PMc -> mat_stable PMc -> lfA_ok X -> rt_sp0 RT Σ0 - STACK_WIN <= lf_lo X ->
    0 < d -> Z.of_nat (length bs) < 2^26 ->
    ((exists p n, In (p, n) (rt_live RT Σ0) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ (bs = [] /\ d < SEGTOP_A)) ->
    (forall p n, In (p, n) (rt_live RT Σ0) -> 0 < n) -> Z.of_nat (length (rt_live RT Σ0)) + FUZZ_LIVE <= LIVE_MAX -> FUZZ_COST <= rt_credit RT Σ0 ->
    cutP4 RT PMc Σ0 m0 X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 K ->
    cutX2 RT PMc (ART RT) Σ0 m0 X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (rt_credit RT Σ0 - el_vcostA bs) K ->
    cutV RT PMc Σ0 m0 X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 K.
Proof using AF RC2.
  intros Σ0 m0 X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 K FDO MST LK LOW D0 BSL INLV LVPOS LVB CR0 CUTP4 CUTX2.
  unfold cutV. intros Σ m x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x11 t3 t4 t5 t6 F fc j0 j1 j2 j8 j10 j15 jr h3 t j56 jp j176 je j224 jos j528 idx act sel A
    BASE FRl ACT SEL FS VR F56 FP F176 FE F224 FO F528 VL CR FRM.
  pose proof BASE as (ARTg & MIg & STg & STp & FRs & FH & BS & LIB & PRES & FRSg & SPg).
  pose proof LK as [(SPR & SPA') (SPT & SPA) (LLO & LOR) (FPOS & F64 & FSEG & FLO) (FSELF & SHB0 & SHT)].
  destruct X as [usp sp' f lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  pose proof (af_sp0_range RT AF Σ m ARTg) as SP0R. rewrite SPg in SP0R.
  pose proof (rc2_rt RT RC2) as RC.
  assert (EU : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; ul).
  assert (INF : In (f, 4%nat) (rt_frames RT Σ)) by (rewrite FRSg; left; reflexivity).
  set (n := Z.of_nat (length bs)) in *.

  pose proof VR as (ELS & SZC & CAPB & A0 & AH & SV & BLK).
  assert (P2 : (2 <= el_PA bs)%nat) by (unfold el_PA, atp_P; lia). pose proof (vcap_iter_inv (el_PA bs) 0 0 ltac:(lia) ltac:(lia)) as CAPI. rewrite Z.add_0_l in CAPI.
  destruct BLK as [(C0 & _)|(CP1 & A16 & APOS & ELTS)]; [exfalso; lia|].
  assert (INA : In (A, 16 * Z.of_nat (el_PA bs)) (rt_live RT Σ)).
  { unfold vliveA, vblockA in VL. rewrite VL. apply in_or_app. left. destruct (Z.eqb_spec (vcap_iter (el_PA bs) 0 0) 0); [lia|]. apply ann_block_vis. }
  pose proof (af_live_range RT AF Σ m A _ ARTg INA) as (AR0 & AR1 & AR2). rewrite SPg in AR1.
  assert (SHZA : shz m A 32).
  { pose proof (shz_live RT AF Σ m A _ ARTg INA ltac:(clear - A16; Z.div_mod_to_equations; lia)) as XZ.
    eapply shz_sub; [exact XZ| lia|]. clear - P2 CAPI. Z.div_mod_to_equations. nia. }

  assert (FDV : 0 <= el_fddA d n + el_fdsA n < 2^64 /\ (el_fddA d n + el_fdsA n = 0 <-> n < 10)).
  { unfold el_fddA, el_fdsA. destruct (Z.leb_spec 10 n); [| split; [lia| split; [lia| reflexivity]]].
    destruct INLV as [(p & k & Hin & P1 & Pk)|(E0 & _)]; [| exfalso; subst bs n; cbn [length] in *; lia].
    pose proof (af_live_range RT AF Σ m p k ARTg ltac:(unfold vliveA in VL; rewrite VL; apply in_or_app; right; exact Hin)) as (_ & R1 & _). rewrite SPg in R1. split; [clear - D0 Pk R1 SP0R; ul| split; lia]. }
  destruct FDV as [FDR FDZ].

  apply (aevt_evt RT AF PMc MST).
  pose proof FRl as FRl'. unfold el_locals3 in FRl'.
  lazymatch type of FRl' with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: rest)
      with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10] ++ c11 :: rest) in FRl' end.
  lazymatch type of FRl' with rw_cells _ _ _ (?pre ++ _) =>
  eapply evt_cut; [eapply (pw_walk0 usp sp' f A (el_fddA d n + el_fdsA n) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz (f + 208)) (wz f) (wz 16) x11 t3 t4 t5 t6 pre _ F fc m
                             FPOS ltac:(ul) ltac:(ul) ltac:(ul) APOS ltac:(lia) ltac:(clear - A16; Z.div_mod_to_equations; lia) FDR eq_refl FRl' ltac:(eapply shz_sub; [exact SHZA| lia| lia]) MIg)|]
  end.
  cbv beta. clear FRl'. intros ms1 [(FD0 & a0' & a1' & ->)|(FD1 & a1' & ->)]; apply evt_done; unfold pw_st.
  -
    eapply (CUTX2 Σ m x1 t0 t1 t2 a0' a1' a2 a3 a4 a5 a6 a7 (wz (f + 208)) (wz SHB) (wz A) (wz 16) x11 t3 t4 t5 t6 F fc
              (el_locals3 j0 j1 j2 idx act j8 f j10 sel (el_fddA d n + el_fdsA n) 0 j15 jr) h3 t (-8) (-8) A);
      cbn [lf_usp lf_S1 lf_F lf_lo];
      [exact ARTg| exact MIg| exact STg| exact STp| exact FRs| exact FH| exact LIB| exact PRES| exact FRSg| exact SPg| reflexivity| exact FRl| exact FS| exact VR| exact VL| exact CR| exact FRM].
  -
    assert (N10 : 10 <= n) by (destruct (Z_lt_dec n 10); [exfalso; apply FD1, FDZ; lia| lia]).
    pose proof (af_frames_range RT AF Σ m f 4%nat ARTg INF) as (_ & _ & _ & FLV). change (fs_size 4) with 1024 in FLV.
    pose proof (af_fshadow_apart RT AF Σ m f 4%nat ARTg INF) as (FSL & _).
    assert (SH128 : shad (f + fs_size 4) = shad f + 128) by (change (fs_size 4) with 1024; unfold shad; clear - F64 FPOS; Z.div_mod_to_equations; lia).
    rewrite SH128 in FSL. clear SH128.
    pose proof (FLV A _ INA) as AFR. pose proof (FSL A _ INA) as ASH.

    destruct (el_els_two d bs) as (erest & EELS & ELEN).
    pose proof ELTS as ELTS'. rewrite EELS in ELTS'. cbn [velts] in ELTS'.
    pose proof (el_els_rng d bs (el_s0A d bs) D0 ltac:(lia) ltac:(rewrite EELS; left; reflexivity)) as R0.
    destruct INLV as [(pL & kL & HinL & PL1 & PL2)|(E0 & _)]; [| exfalso; subst bs n; cbn [length] in *; lia].
    pose proof (af_live_range RT AF Σ m pL kL ARTg ltac:(unfold vliveA in VL; rewrite VL; apply in_or_app; right; exact HinL)) as (_ & RL1 & _). rewrite SPg in RL1.
    assert (R0' : 0 <= fst (el_s0A d bs) < 2^64 /\ 0 <= snd (el_s0A d bs) < 2^64).
    { destruct R0 as [E|(R1 & R2 & R3)]; [rewrite E; cbn; lia|]. clear - R1 R2 R3 D0 PL1 PL2 RL1 SP0R. subst n. ul. }

    pose proof FP as FP'. apply (rw_cells_split_CB asegs _ _ [] 80 _ [] [1; 7; 8; 1; 3; 4; 24; 8; 1; 7; 16]%nat) in FP'; [| reflexivity]. cbn [mk_CB_cells app] in FP'.

    pose proof FRl as FRlw. unfold el_locals3 in FRlw.
    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut; [eapply (pw_walk1 usp sp' f A (fst (el_s0A d bs)) (snd (el_s0A d bs)) _ gp t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 (wz (f + 208)) (wz f) (wz 16) x11 t3 t4 t5 t6
                               _ _ _ _ _ _ _ _ _ _ _ _ t j0 j1 j2 _ F fc m FPOS ltac:(ul) ltac:(ul) ltac:(ul) FSELF ltac:(ul) ltac:(ul) ltac:(ul) APOS ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ul)
                               (proj1 R0') (proj2 R0') ELTS' FRlw FP' FS MIg)|].
    cbv beta. clear FP' ELTS' FRlw. intros ms2 (m1 & -> & MU1 & WM1 & MI1 & FRl1 & FP1 & FS1). apply evt_done. unfold pw_st.

    assert (CLW : forall mx my W, munch W mx my -> Forall (fun iv => (sp' <= fst iv /\ snd iv <= usp) \/ (f <= fst iv /\ snd iv <= f + 1016)
                                                                   \/ (shad f <= fst iv /\ snd iv <= shad f + 128)) W ->
                   agree_on (fun a => ~ aclient (rt_live RT Σ) (rt_frames RT Σ) sp' a) mx my).
    { intros mx my W MU HW a Ha. apply MU. clear - HW Ha FRSg SPR SPT. induction W as [|[lo' hi'] W IH]; [exact I|].
      apply Forall_cons_iff in HW. destruct HW as [H1 HW]. cbn [outside fst snd] in *. split; [| exact (IH HW)].
      intros Hin. apply Ha. destruct H1 as [H1|[H1|H1]].
      - left. unfold USTACK_TOP in *. lia.
      - right; right; right; left. exists f, 4%nat. rewrite FRSg. split; [left; reflexivity| change (fs_size 4) with 1024; lia].
      - right; right; right; right. exists f, 4%nat. rewrite FRSg. split; [left; reflexivity| change (fs_size 4) with 1024; unfold shad in *; Z.div_mod_to_equations; lia]. }
    assert (COK : forall mx, stk asegs mx lo sp' -> call_ok RT Σ mx (Z_to_bv 64 sp') lo).
    { intros mx STx. unfold call_ok. rewrite EU, SPg. split; [exact STx|]. split; [ul|]. split; [ul|]. split; [ul| clear - SPA'; Z.div_mod_to_equations; lia]. }

    assert (RTW : forall mx my dd nn, rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) sp' dd nn mx my -> f <= dd -> dd + nn <= f + 1016 ->
                   forall (P : Z -> Prop), (forall x, P x -> (sp' <= x < usp \/ (f <= x < f + 1016 /\ ~ (dd <= x < dd + nn)) \/ shad f <= x < shad f + 128)) ->
                   agree_on P mx my).
    { intros mx my dd nn PR D1 D2 P HP a Ha. destruct (HP _ Ha) as [H|[[H1 H2]|H]]; apply PR.
      - left. ul. - ul.
      - right; right; right; left. exists f, 4%nat. change (fs_size 4) with 1024. split; [exact INF| lia]. - exact H2.
      - right; right; right; right. exists f, 4%nat. change (fs_size 4) with 1024. split; [exact INF| unfold shad in *; Z.div_mod_to_equations; lia]. - ul. }
    assert (ART1 : ART RT Σ m1).
    { apply (art_client_write RT AF Σ m m1 sp' ARTg ltac:(rewrite SPg; ul)); [| exact WM1]. eapply CLW; [exact MU1|]. repeat constructor; cbn [fst snd]; ul. }
    assert (ST1 : stk asegs m1 lo sp').
    { apply (stk_agree asegs m m1 _ _ STg); [| exact WM1]. apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn [outside]. repeat split; ul. }

    assert (MSTEP : forall (mx : mem) (e os : Z) (t' : list byte) (cs : list cell) (dd nn : Z), ART RT Σ mx ->
              rw_cells asegs mx (shad f) (el_shadowA 0 0 e os t') -> rw_cells asegs mx (f + 96) cs -> cells_size cs = 80%nat ->
              f + 96 <= dd -> dd + nn <= f + 176 -> 0 < nn -> checked_dst RT Σ mx (Z_to_bv 64 sp') dd nn).
    { intros mx e os t' cs dd nn ARTx FSx [_ WRx] SZx D1 D2 NP. rewrite SZx in WRx. change (Z.of_nat 80) with 80 in WRx.
      apply (el_fobj_dst RT Σ mx (Z_to_bv 64 sp') f (f + 96) 80 dd nn (el_parser_fobj RT Σ mx f 0 e os t' FSx FRSg FPOS F64) ltac:(lia) FRSg);
        [apply (wr_at_sub mx (f + 96) 80); [exact WRx| lia| lia| lia]| lia| lia| lia| lia| lia]. }
    eapply (aevt_memsetP RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (f + 120) 24 z8 lo eq_refl eq_refl eq_refl
              ltac:(ul) ltac:(lia) (MSTEP m1 (-8) (-8) t _ (f + 120) 24 ART1 FS1 FP1 eq_refl ltac:(lia) ltac:(lia) ltac:(lia)) ART1 MI1 (COK m1 ST1)).
    intros w0 w1 w2 g1 g2 g3 g4 g5 g6 g7 w3 w4 w5 w6 F2 m2 (ART2 & MI2 & WM2 & ST2) PRES2 BY2. rewrite EU in ST2, PRES2.
    rewrite ret_pc_even by lia. change (Z.to_nat 24) with 24%nat in BY2.
    lazymatch type of FP1 with rw_cells _ _ _ (fz_parser _ ?x1 _ _ ?x17 _ (CB 24 ?x24) (CB 8 ?x48) (CB 1 ?x56) ?x57 (CB 16 ?x64)) =>
      assert (FP2 : rw_cells asegs m2 (f + 96) (fz_parser (C1 (Z_to_bv 8 0)) x1 (C8 (Z_to_bv 64 0)) (C1 (Z_to_bv 8 0)) x17 (C4 (Z_to_bv 64 12))
                                                         (CB 24 (repeat z8 24)) (CB 8 x48) (CB 1 x56) x57 (CB 16 x64)));
      [ unfold fz_parser in *;
        apply (cells_mid_update m1 m2 (f + 96) [C1 (Z_to_bv 8 0); CB 7 x1; C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 3 x17; C4 (Z_to_bv 64 12)]
                 24 x24 (repeat z8 24) [CB 8 x48; CB 1 x56; CB 7 x57; CB 16 x64] FP1); [| exact WM2| | reflexivity];
        [ apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES2); intros x (Hx & Hn); cbn [app cells_size csize Nat.add] in Hx, Hn;
          split; [right; right; right; left; exists f, 4%nat; change (fs_size 4) with 1024; split; [exact INF| lia]| lia]
        | cbn [cells_size csize Nat.add]; replace (f + 96 + Z.of_nat 24) with (f + 120) by lia; exact BY2 ] |]
    end.
    assert (FS2 : rw_cells asegs m2 (shad f) (el_shadowA 0 0 (-8) (-8) t)).
    { eapply rw_cells_agree_nw; [exact FS1|]. eapply RTW; [exact PRES2| lia| lia|]. intros x Hx. rewrite el_shadowA_size in Hx. right; right. lia. }

    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut; [eapply (pw_walk2 usp sp' f _ gp w0 w1 w2 (Z_to_bv 64 (f + 120)) g1 g2 g3 g4 g5 g6 g7 (Z_to_bv 64 (f + 208)) (Z_to_bv 64 SHB) (Z_to_bv 64 f) (Z_to_bv 64 A) (Z_to_bv 64 16) (Z_to_bv 64 (f + 120)) w3 w4 w5 w6
                               _ _ _ _ _ _ _ F2 fc m2 FPOS ltac:(ul) FP2 MI2)|].
    cbv beta. intros ms3 (m3 & -> & MU3 & WM3 & MI3 & FP3). apply evt_done. unfold pw_st.
    assert (ART3 : ART RT Σ m3).
    { apply (art_client_write RT AF Σ m2 m3 sp' ART2 ltac:(rewrite SPg; ul)); [| exact WM3]. eapply CLW; [exact MU3|]. repeat constructor; cbn [fst snd]; lia. }
    assert (ST3 : stk asegs m3 lo sp').
    { apply (stk_agree asegs m2 m3 _ _ ST2); [| exact WM3]. apply (agree_of_munch _ _ _ _ MU3). intros x Hx. cbn [outside]. repeat split; ul. }
    assert (FS3 : rw_cells asegs m3 (shad f) (el_shadowA 0 0 (-8) (-8) t)).
    { eapply rw_cells_agree_nw; [exact FS2|]. apply (agree_of_munch _ _ _ _ MU3). intros x Hx. rewrite el_shadowA_size in Hx. cbn [outside]. split; [ul| exact I]. }

    eapply (aevt_memsetP RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc m3 (f + 160) 16 z8 lo eq_refl eq_refl eq_refl
              ltac:(ul) ltac:(lia) (MSTEP m3 (-8) (-8) t _ (f + 160) 16 ART3 FS3 FP3 eq_refl ltac:(lia) ltac:(lia) ltac:(lia)) ART3 MI3 (COK m3 ST3)).
    intros y0 y1 y2 e1 e2 e3 e4 e5 e6 e7 y3 y4 y5 y6 F4 m4 (ART4 & MI4 & WM4 & ST4) PRES4 BY4. rewrite EU in ST4, PRES4.
    rewrite ret_pc_even by lia. change (Z.to_nat 16) with 16%nat in BY4.
    lazymatch type of FP3 with rw_cells _ _ _ (fz_parser _ ?x1 _ _ ?x17 _ _ _ _ ?x57 (CB 16 ?x64)) =>
      assert (FP4 : rw_cells asegs m4 (f + 96) (parser_init x1 x17 x57));
      [ unfold parser_init, fz_parser in *;
        apply (cells_mid_update m3 m4 (f + 96) [C1 (Z_to_bv 8 0); CB 7 x1; C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 3 x17; C4 (Z_to_bv 64 12); CB 24 (repeat z8 24); C8 (Z_to_bv 64 4294967295); C1 (Z_to_bv 8 0); CB 7 x57]
                 16 x64 (repeat z8 16) [] FP3); [| exact WM4| | reflexivity];
        [ apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES4); intros x (Hx & Hn); cbn [app cells_size csize Nat.add] in Hx, Hn;
          split; [right; right; right; left; exists f, 4%nat; change (fs_size 4) with 1024; split; [exact INF| lia]| lia]
        | cbn [cells_size csize Nat.add]; replace (f + 96 + Z.of_nat 64) with (f + 160) by lia; exact BY4 ] |]
    end.
    assert (FS4 : rw_cells asegs m4 (shad f) (el_shadowA 0 0 (-8) (-8) t)).
    { eapply rw_cells_agree_nw; [exact FS3|]. eapply RTW; [exact PRES4| lia| lia|]. intros x Hx. rewrite el_shadowA_size in Hx. right; right. lia. }

    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut; [eapply (pw_walk3 usp sp' f _ gp y0 y1 y2 (Z_to_bv 64 (f + 160)) e1 e2 e3 e4 e5 e6 e7 (Z_to_bv 64 SHB) (Z_to_bv 64 f) (Z_to_bv 64 A) (Z_to_bv 64 16) (Z_to_bv 64 (f + 120)) y3 y4 y5 y6
                               t F4 fc m4 FPOS ltac:(ul) ltac:(ul) ltac:(ul) FS4 MI4)|].
    cbv beta. intros ms5 (m5 & -> & MU5 & WM5 & MI5 & FS5). apply evt_done. unfold pw_st.
    assert (ART5 : ART RT Σ m5).
    { apply (art_client_write RT AF Σ m4 m5 sp' ART4 ltac:(rewrite SPg; ul)); [| exact WM5]. eapply CLW; [exact MU5|]. repeat constructor; cbn [fst snd]; lia. }
    assert (ST5 : stk asegs m5 lo sp').
    { apply (stk_agree asegs m4 m5 _ _ ST4); [| exact WM5]. apply (agree_of_munch _ _ _ _ MU5). intros x Hx. cbn [outside]. split; [ul| exact I]. }
    assert (FE5 : rw_cells asegs m5 (f + 208) [CB 16 je]).
    { eapply rw_cells_agree_nw; [exact FE|].
      eapply agree_trans; [apply (agree_of_munch _ _ _ _ MU1); intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; repeat split; ul|].
      eapply agree_trans; [eapply RTW; [exact PRES2| lia| lia| intros x Hx; cbn [cells_size csize Nat.add] in Hx; right; left; split; lia]|].
      eapply agree_trans; [apply (agree_of_munch _ _ _ _ MU3); intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; repeat split; ul|].
      eapply agree_trans; [eapply RTW; [exact PRES4| lia| lia| intros x Hx; cbn [cells_size csize Nat.add] in Hx; right; left; split; lia]|].
      apply (agree_of_munch _ _ _ _ MU5); intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; repeat split; ul. }

    pose proof FE5 as [_ WRE]. cbn [cells_size csize Nat.add] in WRE. change (Z.of_nat 16) with 16 in WRE.
    pose proof (el_fobj_dst RT Σ m5 (Z_to_bv 64 sp') f (f + 208) 16 (f + 208) 16 (el_elem_fobj RT Σ m5 f 0 0 (-8) t FS5 FRSg FPOS F64) ltac:(lia) FRSg WRE
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as CDE.
    eapply (aevt_memsetP RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F4 fc m5 (f + 208) 16 z8 lo eq_refl eq_refl eq_refl
              ltac:(ul) ltac:(lia) CDE ART5 MI5 (COK m5 ST5)).
    intros v0 v1 v2 b1 b2 b3 b4 b5 b6 b7 v3 v4 v5 v6 F6 m6 (ART6 & MI6 & WM6 & ST6) PRES6 BY6. rewrite EU in ST6, PRES6.
    rewrite ret_pc_even by lia. change (Z.to_nat 16) with 16%nat in BY6.

    assert (NCL : forall x, (f <= x < f + 1024 \/ shad f <= x < shad f + 128 \/ sp' <= x < usp) -> client_static x \/ in_live (rt_live RT Σ) x -> False).
    { intros x Hx [H|H].
      - pose proof (client_static_range _ H) as R. clear - Hx R FSEG SHB0 SPR LOW LOR SP0R. ul.
      - destruct H as (p & k & Hin & Hr). pose proof (FLV p k Hin) as Y1. pose proof (FSL p k Hin) as Y2.
        pose proof (af_live_range RT AF Σ m p k ARTg Hin) as (_ & Y3 & _). rewrite SPg in Y3. clear - Hx Hr Y1 Y2 Y3 LOW LOR SPR. ul. }
    assert (AG16 : forall P : Z -> Prop,
              (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x /\ ~ ((f + 120 <= x < f + 176) \/ (f + 208 <= x < f + 224) \/ (shad f + 26 <= x < shad f + 28))) ->
              agree_on P m1 m6).
    { intros P HP a Ha. destruct (HP _ Ha) as [CL NR].
      rewrite (PRES6 a), (MU5 a), (PRES4 a), (MU3 a), (PRES2 a); [reflexivity| | | | | | | |].
      - exact CL. - lia.
      - cbn [outside]. split; [lia| exact I].
      - exact CL. - lia.
      - cbn [outside]. split; [lia| exact I].
      - exact CL. - lia. }
    assert (AGW : forall P : Z -> Prop,
              (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x
                              /\ ~ ((f + 96 <= x < f + 176) \/ (f + 208 <= x < f + 224) \/ (shad f + 12 <= x < shad f + 28) \/ (sp' + 24 <= x < sp' + 40))) ->
              agree_on P m m6).
    { intros P HP. eapply agree_trans; [| apply AG16; intros x Hx; destruct (HP _ Hx) as [CL NR]; split; [exact CL| clear - NR; lia]].
      apply (agree_of_munch _ _ _ _ MU1). intros x Hx. destruct (HP _ Hx) as [_ NR]. cbn [outside]. clear - NR. repeat split; lia. }

    assert (AGF : forall P : Z -> Prop,
              (forall x, P x -> (sp' + 40 <= x < usp) \/ (f <= x < f + 1016 /\ ~ (f + 96 <= x < f + 176) /\ ~ (f + 208 <= x < f + 224))
                                \/ (shad f <= x < shad f + 128 /\ ~ (shad f + 12 <= x < shad f + 28))) -> agree_on P m m6).
    { intros P HP. apply AGW. intros x Hx. destruct (HP _ Hx) as [H1|[(H1 & H2 & H3)|[H1 H2]]].
      - split; [left; ul| clear - H1 FLO LOR SHT SPR; ul].
      - split; [right; right; right; left; exists f, 4%nat; change (fs_size 4) with 1024; split; [exact INF| lia]| clear - H1 H2 H3 FLO LOR FSELF SPR; ul].
      - split; [right; right; right; right; exists f, 4%nat; change (fs_size 4) with 1024; split; [exact INF| unfold shad in *; Z.div_mod_to_equations; lia]|].
        clear - H1 H2 FSELF SHT LOR SPR. ul. }
    assert (LIB6 : el_libA m6).
    { apply (el_libA_agree m m6 LIB). apply AGW. intros x Hx. pose proof (el_lib_rng_static x Hx) as [CS _]. split; [right; left; exact CS|].
      intros E. refine (NCL x _ (or_introl CS)). clear - E SPR. lia. }
    assert (BS6 : bytes_at asegs m6 d bs).
    { apply (bytes_at_agree asegs m m6 _ _ BS). apply AGW. intros x Hx. cbv beta in Hx.
      assert (IL : in_live (rt_live RT Σ) x) by (exists pL, kL; split; [unfold vliveA in VL; rewrite VL; apply in_or_app; right; exact HinL| subst n; lia]).
      split; [right; right; left; exact IL| intros E; refine (NCL x _ (or_intror IL)); clear - E SPR; lia]. }
    assert (PRES6' : rt_pres_fp (rt_live RT Σ0) [] usp EL_LIB_FP m0 m6).
    { intros a Ha Ho. rewrite <- (PRES a Ha Ho). apply (AGW (fun x => x = bv_unsigned a)); [| reflexivity]. intros x ->.
      split; [apply (aclient_mono _ _ _ _ _ _ _ Ha); [unfold vliveA in VL; rewrite VL; intros e He; apply in_or_app; right; exact He| intros e []| lia]|]. intros E.
      destruct Ha as [H|[H|[H|[H|H]]]]; [clear - H E SPR FLO LOR SHT; ul| exact (NCL (bv_unsigned a) ltac:(clear - E SPR; lia) (or_introl H))
        | refine (NCL (bv_unsigned a) ltac:(clear - E SPR; lia) (or_intror _)); destruct H as (p & k & Hin & Hr); exists p, k; split; [unfold vliveA in VL; rewrite VL; apply in_or_app; right; exact Hin| exact Hr]
        | destruct H as (? & ? & [] & _)| destruct H as (? & ? & [] & _)]. }
    assert (ELTS6 : rw_cells asegs m6 A (velts (el_elsA d bs))).
    { eapply rw_cells_agree_nw; [exact ELTS|]. apply AGW. intros x Hx. rewrite velts_size, ELEN in Hx.
      assert (IL : in_live (rt_live RT Σ) x) by (exists A, (16 * Z.of_nat (el_PA bs)); split; [exact INA| lia]).
      split; [right; right; left; exact IL| intros E; refine (NCL x _ (or_intror IL)); clear - E SPR; lia]. }
    lazymatch type of FP4 with rw_cells _ _ _ (parser_init ?x1 ?x17 ?x57) =>
    eapply (CUTP4 Σ m6 _ v0 v1 v2 _ b1 b2 b3 b4 b5 b6 b7 _ v3 v4 v5 v6 F6 fc j0 j8 j10 j15 jr h3 t j56 j176 j224 jos j528 x1 x17 x57 idx act sel A);
      cbn [lf_usp lf_S1 lf_F lf_lo] end.
    +   unfold el_baseA. cbn [lf_usp lf_S1 lf_F lf_lo]. split; [exact ART6|]. split; [exact MI6|]. split; [exact ST6|].
      split; [eapply stk_agree_nw; [exact STp|]; apply AGF; intros x Hx; cbv beta in Hx; left; lia|].
      split; [eapply rw_cells_agree_nw; [exact FRs|]; apply AGF; intros x Hx; unfold fa_saved in Hx; cbn [cells_size csize Nat.add] in Hx; left; lia|].
      split; [eapply rw_cells_agree_nw; [exact FH|]; apply AGF; intros x Hx; unfold fz_hdr in Hx; cbn [cells_size csize Nat.add] in Hx; right; left; repeat split; lia|].
      split; [exact BS6|]. split; [exact LIB6|]. split; [exact PRES6'|]. split; [exact FRSg| exact SPg].
    +   unfold el_locals4. eapply rw_cells_agree_nw; [exact FRl1|]. apply AG16. intros x Hx. cbn [cells_size csize Nat.add app] in Hx. split; [left; ul| ul].
    + exact ACT. + exact SEL. + exact N10.
    +   eapply rw_cells_agree_nw; [exact FS5|]. eapply RTW; [exact PRES6| lia| lia|]. intros x Hx. rewrite el_shadowA_size in Hx. right; right. lia.
    +   split; [exact ELS|]. split; [exact SZC|]. split; [exact CAPB|]. split; [exact A0|]. split; [exact AH|]. split; [| right; exact (conj CP1 (conj A16 (conj APOS ELTS6)))].
      eapply rw_cells_agree_nw; [exact SV|]. apply AGF. intros x Hx. cbn [cells_size csize Nat.add] in Hx. right; left. repeat split; lia.
    + eapply rw_cells_agree_nw; [exact F56|]. apply AGF. intros x Hx. cbn [cells_size csize Nat.add] in Hx. right; left. repeat split; lia.
    +   eapply rw_cells_agree_nw; [exact FP4|]. eapply agree_trans.
      * apply (agree_of_munch _ _ _ _ MU5). intros x Hx. unfold parser_init, fz_parser in Hx. cbn [cells_size csize Nat.add] in Hx. cbn [outside]. split; [ul| exact I].
      * eapply RTW; [exact PRES6| lia| lia|]. intros x Hx. unfold parser_init, fz_parser in Hx. cbn [cells_size csize Nat.add] in Hx. right; left. split; lia.
    + eapply rw_cells_agree_nw; [exact F176|]. apply AGF. intros x Hx. cbn [cells_size csize Nat.add] in Hx. right; left. repeat split; lia.
    +   split; [split; [cbn; tauto| change (cells_bytes _) with (repeat z8 16); exact BY6]|].
      cbn [cells_size csize Nat.add]. exact (wr_at_transport asegs m5 m6 (f + 208) 16 WRE WM6).
    + eapply rw_cells_agree_nw; [exact F224|]. apply AGF. intros x Hx. cbn [cells_size csize Nat.add] in Hx. right; left. repeat split; lia.
    + eapply rw_cells_agree_nw; [exact FO|]. apply AGF. intros x Hx. cbn [cells_size csize Nat.add] in Hx. right; left. repeat split; lia.
    + eapply rw_cells_agree_nw; [exact F528|]. apply AGF. intros x Hx. cbn [cells_size csize Nat.add] in Hx. right; left. repeat split; lia.
    + exact VL.
    + exact CR.
    + exact FRM.
Qed.
End Parse1.
