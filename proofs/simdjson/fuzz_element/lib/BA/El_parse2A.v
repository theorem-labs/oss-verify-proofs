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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_iface3 RT_iface5. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_hkit2 Sj_new. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_num_akit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_h_alloc Sj_stage2_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA Atp_setcapA Atp_activewA Atp_activeA Atp_defsA Atp_kitA Atp_h_defsA Atp_h_vkitA Atp_hkit5A Atp_hkit6A Atp_pidwA Atp_pidiA Atp_pid0A Atp_pdtorA RT_rtf Pj_rtkA Pj_lftoi1A Pj_defsA Pj_os_defsA Pj_cpsA El_defsA El_lf1A El_lf2A El_lf2bA El_costA El_phasesA El_frontA El_parsewA El_parsekA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Parse2.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC2 : rt_contracts2 RT.
Hypothesis AFC : forall Σ m, ART RT Σ m -> cli_got_nothrow m.
Variable PMc : Model -> Prop.

Local Ltac ul := unfold FUZZ_STACK, PID_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Theorem el_parse_p2 : forall (Σ0 : rts RT) (m0 : mem) (X : lfA) (d : Z) (bs : list byte) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (K : config -> Prop),
    fdfs_only PMc -> mat_stable PMc -> lfA_ok X -> rt_sp0 RT Σ0 - STACK_WIN <= lf_lo X ->
    0 < d -> Z.of_nat (length bs) < 2^26 ->
    ((exists p n, In (p, n) (rt_live RT Σ0) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ (bs = [] /\ d < SEGTOP_A)) ->
    (forall p n, In (p, n) (rt_live RT Σ0) -> 0 < n) -> Z.of_nat (length (rt_live RT Σ0)) + FUZZ_LIVE <= LIVE_MAX -> FUZZ_COST <= rt_credit RT Σ0 ->
    cutP7 RT PMc Σ0 m0 X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 K ->
    cutP4 RT PMc Σ0 m0 X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 K.
Proof using AF RC2 AFC.
  intros Σ0 m0 X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 K FDO MST LK LOW D0 BSL INLV LVPOS LVB CR0 CUTP7.
  unfold cutP4. intros Σ m x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x10 t3 t4 t5 t6 F fc j0 j8 j10 j15 jr h3 t j56 j176 j224 jos j528 q1 q17 q57 idx act sel A
    BASE FRl ACT SEL N10 FS VR F56 FP F176 FE F224 FO F528 VL CR FRM.
  pose proof BASE as (ARTg & MIg & STg & STp & FRs & FH & BS & LIB & PRES & FRSg & SPg).
  pose proof LK as [(SPR & SPA') (SPT & SPA) (LLO & LOR) (FPOS & F64 & FSEG & FLO) (FSELF & SHB0 & SHT)].
  destruct X as [usp sp' f lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  pose proof (af_sp0_range RT AF Σ m ARTg) as SP0R. rewrite SPg in SP0R.
  pose proof (rc2_rt RT RC2) as RC. pose proof (rtf_of_rt RT RC) as RTF.
  assert (EU : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; ul).
  assert (INF : In (f, 4%nat) (rt_frames RT Σ)) by (rewrite FRSg; left; reflexivity).
  set (n := Z.of_nat (length bs)) in *.

  pose proof VR as (ELS & SZC & CAPB & A0 & AH & SV & BLKq).
  assert (P2 : (2 <= el_PA bs)%nat) by (unfold el_PA, atp_P; lia). pose proof (vcap_iter_inv (el_PA bs) 0 0 ltac:(lia) ltac:(lia)) as CAPI. rewrite Z.add_0_l in CAPI.
  destruct BLKq as [(C0 & _)|(CP1 & A16 & APOS & ELTS)]; [exfalso; lia|].
  assert (INA : In (A, 16 * Z.of_nat (el_PA bs)) (rt_live RT Σ)).
  { unfold vliveA, vblockA in VL. rewrite VL. apply in_or_app. left. destruct (Z.eqb_spec (vcap_iter (el_PA bs) 0 0) 0); [lia|]. apply ann_block_vis. }
  pose proof (af_live_range RT AF Σ m A _ ARTg INA) as (AR0 & AR1 & AR2). rewrite SPg in AR1.
  destruct (el_els_two d bs) as (erest & EELS & ELEN).
  destruct INLV as [(pL & kL & HinL & PL1 & PL2)|(E0 & _)]; [| exfalso; subst bs n; cbn [length] in *; lia].
  assert (HinL' : In (pL, kL) (rt_live RT Σ)) by (unfold vliveA in VL; rewrite VL; apply in_or_app; right; exact HinL).
  pose proof (af_live_range RT AF Σ m pL kL ARTg HinL') as (_ & RL1 & _). rewrite SPg in RL1.
  pose proof (el_els_rng d bs (el_s1A d bs) D0 ltac:(lia) ltac:(rewrite EELS; right; left; reflexivity)) as R1.
  assert (R1' : 0 <= fst (el_s1A d bs) < 2^64 /\ 0 <= snd (el_s1A d bs) < 2^64).
  { destruct R1 as [E|(Q1 & Q2 & Q3)]; [rewrite E; cbn; lia|]. clear - Q1 Q2 Q3 D0 PL1 PL2 RL1 SP0R. subst n. ul. }
  set (p1 := fst (el_s1A d bs)) in *. set (l1 := snd (el_s1A d bs)) in *.
  set (p0 := fst (el_s0A d bs)) in *. set (l0 := snd (el_s0A d bs)) in *.
  assert (COK : forall (Σx : rts RT) mx, rt_sp0 RT Σx = rt_sp0 RT Σ0 -> stk asegs mx lo sp' -> call_ok RT Σx mx (Z_to_bv 64 sp') lo).
  { intros Σx mx SPx STx. unfold call_ok. rewrite EU, SPx. split; [exact STx|]. split; [ul|]. split; [ul|]. split; [ul| clear - SPA'; Z.div_mod_to_equations; lia]. }

  assert (SHZ : shz m (A + 16) 16).
  { pose proof (shz_live RT AF Σ m A _ ARTg INA ltac:(clear - A16; Z.div_mod_to_equations; lia)) as XZ.
    eapply shz_sub; [exact XZ| lia|]. clear - P2 CAPI. Z.div_mod_to_equations. nia. }

  pose proof ELTS as ELTS'. rewrite EELS in ELTS'. cbn [velts] in ELTS'.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pw_walk4 usp sp' f A p0 l0 p1 l1 x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz (f + 208)) (wz f) x10 (wz (f + 120)) t3 t4 t5 t6 _ F fc m
                             APOS ltac:(lia) ltac:(clear - A16; Z.div_mod_to_equations; lia) (proj1 R1') (proj2 R1') ELTS' SHZ (AFC Σ m ARTg) MIg)|].
  cbv beta. clear ELTS'. intros ms1 BR. apply evt_done. unfold pw_st in BR.
  destruct BR as [(BIG & a0' & a1' & ->)|(LEN & ->)].
  -
    eapply (CUTP7 Σ m x1 t0 t1 t2 a0' a1' a2 a3 a4 a5 a6 a7 (wz SHB) t3 t4 t5 t6 F fc j0 j8 j10 j15 jr h3 t j56 j176 j224 jos j528 q1 q17 q57 idx act sel A 0 []);
      [exact BASE| exact FRl| exact ACT| exact SEL| exact N10| exact FS| exact VR| exact F56| exact FP| exact F176| exact FE| exact F224| exact FO| exact F528| | clear - CR; lia| exact FRM].
    left. split; [reflexivity|]. split; [reflexivity| exact VL].
  -
    assert (L1P : 0 <= l1 <= 1048512) by lia.

    eapply (aevt_rt RT PMc Σ K _ _
             (newarr_nt_ok RT AF (rf_malloc RT RTF) Σ PMc (wz 0xb19fc) (wz sp') gp (wz TPV_A) t0 t1 t2 (wz usp) (wz sp') (wz (l1 + 64)) (wz 0x2eae8) a2 a3 a4 a5 a6 a7
                (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 96)) (wz (f + 208)) (wz p1) (wz f) (wz A) (wz l1) (wz (f + 120)) t3 t4 t5 t6 F fc m (l1 + 64) lo
                FDO MST ltac:(lia) eq_refl eq_refl
                ltac:(unfold vliveA in VL; rewrite VL, length_app; pose proof (vblockA_length A (vcap_iter (el_PA bs) 0 0) (Z.of_nat (el_PA bs))); unfold FUZZ_LIVE in LVB; lia)
                ltac:(pose proof (mcost_pad_bound l1 L1P); pose proof (el_vcost_bound bs BSL); unfold FUZZ_COST in CR0; lia)
                ARTg MIg ltac:(rewrite EU; exact STg) ltac:(rewrite SPg; exact LOW) ltac:(rewrite EU; ul) ltac:(rewrite EU; ul) ltac:(rewrite EU; clear - SPA'; Z.div_mod_to_equations; lia) FRM));
      [exact FRM|].
    intros c (Σ1 & p & HA & LV1 & FRS1 & SP1 & CR1 & P0 & P16 & PT). eexists Σ1, _. split; [exact HA|].
    intros ms' (m1 & RS & (ART1 & MI1 & WM1 & ST1) & PRES1 & WR1 & AC1) FRM1.
    destruct RS as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->). cbn [ms_fcsr] in FRM1.
    rewrite EU in ST1, PRES1. rewrite (ret_pc_even 0xb19fc) by lia. rewrite FRSg in FRS1. rewrite SPg in SP1.
    assert (INP : In (p, l1 + 64) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
    pose proof (af_live_range RT AF Σ1 m1 p (l1 + 64) ART1 INP) as (_ & PR1 & PR2). rewrite SP1 in PR1.
    assert (INCL : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ1)) by (intros e He; rewrite LV1; right; exact He).

    assert (FRESH : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x -> ~ (p <= x < p + (l1 + 64))).
    { intros x Hx Hin. destruct Hx as [H|[H|[H|[H|H]]]].
      - clear - H Hin PR1 LOW LOR SPR. ul.
      - pose proof (client_static_range _ H) as R. clear - R Hin PR2. unfold SEGTOP_A in *. lia.
      - destruct H as (q & k & Hq & Hr). pose proof (af_live_disj RT AF Σ1 m1 p (l1 + 64) q k [] _ ART1 ltac:(rewrite LV1; reflexivity) Hq). lia.
      - destruct H as (f' & k' & Hf & Hr). rewrite FRSg in Hf. destruct Hf as [Hf|[]]. injection Hf as <- <-.
        pose proof (af_frames_range RT AF Σ1 m1 f 4%nat ART1 ltac:(rewrite FRS1; left; reflexivity)) as (_ & _ & _ & FLV1). pose proof (FLV1 p (l1 + 64) INP).
        change (fs_size 4) with 1024 in *. lia.
      - destruct H as (f' & k' & Hf & Hr). rewrite FRSg in Hf. destruct Hf as [Hf|[]]. injection Hf as <- <-.
        pose proof (af_fshadow_apart RT AF Σ1 m1 f 4%nat ART1 ltac:(rewrite FRS1; left; reflexivity)) as (FSL1 & _). pose proof (FSL1 p (l1 + 64) INP). lia. }

    assert (FIN : forall (mx : mem) (doc : list byte) (rax a0x a1x a2x t0x t1x t2x a3x a4x a5x a6x a7x t3x t4x t5x t6x : word) (Fx : bvmap 5 word),
              ART RT Σ1 mx -> mem_inv asegs mx -> stk asegs mx lo sp' -> Z.of_nat (length doc) = l1 ->
              (forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) sp' (bv_unsigned a) -> mx a = m a) ->
              bytes_at asegs mx p (doc ++ repeat z8 64) ->
              aevt RT PMc Σ1 K (MS (mkR rax (wz sp') gp (wz TPV_A) t0x t1x t2x (wz usp) (wz sp') a0x a1x a2x a3x a4x a5x a6x a7x
                              (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 96)) (wz (f + 208)) (wz p1) (wz f) (wz p) (wz l1) (wz (f + 120)) t3x t4x t5x t6x)
                         Fx (wz 0xb1a34) fc1 None mx (seg_rom asegs))).
    { intros mx doc rax a0x a1x a2x t0x t1x t2x a3x a4x a5x a6x a7x t3x t4x t5x t6x Fx ARTx MIx STx DL AGm BYP.
      assert (AGP : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x) -> agree_on P m mx).
      { intros P HP a Ha. apply AGm. exact (HP _ Ha). }

      assert (INS : forall x, sp' <= x < usp -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x) by (intros x Hx; left; ul).
      assert (INFR : forall x, f <= x < f + 1016 -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x).
      { intros x Hx. right; right; right; left. exists f, 4%nat. change (fs_size 4) with 1024. split; [exact INF| lia]. }
      assert (INSH : forall x, shad f <= x < shad f + 128 -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x).
      { intros x Hx. right; right; right; right. exists f, 4%nat. change (fs_size 4) with 1024. split; [exact INF| unfold shad in *; Z.div_mod_to_equations; lia]. }
      replace (Z_to_bv 64 l1) with (Z_to_bv 64 (Z.of_nat (length doc))) by (rewrite DL; reflexivity).
      eapply (CUTP7 Σ1 mx rax t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x (wz p1) t3x t4x t5x t6x Fx fc1 j0 j8 j10 j15 jr h3 t j56 j176 j224 jos j528 q1 q17 q57 idx act sel A p doc);
        cbn [lf_usp lf_S1 lf_F lf_lo].
      - unfold el_baseA. cbn [lf_usp lf_S1 lf_F lf_lo]. split; [exact ARTx|]. split; [exact MIx|]. split; [exact STx|].
        split; [eapply stk_agree_nw; [exact STp|]; apply AGP; intros x Hx; cbv beta in Hx; apply INS; lia|].
        split; [eapply rw_cells_agree_nw; [exact FRs|]; apply AGP; intros x Hx; unfold fa_saved in Hx; cbn [cells_size csize Nat.add] in Hx; apply INS; lia|].
        split; [eapply rw_cells_agree_nw; [exact FH|]; apply AGP; intros x Hx; unfold fz_hdr in Hx; cbn [cells_size csize Nat.add] in Hx; apply INFR; lia|].
        split; [apply (bytes_at_agree asegs m mx _ _ BS); apply AGP; intros x Hx; cbv beta in Hx; right; right; left; exists pL, kL; split; [exact HinL'| subst n; lia]|].
        split; [apply (el_libA_agree m mx LIB); apply AGP; intros x Hx; right; left; exact (proj1 (el_lib_rng_static x Hx))|].
        split; [| split; [rewrite FRS1; reflexivity| exact SP1]].
        intros a Ha Ho. rewrite <- (PRES a Ha Ho). apply AGm. apply (aclient_mono _ _ _ _ _ _ _ Ha); [unfold vliveA in VL; rewrite VL; intros e He; apply in_or_app; right; exact He| intros e []| lia].
      - unfold el_locals4. eapply rw_cells_agree_nw; [exact FRl|]. apply AGP. intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply INS. lia.
      - exact ACT. - exact SEL. - exact N10.
      - eapply rw_cells_agree_nw; [exact FS|]. apply AGP. intros x Hx. rewrite el_shadowA_size in Hx. apply INSH. lia.
      - split; [exact ELS|]. split; [exact SZC|]. split; [exact CAPB|]. split; [exact A0|]. split; [exact AH|]. split; [| right; split; [exact CP1|]; split; [exact A16|]; split; [exact APOS|]].
        + eapply rw_cells_agree_nw; [exact SV|]. apply AGP. intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply INFR. lia.
        + eapply rw_cells_agree_nw; [exact ELTS|]. apply AGP. intros x Hx. rewrite velts_size, ELEN in Hx. right; right; left. exists A, (16 * Z.of_nat (el_PA bs)). split; [exact INA| lia].
      - eapply rw_cells_agree_nw; [exact F56|]. apply AGP. intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply INFR. lia.
      - eapply rw_cells_agree_nw; [exact FP|]. apply AGP. intros x Hx. unfold parser_init, fz_parser in Hx. cbn [cells_size csize Nat.add] in Hx. apply INFR. lia.
      - eapply rw_cells_agree_nw; [exact F176|]. apply AGP. intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply INFR. lia.
      - eapply rw_cells_agree_nw; [exact FE|]. apply AGP. intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply INFR. lia.
      - eapply rw_cells_agree_nw; [exact F224|]. apply AGP. intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply INFR. lia.
      - eapply rw_cells_agree_nw; [exact FO|]. apply AGP. intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply INFR. lia.
      - eapply rw_cells_agree_nw; [exact F528|]. apply AGP. intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply INFR. lia.
      - right. split; [exact P0|]. split; [exact P16|]. split; [lia|]. split; [lia|]. split; [rewrite padded_bytes_chars; exact BYP|].
        rewrite LV1, DL. unfold vliveA in VL. rewrite VL. reflexivity.
      - rewrite CR1. pose proof (mcost_pad_bound l1 L1P). clear - H CR. lia.
      - exact FRM1. }

    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut; [eapply (pw_walk5 usp sp' f p l1 (wz 0xb19fc) gp u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 (wz (f + 208)) (wz p1) (wz f) (wz A) (wz (f + 120)) u3 u4 u5 u6 F1 fc1 m1 P0 ltac:(ul) ltac:(lia) MI1)|].
    cbv beta. intros ms2 <-. apply evt_done. unfold pw_st.

    assert (CDP : checked_dst RT Σ1 m1 (Z_to_bv 64 sp') (p + l1) 64).
    { split; [| split].
      - intros _. split; [apply (acc_sub asegs m1 p (l1 + 64)); [exact AC1| lia| lia]|]. left. exists p, (l1 + 64). split; [exact INP| lia].
      - intros i Hi. rewrite EU. right; right; left. exists p, (l1 + 64). split; [exact INP| lia].
      - apply (wr_at_sub m1 p (l1 + 64)); [exact WR1| lia| lia| lia]. }
    eapply (aevt_memsetP RT RC PMc FDO MST Σ1 K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 m1 (p + l1) 64 z8 lo eq_refl eq_refl eq_refl
              ltac:(ul) ltac:(lia) CDP ART1 MI1 (COK Σ1 m1 SP1 ST1)).
    intros w0 w1 w2 g1 g2 g3 g4 g5 g6 g7 w3 w4 w5 w6 F2 m2 (ART2 & MI2 & WM2 & ST2) PRES2 BY2. rewrite EU in ST2, PRES2.
    rewrite (ret_pc_even 0xb1a14) by lia. change (Z.to_nat 64) with 64%nat in BY2.
    assert (AG02 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) sp' (bv_unsigned a) -> m2 a = m a).
    { intros a Ha. rewrite (PRES2 a), (PRES1 a); [reflexivity| exact Ha| | pose proof (FRESH _ Ha); lia].
      apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact INCL| rewrite FRS1, FRSg; intros e He; exact He| lia]. }

    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut; [eapply (pw_walk6 usp sp' f p p1 l1 (wz 0xb1a14) gp w0 w1 w2 (wz (p + l1)) g1 g2 g3 g4 g5 g6 g7 (wz (f + 208)) (wz f) (wz (f + 120)) w3 w4 w5 w6 F2 fc1 m2 ltac:(lia) MI2)|].
    cbv beta. intros ms3 [(LZ & ->)|(LP & ->)]; apply evt_done; unfold pw_st.
    +
      apply (FIN m2 [] (wz 0xb1a14) (wz (p + l1)) g1 g2 w0 w1 w2 g3 g4 g5 g6 g7 w3 w4 w5 w6 F2 ART2 MI2 ST2 ltac:(cbn; lia) AG02).
      cbn [app]. rewrite <- (Z.add_0_r p) at 1. rewrite <- LZ. exact BY2.
    +
      destruct R1 as [E|(Q1 & Q2 & Q3)]; [exfalso; subst p1 l1; rewrite E in LP; cbn in LP; lia|].
      set (doc := firstn (Z.to_nat l1) (skipn (Z.to_nat (p1 - d)) bs)).
      assert (DLEN : Z.of_nat (length doc) = l1) by (subst doc; rewrite length_firstn, length_skipn; subst n; lia).
      assert (BSD : bytes_at asegs m p1 doc).
      { subst doc. replace p1 with (d + Z.of_nat (Z.to_nat (p1 - d))) at 1 by lia. apply bytes_at_firstn. apply bytes_at_skipn; [exact BS| subst n; lia]. }
      assert (ILD : forall x, p1 <= x < p1 + l1 -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x).
      { intros x Hx. right; right; left. exists pL, kL. split; [exact HinL'| subst n; lia]. }
      assert (BSD2 : bytes_at asegs m2 p1 doc) by (apply (bytes_at_agree asegs m m2 _ _ BSD); intros a Ha; apply AG02; apply ILD; rewrite DLEN in Ha; exact Ha).
      pose proof (af_live_disj RT AF Σ1 m1 p (l1 + 64) pL kL [] _ ART1 ltac:(rewrite LV1; reflexivity) HinL') as DJ.
      assert (CSRC : checked_src RT Σ1 m2 (Z_to_bv 64 sp') lo p1 (Z.of_nat (length doc))).
      { rewrite DLEN. split; [| left; clear - Q3 PL2 RL1 LOW; subst n; lia].
        intros _. split.
        - pose proof (af_acc_live RT AF Σ1 m2 pL kL ART2 (INCL _ HinL')) as [_ ACL]. apply (acc_sub asegs m2 pL kL); [exact ACL| lia| subst n; lia].
        - left. exists pL, kL. split; [exact (INCL _ HinL')| subst n; lia]. }
      assert (CDST : checked_dst RT Σ1 m2 (Z_to_bv 64 sp') p (Z.of_nat (length doc))).
      { rewrite DLEN. pose proof (af_acc_live RT AF Σ1 m2 p (l1 + 64) ART2 INP) as [WRp ACp]. split; [| split].
        - intros _. split; [apply (acc_sub asegs m2 p (l1 + 64)); [exact ACp| lia| lia]|]. left. exists p, (l1 + 64). split; [exact INP| lia].
        - intros i Hi. rewrite EU. right; right; left. exists p, (l1 + 64). split; [exact INP| lia].
        - apply (wr_at_sub m2 p (l1 + 64)); [exact WRp| lia| lia| lia]. }
      eapply (aevt_memcpyP RT RC PMc FDO MST Σ1 K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc1 m2 p p1 doc lo eq_refl eq_refl ltac:(rewrite DLEN; reflexivity)
                ltac:(ul) ltac:(clear - Q1 Q2 Q3 PL2 RL1 SP0R D0; subst n; ul) ltac:(rewrite DLEN; lia) BSD2 CSRC CDST ltac:(rewrite DLEN; subst n; lia) ART2 MI2 (COK Σ1 m2 SP1 ST2)).
      intros y0 y1 y2 e1 e2 e3 e4 e5 e6 e7 y3 y4 y5 y6 F3 m3 (ART3 & MI3 & WM3 & ST3) PRES3 BY3. rewrite EU in ST3, PRES3.
      rewrite (ret_pc_even 0xb1a28) by lia. rewrite DLEN in PRES3.
      assert (AG03 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) sp' (bv_unsigned a) -> m3 a = m a).
      { intros a Ha. rewrite (PRES3 a); [exact (AG02 a Ha)| | pose proof (FRESH _ Ha); lia].
        apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact INCL| rewrite FRS1, FRSg; intros e He; exact He| lia]. }

      apply (aevt_evt RT AF PMc MST).
      eapply evt_cut; [eapply (pw_walk6b usp sp' f (wz 0xb1a28) gp y0 y1 y2 (wz p) e1 e2 e3 e4 e5 e6 e7 (wz (f + 208)) (wz p1) (wz f) (wz p) (wz l1) (wz (f + 120)) y3 y4 y5 y6 F3 fc1 m3 MI3)|].
      cbv beta. intros ms4 <-. apply evt_done. unfold pw_st.
      apply (FIN m3 doc (wz 0xb1a28) (wz p) e1 e2 y0 y1 y2 e3 e4 e5 e6 e7 y3 y4 y5 y6 F3 ART3 MI3 ST3 DLEN AG03).
      apply bytes_at_app. split; [exact BY3|]. rewrite DLEN.
      apply (bytes_at_agree asegs m2 m3 _ _ BY2). intros a Ha. cbv beta in Ha. rewrite repeat_length in Ha. change (Z.of_nat 64) with 64 in Ha.
      apply PRES3; [| lia]. right; right; left. exists p, (l1 + 64). split; [exact INP| lia].
Qed.
End Parse2.
