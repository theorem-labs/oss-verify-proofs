(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjTape SjTapeList SjTapeTile.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_fzwA Atp_defsA Atp_kitA Pj_rtkA Pj_defsA Pj_os_defsA El_defsA El_os_defsA El_ins_ifaceA Dmp_hdefsA Dmp_pj_ifaceA Dmp_pj_kitA Dmp_pj_leafA Dmp_pj_aevtA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition pj_frD (jA : list byte) (osp : Z) (jB : list byte) (f : Z) (jC : list byte) (doc i : Z) (sv : list cell) : list cell :=
  [CB 88 jA; C8 (Z_to_bv 64 osp); CB 8 jB; C8 (Z_to_bv 64 f); CB 24 jC; C8 (Z_to_bv 64 doc); C8 (Z_to_bv 64 i)] ++ sv.
Lemma pj_frD_osp : forall m S1 jA osp jB f jC doc i sv, rw_cells bsegs m S1 (pj_frD jA osp jB f jC doc i sv) -> rw_cells bsegs m (S1 + 88) [C8 (Z_to_bv 64 osp)].
Proof.
  intros m S1 jA osp jB f jC doc i sv H. unfold pj_frD in H.
  exact (rw_cells_mid m S1 [CB 88 jA] [C8 (Z_to_bv 64 osp)] ([CB 8 jB; C8 (Z_to_bv 64 f); CB 24 jC; C8 (Z_to_bv 64 doc); C8 (Z_to_bv 64 i)] ++ sv) H).
Qed.
Lemma pj_frD_80 : forall m S1 jA osp jB f jC doc i sv, rw_cells bsegs m S1 (pj_frD jA osp jB f jC doc i sv) ->
  exists j80, rw_cells bsegs m (S1 + 80) [CB 8 j80; C8 (Z_to_bv 64 osp)].
Proof.
  intros m S1 jA osp jB f jC doc i sv H. unfold pj_frD in H.
  change ([CB 88 jA; C8 (Z_to_bv 64 osp); CB 8 jB; C8 (Z_to_bv 64 f); CB 24 jC; C8 (Z_to_bv 64 doc); C8 (Z_to_bv 64 i)] ++ sv)
    with ([] ++ CB 88 jA :: ([C8 (Z_to_bv 64 osp); CB 8 jB; C8 (Z_to_bv 64 f); CB 24 jC; C8 (Z_to_bv 64 doc); C8 (Z_to_bv 64 i)] ++ sv)) in H.
  apply (rw_cells_split_CB bsegs m S1 [] 88 jA _ [80; 8]%nat) in H; [| reflexivity]. cbn [mk_CB_cells app] in H.
  exists (firstn 8 (skipn 80 jA)).
  exact (rw_cells_mid m S1 [CB 80 (firstn 80 jA)] [CB 8 (firstn 8 (skipn 80 jA)); C8 (Z_to_bv 64 osp)]
           ([CB 8 jB; C8 (Z_to_bv 64 f); CB 24 jC; C8 (Z_to_bv 64 doc); C8 (Z_to_bv 64 i)] ++ sv) H).
Qed.
Lemma pj_frD_di : forall m S1 jA osp jB f jC doc i sv, rw_cells bsegs m S1 (pj_frD jA osp jB f jC doc i sv) ->
  rw_cells bsegs m (S1 + 136) [C8 (Z_to_bv 64 doc); C8 (Z_to_bv 64 i)].
Proof.
  intros m S1 jA osp jB f jC doc i sv H. unfold pj_frD in H.
  exact (rw_cells_mid m S1 [CB 88 jA; C8 (Z_to_bv 64 osp); CB 8 jB; C8 (Z_to_bv 64 f); CB 24 jC] [C8 (Z_to_bv 64 doc); C8 (Z_to_bv 64 i)] sv H).
Qed.

Section Entry.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis SM2 : stack_malloc2_contract RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Notation aevt := (aevt RT PMc).
Notation PINVA := (PINVA RT).

Local Ltac ulx := unfold DMP_PJ_LEAF_A, DMP_PJ_FRAME_A, EL_PUT_STACK_A, EL_INS_STACK_A, EL_INSD_STACK_A, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.

Lemma p_enter : forall (d : nat) (Σ : rts RT) (K : config -> Prop) (E : aenvA) (OS q fO : Z) (kO : nat) (i j : Z)
    (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  aenvA_ok E -> elem (ae_T E) (ae_S E) (ae_sn E) ck_any d i j -> 0 <= i -> j <= ae_n E ->
  a_live RT Σ E -> AINV_A E m ->
  In (fO, kO) (rt_frames RT Σ) -> fO <= OS -> OS + 288 <= fO + fs_size kO - 8 -> OS mod 16 = 0 ->
  (ae_DOC E + 16 <= OS \/ OS + 288 <= ae_DOC E) ->
  OSXF m OS -> os_hullA m OS -> LOCBA m -> el_tploc m ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m (ae_lo E) q -> ae_lo E + pj_needA d <= q -> q + 16 <= USTACK_TOP -> q mod 32 = 0 ->
  Z.of_nat (length (rt_frames RT Σ)) + Z.of_nat d + 3 <= FRAMES_TOT -> 1 <= rt_credit RT Σ ->
  (forall (f : Z) (Σ1 : rts RT) (m2 : mem) (jA jB jC : list byte) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word),
     let G := mkG E q OS fO kO f (rt_frames RT Σ) (rt_live RT Σ) (rt_sp0 RT Σ) (rt_credit RT Σ) m d in
     pctx_ok G -> PINVA G (pj_frD jA (OS + 128) jB f jC (ae_DOC E) i (pj_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)) 1 Σ1 m2 ->
     aevt Σ1 K (MS (pjR q f gp (wz DMP_PJ_DISP_A) (wz (ae_TAPE E + 8 * i)) a1' a2' a3' a4' a5' a6' a7' (wz (ae_DOC E)) (wz i) s6 s8 s2 s10 t0' t1' t2' t3' t4' t5' t6')
                  F' (wz DMP_PJ_DISP_A) fc None m2 (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (OS + 128)) (wz (ae_DOC E)) (wz i) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz DMP_PJ_A) fc None m (seg_rom bsegs)).
Proof using AF SM2 FDO MST.
  intros until m. intros OK EL I0 JN AL AI INF FLO FHI O16 DJ OXF HULL LB TPL HA MI ST NEED QT Q32 LEN CR1 HK.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) (S16 & NS8 & SN & SS & SL) PTRR PTR0 (D8 & DF & DL & DS & DT) LOW [HL HT]].
  pose proof AL as (ALT & ALS & ALP & ALF & WLO). pose proof (af_sp0_range RT AF Σ m HA) as SP0R.
  pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ. assert (NR : ae_n E < 2^32) by (destruct WF as (X & _); clear - X; lia).
  pose proof (fframe_ranges RT AF Σ m fO kO HA INF) as (FO0 & FO1 & FOS & _).
  pose proof (af_frames_range RT AF Σ m _ _ HA ALF) as (FD0' & FD1 & _).
  assert (FSD : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  pose proof (pj_needA_0 d) as ND. unfold DMP_PJ_FRAME_A, DMP_PJ_LEAF_A, RT_STACK in ND.
  assert (DR : 0 <= ae_DOC E < 2^63) by (clear - DF DL FD0' FD1 SP0R FSD; ulx).
  assert (OR : 0 <= OS + 128 < 2^64) by (clear - FLO FHI FO1 FO0 SP0R; ulx).

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_walk0 q (ae_lo E) (OS + 128) (ae_DOC E) i ra gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m);
    [exact ST| clear - NEED ND; lia| clear - LOW; lia| clear - QT; ulx| exact Q32| exact OR| clear - DR; lia| clear - I0 IJ JN NR; lia
    | exact (af_client_consts RT AF Σ m HA)| exact MI]|].
  cbv beta. intros ms1 (m1 & a1' & a2' & j0 & j1 & j2 & j3 & -> & MU1 & WM1 & MI1 & ST1 & FRl1 & FRs1). apply evt_done. unfold entry_st.
  assert (EQ : bv_unsigned (wz (q - 256)) = q - 256) by (apply unsigned_lit; clear - NEED ND LOW QT; ulx).
  assert (PRES1 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> m1 a = m a).
  { intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. destruct (aclient_split_c RT AF Σ m q _ HA Ha); clear - H NEED ND WLO; ulx. }
  assert (HA1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 (q - 256) HA ltac:(clear - NEED ND WLO; ulx)); [| exact WM1].
    intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. clear - Hin QT; ulx. }

  eapply (aevt_smalloc2 RT SM2 PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (ae_lo E) eq_refl);
    [unfold FRAMES_MAX2B; unfold FRAMES_TOT in LEN; clear - LEN; lia| clear - CR1; lia| exact HA1| exact MI1| | intros EF; rewrite EF in INF; destruct INF|].
  { unfold call_ok. rewrite EQ. split; [exact ST1|]. split; [exact WLO|]. split; [clear - NEED ND; ulx|]. split; [clear - QT; ulx| clear - Q32; Z.div_mod_to_equations; lia]. }
  intros Σ1 f w0 w1 w2 c1 c2 c3 c4 c5 c6 c7 w3 w4 w5 w6 F1 m2 (HA2 & MI2 & WM2 & ST2) PRES2 WRF WRS FRS1 LV1 SP1 CRE FP F64 FT.
  rewrite EQ in ST2, PRES2. change (fs_size 2) with 256 in WRF, WRS, FT. change (256 / 8) with 32 in WRS. replace (256 - 8) with 248 in WRF by reflexivity.
  rewrite (ret_pc_even DMP_PJ_SMRET_A) by (unfold DMP_PJ_SMRET_A; clear; lia).
  set (G := mkG E q OS fO kO f (rt_frames RT Σ) (rt_live RT Σ) (rt_sp0 RT Σ) (rt_credit RT Σ) m d).
  assert (GOK : pctx_ok G).
  { subst G. apply (pctx_ok_intro RT AF _ Σ1 m2 HA2); cbn [g_E g_q g_OS g_fO g_kO g_ff g_rfr g_L g_sp0 g_cr g_m0 g_d].
    - exact FRS1. - exact LV1. - exact SP1. - exact Q32. - exact QT. - exact NEED. - exact OK. - exact ALT. - exact ALS. - exact ALP.
    - exact ALF. - exact WLO. - exact INF. - exact FLO. - exact FHI. - exact O16. - exact DJ. - exact LEN. }
  pose proof GOK as GOK'. destruct GOK' as [_ _ _ _ _ (F0 & _ & FSEG & FLO' & FHI' & SHLO & SHAP) FFR FFL RFR _ LL _].
  unfold G in F0, FSEG, FLO', FHI', SHLO, SHAP, FFR, FFL, RFR, LL. cbn [g_E g_q g_OS g_fO g_kO g_ff g_rfr g_L g_sp0 g_cr g_m0 g_d] in F0, FSEG, FLO', FHI', SHLO, SHAP, FFR, FFL, RFR, LL.
  assert (FD0 : 0 <= shad f) by (unfold shad, SHB; clear - F0; Z.div_mod_to_equations; lia).

  assert (AGc : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) q x) -> agree_on P m m2).
  { intros P HP a Ha. pose proof (HP _ Ha) as CA. rewrite (PRES2 a); [exact (PRES1 a CA)|]. apply (aclient_mono _ _ _ _ _ _ _ CA); [auto| auto| clear; lia]. }
  assert (CLF : forall x, fO <= x < fO + fs_size kO - 8 -> aclient (rt_live RT Σ) (rt_frames RT Σ) q x).
  { intros x Hx. right; right; right; left. exists fO, kO. split; [exact INF| exact Hx]. }
  assert (CLS : forall x, shad fO <= x < shad (fO + fs_size kO) -> aclient (rt_live RT Σ) (rt_frames RT Σ) q x).
  { intros x Hx. do 4 right. exists fO, kO. split; [exact INF| exact Hx]. }
  assert (CLT : forall x, client_static x -> aclient (rt_live RT Σ) (rt_frames RT Σ) q x) by (intros x Hx; right; left; exact Hx).

  assert (FRl2 : rw_cells bsegs m2 (q - 256) (pj_locals0 j0 j1 (OS + 128) j2 j3)).
  { eapply rw_cells_agree_nw; [exact FRl1|]. intros a Ha. apply PRES2. left. unfold pj_locals0 in Ha. cbn [cells_size csize Nat.add] in Ha. clear - Ha QT. ulx. }
  assert (FRs2 : rw_cells bsegs m2 (q - 104) (pj_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { eapply rw_cells_agree_nw; [exact FRs1|]. intros a Ha. apply PRES2. left. rewrite pj_saved_size in Ha. clear - Ha QT. ulx. }

  destruct (wr_at_rw_CB m2 f 24 (wr_at_sub m2 f 248 f 24 WRF ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (jH & FH2).
  change (Z.to_nat 24) with 24%nat in FH2.
  apply (rw_cells_split_CB bsegs _ _ [] 24 _ [] [8; 8; 8]%nat) in FH2; [| reflexivity]. cbn [mk_CB_cells app] in FH2.
  repeat match type of FH2 with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "h" in set (j := t) in FH2; clearbody j end.
  destruct (wr_at_cells1 m2 (shad f) 20 (wr_at_sub m2 (shad f) 32 (shad f) 20 WRS ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia))) as (ls & LS & FS2).

  apply (aevt_evt RT AF PMc MST).
  lazymatch type of FH2 with rw_cells _ _ _ [CB 8 ?x0; CB 8 ?x1; CB 8 ?x2] =>
  eapply evt_cut; [eapply (pj_walk1 q f (ae_lo E) (OS + 128) (ae_DOC E) i (ae_TAPE E) gp w0 w1 w2 c1 c2 c3 c4 c5 c6 c7 s3 s6 s7 s8 s2 s10 s11 w3 w4 w5 w6 j0 j1 j2 j3 x0 x1 x2 ls F1 fc m2 LS);
    [exact F0| exact FLO'| clear - SHLO; lia| exact FD0| exact SHAP| clear - LOW; lia| clear - NEED ND; lia| clear - QT; ulx
    | clear - D8 DF DL DS DT HL HT FSD; split; [ulx| exact D8]
    | clear - I0 IJ JN NR; lia| exact OR| | exact FRl2| exact FH2| exact FS2| exact MI2| exact ST2| clear - NEED ND; ulx| exact TS
    | clear - T16; Z.div_mod_to_equations; lia| clear - IJ JN TN TL HL HT; ulx| clear - DL DT HL HT FSD; ulx| left; clear - DL DT NEED ND FSD; ulx]|]
  end.
  {
    intros m' MU WM.
    assert (AI' : AINV_A E m').
    { apply (AINV_A_agree E m m'); [exact AI|].
      intros a Ha. pose proof (proj1 (ainv_caller RT AF G GOK (bv_unsigned a) Ha)) as CA. pose proof (ownB_not_caller RT AF G GOK (bv_unsigned a)) as NOC.
      unfold ownB in NOC. unfold G in CA, NOC. cbn [g_E g_L g_rfr g_q g_ff g_OS] in CA, NOC.
      rewrite (MU a).
      + exact (AGc (ainv_rng E) (fun x Hx => proj1 (ainv_caller RT AF G GOK x Hx)) a Ha).
      + unfold pj_W1. cbn [outside]. repeat split; try exact I; intros X; (apply NOC; [| exact CA]);
        clear - X NEED ND; unfold DMP_PJ_FRAME_A, DMP_PJ_LEAF_A, RT_STACK in ND; lia. }
    pose proof AI' as (_ & _ & _ & DC & DSH).
    change [C8 (Z_to_bv 64 (ae_TAPE E)); C8 (Z_to_bv 64 (ae_SBUF E))] with ([C8 (Z_to_bv 64 (ae_TAPE E))] ++ [C8 (Z_to_bv 64 (ae_SBUF E))]) in DC.
    apply rw_cells_app in DC. destruct DC as [DC _].
    split; [exact DC|]. split; [unfold shad, SHB in *; exact DSH|].
    apply (client_consts_munch _ m2 m' (af_client_consts RT AF Σ1 m2 HA2) MU). intros x Hx. unfold pj_W1. cbn [outside].
    clear - Hx FSEG LOW NEED ND. unfold shad. repeat split; try exact I; ulx. }
  cbv beta. intros ms3 (m3 & a4x & -> & MU3 & WM3 & MI3 & ST3 & FRl3 & FH3 & FS3). apply evt_done.

  assert (OWN3 : forall a, outside (pj_W1 q f) a \/ ownB G a).
  { intros a. destruct (outside_dec (pj_W1 q f) a) as [O|IN]; [left; exact O| right]. unfold ownB, G. unfold pj_W1 in IN. cbn [inW g_q g_ff g_E] in IN |- *.
    clear - IN NEED ND. unfold DMP_PJ_FRAME_A, DMP_PJ_LEAF_A, RT_STACK in ND. lia. }
  pose proof (rw_cells_merge bsegs m3 (q - 256) [] [CB 8 j0; CB 80 j1]
                [C8 (wz (OS + 128)); CB 8 (firstn 8 j2); C8 (wz f); CB 24 (firstn 24 (skipn 16 j2)); C8 (wz (ae_DOC E)); C8 (wz i)] FRl3) as FRl3'.
  cbn [cells_size csize Nat.add cells_bytes cbytes app] in FRl3'.
  lazymatch type of FRl3' with rw_cells _ _ _ (CB 88 ?jx :: _) => set (jA := jx) in FRl3'; clearbody jA end.
  unfold pjR in HK.
  apply (HK f Σ1 m3 jA (firstn 8 j2) (firstn 24 (skipn 16 j2)) w0 w1 w2 (wz 0) (wz (ae_TAPE E)) (wz (2^60)) a4x c5 c6 c7 w3 w4 w5 w6 F1 GOK).

  assert (GI2 : PINVA G (pj_locals0 j0 j1 (OS + 128) j2 j3 ++ pj_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) 1 Σ1 m2).
  { split; [exact HA2|]. split; [exact MI2|].
    split; [subst G; cbn; exact FRS1|]. split; [subst G; cbn; exact LV1|]. split; [subst G; cbn; exact SP1|]. split; [subst G; cbn [g_cr]; clear - CRE; lia|].
    split; [subst G; cbn; exact ST2|].
    split. { destruct OXF as (fill & OX & FOK). exists fill. split; [| exact FOK]. subst G; cbn [g_OS].
             apply (OSX_agree m m2 _ _ OX); [| exact (wmono_trans _ _ _ _ WM1 WM2)]. apply AGc. intros x Hx. apply CLF. clear - Hx FLO FHI. lia. }
    split. { subst G; cbn [g_OS]. destruct HULL as [_ SHO]. apply (bytes_at_agree bsegs m m2 _ _ SHO). apply AGc. intros x Hx. rewrite repeat_length in Hx. apply CLS.
             assert (X1 : (OS + 288) / 8 <= (fO + fs_size kO) / 8) by (apply Z.div_le_mono; clear - FHI; lia).
             assert (X2 : fO / 8 <= OS / 8) by (apply Z.div_le_mono; clear - FLO; lia).
             unfold shad in *. clear - Hx X1 X2 O16. Z.div_mod_to_equations. lia. }
    split. { unfold el_tploc in *. apply (rw_cells_agree_nw bsegs m m2 _ _ TPL). apply AGc. intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply CLT. apply client_static_intro; clear - Hx; lia. }
    split. { apply (LOCBA_agree m m2 LB). apply AGc. intros x Hx. apply CLT. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx. apply client_static_intro; clear - Hx; lia. }
    split. { split; [| reflexivity]. subst G; cbn [g_q]. apply rw_cells_app. split; [exact FRl2|]. cbn [cells_size csize Nat.add pj_locals0].
             replace (q - 256 + Z.of_nat 152) with (q - 104) by (clear; lia). exact FRs2. }
    split; [subst G; cbn; exact WRF|]. split; [subst G; cbn; exact WRS|].
    subst G. cbn [g_L g_rfr g_q g_m0 g_OS]. intros a Ha _.
    rewrite (PRES2 a); [exact (PRES1 a Ha)|]. apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| clear; lia]. }
  eapply (PINVA_cwB RT AF G GOK _ _ 1 Σ1 m2 m3 (pj_W1 q f) GI2 MU3 WM3 MI3 OWN3); [subst G; cbn [g_q g_E]; exact ST3| | reflexivity].
  unfold pj_frD. subst G; cbn [g_q]. apply rw_cells_app. split; [exact FRl3'|]. cbn [cells_size csize Nat.add].
  replace (q - 256 + Z.of_nat 152) with (q - 104) by (clear; lia).
  eapply rw_cells_agree_nw; [exact FRs2|]. apply (agree_of_munch _ _ _ _ MU3). intros x Hx. rewrite pj_saved_size in Hx. unfold pj_W1. cbn [outside].
  clear - Hx FLO' SHLO NEED ND. repeat split; try exact I; lia.
Qed.

Lemma p_exit : forall (G : pctx) (LC : list cell) (k : Z) (Σ : rts RT) (K : config -> Prop)
    (xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 : word)
    (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  pctx_ok G -> PINVA G (LC ++ pj_saved xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11) k Σ m -> cells_size LC = 152%nat ->
  AINV_A (g_E G) (g_m0 G) ->
  (forall (Σ' : rts RT) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (m' : mem),
     ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' (g_lo G) (g_q G) ->
     OSXF m' (g_OS G) -> os_hullA m' (g_OS G) -> LOCBA m' -> el_tploc m' -> AINV_A (g_E G) m' ->
     rt_live RT Σ' = g_L G -> rt_frames RT Σ' = g_rfr G -> rt_sp0 RT Σ' = g_sp0 G -> g_cr G - k <= rt_credit RT Σ' ->
     (forall a : word, aclient (g_L G) (g_rfr G) (g_q G) (bv_unsigned a) -> outside (pj_WA (g_OS G)) (bv_unsigned a) -> m' a = g_m0 G a) ->
     aevt Σ' K (MS (mkR xra (wz (g_q G)) gp (wz TPV_A) t0' t1' t2' xs0 xs1 a0' a1' a2' a3' a4' a5' a6' a7' xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 t3' t4' t5' t6')
                F' (ret_pc xra) fc None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra (wz (g_S1 G)) gp (wz TPV_A) t0 t1 t2 (wz (g_q G)) (wz (g_S1 G)) a0 a1 a2 a3 a4 a5 a6 a7
                    s2 (wz (g_ff G)) s4 s5 s6 (wz (g_ff G)) s8 s9 s10 (wz (shad (g_ff G))) t3 t4 t5 t6)
               F (wz DMP_PJ_EXIT_A) fc None m (seg_rom bsegs)).
Proof using AF FDO MST.
  intros until m. intros GOK GI SZ AI0 HK.
  pose proof GI as (HA & MI & FRS & LV & SP0 & CR & ST & (fill & OX & FOK) & SHO & TPL & LB & (FR & _) & WF1 & WF2 & REL).
  pose proof GOK as GOK'. destruct GOK' as [(Q32 & QT & LQ) (LO1 & LO2) (SP1 & SP2) (OK & _) (EIN & ELO & EHI & E16 & _) (F0 & F64 & FSEG & FLO & FHI & SHLO & SHAP) FFR FFL RFR _ LL _].
  pose proof (pj_needA_0 (g_d G)) as ND. unfold DMP_PJ_FRAME_A, DMP_PJ_LEAF_A, RT_STACK in ND.
  assert (FD0 : 0 <= shad (g_ff G)) by (unfold shad, SHB; clear - F0; Z.div_mod_to_equations; lia).
  assert (SZ' : cells_size (LC ++ pj_saved xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11) = 256%nat) by (rewrite cells_size_app, SZ, pj_saved_size; reflexivity).
  pose proof FR as FR0. apply rw_cells_app in FR. destruct FR as [FRl FRs]. rewrite SZ in FRs. replace (g_S1 G + Z.of_nat 152) with (g_q G - 104) in FRs by (clear; lia).

  destruct (wr_at_rw_CB m (g_ff G) 8 (wr_at_sub m (g_ff G) 248 (g_ff G) 8 WF1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (hj & FH).
  change (Z.to_nat 8) with 8%nat in FH.
  destruct (wr_at_cells1 m (shad (g_ff G)) 32 WF2) as (ls & LS & FS).

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_walkX1 (g_ff G) _ (wz (g_S1 G)) gp t0 t1 t2 (wz (g_q G)) (wz (g_S1 G)) a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s8 s9 s10 t3 t4 t5 t6 hj ls F fc m LS F0);
    [clear - FLO LO1 LQ QT ND; ulx| exact FD0| clear - SHLO LO1 LQ QT ND; ulx| exact SHAP| exact FH| exact FS| exact MI]|].
  cbv beta. intros ms4 (m4 & a0x & -> & MU4 & WM4 & MI4). apply evt_done.
  assert (OWN4 : forall a, outside [(g_ff G, g_ff G + 8); (shad (g_ff G), shad (g_ff G) + 32)] a \/ own G a).
  { intros a. destruct (outside_dec [(g_ff G, g_ff G + 8); (shad (g_ff G), shad (g_ff G) + 32)] a) as [O|IN]; [left; exact O| right]. unfold own. cbn [inW] in IN. clear - IN. lia. }
  assert (GI4 : PINVA G (LC ++ pj_saved xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11) k Σ m4).
  { eapply (PINVA_cw RT AF G GOK _ _ k Σ m m4 _ GI MU4 WM4 MI4 OWN4); [| exact SZ'].
    eapply rw_cells_agree_nw; [exact FR0|]. apply (agree_of_munch _ _ _ _ MU4). intros x Hx. rewrite SZ' in Hx. cbn [outside].
    clear - Hx FLO SHLO LQ ND. repeat split; try exact I; lia. }
  pose proof GI4 as (HA4 & _ & FRS4 & LV4 & SP4 & CR4 & ST4 & (fill4 & OX4 & FOK4) & SHO4 & TPL4 & LB4 & (FR4 & _) & _ & _ & REL4).
  pose proof (PINVA_ainv RT AF G GOK _ _ _ _ AI0 GI4) as AI4.
  apply rw_cells_app in FR4. destruct FR4 as [FRl4 FRs4]. rewrite SZ in FRs4. replace (g_S1 G + Z.of_nat 152) with (g_q G - 104) in FRs4 by (clear; lia).
  clear FRl FRs FR0 FH FS MU4 WM4 ST OX SHO TPL LB REL HA MI CR.

  destruct (af_frame_release RT AF Σ m4 (g_ff G) 2%nat (g_rfr G) HA4 FRS4) as (Σ5 & fl & FLC & NAC & FL0 & FLW & FW & RELF).
  change (fs_size 2) with 256 in FW. replace (g_ff G + 256 - 8) with (g_ff G + 248) in FW by (clear; lia). rewrite SP4 in FLW.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_walkX2 (g_q G) (g_ff G) fl (g_lo G) _ gp t0 t1 t2 a0x a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s8 s9 s10 t3 t4 t5 t6
                             xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 LC F fc m4);
    [exact F0| clear - FLO LO1 LQ QT ND; ulx| exact FL0| clear - FLW LO2; lia| clear - LO1; lia| clear - LQ ND; lia| clear - QT; ulx| exact SZ
    | exact ST4| exact FRl4| exact FRs4| exact FW| exact FLC| exact MI4]|].
  cbv beta. intros ms5 (m5 & RS5 & FC5 & MU5 & WM5 & MI5 & ST5 & FL5). apply evt_done.
  destruct (RELF m5 MU5 WM5 FL5) as (HA5 & FRS5 & LV5 & SP5 & CR5 & AL5 & AM5).
  apply (aevt_switch RT PMc Σ Σ5 K _ AL5 AM5).

  assert (NFL : forall x, aclient (g_L G) (g_rfr G) (g_q G) x -> fl <= x < fl + 1 -> False).
  { intros x CA X. destruct CA as [SX|CA']; [clear - SX X FLW LO2 LQ ND; ulx|].
    apply NAC. rewrite LV4, FRS4. replace fl with x by (clear - X; lia).
    apply (aclient_mono (g_L G) (g_rfr G) USTACK_TOP); [right; exact CA'| auto| intros e He; right; exact He| clear; lia]. }
  assert (REL5 : forall a : word, aclient (g_L G) (g_rfr G) (g_q G) (bv_unsigned a) -> outside (pj_WA (g_OS G)) (bv_unsigned a) -> m5 a = g_m0 G a).
  { intros a CA OU. rewrite (MU5 a); [exact (REL4 a CA OU)|]. cbn [outside]. split; [| exact I]. intros X. exact (NFL _ CA X). }
  revert FC5. apply (ret_st_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 ms5 (fun ms => ms_fcsr ms = fc -> aevt Σ5 K ms) RS5).
  intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F5 fc5 FC5. change (fc5 = fc) in FC5. subst fc5.
  pose proof (RFR _ _ EIN) as (_ & ESEG & _ & _ & _ & _ & FAP).
  assert (AG5 : forall P : Z -> Prop, (forall x, P x -> aclient (g_L G) (g_rfr G) (g_q G) x) -> agree_on P m4 m5).
  { intros P HP a Ha. apply MU5. cbn [outside]. split; [| exact I]. intros X. exact (NFL _ (HP _ Ha) X). }
  assert (CLF : forall x, g_fO G <= x < g_fO G + fs_size (g_kO G) - 8 -> aclient (g_L G) (g_rfr G) (g_q G) x).
  { intros x Hx. right; right; right; left. exists (g_fO G), (g_kO G). split; [exact EIN| exact Hx]. }
  assert (CLS : forall x, shad (g_fO G) <= x < shad (g_fO G + fs_size (g_kO G)) -> aclient (g_L G) (g_rfr G) (g_q G) x).
  { intros x Hx. do 4 right. exists (g_fO G), (g_kO G). split; [exact EIN| exact Hx]. }
  assert (CLT : forall x, client_static x -> aclient (g_L G) (g_rfr G) (g_q G) x) by (intros x Hx; right; left; exact Hx).
  assert (OX5 : OSX m5 (g_OS G) fill4).
  { apply (OSX_agree m4 m5 _ _ OX4); [| exact WM5]. apply AG5. intros x Hx. apply CLF. clear - Hx ELO EHI. lia. }
  eapply (HK Σ5 q0 q1 q2 (wz fl) q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F5 m5 HA5 MI5 ST5); [| | | | | rewrite LV5; exact LV4| exact FRS5| rewrite SP5; exact SP4| rewrite CR5; exact CR4| exact REL5].
  - exists fill4. split; [exact OX5| exact FOK4].
  - split.
    + destruct OX5 as (pb & pp & ep & dum & j148 & j284 & H & _). apply rw_cells_forget in H. rewrite os_cellsX_size in H. exact H.
    + apply (bytes_at_agree bsegs m4 m5 _ _ SHO4). apply AG5. intros x Hx. rewrite repeat_length in Hx. apply CLS.
      assert (X1 : (g_OS G + 288) / 8 <= (g_fO G + fs_size (g_kO G)) / 8) by (apply Z.div_le_mono; clear - EHI; lia).
      assert (X2 : g_fO G / 8 <= g_OS G / 8) by (apply Z.div_le_mono; clear - ELO; lia).
      unfold shad in *. clear - Hx X1 X2 E16. Z.div_mod_to_equations. lia.
  - apply (LOCBA_agree m4 m5 LB4). apply AG5. intros x Hx. apply CLT. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx. apply client_static_intro; clear - Hx; lia.
  - unfold el_tploc in *. apply (rw_cells_agree_nw bsegs m4 m5 _ _ TPL4). apply AG5. intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply CLT. apply client_static_intro; clear - Hx; lia.
  - apply (AINV_A_agree (g_E G) m4 m5 AI4). apply AG5. intros x Hx. exact (proj1 (ainv_caller RT AF G GOK x Hx)).
Qed.

Lemma p_endl : forall (G : pctx) (kk : Z) fcs k Σ (K : config -> Prop)
    (ra gp a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  pctx_ok G -> os_put_cpsA RT PMc -> PINVA G fcs k Σ m -> 1 <= kk <= 6 -> k + 2 <= g_cr G ->
  (forall (Σ' : rts RT) (a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (m' : mem),
     PINVA G fcs (k + 2) Σ' m' ->
     aevt Σ' K (MS (pjR (g_q G) (g_ff G) gp (wz (pj_endl_pc kk + 28)) a0' a1' a2' a3' a4' a5' a6' a7' s4 s5 s6 s8 s9 s11 t0' t1' t2' t3' t4' t5' t6')
                F' (wz DMP_PJ_EXIT_A) fc None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (pjR (g_q G) (g_ff G) gp ra (wz (g_OS G + 128)) a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
               F (wz (pj_endl_pc kk)) fc None m (seg_rom bsegs)).
Proof using AF FDO MST.
  intros until m. intros GOK PUT GI KK CRK HK.
  pose proof GI as (HA & MI & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR & FSZ) & WF1 & WF2 & _).
  pose proof GOK as GOK'. destruct GOK' as [(Q32 & QT & LQ) (LO1 & LO2) _ _ _ (F0 & F64 & FSEG & FLO & FHI & SHLO & SHAP) _ _ _ _ _ _].
  pose proof (pj_needA_0 (g_d G)) as ND. unfold DMP_PJ_FRAME_A, DMP_PJ_LEAF_A, RT_STACK in ND.
  assert (FD0 : 0 <= shad (g_ff G)) by (unfold shad, SHB; clear - F0; Z.div_mod_to_equations; lia).

  destruct (wr_at_cell m (shad (g_ff G)) 32 (pj_gofs kk) 1 WF2 ltac:(unfold pj_gofs; clear - KK; lia) ltac:(clear; lia) ltac:(unfold pj_gofs; clear - KK; lia)) as [gj FG].
  destruct (wr_at_cell m (g_ff G) 248 (32 + 16 * kk) 1 WF1 ltac:(clear - KK; lia) ltac:(clear; lia) ltac:(clear - KK; lia)) as [bj FB].
  change (Z.to_nat 1) with 1%nat in FG, FB.

  apply (aevt_evt RT AF PMc MST). unfold pjR.
  eapply evt_cut; [eapply (pj_endl1 kk (g_q G) (g_ff G) gp ra (wz (g_OS G + 128)) a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 gj bj F fc m KK F0);
    [clear - FLO LO1 LQ QT ND; ulx| exact FD0| clear - SHLO LO1 LQ QT ND; ulx| exact SHAP| exact FG| exact FB| exact MI]|].
  cbv beta. intros ms1 (m1 & -> & MU1 & WM1 & MI1 & FG1 & FB1). apply evt_done.
  assert (OWN1 : forall a, outside [(shad (g_ff G) + pj_gofs kk, shad (g_ff G) + pj_gofs kk + 1); (pj_slot (g_ff G) kk, pj_slot (g_ff G) kk + 1)] a \/ own G a).
  { intros a. match goal with |- outside ?W _ \/ _ => destruct (outside_dec W a) as [O|IN]; [left; exact O| right] end.
    unfold own. unfold pj_slot, pj_gofs in IN. cbn [inW] in IN. clear - IN KK. lia. }
  assert (GI1 : PINVA G fcs k Σ m1).
  { eapply (PINVA_cw RT AF G GOK _ _ k Σ m m1 _ GI MU1 WM1 MI1 OWN1); [| exact FSZ].
    eapply rw_cells_agree_nw; [exact FR|]. apply (agree_of_munch _ _ _ _ MU1). intros x Hx. rewrite FSZ in Hx. unfold pj_slot, pj_gofs. cbn [outside].
    clear - Hx FLO SHLO LQ ND KK. repeat split; try exact I; lia. }
  unfold pjR, pj_slot.
  eapply (p_put_ownc RT AF PMc FDO MST G GOK fcs k Σ K (32 + 16 * kk) (Z_to_bv 8 10)); [exact PUT| exact GI1| exact FB1| | clear - KK; Z.div_mod_to_equations; lia| clear - KK; lia| clear - KK; lia| exact CRK|].
  { replace ((32 + 16 * kk) / 8) with (pj_gofs kk) by (unfold pj_gofs; clear - KK; Z.div_mod_to_equations; lia). exact FG1. }
  intros Σ2 u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 m2 GI2.
  rewrite (ret_pc_even (pj_endl_pc kk + 28)) by (clear - KK; assert (X : kk = 1 \/ kk = 2 \/ kk = 3 \/ kk = 4 \/ kk = 5 \/ kk = 6) by lia;
                                               destruct X as [-> |[-> |[-> |[-> |[-> | ->]]]]]; cbn [pj_endl_pc]; lia).
  pose proof GI2 as (_ & MI2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR2 & _) & _ & WF2' & _).
  destruct (wr_at_cell m2 (shad (g_ff G)) 32 (pj_gofs kk) 1 WF2' ltac:(unfold pj_gofs; clear - KK; lia) ltac:(clear; lia) ltac:(unfold pj_gofs; clear - KK; lia)) as [gj2 FG2].
  change (Z.to_nat 1) with 1%nat in FG2.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_endl2 kk (g_q G) (g_ff G) gp (wz (pj_endl_pc kk + 28)) (wz (g_OS G + 128)) e1 e2 e3 e4 e5 e6 e7 s4 s5 s6 s8 s9 s11 u0 u1 u2 u3 u4 u5 u6 gj2 F2 fc m2 KK FD0);
    [clear - SHLO LO1 LQ QT ND; ulx| exact FG2| exact MI2]|].
  cbv beta. intros ms3 (m3 & a0x & -> & MU3 & WM3 & MI3 & FG3). apply evt_done.
  assert (OWN3 : forall a, outside [(shad (g_ff G) + pj_gofs kk, shad (g_ff G) + pj_gofs kk + 1)] a \/ own G a).
  { intros a. match goal with |- outside ?W _ \/ _ => destruct (outside_dec W a) as [O|IN]; [left; exact O| right] end.
    unfold own. unfold pj_gofs in IN. cbn [inW] in IN. clear - IN KK. lia. }
  apply (HK Σ2 a0x e1 e2 e3 e4 e5 e6 e7 u0 u1 u2 u3 u4 u5 u6 F2 m3).
  eapply (PINVA_cw RT AF G GOK _ _ (k + 2) Σ2 m2 m3 _ GI2 MU3 WM3 MI3 OWN3); [| exact FSZ].
  eapply rw_cells_agree_nw; [exact FR2|]. apply (agree_of_munch _ _ _ _ MU3). intros x Hx. rewrite FSZ in Hx. unfold pj_gofs. cbn [outside].
  clear - Hx SHLO LQ ND KK. repeat split; try exact I; lia.
Qed.

Lemma PINVA_leafD : forall (G : pctx) (jA : list byte) (osp : Z) (jB : list byte) (f : Z) (jC : list byte) (doc i : Z) (sv : list cell)
    (k : Z) (Σ : rts RT) (m m' : mem) (W0 : list (Z * Z)),
  pctx_ok G -> PINVA G (pj_frD jA osp jB f jC doc i sv) k Σ m -> munch W0 m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
  stk bsegs m' (g_lo G) (g_S1 G) ->
  (forall a, outside W0 a \/ g_lo G <= a < g_S1 G \/ g_S1 G <= a < g_S1 G + 88 \/ g_S1 G + 112 <= a < g_S1 G + 136) ->
  exists jA' jC', PINVA G (pj_frD jA' osp jB f jC' doc i sv) k Σ m'.
Proof using AF.
  intros until W0. intros GOK GI MU WM MI' ST' HW.
  pose proof GI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR & FSZ) & _).
  pose proof GOK as GK. destruct GK as [(_ & _ & LQ) _ _ _ _ _ _ _ _ _ _ _].
  pose proof (pj_needA_0 (g_d G)) as ND. unfold DMP_PJ_FRAME_A, DMP_PJ_LEAF_A, RT_STACK in ND.
  assert (SVZ : cells_size sv = 104%nat) by (unfold pj_frD in FSZ; rewrite cells_size_app in FSZ; cbn [cells_size csize Nat.add] in FSZ; lia).
  unfold pj_frD in FR.
  change ([CB 88 jA; C8 (wz osp); CB 8 jB; C8 (wz f); CB 24 jC; C8 (wz doc); C8 (wz i)] ++ sv)
    with ([CB 88 jA] ++ ([C8 (wz osp); CB 8 jB; C8 (wz f)] ++ ([CB 24 jC] ++ ([C8 (wz doc); C8 (wz i)] ++ sv)))) in FR.
  apply rw_cells_app in FR. destruct FR as [F1 FR]. apply rw_cells_app in FR. destruct FR as [F2 FR]. apply rw_cells_app in FR. destruct FR as [F3 F4].
  cbn [cells_size csize Nat.add] in F2, F3, F4.
  destruct (wr_at_rw_CB m' (g_S1 G) 88 (wr_at_transport bsegs m m' _ _ (rw_cells_wr_at bsegs m _ _ 88 F1 ltac:(cbn; lia)) WM) ltac:(lia)) as (jA' & F1').
  destruct (wr_at_rw_CB m' (g_S1 G + Z.of_nat 88 + Z.of_nat 24) 24
              (wr_at_transport bsegs m m' _ _ (rw_cells_wr_at bsegs m _ _ 24 F3 ltac:(cbn; lia)) WM) ltac:(lia)) as (jC' & F3').
  change (Z.to_nat 88) with 88%nat in F1'. change (Z.to_nat 24) with 24%nat in F3'.
  exists jA', jC'.
  eapply (PINVA_cwB RT AF G GOK _ _ k Σ m m' W0 GI MU WM MI'); [| exact ST'| | unfold pj_frD; rewrite cells_size_app, SVZ; reflexivity].
  - intros a. destruct (HW a) as [X|[X|[X|X]]]; [left; exact X| right; left; lia| right; left; lia| right; left; lia].
  - unfold pj_frD.
    change ([CB 88 jA'; C8 (wz osp); CB 8 jB; C8 (wz f); CB 24 jC'; C8 (wz doc); C8 (wz i)] ++ sv)
      with ([CB 88 jA'] ++ ([C8 (wz osp); CB 8 jB; C8 (wz f)] ++ ([CB 24 jC'] ++ ([C8 (wz doc); C8 (wz i)] ++ sv)))).
    apply rw_cells_app. split; [exact F1'|]. cbn [cells_size csize Nat.add].
    apply rw_cells_app. split.
    + eapply rw_cells_agree_nw; [exact F2|]. apply (agree_of_munch _ _ _ _ MU). intros x Hx. cbn [cells_size csize Nat.add] in Hx.
      destruct (HW x) as [X|[X|[X|X]]]; [exact X| exfalso; lia| exfalso; lia| exfalso; lia].
    + cbn [cells_size csize Nat.add]. apply rw_cells_app. split; [exact F3'|]. cbn [cells_size csize Nat.add].
      eapply rw_cells_agree_nw; [exact F4|]. apply (agree_of_munch _ _ _ _ MU). intros x Hx. rewrite cells_size_app, SVZ in Hx. cbn [cells_size csize Nat.add] in Hx.
      destruct (HW x) as [X|[X|[X|X]]]; [exact X| exfalso; lia| exfalso; lia| exfalso; lia].
Qed.

End Entry.
