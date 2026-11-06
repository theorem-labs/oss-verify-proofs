(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun Stdio SjModel AtpModel.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit Atp_h_defs.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 RT_iface5 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2
     Sj_num_akit Sj_h_alloc Sj_stage2_iface Atp_fzwA Atp_setcapA Atp_activewA Atp_activeA Atp_defsA Atp_kitA Atp_arrlA Atp_h_defsA Atp_pidiA Atp_pdtorA
     Pj_rtkA Pj_lftoi1A Pj_defsA Pj_os_defsA El_defsA El_lf1A El_lf2A El_lf2bA El_phasesA El_frontA El_parsekA El_armkitA El_armkit2A El_haccA Atp_objkwA El_atkeyA El_arm25wA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Section Arm25.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis RC2 : rt_contracts2 RT.
Variable PMc : Model -> Prop.

Local Ltac ul := unfold FUZZ_STACK, PID_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.

Theorem arm25_okA : forall W, arm_cpsA RT PMc W 25.
Proof using AF RC RC2.
  intros W Σ K X E sel idx jr jos t ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 t3 t4 t5 t6 F fc m
    FDO MST LK OKE LE WFS SEL IDX AL FRS LPA LVB CRB ARTg MIg STg NEED AM FRM XD AUX SPB POST.
  pose proof (arm_nbelow RT AF X E Σ m 256 LK LE AL FRS ARTg ltac:(lia) ltac:(clear - NEED; unfold arm_needA in NEED; cbn in NEED; ul)) as NBELOW.
  pose proof LK as [(SPR & SPA') (SPT & SPA) (LLO & LOR) (FPOS & F64 & FSEG & FLO) (FSELF & SHB0 & SHT)].
  destruct X as [usp sp' f lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  pose proof LE as LE'. destruct LE as (EDOC & EFD & EKD & ELO & EHI). cbn [lf_usp lf_S1 lf_F lf_lo] in EDOC, EFD, EKD, ELO, EHI.
  pose proof AM as (C16 & C100 & C128 & CE & CO & CS & AI & LIB & NL & IOS). cbn [lf_usp lf_S1 lf_F lf_lo] in C16, C100, C128, CE, CO, CS.
  pose proof (af_sp0_range RT AF Σ m ARTg) as SP0R. pose proof AL as (ALT & ALS & ALP & ALF & WLO).
  unfold lf_st. cbn [lf_usp lf_S1 lf_F lf_lo el_arm_pcA Z.leb Z.ltb andb nth Z.to_nat Pos.to_nat Pos.iter_op Nat.add EL_ARMS_A].
  pose proof OKE as OK'. destruct OK' as [_ _ P1F P1L (T16 & NT8 & TN & TS & TL) _ PTRR P0' _ LOW' [HL HT]].
  assert (ES96 : bv_unsigned (wz (sp' + -96)) = sp' + -96) by (apply unsigned_lit; ul).
  assert (NEED' : lo + 1024 + RT_STACK <= sp') by (clear - NEED; unfold arm_needA in NEED; cbn [Z.eqb Pos.eqb orb] in NEED; unfold RT_STACK in *; lia).
  assert (SLO : shad f + 128 <= sp' - 256) by (clear - SHT LOR SPR; ul).
  assert (FPW : forall Σx, fp_client RT Σx (ae_lo E) (w25_W sp')) by (intros Σx; unfold w25_W; apply (fp_client_stack2 RT E Σx); rewrite ?ELO; clear - LOR SPR SPT; ul).
  assert (FPO : forall Σx, fp_client RT Σx (ae_lo E) [(sp' + 128, sp' + 152)]) by (intros Σx; apply (fp_client_stack1 RT E Σx); rewrite ?ELO; clear - LOR SPR SPT; ul).
  assert (ARTM : forall m', munch (w25_W sp') m m' -> wmono bsegs m m' -> ART RT Σ m') by (intros m' MU WM; exact (lvl_art_munch RT AF E Σ _ m m' ARTg AL (FPW Σ) MU WM)).
  assert (SZN : forall m', munch (w25_W sp') m m' -> wmono bsegs m m' -> shz m' (f + 208) 16).
  { intros m' MU WM. apply (fobj_shz RT AF Σ m' (f + 208) 16 (ARTM m' MU WM)). apply (el_elem_fobj RT Σ m' f 0 0 (-8) t); [| exact FRS| exact FPOS| exact F64].
    eapply rw_cells_agree_nw; [exact CS|]. apply (agree_of_munch _ _ _ _ MU). intros x Hx. unfold el_shadow_armA in Hx. rewrite el_shadowA_size in Hx. unfold w25_W. cbn [outside].
    clear - Hx SLO. repeat split; lia. }
  assert (HWlo : Forall (fun r => ae_lo E <= fst r) (w25_W sp')) by (unfold w25_W; rewrite ELO; constructor; [cbn; clear - LOR SPR; ul|]; constructor; [cbn; clear - LOR SPR; ul| constructor]).
  assert (AIM : forall m', munch (w25_W sp') m m' -> AINV_A E m') by (intros m' MU; exact (AINV_A_munch E _ m m' OKE AI MU HWlo)).
  assert (SZD : forall m', munch (w25_W sp') m m' -> wmono bsegs m m' -> shz m' (ae_DOC E) 16) by (intros m' MU WM; exact (lvl_shz_doc E OKE m' (AIM m' MU))).
  assert (SZT : forall m', munch (w25_W sp') m m' -> wmono bsegs m m' -> shz m' (ae_TAPE E) (8 * ae_n E)) by (intros m' MU WM; exact (lvl_shz_tape RT AF E OKE Σ m' (ARTM m' MU WM) AL)).
  assert (SZOa : forall m', ART RT Σ m' -> shz m' (sp' + 128) 24).
  { intros m' HA. apply (lvl_shz_rec RT AF E OKE Σ m' (sp' + 128) 24 HA AL); rewrite ?ELO, ?EHI; [clear - LOR SPR; ul| clear - SPR; lia| clear - SPA'; Z.div_mod_to_equations; lia| reflexivity| lia]. }

  pose proof AI as (_ & _ & PTRB & _ & _). pose proof (bytes_at_bound bsegs m _ _ PTRB) as [PT0 PTL]. rewrite length_map in PTL.
  set (Lk := zlength (ae_p1 E)) in *. set (kb := map (Z_to_bv 8) (ae_p1 E)).
  assert (LKB : Z.of_nat (length kb) = Lk) by (subst kb Lk; unfold zlength; rewrite length_map; reflexivity).
  assert (LK0 : 0 <= Lk) by (subst Lk; unfold zlength; lia).
  set (Kp := ae_PTR E mod 2^64).
  assert (KPR : 0 <= Kp < 2^64) by (subst Kp; apply Z.mod_pos_bound; lia).
  assert (KNE : 0 < Lk -> ae_p1 E <> [] /\ Kp = ae_PTR E).
  { intros H. assert (NE : ae_p1 E <> []) by (intros X'; subst Lk; unfold zlength in H; rewrite X' in H; cbn in H; lia).
    split; [exact NE|]. subst Kp. apply Z.mod_small. pose proof (PTRR NE). clear - H0 P0' LLO LOR SPT SPR ELO. unfold zlength in *. ul. }
  assert (KEYB : forall mx, AINV_A E mx -> bytes_at bsegs mx Kp kb).
  { intros mx (_ & _ & PB & _ & _). destruct (Z.eq_dec Lk 0) as [L0|LP].
    - assert (E0 : ae_p1 E = []) by (destruct (ae_p1 E) eqn:EP; [reflexivity| exfalso; subst Lk; unfold zlength in L0; cbn [length] in L0; lia]).
      subst kb. rewrite E0. cbn [map]. apply bytes_at_nil. clear - KPR. lia.
    - destruct (KNE ltac:(lia)) as [_ EK]. rewrite EK. exact PB. }
  replace (Z_to_bv 64 (ae_PTR E)) with (Z_to_bv 64 Kp) by (subst Kp; apply Z_to_bv_mod64).

  apply (aevt_evt RT AF PMc MST).
  eapply (w25_walk1 E OKE _ m F fc sp' f usp idx Kp Lk 25 jr ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 (wz 0) (wz (f + 120)) t3 t4 t5 t6);
    [rewrite ELO; exact STg| rewrite ELO; clear - NEED'; ul| rewrite EHI; clear - SPR; lia| exact SPA'| exact MIg| exact KPR| subst Lk; clear - P1L LK0; lia
    | exact C16| exact CE| exact FPOS| rewrite ELO; clear - FLO; lia| exact C128| exact AIM| intros m' MU WM; exact (shb_cells_of_art RT AF Σ m' (ARTM m' MU WM))| exact SZN| exact SZD| exact SZT| |].
  -
    intros m1 xa3 xa4 j0 j8 j16 j20 MU1 WM1 MI1 ST1 FR1 OUT1 NA. apply evt_done.
    pose proof (ARTM m1 MU1 WM1) as ART1.
    pose proof OUT1 as [_ WRO1]. cbn [cells_size csize Nat.add] in WRO1. change (Z.of_nat 24) with 24 in WRO1.
    pose proof (call_ok_lvl RT E OKE Σ m1 (sp' + -96) AL ST1 ltac:(rewrite ELO; clear - NEED'; ul) ltac:(clear - SPT SPR; ul) ltac:(clear - SPA'; Z.div_mod_to_equations; lia)) as COK1.
    eapply (aevt_memsetP RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (sp' + 128) 16 z8 (ae_lo E) eq_refl eq_refl eq_refl
              ltac:(clear - SPR SPT LLO LOR; ul) ltac:(clear; lia)
              (checked_dst_stack RT AF Σ m1 (wz (sp' + -96)) (sp' + 128) 16 ART1 ltac:(rewrite ELO in WLO; clear - WLO LOR SPR; ul) ltac:(clear - SPT SPR; ul) ltac:(rewrite ES96; lia)
                 (wr_at_sub m1 (sp' + 128) 24 (sp' + 128) 16 WRO1 ltac:(lia) ltac:(lia) ltac:(lia))) ART1 MI1 COK1).
    intros w0 w1 w2 g1 g2 g3 g4 g5 g6 g7 w3 w4 w5 w6 F2 m2 (ART2 & MI2 & WM2 & ST2) PRES2 BY2. rewrite ES96 in ST2, PRES2. change (Z.to_nat 16) with 16%nat in BY2.
    rewrite (ret_pc_even 0xb56cc) by lia.
    assert (AG12 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) (sp' + -96) x /\ ~ (sp' + 128 <= x < sp' + 128 + 16)) -> agree_on P m1 m2).
    { intros P HP ad Ha. destruct (HP _ Ha) as [H N]. exact (PRES2 ad H N). }
    pose proof (rw_cells_merge bsegs m1 (sp' + -96) [] [CB 8 j0; CB 8 j8; CB 4 j16; CB 4 j20] _ FR1) as FRj1. cbn [app cells_size csize Nat.add cells_bytes] in FRj1.
    lazymatch type of FRj1 with rw_cells _ _ _ (CB _ ?bs :: _) => set (j24 := bs) in FRj1; clearbody j24 end.
    assert (FR2 : rw_cells bsegs m2 (sp' + -96) (CB 24 j24 :: w25_saved s7 s6 (wz (f + 96)) (wz (f + 32)) (wz (shad f)) (wz f) (wz sp') (wz usp) (wz 0xb23c0))).
    { eapply rw_cells_agree_nw; [exact FRj1|]. apply AG12. intros x Hx. unfold w25_saved in Hx. cbn [cells_size csize Nat.add app length] in Hx. split; [left; clear - Hx SPT SPR; ul| lia]. }
    pose proof OUT1 as OUT1'. apply (rw_cells_split_CB bsegs _ _ [] 24 _ [] [16; 4; 4]%nat) in OUT1'; [| reflexivity]. cbn [mk_CB_cells app] in OUT1'.
    lazymatch type of OUT1' with rw_cells _ _ _ [CB 16 ?xa; CB 4 ?xb; CB 4 ?xc] =>
      pose proof (rec_copy16 m1 m2 (sp' + 128) [CB 16 xa] (CB 4 xb) xc (repeat z8 16) _ _ _ OUT1' eq_refl eq_refl BY2 eq_refl WM2 PRES2 ltac:(lia) ltac:(clear - SPT SPR; ul)) as OUT2 end.
    apply (aevt_evt RT AF PMc MST).
    eapply evt_eq; [| eapply (w25_after_set E OKE _ m2 F2 fc sp' (sp' + 128));
      [exact FR2| exact ST2| rewrite ELO; clear - NEED'; ul| rewrite EHI; clear - SPR; lia| exact MI2| clear; lia| reflexivity| exact OUT2| clear; lia| rewrite EHI; clear - SPR; lia| exact (SZOa m2 ART2)|]];
      [atp_st_eq|].
    intros m3 MU3 WM3 MI3 ST3 OUT3. rewrite ELO in ST3. replace (sp' + 128 + 24) with (sp' + 152) in MU3 by lia.
    assert (OUTm : rw_cells bsegs m3 (sp' + 128) ([] ++ [CB 16 (repeat z8 16); C4 (wz 17); CB 4 (firstn 4 (skipn 4 (skipn 16 jr)))] ++ [])) by (cbn [app]; exact OUT3).
    pose proof (rw_cells_merge bsegs m3 (sp' + 128) [] _ [] OUTm) as OUTj. cbn [app cells_size csize Nat.add cells_bytes] in OUTj.
    apply (aevt_evt RT AF PMc MST). zstep. apply evt_done. apply (POST false (rt_credit RT Σ) Σ m3 fc F2).
    eapply (arm_post_out RT AF W 25 (mkLF usp sp' f lo) E Σ sel idx jr jos t m m3 fc _ LK OKE LE' AL FRS ARTg AM (lvl_art_munch RT AF E Σ _ m2 m3 ART2 AL (FPO Σ) MU3 WM3) MI3 ST3 FRM);
      [| exact OUTj| reflexivity].
    intros ad Ha Hn. cbn [lf_S1] in Ha, Hn. rewrite (MU3 ad), (PRES2 ad), (MU1 ad); [reflexivity| | | |].
    + unfold w25_W. cbn [outside]. split; [pose proof (NBELOW _ Ha) as X'; cbn [lf_S1] in X'; clear - X'; lia| split; [clear - Hn; lia| exact I]].
    + apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e He; exact He| lia].
    + clear - Hn. lia.
    + cbn [outside]. split; [clear - Hn; lia| exact I].
  -
    intros m1 d' e c xa4 j20 MU1 WM1 MI1 ST1 FR1 OUT1 TY NXT TILES EN. apply evt_done.
    pose proof (ARTM m1 MU1 WM1) as ART1.
    assert (ND1 : rw_cells bsegs m1 (sp' + -96) [C8 (wz (ae_DOC E)); C8 (wz 1)]).
    { pose proof FR1 as X'. change ([C8 (wz (ae_DOC E)); C8 (wz 1); C4 (wz 0); CB 4 j20] ++ ?r) with ([C8 (wz (ae_DOC E)); C8 (wz 1)] ++ ([C4 (wz 0); CB 4 j20] ++ r)) in X'.
      apply Sj_stage1_kit.rw_cells_app in X' as [X' _]. exact X'. }
    pose proof OUT1 as OUT1'. apply (rw_cells_split_CB bsegs _ _ [] 24 _ [] [8; 8; 4; 4]%nat) in OUT1'; [| reflexivity]. cbn [mk_CB_cells app] in OUT1'.

    assert (FRK : forall mx, agree_on (PK RT Σ (sp' + -96) (sp' + 128)) m1 mx ->
      rw_cells bsegs mx (sp' + -96) ([C8 (wz (ae_DOC E)); C8 (wz 1); C4 (wz 0); CB 4 j20] ++ w25_saved s7 s6 (wz (f + 96)) (wz (f + 32)) (wz (shad f)) (wz f) (wz sp') (wz usp) (wz 0xb23c0))).
    { intros mx AG. eapply rw_cells_agree_nw; [exact FR1|]. eapply agree_sub; [exact AG|]. intros x Hx. unfold w25_saved in Hx. cbn [cells_size csize Nat.add app length] in Hx.
      unfold PK. split; [left; clear - Hx SPT SPR; ul| clear - Hx; lia]. }

    assert (FIN : forall (mx : mem) (Fx : bvmap 5 word) (rec : list cell) (y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 : word),
      ART RT Σ mx -> mem_inv bsegs mx -> stk bsegs mx (ae_lo E) (sp' + -96) -> agree_on (PK RT Σ (sp' + -96) (sp' + 128)) m1 mx ->
      rw_cells bsegs mx (sp' + 128) rec -> cells_size rec = 24%nat ->
      aevt RT PMc Σ K (MS (mkR (wz 0xb56b0) (wz (sp' + -96)) gp (wz TPV) y5 y6 y7 (wz Lk) (wz Kp) ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7
                           (wz (sp' + 128)) (wz (f + 208)) (wz (f + 216)) (wz SHB) (wz (shad (f + 208))) (wz (shad (f + 216))) (wz Kp) (wz 0) (wz Lk) (wz (f + 120)) y28 y29 y30 y31)
                      Fx (wz 0xb56b0) fc None mx (seg_rom bsegs))).
    { intros until y31. intros ARTx MIx STx AGx OUTx RSZ.
      pose proof (FRK mx AGx) as FRx.
      pose proof (rw_cells_merge bsegs mx (sp' + -96) [] [C8 (wz (ae_DOC E)); C8 (wz 1); C4 (wz 0); CB 4 j20] _ FRx) as FRj. cbn [app cells_size csize Nat.add cells_bytes] in FRj.
      apply (aevt_evt RT AF PMc MST).
      eapply (w25_epi E OKE true _ mx Fx fc sp' []); [exact FRj| exact STx| rewrite ELO; clear - NEED'; ul| rewrite EHI; clear - SPR; lia| exact MIx| clear; lia| reflexivity|].
      intros STx'. rewrite ELO in STx'.
      assert (OUTm : rw_cells bsegs mx (sp' + 128) ([] ++ rec ++ [])) by (cbn [app]; rewrite app_nil_r; exact OUTx).
      pose proof (rw_cells_merge bsegs mx (sp' + 128) [] _ [] OUTm) as OUTj. rewrite RSZ in OUTj. cbn [app] in OUTj.
      apply (aevt_evt RT AF PMc MST). zstep. apply evt_done. apply (POST false (rt_credit RT Σ) Σ mx fc Fx).
      eapply (arm_post_out RT AF W 25 (mkLF usp sp' f lo) E Σ sel idx jr jos t m mx fc _ LK OKE LE' AL FRS ARTg AM ARTx MIx STx' FRM); [| exact OUTj| reflexivity].
      intros ad Ha Hn. cbn [lf_S1] in Ha, Hn. rewrite <- (MU1 ad); [apply AGx; unfold PK; split; [apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros ee He; exact He| intros ee He; exact He| lia]| clear - Hn; lia]|].
      unfold w25_W. cbn [outside]. split; [pose proof (NBELOW _ Ha) as X'; cbn [lf_S1] in X'; clear - X'; lia| split; [clear - Hn; lia| exact I]]. }
    lazymatch type of OUT1' with rw_cells _ _ _ [CB 8 ?xa; CB 8 ?xb; CB 4 ?xc; CB 4 ?xd] =>
    eapply (el_atkeyB RT AF RC2 E OKE d' PMc FDO MST Σ K m1 fc (sp' + -96) (sp' + 128) (sp' + -96) 1 e c Kp Lk 0xb56b0 kb gp
              (wz Lk) (wz Kp) (wz (sp' + 128)) (wz (f + 208)) (wz (f + 216)) (wz SHB) (wz (shad (f + 208))) (wz (shad (f + 216))) (wz Kp) (wz 0) (wz Lk) (wz (f + 120)) xd) end;
      [exact AL| exact TY| exact NXT| exact TILES| clear; lia| exact EN| rewrite ELO; clear - NEED'; ul| clear; lia| clear; lia| clear; lia| rewrite EHI; clear - SPR; lia
      | clear - SPA'; Z.div_mod_to_equations; lia| rewrite EHI; clear - SPR; lia| clear - SPA'; Z.div_mod_to_equations; lia| clear - SPA'; Z.div_mod_to_equations; lia
      | exact LKB| exact KPR
      | intros H; destruct (KNE H) as [NE EK]; rewrite EK; pose proof (PTRR NE) as (Q1 & Q2 & Q3 & Q4); clear - Q1 Q2; lia
      | intros H; destruct (KNE H) as [NE EK]; rewrite EK; pose proof (PTRR NE) as (Q1 & Q2 & Q3 & Q4); subst Lk; clear - Q3 Q4; lia
      | subst Lk; clear - P1L LK0; lia
      | intros H mx HA _; destruct (KNE H) as [NE EK]; rewrite EK; destruct ALP as [E0|INPB]; [exfalso; exact (NE E0)|]; pose proof (PTRR NE) as (Q1 & Q2 & Q3 & Q4);
        apply (checked_src_live RT AF Σ mx _ (ae_lo E) (ae_PB E) (ae_NPB E) (ae_PTR E) Lk HA INPB); [exact Q2| subst Lk; exact Q3| exact WLO]
      | intros ad Had; destruct (Z.eq_dec Lk 0) as [L0|LP]; [exfalso; clear - Had L0; lia|]; destruct (KNE ltac:(clear - LP LK0; lia)) as [NE EK]; rewrite EK in Had;
        destruct ALP as [E0|INPB]; [exfalso; exact (NE E0)|]; pose proof (PTRR NE) as (Q1 & Q2 & Q3 & Q4);
        right; right; left; exists (ae_PB E), (ae_NPB E); split; [exact INPB| subst Lk; clear - Had Q2 Q3; lia]
      | clear; lia| reflexivity
      | | | exact ART1| exact MI1| exact ST1| exact (AIM m1 MU1)| exact ND1| exact OUT1'| exact (KEYB m1 (AIM m1 MU1))].
    +
      intros m' F' it j' y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 ART' MI' ST' AI' AGK NODE' STR EL' ITLO JE REC.
      eapply (FIN m' F'); [exact ART'| exact MI'| exact ST'| exact AGK| exact REC| reflexivity].
    +
      intros m' F' y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 ART' MI' ST' AI' AGK NODE' REC.
      eapply (FIN m' F'); [exact ART'| exact MI'| exact ST'| exact AGK| exact REC| reflexivity].
Qed.

Theorem arm29_okA : forall W, arm_cpsA RT PMc W 29.
Proof using AF RC RC2.
  intros W Σ K X E sel idx jr jos t ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 t3 t4 t5 t6 F fc m
    FDO MST LK OKE LE WFS SEL IDX AL FRS LPA LVB CRB ARTg MIg STg NEED AM FRM XD AUX SPB POST.
  pose proof (arm_nbelow RT AF X E Σ m 256 LK LE AL FRS ARTg ltac:(lia) ltac:(clear - NEED; unfold arm_needA in NEED; cbn in NEED; ul)) as NBELOW.
  pose proof LK as [(SPR & SPA') (SPT & SPA) (LLO & LOR) (FPOS & F64 & FSEG & FLO) (FSELF & SHB0 & SHT)].
  destruct X as [usp sp' f lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  pose proof LE as LE'. destruct LE as (EDOC & EFD & EKD & ELO & EHI). cbn [lf_usp lf_S1 lf_F lf_lo] in EDOC, EFD, EKD, ELO, EHI.
  pose proof AM as (C16 & C100 & C128 & CE & CO & CS & AI & LIB & NL & IOS). cbn [lf_usp lf_S1 lf_F lf_lo] in C16, C100, C128, CE, CO, CS.
  pose proof (af_sp0_range RT AF Σ m ARTg) as SP0R. pose proof AL as (ALT & ALS & ALP & ALF & WLO).
  unfold lf_st. cbn [lf_usp lf_S1 lf_F lf_lo el_arm_pcA Z.leb Z.ltb andb nth Z.to_nat Pos.to_nat Pos.iter_op Nat.add EL_ARMS_A].
  pose proof OKE as OK'. destruct OK' as [_ _ P1F P1L (T16 & NT8 & TN & TS & TL) _ PTRR P0' _ LOW' [HL HT]].
  assert (ES96 : bv_unsigned (wz (sp' + -96)) = sp' + -96) by (apply unsigned_lit; ul).
  assert (NEED' : lo + 1024 + RT_STACK <= sp') by (clear - NEED; unfold arm_needA in NEED; cbn [Z.eqb Pos.eqb orb] in NEED; unfold RT_STACK in *; lia).
  assert (SLO : shad f + 128 <= sp' - 256) by (clear - SHT LOR SPR; ul).
  assert (FPW : forall Σx, fp_client RT Σx (ae_lo E) (w25_W sp')) by (intros Σx; unfold w25_W; apply (fp_client_stack2 RT E Σx); rewrite ?ELO; clear - LOR SPR SPT; ul).
  assert (FPO : forall Σx, fp_client RT Σx (ae_lo E) [(sp' + 128, sp' + 152)]) by (intros Σx; apply (fp_client_stack1 RT E Σx); rewrite ?ELO; clear - LOR SPR SPT; ul).
  assert (ARTM : forall m', munch (w25_W sp') m m' -> wmono bsegs m m' -> ART RT Σ m') by (intros m' MU WM; exact (lvl_art_munch RT AF E Σ _ m m' ARTg AL (FPW Σ) MU WM)).
  assert (SZN : forall m', munch (w25_W sp') m m' -> wmono bsegs m m' -> shz m' (f + 208) 16).
  { intros m' MU WM. apply (fobj_shz RT AF Σ m' (f + 208) 16 (ARTM m' MU WM)). apply (el_elem_fobj RT Σ m' f 0 0 (-8) t); [| exact FRS| exact FPOS| exact F64].
    eapply rw_cells_agree_nw; [exact CS|]. apply (agree_of_munch _ _ _ _ MU). intros x Hx. unfold el_shadow_armA in Hx. rewrite el_shadowA_size in Hx. unfold w25_W. cbn [outside].
    clear - Hx SLO. repeat split; lia. }
  assert (HWlo : Forall (fun r => ae_lo E <= fst r) (w25_W sp')) by (unfold w25_W; rewrite ELO; constructor; [cbn; clear - LOR SPR; ul|]; constructor; [cbn; clear - LOR SPR; ul| constructor]).
  assert (AIM : forall m', munch (w25_W sp') m m' -> AINV_A E m') by (intros m' MU; exact (AINV_A_munch E _ m m' OKE AI MU HWlo)).
  assert (SZD : forall m', munch (w25_W sp') m m' -> wmono bsegs m m' -> shz m' (ae_DOC E) 16) by (intros m' MU WM; exact (lvl_shz_doc E OKE m' (AIM m' MU))).
  assert (SZT : forall m', munch (w25_W sp') m m' -> wmono bsegs m m' -> shz m' (ae_TAPE E) (8 * ae_n E)) by (intros m' MU WM; exact (lvl_shz_tape RT AF E OKE Σ m' (ARTM m' MU WM) AL)).
  assert (SZOa : forall m', ART RT Σ m' -> shz m' (sp' + 128) 24).
  { intros m' HA. apply (lvl_shz_rec RT AF E OKE Σ m' (sp' + 128) 24 HA AL); rewrite ?ELO, ?EHI; [clear - LOR SPR; ul| clear - SPR; lia| clear - SPA'; Z.div_mod_to_equations; lia| reflexivity| lia]. }

  pose proof AI as (_ & _ & PTRB & _ & _). pose proof (bytes_at_bound bsegs m _ _ PTRB) as [PT0 PTL]. rewrite length_map in PTL.
  set (Lk := zlength (ae_p1 E)) in *. set (kb := map (Z_to_bv 8) (ae_p1 E)).
  assert (LKB : Z.of_nat (length kb) = Lk) by (subst kb Lk; unfold zlength; rewrite length_map; reflexivity).
  assert (LK0 : 0 <= Lk) by (subst Lk; unfold zlength; lia).
  set (Kp := ae_PTR E mod 2^64).
  assert (KPR : 0 <= Kp < 2^64) by (subst Kp; apply Z.mod_pos_bound; lia).
  assert (KNE : 0 < Lk -> ae_p1 E <> [] /\ Kp = ae_PTR E).
  { intros H. assert (NE : ae_p1 E <> []) by (intros X'; subst Lk; unfold zlength in H; rewrite X' in H; cbn in H; lia).
    split; [exact NE|]. subst Kp. apply Z.mod_small. pose proof (PTRR NE). clear - H0 P0' LLO LOR SPT SPR ELO. unfold zlength in *. ul. }
  assert (KEYB : forall mx, AINV_A E mx -> bytes_at bsegs mx Kp kb).
  { intros mx (_ & _ & PB & _ & _). destruct (Z.eq_dec Lk 0) as [L0|LP].
    - assert (E0 : ae_p1 E = []) by (destruct (ae_p1 E) eqn:EP; [reflexivity| exfalso; subst Lk; unfold zlength in L0; cbn [length] in L0; lia]).
      subst kb. rewrite E0. cbn [map]. apply bytes_at_nil. clear - KPR. lia.
    - destruct (KNE ltac:(lia)) as [_ EK]. rewrite EK. exact PB. }
  replace (Z_to_bv 64 (ae_PTR E)) with (Z_to_bv 64 Kp) by (subst Kp; apply Z_to_bv_mod64).

  apply (aevt_evt RT AF PMc MST).
  eapply (w29_walk1 E OKE _ m F fc sp' f usp idx Kp Lk 29 jr ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 (wz 0) (wz (f + 120)) t3 t4 t5 t6);
    [rewrite ELO; exact STg| rewrite ELO; clear - NEED'; ul| rewrite EHI; clear - SPR; lia| exact SPA'| exact MIg| exact KPR| subst Lk; clear - P1L LK0; lia
    | exact C16| exact CE| exact FPOS| rewrite ELO; clear - FLO; lia| exact C128| exact AIM| intros m' MU WM; exact (shb_cells_of_art RT AF Σ m' (ARTM m' MU WM))| exact SZN| exact SZD| exact SZT| |].
  -
    intros m1 xa3 xa4 j0 j8 j16 j20 MU1 WM1 MI1 ST1 FR1 OUT1 NA. apply evt_done.
    pose proof (ARTM m1 MU1 WM1) as ART1.
    pose proof OUT1 as [_ WRO1]. cbn [cells_size csize Nat.add] in WRO1. change (Z.of_nat 24) with 24 in WRO1.
    pose proof (call_ok_lvl RT E OKE Σ m1 (sp' + -96) AL ST1 ltac:(rewrite ELO; clear - NEED'; ul) ltac:(clear - SPT SPR; ul) ltac:(clear - SPA'; Z.div_mod_to_equations; lia)) as COK1.
    eapply (aevt_memsetP RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (sp' + 128) 16 z8 (ae_lo E) eq_refl eq_refl eq_refl
              ltac:(clear - SPR SPT LLO LOR; ul) ltac:(clear; lia)
              (checked_dst_stack RT AF Σ m1 (wz (sp' + -96)) (sp' + 128) 16 ART1 ltac:(rewrite ELO in WLO; clear - WLO LOR SPR; ul) ltac:(clear - SPT SPR; ul) ltac:(rewrite ES96; lia)
                 (wr_at_sub m1 (sp' + 128) 24 (sp' + 128) 16 WRO1 ltac:(lia) ltac:(lia) ltac:(lia))) ART1 MI1 COK1).
    intros w0 w1 w2 g1 g2 g3 g4 g5 g6 g7 w3 w4 w5 w6 F2 m2 (ART2 & MI2 & WM2 & ST2) PRES2 BY2. rewrite ES96 in ST2, PRES2. change (Z.to_nat 16) with 16%nat in BY2.
    rewrite (ret_pc_even 0xb5c2c) by lia.
    assert (AG12 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) (sp' + -96) x /\ ~ (sp' + 128 <= x < sp' + 128 + 16)) -> agree_on P m1 m2).
    { intros P HP ad Ha. destruct (HP _ Ha) as [H N]. exact (PRES2 ad H N). }
    pose proof (rw_cells_merge bsegs m1 (sp' + -96) [] [CB 8 j0; CB 8 j8; CB 4 j16; CB 4 j20] _ FR1) as FRj1. cbn [app cells_size csize Nat.add cells_bytes] in FRj1.
    lazymatch type of FRj1 with rw_cells _ _ _ (CB _ ?bs :: _) => set (j24 := bs) in FRj1; clearbody j24 end.
    assert (FR2 : rw_cells bsegs m2 (sp' + -96) (CB 24 j24 :: w25_saved s7 s6 (wz (f + 96)) (wz (f + 32)) (wz (shad f)) (wz f) (wz sp') (wz usp) (wz 0xb23f0))).
    { eapply rw_cells_agree_nw; [exact FRj1|]. apply AG12. intros x Hx. unfold w25_saved in Hx. cbn [cells_size csize Nat.add app length] in Hx. split; [left; clear - Hx SPT SPR; ul| lia]. }
    pose proof OUT1 as OUT1'. apply (rw_cells_split_CB bsegs _ _ [] 24 _ [] [16; 4; 4]%nat) in OUT1'; [| reflexivity]. cbn [mk_CB_cells app] in OUT1'.
    lazymatch type of OUT1' with rw_cells _ _ _ [CB 16 ?xa; CB 4 ?xb; CB 4 ?xc] =>
      pose proof (rec_copy16 m1 m2 (sp' + 128) [CB 16 xa] (CB 4 xb) xc (repeat z8 16) _ _ _ OUT1' eq_refl eq_refl BY2 eq_refl WM2 PRES2 ltac:(lia) ltac:(clear - SPT SPR; ul)) as OUT2 end.
    apply (aevt_evt RT AF PMc MST).
    eapply evt_eq; [| eapply (w29_after_set E OKE _ m2 F2 fc sp' (sp' + 128));
      [exact FR2| exact ST2| rewrite ELO; clear - NEED'; ul| rewrite EHI; clear - SPR; lia| exact MI2| clear; lia| reflexivity| exact OUT2| clear; lia| rewrite EHI; clear - SPR; lia| exact (SZOa m2 ART2)|]];
      [atp_st_eq|].
    intros m3 MU3 WM3 MI3 ST3 OUT3. rewrite ELO in ST3. replace (sp' + 128 + 24) with (sp' + 152) in MU3 by lia.
    assert (OUTm : rw_cells bsegs m3 (sp' + 128) ([] ++ [CB 16 (repeat z8 16); C4 (wz 17); CB 4 (firstn 4 (skipn 4 (skipn 16 jr)))] ++ [])) by (cbn [app]; exact OUT3).
    pose proof (rw_cells_merge bsegs m3 (sp' + 128) [] _ [] OUTm) as OUTj. cbn [app cells_size csize Nat.add cells_bytes] in OUTj.
    apply (aevt_evt RT AF PMc MST). zstep. apply evt_done. apply (POST false (rt_credit RT Σ) Σ m3 fc F2).
    eapply (arm_post_out RT AF W 29 (mkLF usp sp' f lo) E Σ sel idx jr jos t m m3 fc _ LK OKE LE' AL FRS ARTg AM (lvl_art_munch RT AF E Σ _ m2 m3 ART2 AL (FPO Σ) MU3 WM3) MI3 ST3 FRM);
      [| exact OUTj| reflexivity].
    intros ad Ha Hn. cbn [lf_S1] in Ha, Hn. rewrite (MU3 ad), (PRES2 ad), (MU1 ad); [reflexivity| | | |].
    + unfold w25_W. cbn [outside]. split; [pose proof (NBELOW _ Ha) as X'; cbn [lf_S1] in X'; clear - X'; lia| split; [clear - Hn; lia| exact I]].
    + apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e He; exact He| lia].
    + clear - Hn. lia.
    + cbn [outside]. split; [clear - Hn; lia| exact I].
  -
    intros m1 d' e c xa4 j20 MU1 WM1 MI1 ST1 FR1 OUT1 TY NXT TILES EN. apply evt_done.
    pose proof (ARTM m1 MU1 WM1) as ART1.
    assert (ND1 : rw_cells bsegs m1 (sp' + -96) [C8 (wz (ae_DOC E)); C8 (wz 1)]).
    { pose proof FR1 as X'. change ([C8 (wz (ae_DOC E)); C8 (wz 1); C4 (wz 0); CB 4 j20] ++ ?r) with ([C8 (wz (ae_DOC E)); C8 (wz 1)] ++ ([C4 (wz 0); CB 4 j20] ++ r)) in X'.
      apply Sj_stage1_kit.rw_cells_app in X' as [X' _]. exact X'. }
    pose proof OUT1 as OUT1'. apply (rw_cells_split_CB bsegs _ _ [] 24 _ [] [8; 8; 4; 4]%nat) in OUT1'; [| reflexivity]. cbn [mk_CB_cells app] in OUT1'.

    assert (FRK : forall mx, agree_on (PK RT Σ (sp' + -96) (sp' + 128)) m1 mx ->
      rw_cells bsegs mx (sp' + -96) ([C8 (wz (ae_DOC E)); C8 (wz 1); C4 (wz 0); CB 4 j20] ++ w25_saved s7 s6 (wz (f + 96)) (wz (f + 32)) (wz (shad f)) (wz f) (wz sp') (wz usp) (wz 0xb23f0))).
    { intros mx AG. eapply rw_cells_agree_nw; [exact FR1|]. eapply agree_sub; [exact AG|]. intros x Hx. unfold w25_saved in Hx. cbn [cells_size csize Nat.add app length] in Hx.
      unfold PK. split; [left; clear - Hx SPT SPR; ul| clear - Hx; lia]. }

    assert (FIN : forall (mx : mem) (Fx : bvmap 5 word) (rec : list cell) (y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 : word),
      ART RT Σ mx -> mem_inv bsegs mx -> stk bsegs mx (ae_lo E) (sp' + -96) -> agree_on (PK RT Σ (sp' + -96) (sp' + 128)) m1 mx ->
      rw_cells bsegs mx (sp' + 128) rec -> cells_size rec = 24%nat ->
      aevt RT PMc Σ K (MS (mkR (wz 0xb5c10) (wz (sp' + -96)) gp (wz TPV) y5 y6 y7 (wz Lk) (wz Kp) ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7
                           (wz (sp' + 128)) (wz (f + 208)) (wz (f + 216)) (wz SHB) (wz (shad (f + 208))) (wz (shad (f + 216))) (wz Kp) (wz 0) (wz Lk) (wz (f + 120)) y28 y29 y30 y31)
                      Fx (wz 0xb5c10) fc None mx (seg_rom bsegs))).
    { intros until y31. intros ARTx MIx STx AGx OUTx RSZ.
      pose proof (FRK mx AGx) as FRx.
      pose proof (rw_cells_merge bsegs mx (sp' + -96) [] [C8 (wz (ae_DOC E)); C8 (wz 1); C4 (wz 0); CB 4 j20] _ FRx) as FRj. cbn [app cells_size csize Nat.add cells_bytes] in FRj.
      apply (aevt_evt RT AF PMc MST).
      eapply (w29_epi E OKE true _ mx Fx fc sp' []); [exact FRj| exact STx| rewrite ELO; clear - NEED'; ul| rewrite EHI; clear - SPR; lia| exact MIx| clear; lia| reflexivity|].
      intros STx'. rewrite ELO in STx'.
      assert (OUTm : rw_cells bsegs mx (sp' + 128) ([] ++ rec ++ [])) by (cbn [app]; rewrite app_nil_r; exact OUTx).
      pose proof (rw_cells_merge bsegs mx (sp' + 128) [] _ [] OUTm) as OUTj. rewrite RSZ in OUTj. cbn [app] in OUTj.
      apply (aevt_evt RT AF PMc MST). zstep. apply evt_done. apply (POST false (rt_credit RT Σ) Σ mx fc Fx).
      eapply (arm_post_out RT AF W 29 (mkLF usp sp' f lo) E Σ sel idx jr jos t m mx fc _ LK OKE LE' AL FRS ARTg AM ARTx MIx STx' FRM); [| exact OUTj| reflexivity].
      intros ad Ha Hn. cbn [lf_S1] in Ha, Hn. rewrite <- (MU1 ad); [apply AGx; unfold PK; split; [apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros ee He; exact He| intros ee He; exact He| lia]| clear - Hn; lia]|].
      unfold w25_W. cbn [outside]. split; [pose proof (NBELOW _ Ha) as X'; cbn [lf_S1] in X'; clear - X'; lia| split; [clear - Hn; lia| exact I]]. }
    lazymatch type of OUT1' with rw_cells _ _ _ [CB 8 ?xa; CB 8 ?xb; CB 4 ?xc; CB 4 ?xd] =>
    eapply (el_atkeyB RT AF RC2 E OKE d' PMc FDO MST Σ K m1 fc (sp' + -96) (sp' + 128) (sp' + -96) 1 e c Kp Lk 0xb5c10 kb gp
              (wz Lk) (wz Kp) (wz (sp' + 128)) (wz (f + 208)) (wz (f + 216)) (wz SHB) (wz (shad (f + 208))) (wz (shad (f + 216))) (wz Kp) (wz 0) (wz Lk) (wz (f + 120)) xd) end;
      [exact AL| exact TY| exact NXT| exact TILES| clear; lia| exact EN| rewrite ELO; clear - NEED'; ul| clear; lia| clear; lia| clear; lia| rewrite EHI; clear - SPR; lia
      | clear - SPA'; Z.div_mod_to_equations; lia| rewrite EHI; clear - SPR; lia| clear - SPA'; Z.div_mod_to_equations; lia| clear - SPA'; Z.div_mod_to_equations; lia
      | exact LKB| exact KPR
      | intros H; destruct (KNE H) as [NE EK]; rewrite EK; pose proof (PTRR NE) as (Q1 & Q2 & Q3 & Q4); clear - Q1 Q2; lia
      | intros H; destruct (KNE H) as [NE EK]; rewrite EK; pose proof (PTRR NE) as (Q1 & Q2 & Q3 & Q4); subst Lk; clear - Q3 Q4; lia
      | subst Lk; clear - P1L LK0; lia
      | intros H mx HA _; destruct (KNE H) as [NE EK]; rewrite EK; destruct ALP as [E0|INPB]; [exfalso; exact (NE E0)|]; pose proof (PTRR NE) as (Q1 & Q2 & Q3 & Q4);
        apply (checked_src_live RT AF Σ mx _ (ae_lo E) (ae_PB E) (ae_NPB E) (ae_PTR E) Lk HA INPB); [exact Q2| subst Lk; exact Q3| exact WLO]
      | intros ad Had; destruct (Z.eq_dec Lk 0) as [L0|LP]; [exfalso; clear - Had L0; lia|]; destruct (KNE ltac:(clear - LP LK0; lia)) as [NE EK]; rewrite EK in Had;
        destruct ALP as [E0|INPB]; [exfalso; exact (NE E0)|]; pose proof (PTRR NE) as (Q1 & Q2 & Q3 & Q4);
        right; right; left; exists (ae_PB E), (ae_NPB E); split; [exact INPB| subst Lk; clear - Had Q2 Q3; lia]
      | clear; lia| reflexivity
      | | | exact ART1| exact MI1| exact ST1| exact (AIM m1 MU1)| exact ND1| exact OUT1'| exact (KEYB m1 (AIM m1 MU1))].
    +
      intros m' F' it j' y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 ART' MI' ST' AI' AGK NODE' STR EL' ITLO JE REC.
      eapply (FIN m' F'); [exact ART'| exact MI'| exact ST'| exact AGK| exact REC| reflexivity].
    +
      intros m' F' y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 ART' MI' ST' AI' AGK NODE' REC.
      eapply (FIN m' F'); [exact ART'| exact MI'| exact ST'| exact AGK| exact REC| reflexivity].
Qed.

End Arm25.
