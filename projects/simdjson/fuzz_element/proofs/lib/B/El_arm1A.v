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
     Pj_rtkA Pj_lftoi1A Pj_defsA Pj_os_defsA El_defsA El_lf1A El_lf2A El_lf2bA El_phasesA El_frontA El_parsekA El_armkitA El_armkit2A El_haccA El_arm1wA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Section Arm1.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.

Local Ltac ul := unfold FUZZ_STACK, PID_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.

Theorem arm1_okA : forall W, arm_cpsA RT PMc W 1.
Proof using AF RC.
  intros W Σ K X E sel idx jr jos t ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 t3 t4 t5 t6 F fc m
    FDO MST LK OKE LE WFS SEL IDX AL FRS LPA LVB CRB ARTg MIg STg NEED AM FRM XD AUX SPB POST.
  pose proof (arm_nbelow RT AF X E Σ m 80 LK LE AL FRS ARTg ltac:(lia) ltac:(clear - NEED; unfold arm_needA in NEED; cbn in NEED; ul)) as NBELOW.
  pose proof LK as [(SPR & SPA') (SPT & SPA) (LLO & LOR) (FPOS & F64 & FSEG & FLO) (FSELF & SHB0 & SHT)].
  destruct X as [usp sp' f lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  pose proof LE as LE'. destruct LE as (EDOC & EFD & EKD & ELO & EHI). cbn [lf_usp lf_S1 lf_F lf_lo] in EDOC, EFD, EKD, ELO, EHI.
  pose proof AM as (C16 & C100 & C128 & CE & CO & CS & AI & LIB & NL & IOS). cbn [lf_usp lf_S1 lf_F lf_lo] in C16, C100, C128, CE, CO, CS.
  pose proof (af_sp0_range RT AF Σ m ARTg) as SP0R. pose proof AL as (ALT & ALS & ALP & ALF & WLO).
  unfold lf_st. cbn [lf_usp lf_S1 lf_F lf_lo el_arm_pcA Z.leb Z.ltb andb nth Z.to_nat Pos.to_nat Pos.iter_op Nat.add EL_ARMS_A].
  pose proof OKE as OK'. destruct OK' as [_ _ _ _ (T16 & NT8 & TN & TS & TL) _ _ _ _ LOW' [HL HT]].
  assert (ES64 : bv_unsigned (wz (sp' + -64)) = sp' + -64) by (apply unsigned_lit; ul).
  assert (NEED' : lo + 1024 + RT_STACK <= sp') by (clear - NEED; unfold arm_needA in NEED; cbn [Z.eqb Pos.eqb orb] in NEED; unfold RT_STACK in *; lia).
  assert (SLO : shad f + 128 <= sp' - 80) by (clear - SHT LOR SPR; ul).
  assert (FPW : forall Σx, fp_client RT Σx (ae_lo E) (gw_W sp' (sp' + 128))) by (intros Σx; unfold gw_W; apply (fp_client_stack2 RT E Σx); rewrite ?ELO; clear - LOR SPR SPT; ul).
  assert (FPO : forall Σx, fp_client RT Σx (ae_lo E) [(sp' + 128, sp' + 152)]) by (intros Σx; apply (fp_client_stack1 RT E Σx); rewrite ?ELO; clear - LOR SPR SPT; ul).
  assert (ARTM : forall m', munch (gw_W sp' (sp' + 128)) m m' -> wmono bsegs m m' -> ART RT Σ m') by (intros m' MU WM; exact (lvl_art_munch RT AF E Σ _ m m' ARTg AL (FPW Σ) MU WM)).
  assert (SZN : forall m', munch (gw_W sp' (sp' + 128)) m m' -> wmono bsegs m m' -> shz m' (f + 208) 16).
  { intros m' MU WM. apply (fobj_shz RT AF Σ m' (f + 208) 16 (ARTM m' MU WM)). apply (el_elem_fobj RT Σ m' f 0 0 (-8) t); [| exact FRS| exact FPOS| exact F64].
    eapply rw_cells_agree_nw; [exact CS|]. apply (agree_of_munch _ _ _ _ MU). intros x Hx. unfold el_shadow_armA in Hx. rewrite el_shadowA_size in Hx. unfold gw_W. cbn [outside].
    clear - Hx SLO. repeat split; lia. }
  assert (HWlo : Forall (fun r => ae_lo E <= fst r) (gw_W sp' (sp' + 128))) by (unfold gw_W; rewrite ELO; constructor; [cbn; clear - LOR SPR; ul|]; constructor; [cbn; clear - LOR SPR; ul| constructor]).
  assert (AIM : forall m', munch (gw_W sp' (sp' + 128)) m m' -> AINV_A E m') by (intros m' MU; exact (AINV_A_munch E _ m m' OKE AI MU HWlo)).
  assert (SZD : forall m', munch (gw_W sp' (sp' + 128)) m m' -> wmono bsegs m m' -> shz m' (ae_DOC E) 16) by (intros m' MU WM; exact (lvl_shz_doc E OKE m' (AIM m' MU))).
  assert (SZT : forall m', munch (gw_W sp' (sp' + 128)) m m' -> wmono bsegs m m' -> shz m' (ae_TAPE E) (8 * ae_n E)) by (intros m' MU WM; exact (lvl_shz_tape RT AF E OKE Σ m' (ARTM m' MU WM) AL)).
  assert (SZOa : forall m', ART RT Σ m' -> shz m' (sp' + 128) 24).
  { intros m' HA. apply (lvl_shz_rec RT AF E OKE Σ m' (sp' + 128) 24 HA AL); rewrite ?ELO, ?EHI; [clear - LOR SPR; ul| clear - SPR; lia| clear - SPA'; Z.div_mod_to_equations; lia| reflexivity| lia]. }

  apply (aevt_evt RT AF PMc MST). astep. step. zstep.
  eapply (garr_walk1 E OKE _ m F fc sp' (f + 208) (sp' + 128) 0xb2484 jr gp t0 t1 t2 (wz usp) (wz sp') a2 a3 a4 a5 a6 a7
            (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 96)) s6 s7 (wz (ae_PTR E)) (wz 0) (wz (zlength (ae_p1 E))) (wz (f + 120)) t3 t4 t5 t6);
    [rewrite ELO; exact STg| rewrite ELO; clear - NEED'; ul| rewrite EHI; clear - SPR; lia| clear - SPA'; Z.div_mod_to_equations; lia| exact MIg
    | exact CE| clear - FPOS; lia| clear - FLO LOR SPR NEED'; ul| exact C128| clear; lia| rewrite EHI; clear - SPR; lia| clear - SPA'; Z.div_mod_to_equations; lia
    | clear; lia| reflexivity| exact AIM| intros m' MU WM; exact (shb_cells_of_art RT AF Σ m' (ARTM m' MU WM))| exact SZN| exact SZD| exact SZT
    | intros m' MU WM; exact (SZOa m' (ARTM m' MU WM))| |].
  -
    intros m1 x5 x6 x7 xa0 xa1 xa2 xa3 xa4 x28 x29 x30 x31 j4 MU1 WM1 MI1 ST1 OUT1. rewrite ELO in ST1.
    assert (OUTm : rw_cells bsegs m1 (sp' + 128) ([] ++ [C8 (wz (ae_DOC E)); C8 (wz 1); C4 (wz 0); CB 4 j4] ++ [])) by (cbn [app]; exact OUT1).
    pose proof (rw_cells_merge bsegs m1 (sp' + 128) [] _ [] OUTm) as OUTj. cbn [app cells_size csize Nat.add cells_bytes] in OUTj.
    zstep. apply evt_done. apply (POST false (rt_credit RT Σ) Σ m1 fc F).
    eapply (arm_post_out RT AF W 1 (mkLF usp sp' f lo) E Σ sel idx jr jos t m m1 fc _ LK OKE LE' AL FRS ARTg AM (ARTM m1 MU1 WM1) MI1 ST1 FRM);
      [| exact OUTj| reflexivity].
    intros ad Ha Hn. cbn [lf_S1] in Ha, Hn. apply MU1. unfold gw_W. cbn [outside]. split; [pose proof (NBELOW _ Ha) as X; cbn [lf_S1] in X; clear - X; lia| split; [clear - Hn; lia| exact I]].
  -
    intros m1 x5 x6 x7 xa3 xa4 x28 x29 x30 x31 j0 MU1 WM1 MI1 ST1 FR1 OUT1. apply evt_done.
    pose proof (ARTM m1 MU1 WM1) as ART1.
    pose proof OUT1 as [_ WRO1]. cbn [cells_size csize Nat.add] in WRO1. change (Z.of_nat 24) with 24 in WRO1.
    pose proof (call_ok_lvl RT E OKE Σ m1 (sp' + -64) AL ST1 ltac:(rewrite ELO; clear - NEED'; ul) ltac:(clear - SPT SPR; ul) ltac:(clear - SPA'; Z.div_mod_to_equations; lia)) as COK1.
    eapply (aevt_memsetP RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (sp' + 128) 16 z8 (ae_lo E) eq_refl eq_refl eq_refl
              ltac:(clear - SPR SPT LLO LOR; ul) ltac:(clear; lia)
              (checked_dst_stack RT AF Σ m1 (wz (sp' + -64)) (sp' + 128) 16 ART1 ltac:(rewrite ELO in WLO; clear - WLO LOR SPR; ul) ltac:(clear - SPT SPR; ul) ltac:(rewrite ES64; lia)
                 (wr_at_sub m1 (sp' + 128) 24 (sp' + 128) 16 WRO1 ltac:(lia) ltac:(lia) ltac:(lia))) ART1 MI1 COK1).
    intros w0 w1 w2 g1 g2 g3 g4 g5 g6 g7 w3 w4 w5 w6 F2 m2 (ART2 & MI2 & WM2 & ST2) PRES2 BY2. rewrite ES64 in ST2, PRES2. change (Z.to_nat 16) with 16%nat in BY2.
    rewrite (ret_pc_even 0xb2d7c) by lia.
    assert (AG12 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) (sp' + -64) x /\ ~ (sp' + 128 <= x < sp' + 128 + 16)) -> agree_on P m1 m2).
    { intros P HP ad Ha. destruct (HP _ Ha) as [H N]. exact (PRES2 ad H N). }
    assert (FR2 : rw_cells bsegs m2 (sp' + -64) (gw_frame (wz 0xb2484) (wz usp) (wz sp') (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 96)) j0)).
    { eapply rw_cells_agree_nw; [exact FR1|]. apply AG12. intros x Hx. unfold gw_frame in Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; clear - Hx SPT SPR; ul| lia]. }
    pose proof OUT1 as OUT1'. apply (rw_cells_split_CB bsegs _ _ [] 24 _ [] [16; 4; 4]%nat) in OUT1'; [| reflexivity]. cbn [mk_CB_cells app] in OUT1'.
    lazymatch type of OUT1' with rw_cells _ _ _ [CB 16 ?a; CB 4 ?b; CB 4 ?c] =>
      pose proof (rec_copy16 m1 m2 (sp' + 128) [CB 16 a] (CB 4 b) c (repeat z8 16) _ _ _ OUT1' eq_refl eq_refl BY2 eq_refl WM2 PRES2 ltac:(lia) ltac:(clear - SPT SPR; ul)) as OUT2 end.
    apply (aevt_evt RT AF PMc MST).
    eapply (garr_after_set E OKE _ m2 F2 fc sp' (sp' + 128) 0xb2484);
      [exact FR2| exact ST2| rewrite ELO; clear - NEED'; ul| rewrite EHI; clear - SPR; lia| exact MI2| exact OUT2| clear; lia| rewrite EHI; clear - SPR; lia| exact (SZOa m2 ART2)
      | clear; lia| reflexivity|].
    intros m3 MU3 WM3 MI3 ST3 OUT3. rewrite ELO in ST3. replace (sp' + 128 + 24) with (sp' + 152) in MU3 by lia.
    assert (OUTm : rw_cells bsegs m3 (sp' + 128) ([] ++ [CB 16 (repeat z8 16); C4 (wz 17); CB 4 (firstn 4 (skipn 4 (skipn 16 jr)))] ++ [])) by (cbn [app]; exact OUT3).
    pose proof (rw_cells_merge bsegs m3 (sp' + 128) [] _ [] OUTm) as OUTj. cbn [app cells_size csize Nat.add cells_bytes] in OUTj.
    zstep. apply evt_done. apply (POST false (rt_credit RT Σ) Σ m3 fc F2).
    eapply (arm_post_out RT AF W 1 (mkLF usp sp' f lo) E Σ sel idx jr jos t m m3 fc _ LK OKE LE' AL FRS ARTg AM (lvl_art_munch RT AF E Σ _ m2 m3 ART2 AL (FPO Σ) MU3 WM3) MI3 ST3 FRM);
      [| exact OUTj| reflexivity].
    intros ad Ha Hn. cbn [lf_S1] in Ha, Hn. rewrite (MU3 ad), (PRES2 ad), (MU1 ad); [reflexivity| | | |].
    + unfold gw_W. cbn [outside]. split; [pose proof (NBELOW _ Ha) as X; cbn [lf_S1] in X; clear - X; lia| split; [clear - Hn; lia| exact I]].
    + apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e He; exact He| lia].
    + clear - Hn. lia.
    + cbn [outside]. split; [clear - Hn; lia| exact I].
Qed.

Theorem arm2_okA : forall W, arm_cpsA RT PMc W 2.
Proof using AF RC.
  intros W Σ K X E sel idx jr jos t ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 t3 t4 t5 t6 F fc m
    FDO MST LK OKE LE WFS SEL IDX AL FRS LPA LVB CRB ARTg MIg STg NEED AM FRM XD AUX SPB POST.
  pose proof (arm_nbelow RT AF X E Σ m 80 LK LE AL FRS ARTg ltac:(lia) ltac:(clear - NEED; unfold arm_needA in NEED; cbn in NEED; ul)) as NBELOW.
  pose proof LK as [(SPR & SPA') (SPT & SPA) (LLO & LOR) (FPOS & F64 & FSEG & FLO) (FSELF & SHB0 & SHT)].
  destruct X as [usp sp' f lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  pose proof LE as LE'. destruct LE as (EDOC & EFD & EKD & ELO & EHI). cbn [lf_usp lf_S1 lf_F lf_lo] in EDOC, EFD, EKD, ELO, EHI.
  pose proof AM as (C16 & C100 & C128 & CE & CO & CS & AI & LIB & NL & IOS). cbn [lf_usp lf_S1 lf_F lf_lo] in C16, C100, C128, CE, CO, CS.
  pose proof (af_sp0_range RT AF Σ m ARTg) as SP0R. pose proof AL as (ALT & ALS & ALP & ALF & WLO).
  unfold lf_st. cbn [lf_usp lf_S1 lf_F lf_lo el_arm_pcA Z.leb Z.ltb andb nth Z.to_nat Pos.to_nat Pos.iter_op Nat.add EL_ARMS_A].
  pose proof OKE as OK'. destruct OK' as [_ _ _ _ (T16 & NT8 & TN & TS & TL) _ _ _ _ LOW' [HL HT]].
  assert (ES64 : bv_unsigned (wz (sp' + -64)) = sp' + -64) by (apply unsigned_lit; ul).
  assert (NEED' : lo + 1024 + RT_STACK <= sp') by (clear - NEED; unfold arm_needA in NEED; cbn [Z.eqb Pos.eqb orb] in NEED; unfold RT_STACK in *; lia).
  assert (SLO : shad f + 128 <= sp' - 80) by (clear - SHT LOR SPR; ul).
  assert (FPW : forall Σx, fp_client RT Σx (ae_lo E) (gw_W sp' (sp' + 128))) by (intros Σx; unfold gw_W; apply (fp_client_stack2 RT E Σx); rewrite ?ELO; clear - LOR SPR SPT; ul).
  assert (FPO : forall Σx, fp_client RT Σx (ae_lo E) [(sp' + 128, sp' + 152)]) by (intros Σx; apply (fp_client_stack1 RT E Σx); rewrite ?ELO; clear - LOR SPR SPT; ul).
  assert (ARTM : forall m', munch (gw_W sp' (sp' + 128)) m m' -> wmono bsegs m m' -> ART RT Σ m') by (intros m' MU WM; exact (lvl_art_munch RT AF E Σ _ m m' ARTg AL (FPW Σ) MU WM)).
  assert (SZN : forall m', munch (gw_W sp' (sp' + 128)) m m' -> wmono bsegs m m' -> shz m' (f + 208) 16).
  { intros m' MU WM. apply (fobj_shz RT AF Σ m' (f + 208) 16 (ARTM m' MU WM)). apply (el_elem_fobj RT Σ m' f 0 0 (-8) t); [| exact FRS| exact FPOS| exact F64].
    eapply rw_cells_agree_nw; [exact CS|]. apply (agree_of_munch _ _ _ _ MU). intros x Hx. unfold el_shadow_armA in Hx. rewrite el_shadowA_size in Hx. unfold gw_W. cbn [outside].
    clear - Hx SLO. repeat split; lia. }
  assert (HWlo : Forall (fun r => ae_lo E <= fst r) (gw_W sp' (sp' + 128))) by (unfold gw_W; rewrite ELO; constructor; [cbn; clear - LOR SPR; ul|]; constructor; [cbn; clear - LOR SPR; ul| constructor]).
  assert (AIM : forall m', munch (gw_W sp' (sp' + 128)) m m' -> AINV_A E m') by (intros m' MU; exact (AINV_A_munch E _ m m' OKE AI MU HWlo)).
  assert (SZD : forall m', munch (gw_W sp' (sp' + 128)) m m' -> wmono bsegs m m' -> shz m' (ae_DOC E) 16) by (intros m' MU WM; exact (lvl_shz_doc E OKE m' (AIM m' MU))).
  assert (SZT : forall m', munch (gw_W sp' (sp' + 128)) m m' -> wmono bsegs m m' -> shz m' (ae_TAPE E) (8 * ae_n E)) by (intros m' MU WM; exact (lvl_shz_tape RT AF E OKE Σ m' (ARTM m' MU WM) AL)).
  assert (SZOa : forall m', ART RT Σ m' -> shz m' (sp' + 128) 24).
  { intros m' HA. apply (lvl_shz_rec RT AF E OKE Σ m' (sp' + 128) 24 HA AL); rewrite ?ELO, ?EHI; [clear - LOR SPR; ul| clear - SPR; lia| clear - SPA'; Z.div_mod_to_equations; lia| reflexivity| lia]. }

  apply (aevt_evt RT AF PMc MST). astep. step. zstep.
  eapply (gobj_walk1 E OKE _ m F fc sp' (f + 208) (sp' + 128) 0xb2434 jr gp t0 t1 t2 (wz usp) (wz sp') a2 a3 a4 a5 a6 a7
            (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 96)) s6 s7 (wz (ae_PTR E)) (wz 0) (wz (zlength (ae_p1 E))) (wz (f + 120)) t3 t4 t5 t6);
    [rewrite ELO; exact STg| rewrite ELO; clear - NEED'; ul| rewrite EHI; clear - SPR; lia| clear - SPA'; Z.div_mod_to_equations; lia| exact MIg
    | exact CE| clear - FPOS; lia| clear - FLO LOR SPR NEED'; ul| exact C128| clear; lia| rewrite EHI; clear - SPR; lia| clear - SPA'; Z.div_mod_to_equations; lia
    | clear; lia| reflexivity| exact AIM| intros m' MU WM; exact (shb_cells_of_art RT AF Σ m' (ARTM m' MU WM))| exact SZN| exact SZD| exact SZT
    | intros m' MU WM; exact (SZOa m' (ARTM m' MU WM))| |].
  -
    intros m1 x5 x6 x7 xa0 xa1 xa2 xa3 xa4 x28 x29 x30 x31 j4 MU1 WM1 MI1 ST1 OUT1. rewrite ELO in ST1.
    assert (OUTm : rw_cells bsegs m1 (sp' + 128) ([] ++ [C8 (wz (ae_DOC E)); C8 (wz 1); C4 (wz 0); CB 4 j4] ++ [])) by (cbn [app]; exact OUT1).
    pose proof (rw_cells_merge bsegs m1 (sp' + 128) [] _ [] OUTm) as OUTj. cbn [app cells_size csize Nat.add cells_bytes] in OUTj.
    zstep. apply evt_done. apply (POST false (rt_credit RT Σ) Σ m1 fc F).
    eapply (arm_post_out RT AF W 2 (mkLF usp sp' f lo) E Σ sel idx jr jos t m m1 fc _ LK OKE LE' AL FRS ARTg AM (ARTM m1 MU1 WM1) MI1 ST1 FRM);
      [| exact OUTj| reflexivity].
    intros ad Ha Hn. cbn [lf_S1] in Ha, Hn. apply MU1. unfold gw_W. cbn [outside]. split; [pose proof (NBELOW _ Ha) as X; cbn [lf_S1] in X; clear - X; lia| split; [clear - Hn; lia| exact I]].
  -
    intros m1 x5 x6 x7 xa3 xa4 x28 x29 x30 x31 j0 MU1 WM1 MI1 ST1 FR1 OUT1. apply evt_done.
    pose proof (ARTM m1 MU1 WM1) as ART1.
    pose proof OUT1 as [_ WRO1]. cbn [cells_size csize Nat.add] in WRO1. change (Z.of_nat 24) with 24 in WRO1.
    pose proof (call_ok_lvl RT E OKE Σ m1 (sp' + -64) AL ST1 ltac:(rewrite ELO; clear - NEED'; ul) ltac:(clear - SPT SPR; ul) ltac:(clear - SPA'; Z.div_mod_to_equations; lia)) as COK1.
    eapply (aevt_memsetP RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (sp' + 128) 16 z8 (ae_lo E) eq_refl eq_refl eq_refl
              ltac:(clear - SPR SPT LLO LOR; ul) ltac:(clear; lia)
              (checked_dst_stack RT AF Σ m1 (wz (sp' + -64)) (sp' + 128) 16 ART1 ltac:(rewrite ELO in WLO; clear - WLO LOR SPR; ul) ltac:(clear - SPT SPR; ul) ltac:(rewrite ES64; lia)
                 (wr_at_sub m1 (sp' + 128) 24 (sp' + 128) 16 WRO1 ltac:(lia) ltac:(lia) ltac:(lia))) ART1 MI1 COK1).
    intros w0 w1 w2 g1 g2 g3 g4 g5 g6 g7 w3 w4 w5 w6 F2 m2 (ART2 & MI2 & WM2 & ST2) PRES2 BY2. rewrite ES64 in ST2, PRES2. change (Z.to_nat 16) with 16%nat in BY2.
    rewrite (ret_pc_even 0xb2f18) by lia.
    assert (AG12 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) (sp' + -64) x /\ ~ (sp' + 128 <= x < sp' + 128 + 16)) -> agree_on P m1 m2).
    { intros P HP ad Ha. destruct (HP _ Ha) as [H N]. exact (PRES2 ad H N). }
    assert (FR2 : rw_cells bsegs m2 (sp' + -64) (gw_frame (wz 0xb2434) (wz usp) (wz sp') (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 96)) j0)).
    { eapply rw_cells_agree_nw; [exact FR1|]. apply AG12. intros x Hx. unfold gw_frame in Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; clear - Hx SPT SPR; ul| lia]. }
    pose proof OUT1 as OUT1'. apply (rw_cells_split_CB bsegs _ _ [] 24 _ [] [16; 4; 4]%nat) in OUT1'; [| reflexivity]. cbn [mk_CB_cells app] in OUT1'.
    lazymatch type of OUT1' with rw_cells _ _ _ [CB 16 ?a; CB 4 ?b; CB 4 ?c] =>
      pose proof (rec_copy16 m1 m2 (sp' + 128) [CB 16 a] (CB 4 b) c (repeat z8 16) _ _ _ OUT1' eq_refl eq_refl BY2 eq_refl WM2 PRES2 ltac:(lia) ltac:(clear - SPT SPR; ul)) as OUT2 end.
    apply (aevt_evt RT AF PMc MST).
    eapply (gobj_after_set E OKE _ m2 F2 fc sp' (sp' + 128) 0xb2434);
      [exact FR2| exact ST2| rewrite ELO; clear - NEED'; ul| rewrite EHI; clear - SPR; lia| exact MI2| exact OUT2| clear; lia| rewrite EHI; clear - SPR; lia| exact (SZOa m2 ART2)
      | clear; lia| reflexivity|].
    intros m3 MU3 WM3 MI3 ST3 OUT3. rewrite ELO in ST3. replace (sp' + 128 + 24) with (sp' + 152) in MU3 by lia.
    assert (OUTm : rw_cells bsegs m3 (sp' + 128) ([] ++ [CB 16 (repeat z8 16); C4 (wz 17); CB 4 (firstn 4 (skipn 4 (skipn 16 jr)))] ++ [])) by (cbn [app]; exact OUT3).
    pose proof (rw_cells_merge bsegs m3 (sp' + 128) [] _ [] OUTm) as OUTj. cbn [app cells_size csize Nat.add cells_bytes] in OUTj.
    zstep. apply evt_done. apply (POST false (rt_credit RT Σ) Σ m3 fc F2).
    eapply (arm_post_out RT AF W 2 (mkLF usp sp' f lo) E Σ sel idx jr jos t m m3 fc _ LK OKE LE' AL FRS ARTg AM (lvl_art_munch RT AF E Σ _ m2 m3 ART2 AL (FPO Σ) MU3 WM3) MI3 ST3 FRM);
      [| exact OUTj| reflexivity].
    intros ad Ha Hn. cbn [lf_S1] in Ha, Hn. rewrite (MU3 ad), (PRES2 ad), (MU1 ad); [reflexivity| | | |].
    + unfold gw_W. cbn [outside]. split; [pose proof (NBELOW _ Ha) as X; cbn [lf_S1] in X; clear - X; lia| split; [clear - Hn; lia| exact I]].
    + apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e He; exact He| lia].
    + clear - Hn. lia.
    + cbn [outside]. split; [clear - Hn; lia| exact I].
Qed.

End Arm1.
