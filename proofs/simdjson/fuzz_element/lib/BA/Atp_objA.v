(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun AtpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout Shadow RT_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import IcptSpec D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2 Sj_num_akit Sj_num_amem Sj_num_aframe I_lkit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA Atp_kitA Atp_elemA Atp_objdA Atp_objpA Atp_objkA Z6j Atp_objxA Atp_objcA Atp_objnA Z67 Atp_objmA Atp_objqA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Section ObjA.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RC2 : rt_contracts2 RT.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.
  Variable d : nat.
  Hypothesis HELEM : atp_elem_cpsA RT E d.
  Hypothesis HSSO : forall PMc (Σ Σ1 : rts RT) (I : objI), fdfs_only PMc -> mat_stable PMc -> octx RT E d Σ Σ1 I -> esc_sso_stmt RT E d PMc Σ Σ1 I.
  Hypothesis HHEAP : forall PMc (Σ Σ1 : rts RT) (I : objI), fdfs_only PMc -> mat_stable PMc -> octx RT E d Σ Σ1 I -> esc_heap_stmt RT E d PMc Σ Σ1 I.

  Local Ltac ul := lia_prep; unfold obj_needA, arr_needA, elem_needA, ATP_LEAFB, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

  Theorem atp_objA : atp_obj_cpsA RT E d.
  Proof using AF RC2 OK HELEM HSSO HHEAP.
    intros Σ PMc ptr i e c q out node P ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m jo
      FDO MST LV AI PAT TY NXT TEND TILES I0 EN PRE FRM.
    destruct PRE as (NODE & QN & NB & N8 & OUT & QO & OB & O8 & NO & ART0 & MI0 & ST0 & LOR & Q16 & FRB & CRB & LVB).
    intros T cc [Hc FC0] Hk.
    enough (AE : aevt RT PMc Σ (fun cf => lvl_postA RT E Σ PMc ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 out m (obj_costA d (zlength ptr)) cf /\ cfrm0 cf)
                   (lvl_entry ATP_OBJ_A ra q gp t0 t1 t2 s0 s1 out node P (zlength ptr) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)) by exact (AE T cc Hc Hk).
    pose proof OK as OK'. destruct OK' as [WF SBS P1F P1L (T16 & NT8 & TN & TS & TL) (S16 & NS8 & SN & SS & SL') PTRR P0' (D8 & DF & DL & DS & DT) LOW [HL HT]].
    pose proof LV as (LVT & LVS & _ & LVF & LWIN).
    pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
    assert (LO : ae_lo E + 304 <= q) by ul.
    pose proof (zlength_nonneg ptr) as ZLN.
    assert (CST : 1 <= obj_costA d (zlength ptr)) by (unfold obj_costA, LVL_C1, DCOST; lia).

    apply (aevt_evt RT AF PMc MST).
    eapply (obj_p1 E OK _ q out node P (zlength ptr)); [exact MI0| exact ST0| exact LO| exact Q16| lia| ul| exact (af_client_consts RT AF Σ m ART0)|].
    intros dd m1 jA jB jH xa1 xa2 Hdd B32 MU1 WM1 MI1 ST1 LOC HIGH SAVED. unfold obj_W0 in MU1.
    set (b := q + -288 - dd) in *. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    assert (EU : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; ul).
    pose proof (lvl_art_munch RT AF E Σ _ m m1 ART0 LV (fp_client_stack1 RT E Σ (q + -304) q ltac:(lia) ltac:(ul)) MU1 WM1) as ART1.
    pose proof (AINV_A_munch E _ m m1 OK AI MU1 ltac:(constructor; [cbn; lia| constructor])) as AI1.
    pose proof (rt_pres_fp_of_munch RT AF E Σ m (q + -304) q [(out, out + 24)] m m1 ART0 LV ltac:(lia) ltac:(eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside]; intros x' Hx; lia)) as PRES1.
    mport NODE MU1 WM1. mport OUT MU1 WM1.
    pose proof (call_ok_lvl RT E OK Σ m1 b LV ST1 ltac:(ul) ltac:(ul) ltac:(subst b; clear - B32; Z.div_mod_to_equations; lia)) as COK1.

    change (wz e_stack_malloc_1) with (Z_to_bv 64 e_stack_malloc_1).
    eapply (aevt_smalloc1 RT PMc FDO MST RC2 Σ); [reflexivity| unfold FRAMES_MAX2 in *; lia| lia| exact ART1| exact MI1| exact COK1| intros Efr0; exfalso; pose proof LV as (_ & _ & _ & LVF' & _); rewrite Efr0 in LVF'; exact LVF' |].
    intros Σ1 f t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m2 (ART2 & MI2 & WM2 & ST2) PR2 W1 W2 EF EL ES EC F0 F64 FTOP.
    rewrite EU in ST2, PR2. unfold OBJ_SM1_RA. rewrite (ret_pc_even 0xb5ec8) by lia. fold OBJ_SM1_RA. rewrite fs1 in W1, W2, FTOP. change (128 / 8) with 16 in W2. change (128 - 8) with 120 in W1.
    assert (HinF : In (f, 1%nat) (rt_frames RT Σ1)) by (rewrite EF; left; reflexivity).
    pose proof (new_frame_facts RT AF Σ1 m2 f 1 120 (ae_lo E) ART2 ltac:(rewrite ES; exact LWIN) HinF ltac:(rewrite fs1; reflexivity) eq_refl ltac:(lia)) as (_ & FLO & FHI & FSHw & S0 & SHIw).
    change (120 / 8) with 15 in FSHw, SHIw. fold (shad f) in FSHw, S0, SHIw.
    pose proof (proj2 (af_fshadow_apart RT AF Σ1 m2 f 1%nat ART2 HinF) f 1%nat HinF) as FSH. rewrite fs1s, fs1 in FSH.
    assert (SHI : shad f + 16 <= ae_lo E) by (unfold shad, SHB in *; unfold USTACK_TOP in FTOP; clear - FTOP LOW F0; lia).

    pose proof (agree_of_pres _ _ _ m1 m2 (fun x => aclient (rt_live RT Σ) (rt_frames RT Σ) b x) PR2 (fun x H => H)) as AG.
    xport_core LOC AG ltac:(fun Hx => left; unfold USTACK_TOP in *; flia). xport_core HIGH AG ltac:(fun Hx => left; unfold USTACK_TOP in *; flia).
    xport_core SAVED AG ltac:(fun Hx => left; unfold USTACK_TOP in *; flia). xport_core NODE AG ltac:(fun Hx => left; unfold USTACK_TOP in *; flia).
    xport_core OUT AG ltac:(fun Hx => left; unfold USTACK_TOP in *; flia).
    pose proof (AINV_A_pres RT Σ E b m1 m2 LV OK AI1 PR2) as AI2.
    assert (PRES2 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(out, out + 24)] m m2).
    { eapply rt_pres_fp_trans; [exact PRES1|]. intros a Ha _. apply PR2. apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia]. }
    pose proof (stk_transport_disjoint asegs _ m m1 _ _ ST0 MU1 WM1) as STq. clear STq.
    destruct (wr_at_rw_CB m2 f 120 W1 ltac:(lia)) as [jf HDRj]. destruct (wr_at_rw_CB m2 _ 16 W2 ltac:(lia)) as [js SHj].
    change (Z.to_nat 120) with 120%nat in HDRj. change (Z.to_nat 16) with 16%nat in SHj.
    apply (rw_cells_split_CB asegs m2 f [] 120 jf [] [8; 8; 8; 96]%nat) in HDRj; [| reflexivity]. cbn [mk_CB_cells app] in HDRj.
    apply (proj1 (rw_cells_app asegs m2 _ [_; _; _] _)) in HDRj. destruct HDRj as [HDR24 FREST]. cbn [cells_size csize Nat.add] in FREST.
    replace (f + Z.of_nat 24) with (f + 24) in FREST by lia.

    apply (aevt_evt RT AF PMc MST).
    eapply (obj_p2a E OK _ q dd out node P (zlength ptr) f); [exact MI2| exact Hdd| exact LO| lia| exact F64| exact FLO| exact FHI| exact FSHw| exact S0| exact SHIw| exact LOC| exact HDR24| exact SHj|].
    intros m3 xa0 xb1 xb2 xa3 xa4 jB1 jB2 js4 MU3 WM3 MI3 LOC3 HDR3 SH3.

    set (I := mkOI q dd out node P f ptr i e c ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m jH).
    assert (CTX : octx RT E d Σ Σ1 I).
    { constructor; cbn [oi_q oi_dd oi_out oi_node oi_P oi_f oi_ptr oi_i oi_e oi_c oi_L I]; unfold oi_b, oi_L; cbn [oi_q oi_dd oi_ptr I]; try assumption; repeat split; assumption. }

    assert (EL1i : forall x, In x (rt_live RT Σ) -> In x (rt_live RT Σ1)) by (rewrite EL; auto).
    assert (NEWF : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) q a -> ~ (f <= a < f + 128) /\ ~ (shad f <= a < shad f + 16)).
    { intros a Ha. rewrite <- fs1, <- (fs1s f). rewrite fs1 at 2. exact (newframe_apartI RT AF Σ Σ1 m2 f 1%nat q a ART2 EF EL1i ES ltac:(lia) Ha). }
    assert (SPLIT : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) q a -> q <= a \/ a < ae_lo E).
    { intros a Ha. destruct (aclient_split_c RT AF Σ1 m2 q a ART2 ltac:(rewrite EF; apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact EL1i| intros x Hx; right; exact Hx| lia])); [left; lia| right; rewrite ES in *; lia]. }
    assert (AG3 : agree_on (fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) q a) m2 m3).
    { apply (agree_of_munch _ _ _ _ MU3). intros x Hx. destruct (NEWF x Hx) as [N1 N2]. destruct (SPLIT x Hx) as [Hq|Hq]; cbn [outside]; clear - Hq N1 N2 LO DDR FHI; lia. }
    assert (OB3 : obase RT E Σ I Σ1 m3).
    { unfold obase. cbn [oi_q oi_dd oi_out oi_node oi_P oi_f oi_ptr oi_i oi_e oi_c oi_ra oi_gp oi_s0 oi_s1 oi_s2 oi_s3 oi_s4 oi_s5 oi_s6 oi_s7 oi_s8 oi_s9 oi_s10 oi_s11 oi_m0 oi_jH I]. unfold oi_b. cbn [oi_q oi_dd I]. fold b.
      split; [exact MI3|]. split.
      { lazymatch type of MU3 with munch ?W _ _ => apply (art_of_munch RT AF Σ1 m2 m3 (ae_lo E) W ART2 ltac:(rewrite ES; exact LWIN)); [| exact MU3| exact WM3] end.
        constructor; [left; cbn [fst snd]; ul|]. constructor; [right; right; left; cbn [fst snd]; exists f, 1%nat; split; [exact HinF| rewrite fs1; lia]|].
        constructor; [right; right; right; cbn [fst snd]; exists f, 1%nat; split; [exact HinF| rewrite fs1s; lia]| constructor]. }
      split. { apply (stk_transport_disjoint asegs _ m2 m3 (ae_lo E) b ST2 MU3 WM3). cbn [disjoint_from fst snd]. unfold shad in *. repeat split; lia. }
      split. { apply (AINV_A_agree E m2 m3 AI2). intros x Hx. apply AG3. exact (ainv_rng_aclient RT Σ E q (bv_unsigned x) LV OK Hx). }
      split. { mport SAVED MU3 WM3. exact SAVED. }
      split. { mport HIGH MU3 WM3. replace (q + -104 - dd) with (b + 184) in HIGH by lia. exact HIGH. }
      split; [exact HDR3|].
      eapply rt_pres_fp_trans; [exact PRES2|]. intros a Ha _. apply AG3. exact Ha. }
    mport NODE MU3 WM3. mport OUT MU3 WM3.
    lazymatch type of FREST with rw_cells _ _ _ ?cs => assert (AGF : agree_on (fun x => f + 24 <= x < f + 24 + Z.of_nat (cells_size cs)) m2 m3) end.
    { apply (agree_of_munch _ _ _ _ MU3). intros x Hx. cbn in Hx. cbn [outside]. clear - Hx FSH FHI LO DDR. lia. }
    apply (fun X => rw_cells_agree asegs m2 m3 _ _ X AGF WM3) in FREST. clear AGF.

    pose proof (obj_ddc RT AF RC2 E OK d HELEM PMc FDO MST Σ Σ1 I CTX (HSSO PMc Σ Σ1 I FDO MST CTX) (HHEAP PMc Σ Σ1 I FDO MST CTX) m3
                  t0' t1' t2' xa0 xb1 xb2 xa3 xa4 a5' a6' a7' s7 s9 s10 t3' t4' t5' t6' F' fc js4 jo jA jB1 jB2 _ OB3 FRM NODE LOC3 FREST SH3 OUT) as FIN.
    unfold Kpost in FIN. cbn [oi_q oi_dd oi_out oi_node oi_P oi_f oi_ptr oi_i oi_e oi_c oi_ra oi_gp oi_s0 oi_s1 oi_s2 oi_s3 oi_s4 oi_s5 oi_s6 oi_s7 oi_s8 oi_s9 oi_s10 oi_s11 oi_m0 oi_jH oi_L I] in FIN.
    unfold oi_b, oi_L in FIN. cbn [oi_q oi_dd oi_ptr I] in FIN. fold b in FIN. exact FIN.
  Qed.
End ObjA.
