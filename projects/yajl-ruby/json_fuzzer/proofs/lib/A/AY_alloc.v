(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep SFW1_lemmas Arr Cells.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlParser YajlFactsBuf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep RY_lib RY_yalloc.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AI_shadow AI_globals2 AI_region_is_poisoned AI_asan_memcpy1 AI_asan_memcpy AI_asan_memset
     AYajlRep AYajl_iface AY_rz AY_hand AY_set_default AY_client AY_alloc1 AY_alloc2 AY_alloc3 AY_alloc4 AY_alloc5 AY_alloc6 AY_allocj4 AY_alloc8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section W.
Variable Y : ay_params.
Hypothesis KIPY : AHK_y_kip_stmt Y.
Hypothesis FRAMEY : AHK_y_frame_stmt Y.
Hypothesis BLKY : AHK_y_blocks_stmt Y.
Hypothesis BSHY : AHK_y_block_shadow_stmt Y.
Hypothesis BSMALL : AHK_y_small_high_stmt Y.   (* [comment removed for export] *)
Hypothesis LAYY : AHK_y_layout_stmt Y.
Hypothesis AFLSEP : AHK_y_aflsep_stmt Y.
Hypothesis PERMY : AHK_y_perm_stmt Y.
Hypothesis GLOBY : AHK_y_globals_shadow_stmt Y.
Hypothesis RRT : ayR_trans_stmt Y.
Hypothesis RREFL : ayR_refl_stmt Y.
Hypothesis NONNEG : yacct_nonneg_stmt Y.
Hypothesis YFREE : yacct_free_stmt Y.
Hypothesis YNEW : yphi_new_alloc_stmt Y.
Hypothesis ASM1 : astack_malloc_stmt Y 1 AY_STACK_MALLOC_1.
Hypothesis FREL : AHK_y_fake_release_stmt Y.
Hypothesis FND : AHK_y_fnodup_stmt Y.
Hypothesis AFLC : AHK_y_flag_cell_stmt Y.
Hypothesis WMAL : aywrap_malloc_stmt Y.
Hypothesis WREA0 : aywrap_realloc_null_stmt Y.
Hypothesis LALLOC : aylex_alloc_stmt Y.
Hypothesis BALLOC : aybuf_alloc_stmt Y.
Variable URA : list Z.
Hypothesis UTRIV : forall m SP ra s0, bv_unsigned s0 < alloc_ceiling -> In (bv_unsigned ra) URA -> y_uanchor Y m SP ra s0.
Hypothesis USTEP : forall m SP ra s0 ra' s0', In (bv_unsigned ra) URA -> SP + 16 <= bv_unsigned s0 < 2^47 ->
    rw_cells asegs m (bv_unsigned s0 - 16) [C8 s0'; C8 ra'] -> y_uanchor Y m (bv_unsigned s0) ra' s0' -> y_uanchor Y m SP ra s0.
Hypothesis UFRAME : forall m m' SP ra s0, (forall a, SP <= a < 2^47 -> m' (wa a) = m (wa a)) -> y_uanchor Y m SP ra s0 -> y_uanchor Y m' SP ra s0.
Hypothesis URA_mal : In 0x82640 URA.      (* [comment removed for export] *)
Hypothesis URA_lxa : In 0x826d4 URA.      (* [comment removed for export] *)
Hypothesis URA_ba : In 0x82710 URA.       (* [comment removed for export] *)
Hypothesis URA_rea : In 0x827a8 URA.      (* [comment removed for export] *)
Hypothesis ICPG : forall s LB LF m mo, y_AHK Y s LB LF m mo -> icp_globals asegs m A_SB.
Hypothesis ICPB : forall s LB LF m mo b A n, y_AHK Y s LB LF m mo -> In b LB ->
    ab_addr b <= A -> 1 <= n -> A + n <= ab_addr b + ab_size b ->
    exists ws, shadow_window asegs m A_SB A n ws /\ range_clean A_SB A n ws
               /\ shw_hi A_SB A n <= 0x10007fff8000 /\ amem (ab_addr b) (ab_size b).   (* [comment removed for export] *)
Hypothesis ICPR : forall s LB LF m mo b A n, y_AHK Y s LB LF m mo -> In b LB -> ab_addr b <= A -> 1 <= n -> A + n <= ab_addr b + ab_size b ->
    pages_budgeted (y_aS Y s) (shw_lo A_SB A) (shw_hi A_SB A n).
Hypothesis STATY : AHK_y_statics_stmt Y.

Ltac rchain := first [eassumption | eapply RRT; [eassumption| rchain]].

Theorem ayalloc_proof' : ayalloc_stmt Y.
Proof. aceil.
  unfold ayalloc_stmt. intros LF REST CFGP CX lo L RR K. intros until s.
  intros K0 AY CFC OSC OSX L0 CXSH ECFG CFGH FFL FLC FP EA0 EA1 EA2 EA3 CRED RR0 NBIG UA CONT. subst a0 a1 a2 a3.
  destruct FP as (ST & CEIL & LO & SPLT & SP16 & MI & TP & FRM). pose proof SPLT as SPH. rewrite ?unsigned_lit in * by lia.
  apply AYST_split in AY. destruct AY as [AHK0 YS]. pose proof YS as (YCB & YBAE & YNOOP & STA). ay_statics_open STA.
  destruct FFL as ([NL AL] & FLin & FLcx & FL1). cbn [fst snd] in FLcx, FL1. subst NL.
  unfold AY_ALLOC_STACK, AY_LEX_ALLOC_STACK, AY_BUF_ALLOC_STACK, AMALLOC_STACK, wz in *.
  aceil.
  unfold amem in CXSH.
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  destruct NONNEG as (NA0 & NB0 & NH0 & NN0). pose proof (NB0 ybuf_zero) as NBZ. pose proof YFREE as YF0. unfold yacct_free_stmt in YF0.
  pose proof (NA0 104) as NA104. pose proof (NA0 48) as NA48. pose proof (NA0 32) as NA32. pose proof (NA0 128) as NA128. pose proof (NN0 L) as NNL.
  (* [comment removed for export] *)
  destruct (LAYY _ _ _ _ _ AHK0) as (LAYF0 & _ & _). destruct (LAYF0 _ FLin) as (FL_1 & FL_2 & FL_3 & FL_4 & _). clear LAYF0. cbn [fst snd] in FL_1, FL_2, FL_3, FL_4.
  rewrite ff_bytes_1 in FL_1, FL_2, FL_3. unfold amem in FL_1. aceil.
  assert (E8L : AL = 8 * (AL / 8)) by (clear -CEILB FL_3; Z.div_mod_to_equations; lia).
  assert (ECF8 : CFGP / 8 = AL / 8 + 8) by (clear -CEILB ECFG FLcx E8L; Z.div_mod_to_equations; lia).
  assert (ECX8 : CX / 8 = AL / 8 + 4) by (clear -CEILB FLcx E8L; Z.div_mod_to_equations; lia).
  pose proof OSC as OSC0. destruct OSC as (CF8 & _ & CSH). unfold A_SB in CSH.
  (* [comment removed for export] *)
  arz_seg KIPY AHK0.
  pose proof (aypol_stack Y _ LF _ _ LINK lo (bv_unsigned sp) ltac:(aceil; lia) ltac:(lia)) as PSTK.
  pose proof (aypol_img Y _ LF _ _ LINK) as PIMG. unfold AY_IMG_LO, AY_IMG_HI in PIMG.
  eapply evtA_cut.
  { eapply aal1_seg; [ exact ST | exact MI | lia | lia | lia | exact SP16 | exact G1 | exact G2 | exact G3 | exact G4
      | unfold AY_CALLBACKS; lia | lia | lia | lia | exact PSTK | exact PIMG ]. }
  cbv beta. intros ms1 (SQ & jq & m1 & -> & SQ32 & SQR & MU & WM & MI1 & ST1 & FR1 & SV1 & GAP1).
  apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHKb R1].
  assert (AHK1 : y_AHK Y s REST LF m1 mo1).
  { eapply FRAMEY; [exact AHKb| exact MU| exact WM|]. constructor; [left; cbn [fst snd]; aceil; lia| constructor]. }
  clear AHKb.
  pose proof (aystatics_munch _ _ _ YS MU WM ltac:(constructor; [cbn [fst snd]; lia| constructor])) as YS1.
  assert (PRES1 : ay_pres REST LF (bv_unsigned sp) [] m m1).
  { eapply ay_pres_of_munch; [exact MU| exact WM|]. intros a Ha Hc _.
    eapply (ay_client_outside_stack Y BLKY LAYY _ _ _ _ _ REST (bv_unsigned sp)); [exact AHK0| intros b0 Hb0; exact Hb0| aceil; lia| lia| exact Hc]. }
  assert (AGREE1 : forall a, bv_unsigned sp <= a < 2^47 -> m1 (wa a) = m (wa a)).
  { intros a Ha. destruct (PRES1 a ltac:(lia) ltac:(left; lia) ltac:(intros F0; exact F0)) as [E _]. exact E. }
  pose proof (aypres_fframe _ _ _ _ _ _ _ (1, AL) PRES1 CFC FLin ltac:(left; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ff_bytes_1; lia)) as CFC1.
  assert (OSC1 : oshadow m1 CFGP 8).
  { eapply oshadow_agree; [eapply ay_pres_agree; exact PRES1| exact OSC0|]. intros a Ha. split; [| intros F0; exact F0].
    right; right; left. exists (1, AL). split; [exact FLin|]. right. cbn [fst snd]. unfold oshw_lo, oshw_hi, A_SB, amem in Ha |- *. rewrite shl8_1. clear -CEILB Ha FLcx ECFG E8L. Z.div_mod_to_equations. lia. }
  assert (OSX1 : oshadow m1 CX 8).
  { eapply oshadow_agree; [eapply ay_pres_agree; exact PRES1| exact OSX|]. intros a Ha. split; [| intros F0; exact F0].
    right; right; left. exists (1, AL). split; [exact FLin|]. right. cbn [fst snd]. unfold oshw_lo, oshw_hi, A_SB, amem in Ha |- *. rewrite shl8_1. clear -CEILB Ha FLcx ECFG E8L. Z.div_mod_to_equations. lia. }
  clear LINK BACK PSTK PIMG. unfold AAL_RET1, AY_STACK_MALLOC_1.
  (* [comment removed for export] *)
  eapply ASM1;
    [ exact K0 | exact AHK1 | exact FLC
    | rewrite unsigned_lit by lia; exact ST1
    | aceil; lia
    | rewrite unsigned_lit by lia; unfold AMALLOC_STACK; lia
    | rewrite unsigned_lit by lia; lia
    | rewrite unsigned_lit by lia; clear -CEILB SQ32; Z.div_mod_to_equations; lia
    | exact MI1 | exact TP | exact FRM
    | exact CRED
    | ].
  cbv beta. intros t0a t1a t2a a1a a2a a3a a4a a5a a6a a7a t3a t4a t5a t6a F2 fc2 m2 mo2 sa2 ff junk ST2 PRES2 WM2 MI2 FRM2 SO2 FF0 FFal FFsh FFce FFfr FFC FFS FLG AHK2 R2 CRED2.
  rewrite unsigned_lit in ST2, PRES2 by lia.
  rewrite ff_bytes_1 in FFal, FFsh, FFce, FFC. unfold amem in FFsh. aceil.
  change (Z.to_nat (128 - 8)) with 120%nat in FFC. unfold oshw_lo, A_SB in FFS. rewrite shl8_1 in FFS. change (Z.to_nat 16) with 16%nat in FFS.
  set (PF := y_aflag Y 1 ff) in FFC.
  assert (E8F : ff = 8 * (ff / 8)) by (clear -CEILB FFal; Z.div_mod_to_equations; lia).
  clear FLG.
  assert (FRESH : forall g, In g LF -> In g ((1, ff) :: LF) /\ snd g <> snd (1, ff)).
  { intros g Hg. split; [right; exact Hg|]. cbn [snd]. eapply notin_map_snd; [eapply FND; exact AHK2| exact Hg]. }
  destruct (LAYY _ _ _ _ _ AHK2) as (LAYF2 & LAYFB2 & LAYFF2).
  pose proof (LAYFF2 _ _ (or_intror FLin) (or_introl eq_refl) (proj2 (FRESH _ FLin))) as FL_ff. cbn [fst snd] in FL_ff. rewrite !ff_bytes_1 in FL_ff.
  pose proof (LAYF2 _ (or_introl eq_refl)) as (_ & _ & _ & _ & PFR). cbn [fst snd] in PFR. fold PF in PFR. unfold amem in PFR. aceil.
  clear LAYF2 LAYFB2 LAYFF2.
  pose proof (aypres_frame _ _ _ _ _ _ _ PRES2 FR1 ltac:(lia)) as FR2. pose proof (aypres_frame _ _ _ _ _ _ _ PRES2 SV1 ltac:(lia)) as SV2. clear FR1 SV1.
  assert (GAP2 : stk asegs m2 (SQ + 56) (bv_unsigned sp + -104)) by (eapply stk_agree; [eapply ay_pres_agree; exact PRES2| exact GAP1| intros a Ha; split; [left; lia| intros F0; exact F0]]). clear GAP1.
  pose proof (aypres_fframe _ _ _ _ _ _ _ (1, AL) PRES2 CFC1 FLin ltac:(left; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ff_bytes_1; lia)) as CFC2. clear CFC1.
  assert (OSC2 : oshadow m2 CFGP 8).
  { eapply oshadow_agree; [eapply ay_pres_agree; exact PRES2| exact OSC1|]. intros a Ha. split; [| intros F0; exact F0].
    right; right; left. exists (1, AL). split; [exact FLin|]. right. cbn [fst snd]. unfold oshw_lo, oshw_hi, A_SB, amem in Ha |- *. rewrite shl8_1. clear -CEILB Ha FLcx ECFG E8L. Z.div_mod_to_equations. lia. }
  assert (OSX2 : oshadow m2 CX 8).
  { eapply oshadow_agree; [eapply ay_pres_agree; exact PRES2| exact OSX1|]. intros a Ha. split; [| intros F0; exact F0].
    right; right; left. exists (1, AL). split; [exact FLin|]. right. cbn [fst snd]. unfold oshw_lo, oshw_hi, A_SB, amem in Ha |- *. rewrite shl8_1. clear -CEILB Ha FLcx ECFG E8L. Z.div_mod_to_equations. lia. }
  pose proof (aystatics_pres _ _ _ _ _ YS1 PRES2) as (YCB2 & YBAE2 & YNOOP2). pose proof (STATY _ _ _ _ _ AHK2) as STA2.
  assert (YS2 : aystatics m2) by (exact (conj YCB2 (conj YBAE2 (conj YNOOP2 STA2)))). clear YCB2 YBAE2 YNOOP2.
  assert (PRES2w : ay_pres REST LF (bv_unsigned sp) [] m m2).
  { eapply ay_pres_trans; [exact PRES1|]. eapply (ay_pres_weaken Y); [exact PRES2| lia| intros b0 Hb0; exact Hb0| auto| auto]. }
  assert (AGREE2 : forall a, bv_unsigned sp <= a < 2^47 -> m2 (wa a) = m (wa a)).
  { intros a Ha. rewrite <- (AGREE1 a Ha). destruct (PRES2 a ltac:(lia) ltac:(left; lia) ltac:(intros F0; exact F0)) as [E _]. exact E. }
  clear ST1 MI1 PRES2 AHK1 YS1 OSC1 OSX1 AGREE1 PRES1 AHK0 ST MI.
  (* [comment removed for export] *)
  arz_seg KIPY AHK2. ret_pc_lit. unfold wz.
  pose proof (aypol_stack Y _ ((1, ff) :: LF) _ _ LINK lo (SQ + 56) ltac:(aceil; lia) ltac:(lia)) as PSTK.
  pose proof (aypol_img Y _ ((1, ff) :: LF) _ _ LINK) as PIMG. unfold AY_IMG_LO, AY_IMG_HI in PIMG.
  pose proof (aypol_fframe Y _ ((1, ff) :: LF) _ _ LINK (1, ff) ff (ff + 128) (or_introl eq_refl) ltac:(cbn; lia) ltac:(cbn; rewrite ff_bytes_1; lia) ltac:(lia) ltac:(cbn; rewrite ff_bytes_1; lia)) as PFF.
  pose proof (aypol_ffshadow Y _ ((1, ff) :: LF) _ _ LINK (1, ff) (2147450880 + ff / 8) (2147450880 + ff / 8 + 16) (or_introl eq_refl)
                ltac:(cbn [snd]; unfold oshw_lo, A_SB; lia) ltac:(cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_1; lia) ltac:(lia) ltac:(cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_1; lia)) as PFFS.
  eapply evtA_cut.
  { eapply aal2_seg; [ exact ST2 | exact MI2 | lia | lia | lia | exact SQ32 | exact FR2 | exact FFC | exact FFS | exact FFsh | lia | exact FFal | exact PSTK | exact PFF | exact PFFS ]. }
  cbv beta. intros ms3 (jq0 & jq1 & j1 & m3 & -> & MU3 & WM3 & MI3 & ST3 & FR3 & FFH3 & FSH3 & LJQ0 & LJQ1 & LJ1).
  pose proof (aystatics_munch _ _ _ YS2 MU3 WM3 ltac:(constructor; [cbn [fst snd]; lia| constructor; [cbn [fst snd]; lia| constructor; [cbn [fst snd]; lia| constructor]]])) as YS3.
  (* [comment removed for export] *)
  apply (rw_cells_split_CB asegs _ _ [_; _; _] 96 _ [_] [8; 32; 56]%nat) in FFH3; [| reflexivity]. cbn [app mk_CB_cells] in FFH3.
  pose proof FFH3 as FFX. apply (proj1 (ycells_app asegs _ _ [_; _; _; _] [_; _; _])) in FFX. destruct FFX as [FFA FFB].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FFB.
  apply (proj1 (ycells_app asegs _ _ [_] [_; _])) in FFB. destruct FFB as [YAFJ FFT].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FFT. clear FFH3.
  (* [comment removed for export] *)
  eapply rw_cells_reshape with (cs' := [CB 4 [Z_to_bv 8 241; Z_to_bv 8 241; Z_to_bv 8 241; Z_to_bv 8 241]; CB 4 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0];
                                        CB 8 [Z_to_bv 8 243; Z_to_bv 8 243; Z_to_bv 8 243; Z_to_bv 8 243; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]) in FSH3;
    [| cbn; repeat split; reflexivity| reflexivity| reflexivity].
  pose proof FSH3 as FSX. apply (proj1 (ycells_app asegs _ _ [_] [_; _])) in FSX. destruct FSX as [_ FSX].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FSX.
  apply (proj1 (ycells_app asegs _ _ [_] [_])) in FSX. destruct FSX as [FSZ _].
  apply u8arr_of_rw_cells in FSZ.
  assert (OSA3 : oshadow m3 (ff + 32) 32).
  { split; [clear -CEILB E8F; Z.div_mod_to_equations; lia|]. split; [lia|]. unfold A_SB.
    replace (2147450880 + (ff + 32) / 8) with (ff / 8 + 2147450880 + 4) by (clear -CEILB E8F; Z.div_mod_to_equations; lia).
    change (blk_shadow 32) with [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]. exact FSZ. }
  clear FSZ.
  pose proof YS3 as (YCB3 & YBAE3 & YNOOP3 & STA3).
  (* [comment removed for export] *)
  eapply evtA_cut.
  { eapply (ayset_default_proof _ (ff + 32) lo);
      [ exact STA3 | exact YAFJ | exact OSA3 | unfold amem; clear -CEILB FFsh; lia | aceil; lia | exact MI3
      | rewrite unsigned_lit by lia; exact ST3 | aceil; lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
      | reflexivity
      | rewrite unsigned_lit by lia; eapply pol_sub; [exact PSTK| lia| lia]
      | unfold AY_IMG_LO, AY_IMG_HI; exact PIMG
      | split; [eapply pol_sub; [exact PFF| lia| lia]| unfold oshw_lo, oshw_hi, A_SB, amem; eapply pol_sub; [exact PFFS| clear -CEILB E8F; Z.div_mod_to_equations; lia| clear -CEILB E8F; Z.div_mod_to_equations; lia]] ]. }
  cbv beta. intros ms4 (t0b & t1b & t2b & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m4 & -> & MU4 & WM4 & MI4 & ST4 & YAF4 & OSA4 & STA4).
  rewrite unsigned_lit in MU4, ST4 by lia. unfold AAL_RET2. ret_pc_lit.
  eapply (rw_cells_transport asegs) in FR3; [| exact MU4| exact WM4| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
  unfold alloc_cells in YAF4. cbn [yc_malloc_w yc_realloc_w yc_free_w ayc] in YAF4. unfold wz in YAF4.
  pose proof OSA4 as (_ & _ & ASH4). unfold A_SB in ASH4.
  (* [comment removed for export] *)
  eapply evtA_cut.
  { eapply aal3_seg; [ exact ST4 | exact MI4 | lia | lia | lia | exact FR3 | exact YAF4 | exact ASH4 | reflexivity | exact FFsh | lia | exact FFal | exact PSTK | exact PFF | exact PFFS ]. }
  cbv beta. intros ms5 (k0 & m5 & -> & MU5 & WM5 & MI5 & ST5 & FR5 & LK0).
  apply evtA_done. intros mo5 Hag5 HLI5 Hh5. destruct (BACK mo5 Hag5 HLI5) as [AHKb R5].
  pose proof (munch_app _ _ _ _ _ MU3 (munch_app _ _ _ _ _ MU4 MU5)) as MU35. cbn [app] in MU35.
  pose proof (wmono_trans _ _ _ _ WM3 (wmono_trans _ _ _ _ WM4 WM5)) as WM35.
  assert (AHK5 : y_AHK Y sa2 REST ((1, ff) :: LF) m5 mo5).
  { eapply FRAMEY; [exact AHKb| exact MU35| exact WM35|].
    constructor; [left; cbn [fst snd]; aceil; lia|].
    constructor; [right; right; left; exists (1, ff); split; [left; reflexivity| cbn [fst snd]; rewrite ff_bytes_1; lia]|].
    constructor; [right; right; right; left; exists (1, ff); split; [left; reflexivity| cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_1; lia]|].
    constructor; [left; cbn [fst snd]; aceil; lia|].
    constructor; [right; right; left; exists (1, ff); split; [left; reflexivity| cbn [fst snd]; rewrite ff_bytes_1; lia]|].
    constructor; [left; cbn [fst snd]; aceil; lia| constructor]. }
  clear AHKb.
  pose proof (aystatics_munch _ _ _ YS2 MU35 WM35 ltac:(do 6 (constructor; [cbn [fst snd]; lia|]); constructor)) as YS5.
  assert (PRES5w : ay_pres REST LF (bv_unsigned sp) [] m m5).
  { eapply ay_pres_trans; [exact PRES2w|]. eapply ay_pres_of_munch; [exact MU35| exact WM35|]. intros a Ha Hc _.
    apply outside_cons; [| apply outside_cons; [| apply outside_cons; [| apply outside_cons; [| apply outside_cons; [| apply outside_cons; [| exact I]]]]]].
    - eapply (ay_client_outside_stack Y BLKY LAYY _ _ _ _ _ REST (bv_unsigned sp)); [exact AHK2| intros b0 Hb0; exact Hb0| aceil; lia| lia| exact (ay_client_addr_mono _ _ ((1, ff) :: LF) _ _ (fun f Hf => or_intror Hf) Hc)].
    - eapply (ay_client_outside_fframe Y BLKY BSHY LAYY _ _ _ _ _ REST LF (bv_unsigned sp) (1, ff)); [exact AHK2| left; reflexivity| exact FRESH| intros b0 Hb0; exact Hb0| left; cbn [fst snd]; rewrite ff_bytes_1; lia| lia| aceil; lia| exact Hc].
    - eapply (ay_client_outside_fframe Y BLKY BSHY LAYY _ _ _ _ _ REST LF (bv_unsigned sp) (1, ff)); [exact AHK2| left; reflexivity| exact FRESH| intros b0 Hb0; exact Hb0| right; cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_1; lia| lia| aceil; lia| exact Hc].
    - eapply (ay_client_outside_stack Y BLKY LAYY _ _ _ _ _ REST (bv_unsigned sp)); [exact AHK2| intros b0 Hb0; exact Hb0| aceil; lia| lia| exact (ay_client_addr_mono _ _ ((1, ff) :: LF) _ _ (fun f Hf => or_intror Hf) Hc)].
    - eapply (ay_client_outside_fframe Y BLKY BSHY LAYY _ _ _ _ _ REST LF (bv_unsigned sp) (1, ff)); [exact AHK2| left; reflexivity| exact FRESH| intros b0 Hb0; exact Hb0| left; cbn [fst snd]; rewrite ff_bytes_1; lia| lia| aceil; lia| exact Hc].
    - eapply (ay_client_outside_stack Y BLKY LAYY _ _ _ _ _ REST (bv_unsigned sp)); [exact AHK2| intros b0 Hb0; exact Hb0| aceil; lia| lia| exact (ay_client_addr_mono _ _ ((1, ff) :: LF) _ _ (fun f Hf => or_intror Hf) Hc)]. }
  assert (AGREE5 : forall a, bv_unsigned sp <= a < 2^47 -> m5 (wa a) = m (wa a)).
  { intros a Ha. rewrite <- (AGREE2 a Ha). destruct (PRES5w a ltac:(lia) ltac:(left; lia) ltac:(intros F0; exact F0)) as [E5 _].
    destruct (PRES2w a ltac:(lia) ltac:(left; lia) ltac:(intros F0; exact F0)) as [E2 _]. rewrite E5, E2. reflexivity. }
  (* [comment removed for export] *)
  eapply (rw_cells_transport asegs) in SV2; [| exact MU35| exact WM35| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
  eapply (stk_transport_disjoint asegs) in GAP2; [| exact MU35| exact WM35| cbv [disjoint_from fst snd]; lia].
  eapply (rw_cells_transport asegs) in CFC2; [| exact MU35| exact WM35| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; clear -CEILB FL_ff FLcx ECFG SQR LO CEIL FFsh FFce FL_1 CFGH E8F; lia].
  assert (OSC5 : oshadow m5 CFGP 8).
  { eapply oshadow_munch; [exact OSC2| exact MU35| exact WM35|]. unfold oshw_lo, A_SB. rewrite ECF8. change ((8 + 7) / 8) with 1.
    cbv [disjoint_from fst snd]. clear -CEILB FL_ff SQR LO CEIL FFsh FFce FL_1 FL_2 E8F E8L. lia. }
  assert (OSX5 : oshadow m5 CX 8).
  { eapply oshadow_munch; [exact OSX2| exact MU35| exact WM35|]. unfold oshw_lo, A_SB. rewrite ECX8. change ((8 + 7) / 8) with 1.
    cbv [disjoint_from fst snd]. clear -CEILB FL_ff SQR LO CEIL FFsh FFce FL_1 FL_2 E8F E8L. lia. }
  eapply (rw_cells_transport asegs) in FFA; [| exact MU4| exact WM4| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
  eapply (rw_cells_transport asegs) in FFA; [| exact MU5| exact WM5| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
  eapply (rw_cells_transport asegs) in FFT; [| exact MU4| exact WM4| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
  eapply (rw_cells_transport asegs) in FFT; [| exact MU5| exact WM5| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
  eapply (rw_cells_transport asegs) in FSH3; [| exact MU4| exact WM4| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
  eapply (rw_cells_transport asegs) in FSH3; [| exact MU5| exact WM5| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
  eapply (rw_cells_transport asegs) in YAF4; [| exact MU5| exact WM5| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
  eapply (u8arr_transport asegs) in ASH4; [| exact MU5| exact WM5| cbv [disjoint_from fst snd]; rewrite (blk_shadow_length 32) by lia; lia].
  (* [comment removed for export] *)
  pose proof (proj1 (proj1 (ycells_app asegs _ _ [_] [_; _; _]) FFA)) as FF8. clear FFA.
  pose proof (sub_chunk m5 _ [_] [_] [] ltac:(rewrite app_nil_r; exact FFT)) as FFP. clear FFT.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FFP. replace (ff + 32 + 32 + 56) with (ff + 120) in FFP by lia. subst PF.
  eapply rw_cells_reshape with (cs' := [CB 16 [Z_to_bv 8 241; Z_to_bv 8 241; Z_to_bv 8 241; Z_to_bv 8 241; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0;
                                               Z_to_bv 8 243; Z_to_bv 8 243; Z_to_bv 8 243; Z_to_bv 8 243; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]) in FSH3;
    [| cbn; split; [reflexivity| exact I]| reflexivity| reflexivity].
  rename FSH3 into SHC.
  pose proof (sub_chunk m5 _ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] [] ltac:(rewrite app_nil_r; exact SV2)) as SV16.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SV16. replace (bv_unsigned sp + -104 + 88) with (bv_unsigned sp - 16) in SV16 by lia.
  clear LINK BACK PSTK PIMG PFF PFFS MU3 WM3 MI3 ST3 MU4 WM4 MI4 ST4 MU5 WM5 MU35 WM35 YS2 YS3 YCB3 YBAE3 YNOOP3 STA3 STA4 OSA3 OSA4 OSC2 OSX2 AGREE2 PRES2w ST2 MI2 FR3.
  pose proof (YNEW L 0%nat 0%nat 0%nat 0%nat 0%nat L0) as YN0. pose proof (NH0 (yalloc_hand 0%nat 0%nat 0%nat 0%nat 0%nat) L) as NHX.
  (* [comment removed for export] *)
  unfold AAL_RET3.
  eapply (WMAL 104 REST ((1, ff) :: LF) lo (y_phi_new Y L + RR - y_acharge Y 104));
    [ exact K0
    | apply AYST_split; split; [exact AHK5| exact YS5]
    | reflexivity
    | lia
    | lia
    | clear -CEILB YN0 NHX RR0 NA48 NA32 NA128 YF0 NBZ; lia
    | unfold AY_NBIG_REST in NBIG; lia
    | unfold ayframe_pre, AY_WRAP_STACK, AMALLOC_STACK; aceil; rewrite unsigned_lit by lia;
      split; [exact ST5|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [clear -CEILB SQ32; Z.div_mod_to_equations; lia|];
      split; [exact MI5|]; split; [exact TP| exact FRM2]
    | rewrite unsigned_lit by lia; eapply USTEP; [rewrite unsigned_lit by lia; exact URA_mal| lia| exact SV16| eapply UFRAME; [exact AGREE5| exact UA]]
    | ].
  cbv beta. intros t0c t1c t2c a0c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c F6 fc6 m6 mo6 sa6 H (MI6 & ST6 & FRM6 & _ & PRES6) SO6 R6 CRED6 RES.
  rewrite unsigned_lit in ST6, PRES6 by lia.
  replace (ret_pc (Z_to_bv 64 0x82640)) with (Z_to_bv 64 0x82640) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  (* [comment removed for export] *)
  pose proof (aypres_frame _ _ _ _ _ _ _ PRES6 FR5 ltac:(lia)) as FR6. clear FR5.
  pose proof (aypres_frame _ _ _ _ _ _ _ PRES6 SV2 ltac:(lia)) as SV6. clear SV2 SV16.
  assert (GAP6 : stk asegs m6 (SQ + 56) (bv_unsigned sp + -104)).
  { eapply stk_agree; [eapply ay_pres_agree; exact PRES6| exact GAP2| intros a Ha; split; [left; lia| intros F0; exact F0]]. }
  clear GAP2.
  pose proof (aypres_fframe _ _ _ _ _ _ _ (1, ff) PRES6 FF8 (or_introl eq_refl) ltac:(left; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ff_bytes_1; lia)) as FF8_6. clear FF8.
  pose proof (aypres_fframe _ _ _ _ _ _ _ (1, ff) PRES6 FFP (or_introl eq_refl) ltac:(left; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ff_bytes_1; lia)) as FFP6. clear FFP.
  pose proof (aypres_fframe _ _ _ _ _ _ _ (1, ff) PRES6 YAF4 (or_introl eq_refl) ltac:(left; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ff_bytes_1; lia)) as YAF6. clear YAF4.
  pose proof (aypres_fframe _ _ _ _ _ _ _ (1, ff) PRES6 SHC (or_introl eq_refl) ltac:(right; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; unfold oshw_lo, A_SB; rewrite shl8_1; lia)) as SHC6. clear SHC.
  assert (ASH6 : u8arr asegs m6 (2147450880 + (ff + 32) / 8) (blk_shadow 32)).
  { eapply u8arr_agree; [eapply ay_pres_agree; exact PRES6| exact ASH4|]. intros a Ha. rewrite (blk_shadow_length 32) in Ha by lia. split; [| intros F0; exact F0].
    right; right; left. exists (1, ff). split; [left; reflexivity|]. right. cbn [fst snd]. unfold oshw_lo, A_SB. rewrite shl8_1. clear -CEILB Ha E8F. Z.div_mod_to_equations. lia. }
  clear ASH4.
  pose proof (aypres_fframe _ _ _ _ _ _ _ (1, AL) PRES6 CFC2 (or_intror FLin) ltac:(left; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ff_bytes_1; lia)) as CFC6. clear CFC2.
  assert (OSC6 : oshadow m6 CFGP 8).
  { eapply oshadow_agree; [eapply ay_pres_agree; exact PRES6| exact OSC5|]. intros a Ha. split; [| intros F0; exact F0].
    right; right; left. exists (1, AL). split; [right; exact FLin|]. right. cbn [fst snd]. unfold oshw_lo, oshw_hi, A_SB, amem in Ha |- *. rewrite shl8_1. clear -CEILB Ha ECF8. Z.div_mod_to_equations. lia. }
  assert (OSX6 : oshadow m6 CX 8).
  { eapply oshadow_agree; [eapply ay_pres_agree; exact PRES6| exact OSX5|]. intros a Ha. split; [| intros F0; exact F0].
    right; right; left. exists (1, AL). split; [right; exact FLin|]. right. cbn [fst snd]. unfold oshw_lo, oshw_hi, A_SB, amem in Ha |- *. rewrite shl8_1. clear -CEILB Ha ECX8. Z.div_mod_to_equations. lia. }
  clear OSC5 OSX5.
  assert (PRES6w : ay_pres REST LF (bv_unsigned sp) [] m m6).
  { eapply ay_pres_trans; [exact PRES5w|]. eapply (ay_pres_weaken Y); [exact PRES6| lia| intros b0 Hb0; exact Hb0| intros f Hf; right; exact Hf| auto]. }
  clear PRES5w AGREE5 ST5 MI5.
  (* [comment removed for export] *)
  destruct RES as (EA0 & HR & HAM & HSH & OSH & (hj & HC) & AY6). subst a0c. unfold wz. specialize (HSH ltac:(lia)).
  unfold ablock_range, ACONSTS in HR. cbn [c_img_hi] in HR. aceil. rewrite oshw_hi_0 in HSH.
  apply AYST_split in AY6. destruct AY6 as [AHK6 YS6].
  change (Z.to_nat 104) with 104%nat in HC.
  destruct (BLKY _ _ _ _ _ AHK6) as (RNG6 & SEP6 & ND6).
  destruct (LAYY _ _ _ _ _ AHK6) as (_ & LAYFB6 & _).
  pose proof (proj1 (LAYFB6 (1, ff) (mkABlock H 104) (or_introl eq_refl) (or_introl eq_refl))) as SEPHF. cbn [fst snd ab_addr ab_size] in SEPHF. rewrite ff_bytes_1 in SEPHF.
  pose proof (proj1 (LAYFB6 (1, AL) (mkABlock H 104) (or_intror FLin) (or_introl eq_refl))) as SEPHL. cbn [fst snd ab_addr ab_size] in SEPHL. rewrite ff_bytes_1 in SEPHL.
  clear LAYFB6.
  destruct (ICPB _ _ _ _ _ (mkABlock H 104) (H + 72) 32 AHK6 (or_introl eq_refl) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia)) as (wsD & SWD & RCD & _ & _).
  pose proof (ICPR _ _ _ _ _ (mkABlock H 104) (H + 72) 32 AHK6 (or_introl eq_refl) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia)) as PGD.
  pose proof (ICPG _ _ _ _ _ AHK6) as IG6. unfold A_SB in SWD, RCD, PGD, IG6.
  pose proof (shw_geom 2147450880 (H + 72) 32 ltac:(lia) ltac:(lia) ltac:(lia)) as GEOD. cbv zeta in GEOD.
  assert (WDH : shw_hi 2147450880 (H + 72) 32 <= 17594333495296) by (clear -CEILB GEOD HR; lia).
  pose proof OSH as (H8 & _ & HS6). unfold A_SB in HS6.
  pose proof OSC6 as (_ & _ & CSH6). unfold A_SB in CSH6.
  pose proof (rw_cells_bytes_at _ _ _ _ SHC6) as AW6. cbn [cells_bytes cbytes app] in AW6. apply (bytes_at_firstn _ _ _ _ 8) in AW6. cbn [firstn] in AW6.
  (* [comment removed for export] *)
  arz_seg KIPY AHK6.
  pose proof (aypol_stack Y _ ((1, ff) :: LF) _ _ LINK lo (SQ + 56) ltac:(aceil; lia) ltac:(lia)) as PSTK.
  pose proof (aypol_img Y _ ((1, ff) :: LF) _ _ LINK) as PIMG. unfold AY_IMG_LO, AY_IMG_HI in PIMG.
  pose proof (aypol_fframe Y _ ((1, ff) :: LF) _ _ LINK (1, ff) ff (ff + 128) (or_introl eq_refl) ltac:(cbn; lia) ltac:(cbn; rewrite ff_bytes_1; lia) ltac:(lia) ltac:(cbn; rewrite ff_bytes_1; lia)) as PFF.
  pose proof (aypol_ffshadow Y _ ((1, ff) :: LF) _ _ LINK (1, ff) (2147450880 + ff / 8) (2147450880 + ff / 8 + 16) (or_introl eq_refl)
                ltac:(cbn [snd]; unfold oshw_lo, A_SB; lia) ltac:(cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_1; lia) ltac:(lia) ltac:(cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_1; lia)) as PFFS.
  pose proof (aypol_opol_block Y _ ((1, ff) :: LF) _ _ LINK (mkABlock H 104) (or_introl eq_refl) ltac:(cbn; (clear -HR; lia)) ltac:(cbn; unfold oshw_lo, A_SB; (clear -HR; lia)) ltac:(cbn; unfold oshw_hi, A_SB, amem; (clear -CEILB HR; lia)) ltac:(cbn; (clear -CEILB HR; lia))) as [PH PHS].
  cbn [ab_addr ab_size] in PH, PHS. unfold oshw_lo, oshw_hi, A_SB, amem in PHS. change ((104 + 7) / 8) with 13 in PHS.
  pose proof (aypol_pages (m_vm_lazy mo6) _ _ _ PGD ltac:(unfold shw_lo, al8 in *; clear -CEILB GEOD HR; Z.div_mod_to_equations; lia) ltac:(lia)) as PWD.
  pose proof (aypol_fframe Y _ ((1, ff) :: LF) _ _ LINK (1, AL) CFGP (CFGP + 8) (or_intror FLin) ltac:(cbn; (clear -ECFG FLcx; lia)) ltac:(cbn; rewrite ff_bytes_1; (clear -ECFG FLcx; lia)) ltac:((clear -CXSH ECFG; lia)) ltac:(cbn; rewrite ff_bytes_1; (clear -CEILB ECFG CFGH FLcx; lia))) as PC.
  pose proof (aypol_ffshadow Y _ ((1, ff) :: LF) _ _ LINK (1, AL) (2147450880 + CFGP / 8) (2147450880 + CFGP / 8 + 1) (or_intror FLin)
                ltac:(cbn [snd]; unfold oshw_lo, A_SB; (clear -ECFG FLcx; lia)) ltac:(cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_1; (clear -ECFG FLcx; lia)) ltac:((clear -CXSH ECFG; lia)) ltac:(cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_1; (clear -CEILB ECFG CFGH FLcx; lia))) as PCS.
  eapply evtA_cut.
  { eapply aal4_seg;
      [ exact ST6 | exact MI6 | (clear -CEIL; lia) | (clear -LO SQR; lia) | (clear -SPLT SQ32 SQR; lia) | exact FR6 | exact YAF6 | exact AW6 | exact FFsh | (clear -FFce; lia) | exact FFal
      | exact HC | exact HS6 | reflexivity | (clear -HSH; lia) | (clear -HR; lia) | (clear -HR; lia) | exact SEPHF
      | exact SWD | exact RCD | exact WDH | exact IG6
      | exact CFC6 | exact CSH6 | reflexivity | unfold amem; clear -CEILB FL_1 ECFG FLcx; (clear -ECFG FLcx FL_1; lia) | (clear -CFGH; lia) | exact CF8 | clear -CEILB SEPHL FLcx ECFG; (clear -ECFG FLcx SEPHL; lia) | unfold AY_CALLBACKS; (clear; lia) | (clear -CEILB CXSH ECFG CFGH; lia)
      | exact PSTK | eapply pol_sub; [exact PIMG| (clear; lia)| (clear; lia)] | exact PFF | exact PFFS | exact PH | exact PHS | exact PWD | exact PC | exact PCS ]. }
  cbv beta. intros ms7 (t0d & t1d & t2d & a3d & a4d & a5d & a6d & a7d & t3d & t4d & t5d & t6d & k32 & hj' & m7 & -> & MU7 & WM7 & MI7 & ST7 & FR7 & HC7 & HA7 & LK32 & LHJ' & HS7 & AW7 & IG7).
  apply evtA_done. intros mo7 Hag7 HLI7 Hh7. destruct (BACK mo7 Hag7 HLI7) as [AHKb R7].
  assert (AHK7 : y_AHK Y sa6 (mkABlock H 104 :: REST) ((1, ff) :: LF) m7 mo7).
  { eapply FRAMEY; [exact AHKb| exact MU7| exact WM7|].
    constructor; [left; cbn [fst snd]; aceil; lia|].
    constructor; [right; left; exists (mkABlock H 104); split; [left; reflexivity| cbn; lia]| constructor]. }
  clear AHKb.
  pose proof (aystatics_munch _ _ _ YS6 MU7 WM7 ltac:(constructor; [cbn [fst snd]; lia| constructor; [cbn [fst snd]; lia| constructor]])) as YS7.
  assert (PRES7w : ay_pres REST LF (bv_unsigned sp) [] m m7).
  { eapply ay_pres_trans; [exact PRES6w|]. eapply ay_pres_of_munch; [exact MU7| exact WM7|]. intros a Ha Hc _.
    apply outside_cons; [| apply outside_cons; [| exact I]].
    - eapply (ay_client_outside_stack Y BLKY LAYY _ _ _ _ _ REST (bv_unsigned sp)); [exact AHK6| intros b0 Hb0; right; exact Hb0| aceil; lia| lia| exact (ay_client_addr_mono _ _ ((1, ff) :: LF) _ _ (fun f Hf => or_intror Hf) Hc)].
    - eapply (ay_client_outside_block Y BLKY BSHY LAYY _ _ _ _ _ REST (bv_unsigned sp) (mkABlock H 104));
        [exact AHK6| left; reflexivity| | cbn; lia| cbn; lia| lia| aceil; lia| exact (ay_client_addr_mono _ _ ((1, ff) :: LF) _ _ (fun f Hf => or_intror Hf) Hc)].
      intros b0 Hb0. split; [right; exact Hb0|]. cbn. intros E. exact (nd_head_ne _ _ _ ND6 Hb0 (eq_sym E)). }
  assert (AGREE7 : forall a, bv_unsigned sp <= a < 2^47 -> m7 (wa a) = m (wa a)).
  { intros a Ha. destruct (PRES7w a ltac:(lia) ltac:(left; lia) ltac:(intros F0; exact F0)) as [E _]. exact E. }
  eapply (rw_cells_transport asegs) in SV6; [| exact MU7| exact WM7| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
  eapply (stk_transport_disjoint asegs) in GAP6; [| exact MU7| exact WM7| cbv [disjoint_from fst snd]; lia].
  eapply (rw_cells_transport asegs) in FF8_6; [| exact MU7| exact WM7| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; clear -CEILB FFce CEIL LO SQR SEPHF; lia].
  eapply (rw_cells_transport asegs) in FFP6; [| exact MU7| exact WM7| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; clear -CEILB FFce CEIL LO SQR SEPHF; lia].
  eapply (rw_cells_transport asegs) in SHC6; [| exact MU7| exact WM7| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
  eapply (rw_cells_transport asegs) in YAF6; [| exact MU7| exact WM7| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; clear -CEILB FFce CEIL LO SQR SEPHF; lia].
  eapply (u8arr_transport asegs) in ASH6; [| exact MU7| exact WM7| cbv [disjoint_from fst snd]; rewrite (blk_shadow_length 32) by lia; clear -CEILB SQR LO CEIL HSH E8F FFce; Z.div_mod_to_equations; lia].
  eapply (rw_cells_transport asegs) in CFC6; [| exact MU7| exact WM7| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; clear -CEILB SEPHL FLcx ECFG CFGH SQR LO CEIL; lia].
  assert (OSC7 : oshadow m7 CFGP 8).
  { eapply oshadow_munch; [exact OSC6| exact MU7| exact WM7|]. unfold oshw_lo, A_SB. rewrite ECF8. change ((8 + 7) / 8) with 1.
    cbv [disjoint_from fst snd]. clear -CEILB SQR LO CEIL HSH FL_1 FL_2 E8L. lia. }
  assert (OSX7 : oshadow m7 CX 8).
  { eapply oshadow_munch; [exact OSX6| exact MU7| exact WM7|]. unfold oshw_lo, A_SB. rewrite ECX8. change ((8 + 7) / 8) with 1.
    cbv [disjoint_from fst snd]. clear -CEILB SQR LO CEIL HSH FL_1 FL_2 E8L. lia. }
  pose proof (sub_chunk m7 _ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] [] ltac:(rewrite app_nil_r; exact SV6)) as SV16.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SV16. replace (bv_unsigned sp + -104 + 88) with (bv_unsigned sp - 16) in SV16 by lia.
  clear LINK BACK PSTK PIMG PFF PFFS PH PHS PWD PC PCS OSC6 OSX6 YS6 PRES6 PRES6w ST6 MI6 FR6 SWD RCD PGD IG6 WDH AW6 HS6 CSH6 HC.
  rewrite (ysx32_small 1) by lia. unfold AAL_RET4.
  (* [comment removed for export] *)
  eapply (LALLOC ((1, ff) :: LF) (mkABlock H 104 :: REST) (H + 72) 1 1 lo (y_phi_new Y L + RR - y_acharge Y 104 - (y_acharge Y 48 + y_acharge Y 32 + y_phi_buf Y ybuf_zero + y_free_cost Y)));
    [ exact K0
    | apply AYST_split; split; [exact AHK7| exact YS7]
    | unfold alloc_cells; cbn [yc_malloc_w yc_realloc_w yc_free_w ayc]; unfold wz; exact HA7
    | exists (mkABlock H 104); split; [left; reflexivity|]; cbn [ab_addr ab_size]; split; [(clear; lia)|]; split; [change (8 * (104 / 8)) with 104; (clear; lia)|];
      split; [clear -CEILB HR; Z.div_mod_to_equations; lia|]; split; [split; [exact H8|]; split; [(clear; lia)|]; unfold A_SB; exact HS7| rewrite oshw_hi_0; (clear -HSH; lia)]
    | (clear; lia) | (clear; lia)
    | unfold ayframe_pre, AY_LEX_ALLOC_STACK, AY_BUF_ALLOC_STACK, AMALLOC_STACK; aceil; rewrite unsigned_lit by (clear -CEILB CEIL LO SPLT SQR; lia);
      split; [exact ST7|]; split; [(clear -CEIL; lia)|]; split; [(clear -LO SQR; lia)|]; split; [(clear -SPLT SQR; lia)|]; split; [clear -CEILB SQ32; Z.div_mod_to_equations; lia|];
      split; [exact MI7|]; split; [exact TP| exact FRM6]
    | reflexivity | reflexivity | reflexivity
    | unfold SIZEOF_LEXER, SIZEOF_BUF; clear -CEILB CRED6; (clear -CRED6; lia)
    | clear -CEILB YN0 NHX RR0 NA48 NA32 NA128 YF0 NBZ; (clear -RR0 NBZ YF0 NA32 NA128 YN0 NHX; lia)
    | change (nbig (mkABlock H 104 :: REST)) with (nbig REST); unfold AY_NBIG_REST in NBIG |- *; (clear -NBIG; lia)
    | rewrite unsigned_lit by (clear -CEILB CEIL LO SPLT SQR; lia); eapply USTEP; [rewrite unsigned_lit by (clear; lia); exact URA_lxa| (clear -SPLT SQR; lia)| exact SV16| eapply UFRAME; [exact AGREE7| exact UA]]
    | ].
  cbv beta. intros t0e t1e t2e a0e a1e a2e a3e a4e a5e a6e a7e t3e t4e t5e t6e F8 fc8 m8 mo8 sa8 Lx mbl lx (SO8 & R8 & CRED8 & (MI8 & ST8 & FRM8 & _ & PRES8) & HA8 & RESL).
  rewrite unsigned_lit in ST8, PRES8 by lia.
  replace (ret_pc (Z_to_bv 64 0x826d4)) with (Z_to_bv 64 0x826d4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  unfold alloc_cells in HA8. cbn [yc_malloc_w yc_realloc_w yc_free_w ayc] in HA8. unfold wz in HA8.
  (* [comment removed for export] *)
  pose proof (aypres_frame _ _ _ _ _ _ _ PRES8 FR7 ltac:(lia)) as FR8. clear FR7.
  pose proof (aypres_frame _ _ _ _ _ _ _ PRES8 SV6 ltac:(lia)) as SV8. clear SV6 SV16.
  assert (GAP8 : stk asegs m8 (SQ + 56) (bv_unsigned sp + -104)).
  { eapply stk_agree; [eapply ay_pres_agree; exact PRES8| exact GAP6| intros a Ha; split; [left; lia| intros F0; exact F0]]. }
  clear GAP6.
  pose proof (aypres_fframe _ _ _ _ _ _ _ (1, ff) PRES8 FF8_6 (or_introl eq_refl) ltac:(left; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ff_bytes_1; lia)) as FF8_8. clear FF8_6.
  pose proof (aypres_fframe _ _ _ _ _ _ _ (1, ff) PRES8 FFP6 (or_introl eq_refl) ltac:(left; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ff_bytes_1; lia)) as FFP8. clear FFP6.
  pose proof (aypres_fframe _ _ _ _ _ _ _ (1, ff) PRES8 YAF6 (or_introl eq_refl) ltac:(left; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ff_bytes_1; lia)) as YAF8. clear YAF6.
  pose proof (aypres_fframe _ _ _ _ _ _ _ (1, ff) PRES8 SHC6 (or_introl eq_refl) ltac:(right; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; unfold oshw_lo, A_SB; rewrite shl8_1; lia)) as SHC8. clear SHC6.
  assert (ASH8 : u8arr asegs m8 (2147450880 + (ff + 32) / 8) (blk_shadow 32)).
  { eapply u8arr_agree; [eapply ay_pres_agree; exact PRES8| exact ASH6|]. intros a Ha. rewrite (blk_shadow_length 32) in Ha by lia. split; [| intros F0; exact F0].
    right; right; left. exists (1, ff). split; [left; reflexivity|]. right. cbn [fst snd]. unfold oshw_lo, A_SB. rewrite shl8_1. clear -CEILB Ha E8F. Z.div_mod_to_equations. lia. }
  clear ASH6.
  pose proof (aypres_fframe _ _ _ _ _ _ _ (1, AL) PRES8 CFC6 (or_intror FLin) ltac:(left; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ff_bytes_1; lia)) as CFC8. clear CFC6.
  assert (OSC8 : oshadow m8 CFGP 8).
  { eapply oshadow_agree; [eapply ay_pres_agree; exact PRES8| exact OSC7|]. intros a Ha. split; [| intros F0; exact F0].
    right; right; left. exists (1, AL). split; [right; exact FLin|]. right. cbn [fst snd]. unfold oshw_lo, oshw_hi, A_SB, amem in Ha |- *. rewrite shl8_1. clear -CEILB Ha ECF8. Z.div_mod_to_equations. lia. }
  assert (OSX8 : oshadow m8 CX 8).
  { eapply oshadow_agree; [eapply ay_pres_agree; exact PRES8| exact OSX7|]. intros a Ha. split; [| intros F0; exact F0].
    right; right; left. exists (1, AL). split; [right; exact FLin|]. right. cbn [fst snd]. unfold oshw_lo, oshw_hi, A_SB, amem in Ha |- *. rewrite shl8_1. clear -CEILB Ha ECX8. Z.div_mod_to_equations. lia. }
  clear OSC7 OSX7.
  pose proof (aypres_block _ _ _ _ _ _ _ PRES8 HC7 ltac:(exists (mkABlock H 104); split; [left; reflexivity| cbn; lia])) as HC8. clear HC7.
  assert (PRES8w : ay_pres REST LF (bv_unsigned sp) [] m m8).
  { eapply ay_pres_trans; [exact PRES7w|]. eapply (ay_pres_weaken Y); [exact PRES8| lia| intros b0 Hb0; right; exact Hb0| intros f Hf; right; exact Hf| auto]. }
  assert (AGREE8 : forall a, bv_unsigned sp <= a < 2^47 -> m8 (wa a) = m (wa a)).
  { intros a Ha. destruct (PRES8w a ltac:(lia) ltac:(left; lia) ltac:(intros F0; exact F0)) as [E _]. exact E. }
  clear PRES7w AGREE7 ST7 MI7 PRES8 HS7 IG7 AW7.
  (* [comment removed for export] *)
  destruct RESL as (EA0 & LX0 & LXSH & LBSH & (lblk & HLX) & LXR & MBD0 & OSL & OSLB & AY8). subst a0e. unfold wz.
  rewrite oshw_hi_0 in LXSH, LBSH.
  destruct (ylex_alloc_leaf_some _ _ _ _ HLX) as [bb ELX]. subst lx.
  cbn [lx_buf buf_blocks yb_data ybuf_zero abl map blk_addr blk_size fst snd app] in AY8.
  apply AYST_split in AY8. destruct AY8 as [AHK8 YS8].
  pose proof (proj1 (BSHY _ _ _ _ _ (mkABlock H 104) AHK8 ltac:(right; right; left; reflexivity) ltac:(cbn; lia))) as OSH8. cbn [ab_addr ab_size] in OSH8.
  pose proof OSH8 as (_ & _ & HS8). unfold A_SB in HS8.
  destruct (BLKY _ _ _ _ _ AHK8) as (RNG8 & SEP8 & ND8).
  pose proof (RNG8 _ (or_introl eq_refl)) as RLX. pose proof (RNG8 _ (or_intror (or_introl eq_refl))) as RLB. cbn [ab_addr ab_size] in RLX, RLB.
  unfold ablock_range, ACONSTS in RLX, RLB; aceil. cbn [c_img_hi] in RLX, RLB.
  pose proof (SEP8 _ _ (or_introl eq_refl) (or_intror (or_intror (or_introl eq_refl))) (nd_head_ne _ _ _ ND8 (or_intror (or_introl eq_refl)))) as SLH. cbn [ab_addr ab_size] in SLH.
  pose proof (SEP8 _ _ (or_intror (or_introl eq_refl)) (or_intror (or_intror (or_introl eq_refl))) (nd_head_ne _ _ _ (nd_tail _ _ ND8) (or_introl eq_refl))) as SBH. cbn [ab_addr ab_size] in SBH.
  destruct LXR as ((LXC & _) & ((LBC & _) & _)). rewrite MBD0 in LBC. unfold SIZEOF_LEXER in *. unfold SIZEOF_BUF in *.
  (* [comment removed for export] *)
  arz_seg KIPY AHK8.
  pose proof (aypol_opol_block Y _ ((1, ff) :: LF) _ _ LINK (mkABlock H 104) ltac:(right; right; left; reflexivity) ltac:(cbn; (clear -HR; lia)) ltac:(cbn; unfold oshw_lo, A_SB; (clear -HR; lia)) ltac:(cbn; unfold oshw_hi, A_SB, amem; (clear -CEILB HR; lia)) ltac:(cbn; (clear -CEILB HR; lia))) as [PH PHS].
  cbn [ab_addr ab_size] in PH, PHS. unfold oshw_lo, oshw_hi, A_SB, amem in PHS. change ((104 + 7) / 8) with 13 in PHS.
  eapply evtA_cut.
  { eapply aal5_seg with (L := Lx) (lo := lo);
      [ exact MI8 | (clear -CEILB CEIL LO SQR; lia) | (clear -SPLT SQ32 SQR; lia) | exact HC8 | exact HA8 | exact HS8 | reflexivity | (clear -HSH; lia) | (clear -HR; lia) | (clear -HR; lia) | (clear -CEILB RLX; lia) | exact PH | exact PHS ]. }
  cbv beta. intros ms9 (a1x & a2x & pew & bc & pad & DB & SBw & SZ & U & YFw & m9 & MU9 & WM9 & MI9 & HS9 & HC9 & ->).
  apply evtA_done. intros mo9 Hag9 HLI9 Hh9. destruct (BACK mo9 Hag9 HLI9) as [AHKb R9].
  assert (AHK9 : y_AHK Y sa8 (mkABlock Lx 48 :: mkABlock (mb_addr mbl) 32 :: mkABlock H 104 :: REST) ((1, ff) :: LF) m9 mo9).
  { eapply FRAMEY; [exact AHKb| exact MU9| exact WM9|]. constructor; [right; left; exists (mkABlock H 104); split; [right; right; left; reflexivity| cbn; lia]| constructor]. }
  clear AHKb LINK BACK PH PHS.
  pose proof (aystatics_munch _ _ _ YS8 MU9 WM9 ltac:(constructor; [cbn [fst snd]; lia| constructor])) as YS9.
  assert (PRES9w : ay_pres REST LF (bv_unsigned sp) [] m m9).
  { eapply ay_pres_trans; [exact PRES8w|]. eapply ay_pres_of_munch; [exact MU9| exact WM9|]. intros a Ha Hc _.
    apply outside_cons; [| exact I].
    eapply (ay_client_outside_block Y BLKY BSHY LAYY _ _ _ _ _ REST (bv_unsigned sp) (mkABlock H 104));
      [exact AHK8| right; right; left; reflexivity| | cbn; lia| cbn; lia| lia| aceil; lia| exact (ay_client_addr_mono _ _ ((1, ff) :: LF) _ _ (fun f Hf => or_intror Hf) Hc)].
    intros b0 Hb0. split; [right; right; right; exact Hb0|]. cbn. intros E. exact (nd_head_ne _ _ _ ND6 Hb0 (eq_sym E)). }
  eapply (rw_cells_transport asegs) in SV8; [| exact MU9| exact WM9| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
  eapply (rw_cells_transport asegs) in FR8; [| exact MU9| exact WM9| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
  eapply (stk_transport_disjoint asegs) in GAP8; [| exact MU9| exact WM9| cbv [disjoint_from fst snd]; lia].
  eapply (stk_transport_disjoint asegs) in ST8; [| exact MU9| exact WM9| cbv [disjoint_from fst snd]; lia].
  eapply (rw_cells_transport asegs) in FF8_8; [| exact MU9| exact WM9| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; clear -CEILB SEPHF; lia].
  eapply (rw_cells_transport asegs) in FFP8; [| exact MU9| exact WM9| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; clear -CEILB SEPHF; lia].
  eapply (rw_cells_transport asegs) in SHC8; [| exact MU9| exact WM9| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
  eapply (rw_cells_transport asegs) in YAF8; [| exact MU9| exact WM9| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; clear -CEILB SEPHF; lia].
  eapply (u8arr_transport asegs) in ASH8; [| exact MU9| exact WM9| cbv [disjoint_from fst snd]; rewrite (blk_shadow_length 32) by lia; clear -CEILB HSH E8F FFce; Z.div_mod_to_equations; lia].
  eapply (rw_cells_transport asegs) in CFC8; [| exact MU9| exact WM9| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; clear -CEILB SEPHL FLcx ECFG; lia].
  assert (OSC9 : oshadow m9 CFGP 8).
  { eapply oshadow_munch; [exact OSC8| exact MU9| exact WM9|]. unfold oshw_lo, A_SB. rewrite ECF8. change ((8 + 7) / 8) with 1. cbv [disjoint_from fst snd]. clear -CEILB HSH FL_1 FL_2 E8L. lia. }
  assert (OSX9 : oshadow m9 CX 8).
  { eapply oshadow_munch; [exact OSX8| exact MU9| exact WM9|]. unfold oshw_lo, A_SB. rewrite ECX8. change ((8 + 7) / 8) with 1. cbv [disjoint_from fst snd]. clear -CEILB HSH FL_1 FL_2 E8L. lia. }
  eapply (rw_cells_transport asegs) in LXC; [| exact MU9| exact WM9| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length lexer_cells Z.of_nat Pos.of_succ_nat Pos.succ]; clear -CEILB SLH; lia].
  eapply (rw_cells_transport asegs) in LBC; [| exact MU9| exact WM9| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length buf_cells Z.of_nat Pos.of_succ_nat Pos.succ]; clear -CEILB SBH; lia].
  assert (AGREE9 : forall a, bv_unsigned sp <= a < 2^47 -> m9 (wa a) = m (wa a)).
  { intros a Ha. destruct (PRES9w a ltac:(lia) ltac:(left; lia) ltac:(intros F0; exact F0)) as [E _]. exact E. }
  pose proof (sub_chunk m9 _ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] [] ltac:(rewrite app_nil_r; exact SV8)) as SV16.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SV16. replace (bv_unsigned sp + -104 + 88) with (bv_unsigned sp - 16) in SV16 by lia.
  (* [comment removed for export] *)
  unfold hcells15 in HC9. pose proof HC9 as HX. apply (proj1 (ycells_app asegs _ _ [_; _; _; _; _; _; _; _; _; _; _] [_; _; _; _])) in HX. destruct HX as [HH9 HA9].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HA9. clear HC9 HC8 HA8.
  clear PRES8w AGREE8 MI8 OSC8 OSX8 YS8.
  unfold AAL_RET4, AAL_RET5. cbn [lx_buf] in CRED8.
  (* [comment removed for export] *)
  eapply (BALLOC ((1, ff) :: LF) (mkABlock Lx 48 :: mkABlock (mb_addr mbl) 32 :: mkABlock H 104 :: REST) (H + 72) lo
             (y_phi_new Y L + RR - y_acharge Y 104 - (y_acharge Y 48 + y_acharge Y 32 + y_phi_buf Y ybuf_zero + y_free_cost Y) - y_acharge Y 32));
    [ exact K0
    | apply AYST_split; split; [exact AHK9| exact YS9]
    | unfold alloc_cells; cbn [yc_malloc_w yc_realloc_w yc_free_w ayc]; unfold wz; exact HA9
    | exists (mkABlock H 104); split; [right; right; left; reflexivity|]; cbn [ab_addr ab_size]; split; [(clear; lia)|]; split; [change (8 * (104 / 8)) with 104; (clear; lia)|];
      split; [clear -CEILB HR; Z.div_mod_to_equations; lia|]; split; [split; [exact H8|]; split; [(clear; lia)|]; unfold A_SB; exact HS9| rewrite oshw_hi_0; (clear -HSH; lia)]
    | unfold ayframe_pre, AY_BUF_ALLOC_STACK, AMALLOC_STACK; aceil; rewrite unsigned_lit by (clear -CEILB CEIL LO SPLT SQR; lia);
      split; [exact ST8|]; split; [(clear -CEIL; lia)|]; split; [(clear -LO SQR; lia)|]; split; [(clear -SPLT SQR; lia)|]; split; [clear -CEILB SQ32; Z.div_mod_to_equations; lia|];
      split; [exact MI9|]; split; [exact TP| exact FRM8]
    | reflexivity
    | unfold SIZEOF_BUF; clear -CEILB CRED8; (clear -CRED8; lia)
    | clear -CEILB YN0 NHX RR0 NA48 NA32 NA128 YF0 NBZ; (clear -RR0 NBZ YF0 NA128 YN0 NHX; lia)
    | change (nbig (mkABlock Lx 48 :: mkABlock (mb_addr mbl) 32 :: mkABlock H 104 :: REST)) with (nbig REST); unfold AY_NBIG_REST in NBIG |- *; (clear -NBIG; lia)
    | rewrite unsigned_lit by (clear -CEILB CEIL LO SPLT SQR; lia); eapply USTEP; [rewrite unsigned_lit by (clear; lia); exact URA_ba| (clear -SPLT SQR; lia)| exact SV16| eapply UFRAME; [exact AGREE9| exact UA]]
    | ].
  cbv beta. intros t0f t1f t2f a0f a1f a2f a3f a4f a5f a6f a7f t3f t4f t5f t6f F10 fc10 m10 mo10 sa10 B0 (SO10 & R10 & CRED10 & (MI10 & ST10 & FRM10 & _ & PRES10) & HA10 & RESB).
  destruct RESB as (EA10 & B0P & B0SH & BST & B0S & AY10).
  rewrite unsigned_lit in ST10, PRES10 by (clear -CEILB CEIL LO SPLT SQR; lia).
  replace (ret_pc (Z_to_bv 64 0x82710)) with (Z_to_bv 64 0x82710) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  unfold alloc_cells in HA10. cbn [yc_malloc_w yc_realloc_w yc_free_w ayc] in HA10. unfold wz in HA10.
  (* [comment removed for export] *)
  set (LB8 := mkABlock Lx 48 :: mkABlock (mb_addr mbl) 32 :: mkABlock H 104 :: REST) in *.
  assert (INH : In (mkABlock H 104) LB8) by (right; right; left; reflexivity).
  pose proof (aypres_frame _ _ _ _ _ _ _ PRES10 FR8 ltac:(lia)) as FR10.
  pose proof (aypres_frame _ _ _ _ _ _ _ PRES10 SV8 ltac:(lia)) as SV10.
  assert (GAP10 : stk asegs m10 (SQ + 56) (bv_unsigned sp + -104)).
  { eapply stk_agree; [eapply ay_pres_agree; exact PRES10| exact GAP8| intros a Ha; split; [left; lia| intros F0; exact F0]]. }
  pose proof (aypres_fframe _ _ _ _ _ _ _ (1, ff) PRES10 FF8_8 (or_introl eq_refl) ltac:(left; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ff_bytes_1; lia)) as FF8_10.
  pose proof (aypres_fframe _ _ _ _ _ _ _ (1, ff) PRES10 FFP8 (or_introl eq_refl) ltac:(left; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ff_bytes_1; lia)) as FFP10.
  pose proof (aypres_fframe _ _ _ _ _ _ _ (1, ff) PRES10 YAF8 (or_introl eq_refl) ltac:(left; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ff_bytes_1; lia)) as YAF10.
  pose proof (aypres_fframe _ _ _ _ _ _ _ (1, ff) PRES10 SHC8 (or_introl eq_refl) ltac:(right; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; unfold oshw_lo, A_SB; rewrite shl8_1; lia)) as SHC10.
  pose proof (rw_cells_bytes_at _ _ _ _ SHC10) as AW10. cbn [cells_bytes cbytes app] in AW10. apply (bytes_at_firstn _ _ _ _ 8) in AW10. cbn [firstn] in AW10.
  assert (ASH10 : u8arr asegs m10 (2147450880 + (ff + 32) / 8) (blk_shadow 32)).
  { eapply u8arr_agree; [eapply ay_pres_agree; exact PRES10| exact ASH8|]. intros a Ha. rewrite (blk_shadow_length 32) in Ha by lia. split; [| intros F0; exact F0].
    right; right; left. exists (1, ff). split; [left; reflexivity|]. right. cbn [fst snd]. unfold oshw_lo, A_SB. rewrite shl8_1. clear -CEILB Ha E8F. Z.div_mod_to_equations. lia. }
  pose proof (aypres_fframe _ _ _ _ _ _ _ (1, AL) PRES10 CFC8 (or_intror FLin) ltac:(left; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ff_bytes_1; lia)) as CFC10.
  assert (OSC10 : oshadow m10 CFGP 8).
  { eapply oshadow_agree; [eapply ay_pres_agree; exact PRES10| exact OSC9|]. intros a Ha. split; [| intros F0; exact F0].
    right; right; left. exists (1, AL). split; [right; exact FLin|]. right. cbn [fst snd]. unfold oshw_lo, oshw_hi, A_SB, amem in Ha |- *. rewrite shl8_1. clear -CEILB Ha ECF8. Z.div_mod_to_equations. lia. }
  assert (OSX10 : oshadow m10 CX 8).
  { eapply oshadow_agree; [eapply ay_pres_agree; exact PRES10| exact OSX9|]. intros a Ha. split; [| intros F0; exact F0].
    right; right; left. exists (1, AL). split; [right; exact FLin|]. right. cbn [fst snd]. unfold oshw_lo, oshw_hi, A_SB, amem in Ha |- *. rewrite shl8_1. clear -CEILB Ha ECX8. Z.div_mod_to_equations. lia. }
  pose proof (aypres_block _ _ _ _ _ _ _ PRES10 HH9 ltac:(exists (mkABlock H 104); split; [exact INH| cbn; lia])) as HH10.
  pose proof (aypres_block _ _ _ _ _ _ _ PRES10 LXC ltac:(exists (mkABlock Lx 48); split; [left; reflexivity| cbn [ab_addr ab_size cells_size csize Nat.add length lexer_cells Z.of_nat Pos.of_succ_nat Pos.succ]; lia])) as LXC10.
  pose proof (aypres_block _ _ _ _ _ _ _ PRES10 LBC ltac:(exists (mkABlock (mb_addr mbl) 32); split; [right; left; reflexivity| cbn [ab_addr ab_size cells_size csize Nat.add length buf_cells Z.of_nat Pos.of_succ_nat Pos.succ]; lia])) as LBC10.
  assert (PRES10w : ay_pres REST LF (bv_unsigned sp) [] m m10).
  { eapply ay_pres_trans; [exact PRES9w|]. eapply (ay_pres_weaken Y); [exact PRES10| lia| intros b0 Hb0; right; right; right; exact Hb0| intros f Hf; right; exact Hf| auto]. }
  assert (HS10 : u8arr asegs m10 (2147450880 + H / 8) (blk_shadow 104)).
  { pose proof AY10 as AYx. apply AYST_split in AYx. destruct AYx as [AHKx _].
    pose proof (proj1 (BSHY _ _ _ _ _ _ AHKx (or_intror INH) ltac:(cbn; lia))) as (_ & _ & X). cbn [ab_addr] in X. unfold A_SB in X. exact X. }
  eapply j_bufalloc with (LF := LF) (REST := REST) (CFGP := CFGP) (CX := CX) (lo := lo) (L := L) (RR := RR) (K := K) (m := m) (mo := mo) (s := s) (SQ := SQ) (ff := ff) (AL := AL)
              (CONT := CONT) (H := H) (Lx := Lx) (B0 := B0) (mbl := mbl) (bb := bb) (lblk := lblk)
              (RR1 := y_phi_new Y L + RR - y_acharge Y 104 - (y_acharge Y 48 + y_acharge Y 32 + y_phi_buf Y ybuf_zero + y_free_cost Y) - y_acharge Y 32).
  all: try eassumption.
  all: try (clear -CEILB SEPHL; lia).
  all: try (rewrite ?SO10, ?SO8, ?SO6; exact SO2).
  all: try rchain.
  all: try (clear -CEILB HR; lia).
  all: try (clear -CEILB YN0 NHX RR0 NA48 NA32 NA128 YF0 NBZ; lia).
  all: intros hb lb db sb; pose proof (YNEW L hb lb db sb bb L0) as YNX; clear -CEILB YNX RR0 NA48 NA32 NA128 YF0 NBZ NH0; lia.
Qed.

End W.
End RC__1.
