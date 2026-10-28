(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PgSrcKitA_b PnASrcRead1_b PnASrcReadK_b PnASrcReadP_b Ba0PgSrcReadK16_b Ba0PgSrcReadC16_b Ba0PgSrcReadMB16_b Ba0PgSrcReadMS16_b Ba0PgSrcReadMS2D16_b Ba0PgSrcReadMS2S16_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmParSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmParStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PnASrcReadK_b PnASrcRead1_b PnASrcReadP_b Ba0_code_raf314_af318_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgSrcKitA_b PnRunA_b PmAUarK_b PmAUar_b PnAReadCsK_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].

Module PGSRDMS216.
Abbreviation RSEGS := PGSRDK16.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Ltac pdestr PP := repeat match type of PP with _ /\ _ => let H := fresh "S" in destruct PP as (H & PP) end.

Section G2.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

Lemma ms2_img O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra F M3 model3 LKc Ac :
  PGSRDK16.srd_ctx L ar HI 16 O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra ->
  PGSRDK16.srd_body L ar HI 16 O R0 M0 model0 OB LBX FF LK Aw sp src Wextra F M3 model3 LKc cr Ac ->
  PMSTA.base_okA RSEGS PMA.AD M3 ->
  (L5.img_clear (mrestrict (ahid Ac model3) M3) 65536 1282048)
  /\ (L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) 1309752 2147450880)
  /\ (L5.u32_at RSEGS (mrestrict (ahid Ac model3) M3) 1309760 1).
Proof using All.
  intros _ BD BASE3.
  unfold PGSRDK16.srd_body, PMAUK.binv in BD.
  destruct BD as (HH3 & AM3 & MRT3 & INCA3 & INCL3 & ASTK3 & EK3 & DK3 & OWN3 & DSH3).
  exact (PMASK.mach_vis L ar C HI LY HIok _ _ _ _ _ M3 model3 HH3 BASE3).
Qed.

Lemma ms2_frm O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra F fl LK2 M2 model2 M3 model3 LKc Ac :
  PGSRDK16.srd_ctx L ar HI 16 O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra ->
  PGSRDK16.srd_frame L ar HI 16 R0 OB LBX FF LK Aw cr sp src F fl LK2 M2 model2 ->
  PGSRDK16.srd_body L ar HI 16 O R0 M0 model0 OB LBX FF LK Aw sp src Wextra F M3 model3 LKc cr Ac ->
  L5.writable RSEGS (mrestrict (ahid Ac model3) M3) (sp - 160 - 16) (160 + 16)
  /\ L5.defined (mrestrict (ahid Ac model3) M3) F 128
  /\ L5.writable RSEGS (mrestrict (ahid Ac model3) M3) F 128
  /\ L5.writable RSEGS (mrestrict (ahid Ac model3) M3) (F / 8 + SB) 16
  /\ L5.writable RSEGS (mrestrict (ahid Ac model3) M3) fl 1
  /\ L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) (F + 120) fl.
Proof using All.
  intros CTX G BD.
  pose proof BD as BD'. unfold PGSRDK16.srd_body, PMAUK.binv in BD'.
  destruct BD' as (HH3 & AM3 & MRT3 & INCA3 & INCL3 & ASTK3 & EK3 & DK3 & OWN3 & DSH3).
  pose proof ASTK3 as (A16 & SLO & SHI & SPT & SDEF & SUP).
  change (PMSPA.pm_scr 4) with 20480 in SLO, SDEF.
  pose proof G as G'. unfold PGSRDK16.srd_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  pose proof GFR as (GFR1 & GFR2 & _). change (ff_bytes 1) with 128 in GFS2, GFR2, DSH3. change (128 / 8) with 16 in DSH3.
  assert (VISF : forall i, (sp - 160 - 16 <= i < sp) \/ (F <= i < F + 128) \/ (F / 8 + SB <= i < F / 8 + SB + 16) ->
                   mrestrict (ahid Ac model3) M3 (Z_to_bv 64 i) = M3 (Z_to_bv 64 i)).
  { intros i Hi. unfold mrestrict.
    rewrite (PGSRDC16.srd_vis L ar C HI LY HIok O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra F fl LK2 M2 model2 M3 model3 LKc Ac i CTX G BD
               ltac:(destruct Hi as [Y|[Y|Y]]; [left| right; left| right; right; left]; exact Y)).
    reflexivity. }
  assert (DS : L5.defined M3 (sp - 160 - 16) (160 + 16)).
  { intros i Hi. replace (sp - 160 - 16 + i) with (sp - 20480 + (20480 - 176 + i)) by (clear; lia). apply SDEF. clear - Hi; lia. }
  assert (DSV : L5.defined (mrestrict (ahid Ac model3) M3) (sp - 160 - 16) (160 + 16)).
  { apply (L5C.defined_agree M3 (mrestrict (ahid Ac model3) M3) (sp - 160 - 16) (160 + 16)); [| exact DS].
    intros i Hi. apply VISF. left. clear - Hi; lia. }
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH3) as FSD3. repeat lazymatch type of FSD3 with _ /\ _ => apply proj2 in FSD3 end.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ LKc cr Ac M3 model3 HH3) as VP3; cbv zeta in VP3; destruct VP3 as (_ & _ & _ & VFS3 & _).
  assert (DF128 : L5.defined (mrestrict (ahid Ac model3) M3) F 128).
  { apply (proj2 (L5A.defined_vis (ahid Ac model3) M3 F 128 (VFS3 F 128 ltac:(clear - GFS1; lia) ltac:(clear - GFS2; lia)))).
    intros i Hi. replace (F + i) with (ar_fs ar + (F + i - ar_fs ar)) by (clear; lia). apply FSD3. unfold FS_BYTES in *. clear - Hi GFS1 GFS2; lia. }
  assert (DSH3V : L5.defined (mrestrict (ahid Ac model3) M3) (F / 8 + SB) 16).
  { apply (L5C.defined_agree M3 (mrestrict (ahid Ac model3) M3) (F / 8 + SB) 16); [| exact DSH3].
    intros i Hi. apply VISF. right; right. clear - Hi; lia. }
  pose proof (L5SAR.fl_writable L ar C HI LYa HIok _ _ LKc cr Ac M3 (vml_of model3) fl HH3 GFLP) as (_ & FLW3).
  pose proof GFLR as (FL1 & FL2 & _).
  split; [apply (L5C.writable_of_defined RSEGS); [exact DSV| clear - SLO SHI SPT; lia| clear - SHI SPT; lia]|].
  split; [exact DF128|].
  split; [apply (L5C.writable_of_defined RSEGS); [exact DF128| clear - GFR1; lia| clear - GFR2; lia]|].
  split; [apply (L5C.writable_of_defined RSEGS); [exact DSH3V| clear - GFR1; unfold SB; lia| clear - GFR1 GFR2; unfold SB; lia]|].
  split.
  - apply (proj2 (L5A.writable_vis (ahid Ac model3) M3 fl 1 (L5SAR.fl_vis L ar C HI LYa HIok _ _ LKc cr Ac M3 model3 fl HH3 GFLP) ltac:(clear - FL1; lia) ltac:(clear - FL2; lia))).
    exact FLW3.
  - destruct (L5SAR.flagptr_now L ar C HI LYa HIok _ _ _ _ _ M2 _ _ _ LKc cr Ac M3 model3 F 1 (sp - 160 - 16 + 32) (sp - 160 - 16 + 32) fl
                GHH2 HH3 (or_introl eq_refl) (or_introl eq_refl) ltac:(right; left; reflexivity) GFLC) as (_ & X).
    replace (F + 120) with (F + ff_bytes 1 - 8) by (change (ff_bytes 1) with 128; clear; lia). exact X.
Qed.

Lemma ms_g2_ok : PGSRDMS16.ms_g2_T L ar HI 16.
Proof using All.
  unfold PGSRDMS16.ms_g2_T.
  intros O R0 M0 model0 K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst p k CTX R11 R12
         F fl LK2 M2 model2 G fx R M model LKc Ac V BD XV2 XV36 XV37 XV38 XV50 XV51 XVS XR3 XR4 XV34 XV35 XV45 XIA ST PTH
         len1 fx3 R3 M3 model3 XL1 BD3 XDP PA3 IA3 BASE3 AG E2 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 EKS
         C152 C144 C112 CF32 U1 U2 U3 U4 U5 U6 U7 U8 U9 U10 U11 U12 CF16 CF8 CF0 DF24 DF40.
  assert (XV2' : V 2%nat = sp - 16) by (rewrite XV2; lia).
  pose proof ST as STc. unfold PGSRDK16.srd_stA in STc. pdestr STc.
  assert (K38 : 0 <= k < 2 ^ 64)
    by (rewrite <- XV38; match goal with H : 0 <= V 38%nat < 2 ^ 64 |- _ => exact H end).
  match goal with
  | H2 : _ <= V 2%nat <= _, H36 : _ <= V 36%nat <= _ |- _ => pose proof (conj H2 H36) as KB
  end.
  pose proof (ms2_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX BD3 BASE3) as (I1 & I2 & I3).
  pose proof (ms2_frm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX G BD3) as (W160 & DF & WF & WSH & WFL & C120).
  pose proof (PGSRDMS2S16.ms2_saved L ar C HI LY HIok IL ICok ILY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ V
                CTX G BD3 XV2' XVS) as (SV1 & SV2 & SV3 & SV4 & SV5 & SV6 & SV7 & SV8 & SV9).
  replace (sp - 160 - 16) with (V 2%nat - 160) in W160 by (rewrite XV2'; clear; lia). replace (160 + 16) with 176 in W160 by (clear; lia).
  assert (W160' : L5.writable RSEGS (mrestrict (ahid Ac model3) M3) (V 2%nat - 160) 160) by (eapply L5.writable_sub; [exact W160| clear; lia| clear; lia]).
  rewrite <- XV50 in DF, WF, WSH, C120. rewrite <- XV51 in WFL, C120.
  replace (32 * V 50%nat) with (4 * V 50%nat * 8) in WSH by ring. rewrite Z.div_mul in WSH by lia. unfold SB in WSH.
  assert (AG3 : forall i, (V 2%nat - 160 <= i < V 2%nat - 152 \/ V 2%nat - 136 <= i < V 2%nat - 112 \/ V 2%nat - 104 <= i < V 2%nat)
                          \/ (V 36%nat <= i < V 36%nat + 296) \/ ((V 36%nat + 8) / 8 + SB <= i < (V 36%nat + 8) / 8 + SB + 36) ->
                mrestrict (ahid Ac model3) M3 (Z_to_bv 64 i) = mrestrict (ahid Ac model) M (Z_to_bv 64 i)).
  { intros i Hi.
    assert (NP : ~ (p <= i < p + len1)).
    { intros Hp.
      destruct (PGSRDMS2D16.ms2_disj L ar C HI LY HIok IL ICok ILY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p k CTX R11 R12 K38 G i
                  ltac:(clear - Hp XL1; lia)) as (D1 & D2 & D3 & D4 & D5 & D6).
      rewrite XV2', XV36 in Hi. clear - Hi D1 D4 D5; lia. }
    apply AG.
    - unfold SB in Hi. clear - Hi KB; lia.
    - rewrite XV2', XV36 in Hi. clear - Hi; lia.
    - intros CC. unfold SB in Hi.
      destruct Hi as [[Y|[Y|Y]]|[Y|Y]]; destruct CC as [Z|[Z|[Z|[Z|Z]]]];
        first [clear - Y Z KB; lia | match goal with H : _ \/ _ |- _ => clear - Y Z KB H; lia end].
    - exact NP. }
  unfold SB in AG3.
  unfold PGSRDMS16.srd_stM_C. cbn [PGSRDMS16.vxMS PGSRDMB16.vxC].
  PGSRDC16.sweep ltac:(first [assumption | PGSRDC16.carry (mrestrict (ahid Ac model) M) AG3 KB]).
Qed.

End G2.
End PGSRDMS216.
