(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation Zwf.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanSoundSums SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5CoreSpecsA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParSpecs PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnModelFacts PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnASrcKit_b PnASrcRead1_b PmAUarK_b PmAUar_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrObj. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrObjA_b PnAParKit_b PnAReset1_b PnOwnerOkA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrKitA_b PnSpecsAX_b PnSpecsAXR_b PnAEmbCF_b PnABegDocP_b Ba0_code_ad9e4_ad9e8_b PnABegDocK_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require BatByteCell_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnABegDoc_b.

Module PNABDU1V.
Import L5A. Import L5CA. Import L5SAR. Import PNBKA. Import PNABDK. Import PNABD.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

(* A preserved frame (sp, scr) also holds as the frame (sp + d, scr + d) when [sp, sp + d) is defined. *)
Lemma u1v_ahpres_up (LBx : list (Z * Z)) (FFx : list fframe) (sp scr d : Z) (Wx : list L5.range) (Ma Mb : word -> option byte) :
  L5CA.ahpres L ar LBx FFx sp scr Wx Ma Mb -> 0 <= d -> 0 <= scr -> 0 <= sp -> ahl_ceil ar <= sp -> sp + d <= 2 ^ 47 -> L5.defined Ma sp d ->
  L5CA.ahpres L ar LBx FFx (sp + d) (scr + d) Wx Ma Mb.
Proof.
  intros (AK & DF & DK) Hd Hs Hp Hc Ht DA.
  assert (CL : forall a, HeapIfaceA.aclient L ar LBx FFx (sp + d) (scr + d) a -> HeapIfaceA.aclient L ar LBx FFx sp scr a).
  { intros a X. unfold HeapIfaceA.aclient, HeapIfaceA.aclient_g in X |- *.
    destruct X as [X|[(X1 & X2)|X]]; [left; exact X| right; left; split; [exact X1| intros (Y1 & Y2); apply X2; split; lia]| right; right; exact X]. }
  split; [| split].
  - intros a (A0 & A1 & A2). apply AK. split; [exact A0|]. split; [exact (CL a A1)| exact A2].
  - intros i Hi. replace (sp + d - (scr + d) + i) with (sp - scr + i) by lia.
    destruct (Z_lt_ge_dec i scr) as [Hl|Hg]; [apply DF; lia|].
    replace (sp - scr + i) with (sp + (i - scr)) by lia.
    apply (DK (sp + (i - scr))); [lia| | apply DA; lia].
    unfold HeapIfaceA.aclient, HeapIfaceA.aclient_g. right; left. split; [lia| intros (Y1 & Y2); lia].
  - intros a Ha Hc'. apply DK; [exact Ha| exact (CL a Hc')].
Qed.

(* A byte of the restricted pre-grow memory that the grow call keeps reads the same in the restricted post-grow memory where visible. *)
Lemma u1v_mr (H1 H3 : word -> bool) (M1 M3 : mem) x v :
  mrestrict H1 M1 x = Some v -> H3 x = false -> M3 x = M1 x -> mrestrict H3 M3 x = Some v.
Proof. unfold mrestrict. intros X V E. rewrite V, E. destruct (H1 x); [discriminate| exact X]. Qed.

Lemma u1v_shadow_rng x i : 0 <= x <= 2 ^ 47 -> 0 <= i <= 256 -> 0 <= x / 8 + SB + i < 2 ^ 64.
Proof.
  intros X I. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)) as D0. pose proof (Z.div_le_upper_bound x 8 x ltac:(lia) ltac:(lia)) as D1.
  unfold SB. lia.
Qed.

(* Visible-memory facts at the post-grow memory M3 of the U1 arm: binv at M3 from the grow call's preserved frame, then the
   object, frame, stack and static facts at M1 carried to M3 and read through M3's visibility. *)
Lemma bd_u1_m3vis_ok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 :
  bd_u1_m3vis_T L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2.
Proof using LY HIok ICok ILY.
  unfold bd_u1_m3vis_T.
  intros s6 sm6 ax6 cr6 M1 model1 LK1 Aw1 M3 model3 LK3 Aw3 CTX G LM INV6 ESTK DEPTH NFULL V0' V8' V16' BST3 DEF3 ACC3 ANN3 ACCV3 BASE3 HP3 MRT3 INC3 INCA3 AM3 HH3.
  set (s1 := PNBO.set_more s6 1) in *.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 7) with 26624 in *. change (26624 / 8) with 3328 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  pose proof G as G'. unfold bd_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
  pose proof LM as (BI & RP1 & _).
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  (* the walk's own facts at M1 (arithmetic and apartness part reused at M3) *)
  pose proof (pfacts_of0 L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm6 ax6 cr6 CTX G BI RP1) as (PF1 & _).
  set (FF' := (F, 0, sp - 160 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  destruct RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in *. change (PNRA.o_is PMA.AD fb) with (fb + 96) in *. change (PNRA.o_v PMA.AD fb) with (fb + 432) in *.
  change (PNM.PSIZE + 8) with 424 in OACC1.
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ FF' LK1 cr6 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1 OACC1) as ((O1 & O8 & ONSH) & Zop & OWR & OCE & OVIS & AOP).
  pose proof (PNAPAR.ov_visB L ar C HI LY HIok _ FF' LK1 cr6 Aw1 M1 model1 fb HH1 FOK' VIS1) as VV. cbv zeta in VV.
  destruct VV as ((V1 & V8 & VNS) & VZ & VW & VCE & VU & AOV).
  pose proof PA1 as (_ & _ & _ & _ & _ & CM & _).
  (* binv at M3: the grow call's preserved frame (sp - 224, pm_scr 0) read as the callee frame (sp - 160, 64 + pm_scr 0) *)
  assert (DM1 : L5.defined M1 (sp - 224) 64).
  { pose proof ASTK1 as (_ & _ & _ & _ & SDEF1 & _). apply (L5.defined_sub M1 (sp - 26624) 26624); [exact SDEF1| clear; lia| clear; lia]. }
  assert (HP3w : L5CA.ahpres L ar (rest_own s1 ++ LBX) FF' (sp - 160) (64 + PMSPA.pm_scr 0) [] M1 M3).
  { replace (sp - 160) with (sp - 224 + 64) by (clear; lia). replace (64 + PMSPA.pm_scr 0) with (PMSPA.pm_scr 0 + 64) by (clear; lia).
    apply u1v_ahpres_up; [exact HP3| clear; lia| unfold PMSPA.pm_scr; clear; lia| clear - SLO GFR GFCEIL; lia| clear - SLO; lia| clear - SHI SPT; lia| exact DM1]. }
  assert (BI3 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 26624 (sp - 160) (own sp R) F 0 (PNRA.W_brun PMA.AD PMA.AN fb)
                  (PNM.bvec_own (PNM.b_sb s1) (PNM.b_sk s1) ++ rest_own s1) M3 model3 LK3 cr6 Aw3).
  { eapply (PMAUK.binv_callee L ar C HI HIok); [exact G| exact BI| exact HP3w| rewrite <- app_assoc; exact HH3| exact AM3| exact MRT3| exact INCA3| exact INC3
      | unfold PMSPA.pm_scr; clear; lia| unfold PMSPA.pm_scr; clear; lia| intros rr a []| intros a _ _ rr []| intros a X; exact X]. }
  pose proof BI3 as (_ & _ & _ & _ & _ & ASTK3 & _).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ LK3 cr6 Aw3 M3 model3 HH3) as (_ & VISs3 & _ & VFS3 & _ & _ & VFSSH3 & VSTSH3).
  cbv zeta in VISs3, VFS3, VFSSH3, VSTSH3.
  pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF' LK3 cr6 Aw3 M3 model3 HH3 BASE3) as (VM0 & VM1 & VM2).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF' LK3 cr6 Aw3 M3 model3 sp 26624 240 HH3 ASTK3 ltac:(lia)) as (SL240 & SH240 & SWR240).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF' LK3 cr6 Aw3 M3 model3 sp 26624 160 HH3 ASTK3 ltac:(lia)) as (SL160 & SH160 & SWR).
  destruct (PMAUK.vis_facts L ar C HI LYa HIok M model LBX FF LK Aw sp 26624 (sp - 160) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PNM.bparser_own s) G
              _ _ M3 model3 LK3 cr6 Aw3 BI3) as ((WS3 & _ & _ & _ & _) & OWNv & (FD3 & FW3 & FSW3 & FLC3 & FLW3) & (FLCc3 & FLV3 & VF3 & VS3 & VSH3)).
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *. replace (F + 64 - 8) with (F + 56) in FLC3 by (clear; lia).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF' LK3 cr6 Aw3 M3 model3 (fb + 464) 424 0 0 HH3 (PMKA.aobj_of_aobjA FF' (fb + 464) 424 AOP O8) ltac:(lia) ltac:(reflexivity))
    as ((OB0 & OB1 & OB2 & OB3 & OB4) & _ & ODEF3 & OVIS3 & OSHV3 & _ & _).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF' LK3 cr6 Aw3 M3 model3 (fb + 432) 8 0 0 HH3 (PMKA.aobj_of_aobjA FF' (fb + 432) 8 AOV V8) ltac:(lia) ltac:(reflexivity))
    as ((VB0 & VB1 & VB2 & VB3 & VB4) & _ & _ & VVIS3 & VSHV3 & _ & _).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF' LK1 cr6 Aw1 M1 model1 (fb + 432) 8 0 0 HH1 (PMKA.aobj_of_aobjA FF' (fb + 432) 8 AOV V8) ltac:(lia) ltac:(reflexivity))
    as (_ & _ & _ & VVIS1 & _ & _ & _).
  cbv zeta in OVIS3, OSHV3, VVIS3, VSHV3, VVIS1.
  set (H3 := ahid Aw3 model3) in *. set (MV3 := mrestrict H3 M3) in *.
  set (H1 := ahid Aw1 model1) in *. set (MV1 := mrestrict H1 M1) in *.
  set (op := fb + 464) in *.
  (* bytes the grow call keeps: client bytes of its preserved frame (nothing written outside it) *)
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> aclient L ar (rest_own s1 ++ LBX) FF' (sp - 224) (PMSPA.pm_scr 0) a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha Hc. apply (proj1 HP3). split; [exact Ha| split; [exact Hc| intros rr []]]. }
  assert (CLo : forall a, fb + 32 <= a < fb + 2040 -> aclient L ar (rest_own s1 ++ LBX) FF' (sp - 224) (PMSPA.pm_scr 0) a).
  { intros a Ha. unfold aclient, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [right; exact Hfb|]. cbn [ff_addr ff_class fst snd].
    change (ff_bytes 5) with 2048. split; [clear - Ha; lia| intros Y; clear - Ha Y; lia]. }
  assert (CLs : forall a, fb / 8 + SB <= a < fb / 8 + SB + 256 -> aclient L ar (rest_own s1 ++ LBX) FF' (sp - 224) (PMSPA.pm_scr 0) a).
  { intros a Ha. unfold aclient, aclient_g. do 5 right; left. exists (fb, 5, rs). split; [right; exact Hfb|]. cbn [ff_addr ff_class fst snd].
    change (ff_bytes 5) with 2048. change (fb / 8 + SB <= a <= (fb + 2048 - 1) / 8 + SB). unfold SB in *.
    assert (D1 : (fb + 2048 - 1) / 8 = fb / 8 + 255).
    { pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
      replace (2048 * (fb / 2048) + 2048 - 1) with (7 + (256 * (fb / 2048) + 255) * 8) by (clear; lia). rewrite Z.div_add by lia.
      replace (2048 * (fb / 2048)) with ((256 * (fb / 2048)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
    rewrite D1. clear - Ha. lia. }
  assert (CLst : forall a, sp - 224 <= a < sp -> aclient L ar (rest_own s1 ++ LBX) FF' (sp - 224) (PMSPA.pm_scr 0) a).
  { intros a Ha. unfold aclient, aclient_g. right; left. split; [clear - Ha SLO SHI SPT; lia| intros (Y1 & Y2); clear - Ha Y2; lia]. }
  assert (SHop : op / 8 + SB = fb / 8 + SB + 58).
  { unfold op. pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
    replace (2048 * (fb / 2048) + 464) with ((256 * (fb / 2048) + 58) * 8) by (clear; lia). rewrite Z.div_mul by lia.
    replace (2048 * (fb / 2048)) with ((256 * (fb / 2048)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
  assert (SHov : (fb + 432) / 8 + SB = fb / 8 + SB + 54).
  { pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
    replace (2048 * (fb / 2048) + 432) with ((256 * (fb / 2048) + 54) * 8) by (clear; lia). rewrite Z.div_mul by lia.
    replace (2048 * (fb / 2048)) with ((256 * (fb / 2048)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
  (* the object's shadow and bytes at M3 *)
  assert (ZOP3 : L5KA.zeros_at MV3 (op / 8 + SB) 53).
  { intros i Hi. apply (u1v_mr H1 H3 M1 M3 _ _ (Zop i Hi)).
    - exact (OSHV3 i ltac:(change (424 / 8) with 53; clear - Hi; lia)).
    - apply KEEP; [apply u1v_shadow_rng; clear - Hi OB0 OB2; lia| apply CLs; clear - Hi SHop; unfold SB in *; lia]. }
  assert (Zz0 : L5KA.zeros_at MV3 (op / 8 + SB) 2). { intros i Hi. apply ZOP3. clear - Hi; lia. }
  assert (Zz1 : L5KA.zeros_at MV3 ((op + 10) / 8 + SB) 1).
  { intros i Hi. replace ((op + 10) / 8 + SB + i) with (op / 8 + SB + (1 + i)) by (rewrite (div8_add op 10 O8 ltac:(clear; lia)); change (10 / 8) with 1; clear; lia).
    apply ZOP3. clear - Hi; lia. }
  assert (Zz2 : L5KA.zeros_at MV3 ((op + 312) / 8 + SB) 1).
  { intros i Hi. replace ((op + 312) / 8 + SB + i) with (op / 8 + SB + (39 + i)) by (rewrite (div8_add op 312 O8 ltac:(clear; lia)); change (312 / 8) with 39; clear; lia).
    apply ZOP3. clear - Hi; lia. }
  assert (Zz3 : L5KA.zeros_at MV3 ((op + 392) / 8 + SB) 3).
  { intros i Hi. replace ((op + 392) / 8 + SB + i) with (op / 8 + SB + (49 + i)) by (rewrite (div8_add op 392 O8 ltac:(clear; lia)); change (392 / 8) with 49; clear; lia).
    apply ZOP3. clear - Hi; lia. }
  assert (OWR3 : L5.writable RSEGS MV3 op 424).
  { apply (proj2 (L5A.writable_vis H3 M3 op 424 OVIS3 ltac:(clear - OB0; lia) ltac:(clear - OB2; lia))).
    apply (L5C.writable_of_defined RSEGS); [exact ODEF3| clear - OB0; lia| clear - OB2; lia]. }
  assert (U8o : forall o v, 0 <= o < 424 -> L5.u8_at RSEGS M1 (op + o) v -> L5.u8_at RSEGS MV3 (op + o) v).
  { intros o v Ho X.
    apply (proj2 (L5A.u8_at_vis H3 M3 (op + o) v (L5A.avis_sub H3 op 424 (op + o) 1 OVIS3 ltac:(clear - Ho; lia) ltac:(clear - Ho; lia)) ltac:(clear - Ho OB0; lia) ltac:(clear - Ho OB2; lia))).
    eapply L5C.u8_at_agree; [| | | exact X].
    - intros j Hj. apply KEEP; [clear - Hj Ho OB0 OB2; lia| apply CLo; unfold op in Hj; clear - Hj Ho; lia].
    - clear - Ho OB0; lia.
    - clear - Ho OB2; lia. }
  (* the frame's stack cells [sp - 224, sp) *)
  assert (U64S : forall a v, sp - 224 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1 a v -> L5.u64_at RSEGS MV3 a v).
  { intros a v Ha1 Ha2 X.
    apply (proj2 (L5A.u64_at_vis H3 M3 a v (VISs3 a 8 ltac:(clear - Ha1 SLO; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SLO GFR GFCEIL; lia) ltac:(clear - Ha2 SHI SPT; lia))).
    eapply L5C.u64_at_agree; [| | | exact X].
    - intros j Hj. apply KEEP; [clear - Hj Ha1 Ha2 SLO GFR GFCEIL SHI SPT; lia| apply CLst; clear - Hj Ha1 Ha2; lia].
    - clear - Ha1 SLO GFR GFCEIL; lia.
    - clear - Ha2 SHI SPT; lia. }
  assert (U32S : forall a v, sp - 224 <= a -> a + 4 <= sp -> L5.u32_at RSEGS M1 a v -> L5.u32_at RSEGS MV3 a v).
  { intros a v Ha1 Ha2 X.
    apply (proj2 (L5A.u32_at_vis H3 M3 a v (VISs3 a 4 ltac:(clear - Ha1 SLO; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SLO GFR GFCEIL; lia) ltac:(clear - Ha2 SHI SPT; lia))).
    assert (AG : L5C.agree_on M1 M3 a 4).
    { intros j Hj. apply KEEP; [clear - Hj Ha1 Ha2 SLO GFR GFCEIL SHI SPT; lia| apply CLst; clear - Hj Ha1 Ha2; lia]. }
    unfold L5.u32_at in X |- *. rewrite (L5C.rdn_agree RSEGS M1 M3 4 a ltac:(clear - Ha1 SLO GFR GFCEIL; lia) ltac:(clear - Ha2 SHI SPT; lia) AG). exact X. }
  (* the visitor cell at fb + 432 and its shadow *)
  assert (ZOV3 : L5KA.zeros_at MV3 ((fb + 432) / 8 + SB) 1).
  { intros i Hi. apply (u1v_mr H1 H3 M1 M3 _ _ (VZ i Hi)).
    - exact (VSHV3 i ltac:(change (8 / 8) with 1; clear - Hi; lia)).
    - apply KEEP; [apply u1v_shadow_rng; clear - Hi VB0 VB2; lia| apply CLs; clear - Hi SHov; unfold SB in *; lia]. }
  assert (UOV3 : L5.u64_at RSEGS MV3 (fb + 432) (pa_vp_visitor PMA.AD)).
  { apply (proj2 (L5A.u64_at_vis H3 M3 (fb + 432) _ VVIS3 ltac:(clear - VB0; lia) ltac:(clear - VB2; lia))).
    pose proof (proj1 (L5A.u64_at_vis H1 M1 (fb + 432) _ VVIS1 ltac:(clear - VB0; lia) ltac:(clear - VB2; lia)) VU) as X.
    eapply L5C.u64_at_agree; [| | | exact X].
    - intros j Hj. apply KEEP; [clear - Hj VB0 VB2; lia| apply CLo; clear - Hj; lia].
    - clear - VB0; lia.
    - clear - VB2; lia. }
  (* stack shadow: entry -> M1 (binv's ek) -> M3 (the grow call's preserved frame) *)
  set (WR := PNRA.W_brun PMA.AD PMA.AN fb) in *.
  assert (WAPPR : PMKA.wapp WR).
  { unfold WR, PNRA.W_brun, PGS.W_srcfG, PNST.berr_W, PNST.cat_W, PNST.dec_W, PNRA.o_src, PNRA.o_is, PNRA.o_bb, PNRA.o_nb, PNRA.o_tb, PNRA.o_stk, PNRA.o_ec, PNRA.o_p, PMSP.o_p, PMSP.o_is, PMSP.o_ec.
    cbn [app pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PMA.AD ADDR_A PMA.AN NADDR_A PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj].
    unfold PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK.
    pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
    repeat apply PMKA.wapp_cons; [..| apply PMKA.wapp_nil]; cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct FA1 as [FA1|FA1]; clear - FA0 FA1 FA2 F1 F2; lia. }
  assert (SP8 : (sp - 26624) mod 8 = 0) by (apply PMKA.mod16_8'; replace (sp - 26624) with (sp + (-1664) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16).
  assert (SZ1 : shadow_zero M1 (sp - 26624) 3328).
  { apply (PMKA.stksh_keepA L ar LBX FF sp 26624 WR M M1 EK1 WAPPR (sp - 26624) 3328); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| exact SP8| clear; lia| exact STKSH]. }
  assert (SZ3 : shadow_zero M3 (sp - 26624) 3328).
  { apply (PMKA.stksh_keepA L ar (rest_own s1 ++ LBX) FF' (sp - 224) (PMSPA.pm_scr 0) [] M1 M3 (proj1 HP3) PMKA.wapp_nil (sp - 26624) 3328);
      [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| exact SP8| clear; lia| exact SZ1]. }
  assert (SZB : forall d, 112 <= d <= 224 -> L5KA.zeros_at MV3 ((sp - d) / 8 + SB) 1).
  { intros d Hd i Hi. assert (i = 0) by (clear - Hi; lia). subst i. rewrite Z.add_0_r.
    pose proof (shz_at M3 (sp - 26624) 3328 (sp - d) SZ3 SP8 ltac:(clear - Hd; lia) ltac:(clear - Hd; lia)) as X. change (M3 (Z_to_bv 64 ((sp - d) / 8 + SB)) = Some (Z_to_bv 8 0)) in X.
    unfold MV3. rewrite (AsanAcct.mrestrict_visible H3 M3); [exact X|].
    assert (AV : L5A.avis H3 ((sp - d) / 8 + SB) 1).
    { apply VSTSH3. intros j Hj. change (ahl_ceil ar / 8 + SB <= (sp - d) / 8 + SB + j <= (ahl_ceil ar + (ar_sptop ar - ahl_ceil ar) - 1) / 8 + SB). assert (j = 0) by (clear - Hj; lia). subst j. rewrite Z.add_0_r.
      split; apply Z.add_le_mono_r; apply Z.div_le_mono; clear - Hd SLO SHI SPT; lia. }
    pose proof (AV 0 ltac:(clear; lia)) as Y. rewrite Z.add_0_r in Y. exact Y. }
  (* assemble *)
  unfold pfacts in PF1.
  destruct PF1 as (_ & _ & _ & SPR & SP32' & _ & OPR & OP8 & OPBIG & _ & _ & _ & _ & SAOP & FR & F32 & _ & _ & FBIG & _ & _ & FLR & _ & FLBIG & FFLA & SAF & SAFL & APF & APFL & APS & BND).
  split.
  { unfold pfacts.
    split; [exact VM0|]. split; [exact VM1|]. split; [exact VM2|].
    split; [exact SPR|]. split; [exact SP32'|]. split; [exact SWR|].
    split; [exact OPR|]. split; [exact OP8|]. split; [exact OPBIG|].
    split; [exact Zz0|]. split; [exact Zz1|]. split; [exact Zz2|]. split; [exact Zz3|]. split; [exact SAOP|].
    split; [exact FR|]. split; [exact F32|]. split; [exact FD3|]. split; [exact FW3|]. split; [exact FBIG|]. split; [exact FSW3|].
    split; [exact FLC3|]. split; [exact FLR|]. split; [exact FLW3|]. split; [exact FLBIG|]. split; [exact FFLA|].
    split; [exact SAF|]. split; [exact SAFL|]. split; [exact APF|]. split; [exact APFL|]. split; [exact APS|].
    exact BND. }
  split; [exact OWNv|].
  split; [exact U64S|].
  split; [exact U32S|].
  split; [intros v; exact (U8o 8 v ltac:(clear; lia))|].
  split; [exact OWR3|].
  split; [exact (U8o 10 0 ltac:(clear; lia) CM)|].
  split; [exact SWR240|].
  split; [right; clear - OCE SLO; lia|].
  split; [right; clear - GFCEIL SLO; lia|].
  split; [right; clear - GFLR SLO; lia|].
  split; [right; clear - VCE SLO; lia|].
  split; [exact (SZB 224 ltac:(clear; lia))|].
  split; [exact (SZB 216 ltac:(clear; lia))|].
  split; [exact (SZB 208 ltac:(clear; lia))|].
  split; [exact (SZB 120 ltac:(clear; lia))|].
  split; [exact (SZB 116 ltac:(clear; lia))|].
  split; [exact (SZB 112 ltac:(clear; lia))|].
  split; [exact ZOV3|].
  split; [exact UOV3|].
  match goal with |- L5KA.zeros_at _ ?z 1 => replace z with ((z - SB) * 8 / 8 + SB) by (rewrite Z.div_mul by lia; lia) end.
  apply (PMASK.img_shz_vis L ar C HI LY IL ICok ILY _ FF' LK3 cr6 Aw3 M3 model3 _ 1 HH3); [unfold SB; lia| unfold SB; lia| apply Z_mod_mult| lia| unfold SB; lia].
Qed.

End WithHeap.
End PNABDU1V.
