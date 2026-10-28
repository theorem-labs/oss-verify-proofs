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
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrKitA_b PnSpecsAX_b PnSpecsAXR_b PnAEmbCF_b PnABegArrP_b Ba0_code_b23d8_b23dc_b PnABegArrK_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnABegArr_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnABegArrU1E1_b PnABegArrU1E2_b.

Module PNABAU1V.
Import L5A. Import L5CA. Import L5SAR. Import PNBKA. Import PNABAK. Import PNABA.
Abbreviation mem := (word -> option byte).

Definition m3vis (MV : mem) (sp op b n40 F fl : Z) : Prop :=
  L5.u64_at RSEGS MV (sp - 208) ((b + n40) + 40)
  /\ L5.u64_at RSEGS MV (sp - 216) (b + n40)
  /\ L5.u64_at RSEGS MV (sp - 224) (op + 392)
  /\ L5.u64_at RSEGS MV (sp - 200) (b + n40)
  /\ L5.u64_at RSEGS MV (sp - 192) (((op + 400) / 8) + 2147450880)
  /\ L5.u64_at RSEGS MV (sp - 184) (sp - 160)
  /\ L5.u64_at RSEGS MV (sp - 176) sp
  /\ L5.u64_at RSEGS MV (sp - 168) 735784
  /\ L5.u32_at RSEGS MV (sp - 120) 3
  /\ L5.img_clear MV 65536 1282048
  /\ L5.u64_at RSEGS MV 1309752 2147450880
  /\ L5.u32_at RSEGS MV 1309760 1
  /\ 140735332487296 <= sp <= 140737488355328
  /\ PNABAP.aligned sp 32
  /\ L5.writable RSEGS MV (sp - 224) 224
  /\ 6905856 <= op <= 140737488354912
  /\ PNABAP.aligned op 8
  /\ (2147446784 + 17592186048512 <= op \/ op + 416 <= 2147446784)
  /\ L5KA.zeros_at MV ((op / 8) + 2147450880) 2
  /\ L5KA.zeros_at MV (((op + 10) / 8) + 2147450880) 1
  /\ L5KA.zeros_at MV (((op + 312) / 8) + 2147450880) 1
  /\ L5KA.zeros_at MV (((op + 392) / 8) + 2147450880) 3
  /\ ((sp - 224) + 224 <= op \/ op + 416 <= (sp - 224))
  /\ 6905856 <= F <= 140737488355264
  /\ PNABAP.aligned F 32
  /\ L5.defined MV F 64
  /\ L5.writable RSEGS MV F 64
  /\ (2147446784 + 17592186048512 <= F \/ F + 64 <= 2147446784)
  /\ L5.writable RSEGS MV ((F / 8) + 2147450880) 8
  /\ L5.u64_at RSEGS MV (F + 56) fl
  /\ 4096 <= fl <= 140737488355327
  /\ L5.writable RSEGS MV fl 1
  /\ (2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784)
  /\ (F + 64 <= fl \/ fl + 1 <= F)
  /\ ((sp - 224) + 224 <= F \/ F + 64 <= (sp - 224))
  /\ ((sp - 224) + 224 <= fl \/ fl + 1 <= (sp - 224))
  /\ (op + 416 <= F \/ F + 64 <= op)
  /\ (op + 416 <= fl \/ fl + 1 <= op)
  /\ (((op / 8) + 2147450880) + 52 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 8 <= ((op / 8) + 2147450880))
  /\ L5.u64_at RSEGS MV (sp - 136) (((op + 400) / 8) + 2147450880)
  /\ L5.u64_at RSEGS MV (sp - 144) (op + 400)
  /\ L5.writable RSEGS MV (sp - 4096) 4096
  /\ L5.u64_at RSEGS MV 1275072 1309752
  /\ L5.writable RSEGS MV (op + 392) 24
  /\ ((sp - 4096) + 4096 <= op \/ op + 416 <= (sp - 4096))
  /\ L5.u64_at RSEGS MV (sp - 112) 4.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

Lemma ba_u1_m3vis_ok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 :
  forall s6 sm6 ax6 cr6 (M1 : mem) model1 LK1 Aw1 (M3 : mem) model3 LK3 Aw3,
  ba_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  ba_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  ba_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 (PNBO.set_more s6 1) sm6 ax6 cr6 ->
  L5.u64_at RSEGS M1 (sp - 208) (PNM.b_sb (PNBO.set_more s6 1) + 40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))) + 40) -> L5.u64_at RSEGS M1 (sp - 216) (PNM.b_sb (PNBO.set_more s6 1) + 40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1)))) ->
  L5.u64_at RSEGS M1 (sp - 224) (fb + 464 + 392) -> L5.u64_at RSEGS M1 (sp - 200) (PNM.b_sb (PNBO.set_more s6 1) + 40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1)))) ->
  L5.u64_at RSEGS M1 (sp - 192) ((fb + 464 + 400) / 8 + 2147450880) -> L5.u64_at RSEGS M1 (sp - 184) (sp - 160) ->
  L5.u64_at RSEGS M1 (sp - 176) sp -> L5.u64_at RSEGS M1 (sp - 168) 735784 -> L5.u32_at RSEGS M1 (sp - 120) 3 ->
  L5.u64_at RSEGS M1 (sp - 112) 4 -> spill M1 sp F ->
  L5.u64_at RSEGS M1 (sp - 144) (fb + 464 + 400) -> L5.u64_at RSEGS M1 (sp - 136) ((fb + 464 + 400) / 8 + 2147450880) ->
  PMSPA.ec_at RSEGS M1 (fb + 1024) e cat ->
  PNRA.binv s6 -> PNM.b_stk s6 = PNM.b_stk s -> Z.of_nat (length (PNM.b_stk s6)) <= 1024 -> Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))) < 2 ^ PNM.b_sk (PNBO.set_more s6 1) ->
  PM.unread (PNM.b_src s6) sm6 + 4 <= PM.unread (PNM.b_src s) sm ->
  L5.u64_at RSEGS M3 (fb + 464 + 392) (PNM.b_sb (PNBO.set_more s6 1)) ->
  L5.u64_at RSEGS M3 (fb + 464 + 392 + 8) (PNM.b_sb (PNBO.set_more s6 1) + 40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1)))) ->
  L5.u64_at RSEGS M3 (fb + 464 + 392 + 16) (PNM.b_sb (PNBO.set_more s6 1) + 40 * 2 ^ PNM.b_sk (PNBO.set_more s6 1)) ->
  (forall i, (i < length (PNM.b_stk (PNBO.set_more s6 1)))%nat -> PNM.bstate_at RSEGS M3 (PNM.b_sb (PNBO.set_more s6 1) + 40 * Z.of_nat i) (nth i (PNM.b_stk (PNBO.set_more s6 1)) PNM.bs_root)) ->
  L5.defined M3 (PNM.b_sb (PNBO.set_more s6 1)) (40 * 2 ^ PNM.b_sk (PNBO.set_more s6 1)) -> PMSPA.accA M3 (PNM.b_sb (PNBO.set_more s6 1)) (40 * (Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))) + 1)) ->
  PMSPA.annA M3 (PNM.b_sb (PNBO.set_more s6 1)) (40 * (Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))) + 1)) (40 * 2 ^ PNM.b_sk (PNBO.set_more s6 1)) ->
  PMSPA.accA M3 (fb + 464 + 392) 24 -> PMSTA.base_okA RSEGS PMA.AD M3 ->
  L5CA.ahpres L ar (rest_own (PNBO.set_more s6 1) ++ LBX) ((F, 0, sp - 160 + 32) :: FF) (sp - 224) (PMSPA.pm_scr 0) [] M1 M3 ->
  model_rt model1 model3 -> incl LK3 LK1 -> incl Aw1 Aw3 -> L5CA.amodel_ok Aw3 model3 ->
  ri_inv HI (PNM.bvec_own (PNM.b_sb (PNBO.set_more s6 1)) (PNM.b_sk (PNBO.set_more s6 1)) ++ rest_own (PNBO.set_more s6 1) ++ LBX) ((F, 0, sp - 160 + 32) :: FF) LK3 cr6 Aw3 M3 (vml_of model3) ->
  m3vis (mrestrict (ahid Aw3 model3) M3) sp (fb + 464) (PNM.b_sb (PNBO.set_more s6 1)) (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1)))) F fl.
Proof using LY HIok ICok ILY.
  assert (AHUP : forall (LBx : list (Z * Z)) (FFx : list fframe) (spx scrx d : Z) (Wx : list L5.range) (Ma Mb : word -> option byte),
    L5CA.ahpres L ar LBx FFx spx scrx Wx Ma Mb -> 0 <= d -> 0 <= scrx -> 0 <= spx -> ahl_ceil ar <= spx -> spx + d <= 2 ^ 47 -> L5.defined Ma spx d ->
    L5CA.ahpres L ar LBx FFx (spx + d) (scrx + d) Wx Ma Mb).
  { intros LBx FFx spx scrx d Wx Ma Mb.
    intros (AK & DF & DK) Hd Hs Hp Hc Ht DA.
    assert (CL : forall a, HeapIfaceA.aclient L ar LBx FFx (spx + d) (scrx + d) a -> HeapIfaceA.aclient L ar LBx FFx spx scrx a).
    { intros a X. unfold HeapIfaceA.aclient, HeapIfaceA.aclient_g in X |- *.
      destruct X as [X|[(X1 & X2)|X]]; [left; exact X| right; left; split; [exact X1| intros (Y1 & Y2); apply X2; split; lia]| right; right; exact X]. }
    split; [| split].
    - intros a (A0 & A1 & A2). apply AK. split; [exact A0|]. split; [exact (CL a A1)| exact A2].
    - intros i Hi. replace (spx + d - (scrx + d) + i) with (spx - scrx + i) by lia.
      destruct (Z_lt_ge_dec i scrx) as [Hl|Hg]; [apply DF; lia|].
      replace (spx - scrx + i) with (spx + (i - scrx)) by lia.
      apply (DK (spx + (i - scrx))); [lia| | apply DA; lia].
      unfold HeapIfaceA.aclient, HeapIfaceA.aclient_g. right; left. split; [lia| intros (Y1 & Y2); lia].
    - intros a Ha Hc'. apply DK; [exact Ha| exact (CL a Hc')].
  }
  assert (UMR : forall (H1x H3x : word -> bool) (M1x M3x : mem) x v, mrestrict H1x M1x x = Some v -> H3x x = false -> M3x x = M1x x -> mrestrict H3x M3x x = Some v).
  { intros H1x H3x M1x M3x x v X V E. unfold mrestrict in X |- *. rewrite V, E. destruct (H1x x); [discriminate| exact X]. }
  assert (USR : forall x i, 0 <= x <= 2 ^ 47 -> 0 <= i <= 256 -> 0 <= x / 8 + SB + i < 2 ^ 64).
  { intros x i X I. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)) as D0. pose proof (Z.div_le_upper_bound x 8 x ltac:(lia) ltac:(lia)) as D1.
    unfold SB. lia. }
  intros s6 sm6 ax6 cr6 M1 model1 LK1 Aw1 M3 model3 LK3 Aw3 CTX G LM C208 C216 C224 C200 C192 C184 C176 C168 C120 C112 SPL C144 C136 EC1
    INV6 ESTK DEPTH NFULL UNR6 V0' V8' V16' BST3 DEF3 ACC3 ANN3 ACCV3 BASE3 HP3 MRT3 INC3 INCA3 AM3 HH3.
  unfold m3vis. cbv beta.
  set (s1 := PNBO.set_more s6 1) in *.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 7) with 26624 in *. change (26624 / 8) with 3328 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  pose proof G as G'. unfold ba_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
  pose proof LM as (BI & RP1 & _).
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  pose proof (pfacts_of0 L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm6 ax6 cr6 CTX G BI RP1) as (PF1 & _).
  set (FF' := (F, 0, sp - 160 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  destruct RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in *. change (PNRA.o_is PMA.AD fb) with (fb + 96) in *. change (PNRA.o_v PMA.AD fb) with (fb + 432) in *.
  change (PNM.PSIZE + 8) with 424 in OACC1.
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ FF' LK1 cr6 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1 OACC1) as ((O1 & O8 & ONSH) & Zop & OWR & OCE & OVIS & AOP).
  assert (DM1 : L5.defined M1 (sp - 224) 64).
  { pose proof ASTK1 as (_ & _ & _ & _ & SDEF1 & _). apply (L5.defined_sub M1 (sp - 26624) 26624); [exact SDEF1| clear; lia| clear; lia]. }
  assert (HP3w : L5CA.ahpres L ar (rest_own s1 ++ LBX) FF' (sp - 160) (64 + PMSPA.pm_scr 0) [] M1 M3).
  { replace (sp - 160) with (sp - 224 + 64) by (clear; lia). replace (64 + PMSPA.pm_scr 0) with (PMSPA.pm_scr 0 + 64) by (clear; lia).
    apply AHUP; [exact HP3| clear; lia| unfold PMSPA.pm_scr; clear; lia| clear - SLO GFR GFCEIL; lia| clear - SLO; lia| clear - SHI SPT; lia| exact DM1]. }
  assert (BI3 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 26624 (sp - 160) (own sp R) F 0 (PNRA.W_brun PMA.AD PMA.AN fb)
                  (PNM.bvec_own (PNM.b_sb s1) (PNM.b_sk s1) ++ rest_own s1) M3 model3 LK3 cr6 Aw3).
  { eapply (PMAUK.binv_callee L ar C HI HIok); [exact G| exact BI| exact HP3w| rewrite <- app_assoc; exact HH3| exact AM3| exact MRT3| exact INCA3| exact INC3
      | unfold PMSPA.pm_scr; clear; lia| unfold PMSPA.pm_scr; clear; lia| intros rr a []| intros a _ _ rr []| intros a X; exact X]. }
  pose proof BI3 as (_ & _ & _ & _ & _ & ASTK3 & _).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ LK3 cr6 Aw3 M3 model3 HH3) as (_ & VISs3 & VIMG3 & VFS3 & _ & _ & VFSSH3 & VSTSH3).
  cbv zeta in VISs3, VIMG3, VFS3, VFSSH3, VSTSH3.
  pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF' LK3 cr6 Aw3 M3 model3 HH3 BASE3) as (VM0 & VM1 & VM2).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF' LK3 cr6 Aw3 M3 model3 sp 26624 224 HH3 ASTK3 ltac:(lia)) as (SL224 & SH224 & SWR224).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF' LK3 cr6 Aw3 M3 model3 sp 26624 4096 HH3 ASTK3 ltac:(lia)) as (SL4096 & SH4096 & SWR4096).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF' LK3 cr6 Aw3 M3 model3 sp 26624 160 HH3 ASTK3 ltac:(lia)) as (SL160 & SH160 & SWR).
  destruct (PMAUK.vis_facts L ar C HI LYa HIok M model LBX FF LK Aw sp 26624 (sp - 160) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PNM.bparser_own s) G
              _ _ M3 model3 LK3 cr6 Aw3 BI3) as ((WS3 & _ & _ & _ & _) & OWNv & (FD3 & FW3 & FSW3 & FLC3 & FLW3) & (FLCc3 & FLV3 & VF3 & VS3 & VSH3)).
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *. replace (F + 64 - 8) with (F + 56) in FLC3 by (clear; lia).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF' LK3 cr6 Aw3 M3 model3 (fb + 464) 424 0 0 HH3 (PMKA.aobj_of_aobjA FF' (fb + 464) 424 AOP O8) ltac:(lia) ltac:(reflexivity))
    as ((OB0 & OB1 & OB2 & OB3 & OB4) & _ & ODEF3 & OVIS3 & OSHV3 & _ & _).
  cbv zeta in OVIS3, OSHV3.
  set (H3 := ahid Aw3 model3) in *. set (MV3 := mrestrict H3 M3) in *.
  set (H1 := ahid Aw1 model1) in *. set (MV1 := mrestrict H1 M1) in *.
  set (op := fb + 464) in *.
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> aclient L ar (rest_own s1 ++ LBX) FF' (sp - 224) (PMSPA.pm_scr 0) a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha Hc. apply (proj1 HP3). split; [exact Ha| split; [exact Hc| intros rr []]]. }
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
  assert (ZOP3 : L5KA.zeros_at MV3 (op / 8 + SB) 53).
  { intros i Hi. apply (UMR H1 H3 M1 M3 _ _ (Zop i Hi)).
    - exact (OSHV3 i ltac:(change (424 / 8) with 53; clear - Hi; lia)).
    - apply KEEP; [apply USR; clear - Hi OB0 OB2; lia| apply CLs; clear - Hi SHop; unfold SB in *; lia]. }
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
  unfold pfacts in PF1.
  destruct PF1 as (_ & _ & _ & SPR & SP32' & _ & OPR & OP8 & OPBIG & _ & _ & _ & _ & SAOP & FR & F32 & _ & _ & FBIG & _ & _ & FLR & _ & FLBIG & FFLA & SAF & SAFL & APF & APFL & APS & BND).
  assert (D4 : forall a0 w0 v0, In (a0, w0, v0) L5A.AS0_ALY_CELLS_D4 -> cell_is RSEGS M3 a0 (Z.to_nat w0) v0).
  { intros a0 w0 v0 Hin. pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH3) as (_ & CS). rewrite (L5A.aly_segs L C LYa) in CS.
    rewrite Forall_forall in CS. exact (CS (a0, w0, v0) (L5A.aly_cells L C LYa _ Hin)). }
  split; [apply U64S; [clear; lia| clear; lia| exact C208]|].
  split; [apply U64S; [clear; lia| clear; lia| exact C216]|].
  split; [apply U64S; [clear; lia| clear; lia| exact C224]|].
  split; [apply U64S; [clear; lia| clear; lia| exact C200]|].
  split; [apply U64S; [clear; lia| clear; lia| exact C192]|].
  split; [apply U64S; [clear; lia| clear; lia| exact C184]|].
  split; [apply U64S; [clear; lia| clear; lia| exact C176]|].
  split; [apply U64S; [clear; lia| clear; lia| exact C168]|].
  split; [apply U32S; [clear; lia| clear; lia| exact C120]|].
  split; [exact VM0|]. split; [exact VM1|]. split; [exact VM2|].
  split; [exact SPR|]. split; [exact SP32'|]. split; [exact SWR224|].
  split; [exact OPR|]. split; [exact OP8|]. split; [exact OPBIG|].
  split; [exact Zz0|]. split; [exact Zz1|]. split; [exact Zz2|]. split; [exact Zz3|].
  split; [right; clear - OCE SLO; lia|].
  split; [exact FR|]. split; [exact F32|]. split; [exact FD3|]. split; [exact FW3|]. split; [exact FBIG|]. split; [exact FSW3|].
  split; [exact FLC3|]. split; [exact FLR|]. split; [exact FLW3|]. split; [exact FLBIG|]. split; [exact FFLA|].
  split; [right; clear - GFCEIL SLO; lia|].
  split; [right; clear - GFLR SLO; lia|].
  split; [exact APF|]. split; [exact APFL|]. split; [exact APS|].
  split; [apply U64S; [clear; lia| clear; lia| exact C136]|].
  split; [apply U64S; [clear; lia| clear; lia| exact C144]|].
  split; [exact SWR4096|].
  split.
  { match goal with |- L5.u64_at RSEGS _ ?x ?v =>
      apply (proj2 (L5A.u64_at_vis H3 M3 x v (VIMG3 x 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)));
      exact (D4 x 8 v ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 4 right; left; reflexivity)) end. }
  split.
  { apply (proj2 (L5A.writable_vis H3 M3 (op + 392) 24 (L5A.avis_sub H3 op 424 (op + 392) 24 OVIS3 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - OB0; lia) ltac:(clear - OB2; lia))).
    apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M3 op 424); [exact ODEF3| clear; lia| clear; lia]| clear - OB0; lia| clear - OB2; lia]. }
  split; [right; clear - OCE SLO; lia|].
  apply U64S; [clear; lia| clear; lia| exact C112].
Qed.

End WithHeap.
End PNABAU1V.
