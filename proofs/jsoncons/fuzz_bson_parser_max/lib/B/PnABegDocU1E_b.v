(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
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

From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnABegDoc_b PnAEmbKit_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnAReaderCtorKit_b.

Module PNABDU1E.
Import L5A. Import L5CA. Import L5SAR. Import PNBKA. Import PNABDK. Import PNABD.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

Lemma x11_al16_8 a : a mod 16 = 0 -> a mod 8 = 0.
Proof.
  intros H. pose proof (Z.div_mod a 16 ltac:(lia)) as D. rewrite H, Z.add_0_r in D. rewrite D.
  replace (16 * (a / 16)) with (0 + (2 * (a / 16)) * 8) by ring. rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma x11_al40 x : (40 * x) mod 8 = 0.
Proof. replace (40 * x) with (0 + (5 * x) * 8) by ring. rewrite Z.mod_add by lia. reflexivity. Qed.
Lemma x11_al_add a b : a mod 8 = 0 -> b mod 8 = 0 -> (a + b) mod 8 = 0.
Proof. intros Ha Hb. rewrite Z.add_mod by lia. rewrite Ha, Hb. reflexivity. Qed.

Lemma bd_u1e_zeros K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 :
  forall s6 sm6 ax6 cr6 (M1 : mem) model1 LK1 Aw1 (M3 : mem) model3 LK3 Aw3,
  bd_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  bd_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 (PNBO.set_more s6 1) sm6 ax6 cr6 ->
  PNRA.binv s6 -> PNM.b_stk s6 = PNM.b_stk s -> Z.of_nat (length (PNM.b_stk s6)) <= 1024 -> Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))) < 2 ^ PNM.b_sk (PNBO.set_more s6 1) ->
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
  L5KA.zeros_at (mrestrict (ahid Aw3 model3) M3) ((sp / 8) + 2147450368) 512
  /\ L5KA.zeros_at (mrestrict (ahid Aw3 model3) M3) ((((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) / 8) + 2147450880) 5
  /\ L5.writable RSEGS (mrestrict (ahid Aw3 model3) M3) ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) 40
  /\ L5KA.zeros_at (mrestrict (ahid Aw3 model3) M3) (((((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) + 8) / 8) + 2147450880) 1
  /\ L5KA.zeros_at (mrestrict (ahid Aw3 model3) M3) (((((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) + 16) / 8) + 2147450880) 1
  /\ L5KA.zeros_at (mrestrict (ahid Aw3 model3) M3) (((((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) + 24) / 8) + 2147450880) 1
  /\ L5KA.zeros_at (mrestrict (ahid Aw3 model3) M3) (((((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) + 32) / 8) + 2147450880) 1.
Proof using LY HIok ICok ILY.
  intros s6 sm6 ax6 cr6 M1 model1 LK1 Aw1 M3 model3 LK3 Aw3 CTX G LM INV6 ESTK DEPTH NFULL V0' V8' V16' BST3 DEF3 ACC3 ANN3 ACCV3 BASE3 HP3 MRT3 INC3 INCA3 AM3 HH3.
  set (s1 := PNBO.set_more s6 1) in *.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 7) with 26624 in *. change (26624 / 8) with 3328 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  pose proof LM as (BI & RP1 & _).
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  pose proof RP1 as (PA1 & _).
  pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SV1 & _).
  pose proof SV1 as (_ & _ & _ & Hk & Hlen & Hal & _).
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
  { apply (PMKA.stksh_keepA L ar (rest_own s1 ++ LBX) ((F, 0, sp - 160 + 32) :: FF) (sp - 224) (PMSPA.pm_scr 0) [] M1 M3 (proj1 HP3) PMKA.wapp_nil (sp - 26624) 3328);
      [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| exact SP8| clear; lia| exact SZ1]. }
  assert (SZ12 : shadow_zero M3 (sp - 12288) 1536).
  { apply (PMKA.shadow_zero_sub M3 (sp - 26624) 3328); [exact SP8| | clear; lia| clear; lia| clear; lia| exact SZ3].
    apply PMKA.mod16_8'. replace (sp - 12288) with (sp + (-768) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  pose proof (L5SAR.vis_pack L ar C HI (PMA.ly_as0 L C LY) HIok _ _ LK3 cr6 Aw3 M3 model3 HH3) as (_ & _ & _ & _ & VBLK3 & VBSH3 & _ & VSTSH3).
  cbv zeta in VBLK3, VBSH3, VSTSH3.
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH3) as BRB3.
  set (H3 := ahid Aw3 model3) in *.
  set (b := PNM.b_sb s1) in *. set (k := PNM.b_sk s1) in *. set (n := Z.of_nat (length (PNM.b_stk s1))) in *.
  assert (N0 : 0 <= n) by (unfold n; apply Nat2Z.is_nonneg).
  assert (B8 : b mod 8 = 0) by (apply PMFA.mod16_8; exact Hal).
  assert (K8 : (40 * 2 ^ k) mod 8 = 0) by (replace (40 * 2 ^ k) with ((5 * 2 ^ k) * 8) by (clear; lia); apply Z_mod_mult).
  assert (N8 : (40 * n) mod 8 = 0) by (replace (40 * n) with ((5 * n) * 8) by (clear; lia); apply Z_mod_mult).
  assert (BIN3 : In (b, 40 * 2 ^ k) (PNM.bvec_own b k ++ rest_own s1 ++ LBX)) by (apply in_or_app; left; left; reflexivity).
  destruct (BRB3 _ BIN3) as (BR0 & BR1). cbn [fst snd] in BR0, BR1.
  unfold PMSPA.annA, HAJ.ann_shadow in ANN3. destruct ANN3 as (ZA & _ & _).
  rewrite Z.mul_add_distr_l, Z.mul_1_r, PnAEmbKit_b.PNAEK.d40b in ZA.
  assert (BQ : forall q, (b + q * 8) mod 8 = 0) by (intros q; rewrite Z_mod_plus_full; exact B8).
  assert (ZF : forall a m, a mod 8 = 0 -> b + 40 * n <= a -> a + 8 * m <= b + 40 * n + 40 -> L5KA.zeros_at (mrestrict H3 M3) (a / 8 + SB) m).
  { intros a m A8 Ha1 Ha2 i Hi.
    pose proof (Z.div_mod a 8 ltac:(clear; lia)) as Da. pose proof (Z.div_mod b 8 ltac:(clear; lia)) as Db. rewrite A8 in Da. rewrite B8 in Db.
    assert (Hj : 0 <= a / 8 - b / 8 + i < 5 * n + 5) by (clear - Da Db Ha1 Ha2 Hi N0; lia).
    replace (a / 8 + SB + i) with (S b + (a / 8 - b / 8 + i)) by (unfold S; clear; lia).
    rewrite (AsanAcct.mrestrict_visible H3 M3).
    - apply ZA. exact Hj.
    - assert (AV : L5A.avis H3 (S b + (a / 8 - b / 8 + i)) 1).
      { apply (VBSH3 b (40 * 2 ^ k) _ 1 BIN3). intros j Hj'. replace (S b + (a / 8 - b / 8 + i) + j) with (S b + (a / 8 - b / 8 + i + j)) by (clear; lia).
        apply PnAEmbKit_b.PNAEK.sh_in; [exact B8| exact K8| exact BR0|]. rewrite PnAEmbKit_b.PNAEK.d40. clear - Hj Hj' NFULL; lia. }
      pose proof (AV 0 ltac:(clear; lia)) as X. rewrite Z.add_0_r in X. exact X. }
  split.
  {
    intros i Hi. rewrite (AsanAcct.mrestrict_visible H3 M3).
    - apply (PnAEmbKit_b.PNAEK.stack_zeros12 M3 sp SZ12 A16). exact Hi.
    - match goal with |- _ (Z_to_bv 64 ?x) = false => assert (AV : L5A.avis H3 x 1) end.
      { apply VSTSH3. intros j Hj. unfold in_shadow_of, S, SB. clear - SLO SHI A16 Hi Hj.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      pose proof (AV 0 ltac:(clear; lia)) as X. rewrite Z.add_0_r in X. exact X. }
  split; [exact (ZF (b + 40 * n) 5 ltac:(replace (b + 40 * n) with (b + (5 * n) * 8) by (clear; lia); apply BQ) ltac:(clear; lia) ltac:(clear; lia))|].
  split.
  { apply (proj2 (L5A.writable_vis H3 M3 (b + 40 * n) 40 (VBLK3 b (40 * 2 ^ k) (b + 40 * n) 40 BIN3 ltac:(clear - N0; lia) ltac:(clear - NFULL; lia)) ltac:(clear - BR0 N0; lia) ltac:(clear - BR1 NFULL; lia))).
    apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M3 b (40 * 2 ^ k)); [exact DEF3| clear - N0; lia| clear - NFULL; lia]| clear - BR0 N0; lia| clear - BR1 NFULL; lia]. }
  split; [exact (ZF (b + 40 * n + 8) 1 ltac:(replace (b + 40 * n + 8) with (b + (5 * n + 1) * 8) by (clear; lia); apply BQ) ltac:(clear; lia) ltac:(clear; lia))|].
  split; [exact (ZF (b + 40 * n + 16) 1 ltac:(replace (b + 40 * n + 16) with (b + (5 * n + 2) * 8) by (clear; lia); apply BQ) ltac:(clear; lia) ltac:(clear; lia))|].
  split; [exact (ZF (b + 40 * n + 24) 1 ltac:(replace (b + 40 * n + 24) with (b + (5 * n + 3) * 8) by (clear; lia); apply BQ) ltac:(clear; lia) ltac:(clear; lia))|].
  exact (ZF (b + 40 * n + 32) 1 ltac:(replace (b + 40 * n + 32) with (b + (5 * n + 4) * 8) by (clear; lia); apply BQ) ltac:(clear; lia) ltac:(clear; lia)).
Qed.

Lemma bd_u1e_disj K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 :
  forall s6 sm6 ax6 cr6 (M1 : mem) model1 LK1 Aw1 (M3 : mem) model3 LK3 Aw3,
  bd_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  bd_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 (PNBO.set_more s6 1) sm6 ax6 cr6 ->
  PNRA.binv s6 -> PNM.b_stk s6 = PNM.b_stk s -> Z.of_nat (length (PNM.b_stk s6)) <= 1024 -> Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))) < 2 ^ PNM.b_sk (PNBO.set_more s6 1) ->
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
  (2147446784 + 17592186048512 <= ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) \/ ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) + 40 <= 2147446784)
  /\ ((sp - 224) + 224 <= ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) \/ ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) + 40 <= (sp - 224))
  /\ (((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) + 40 <= F \/ F + 64 <= ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))))
  /\ (((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) + 40 <= fl \/ fl + 1 <= ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))))
  /\ (65536 + 6840320 <= ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) \/ ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) + 40 <= 65536)
  /\ ((sp - 4096) + 4096 <= ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) \/ ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) + 40 <= (sp - 4096))
  /\ ((fb + 464) + 416 <= ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) \/ ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) + 40 <= (fb + 464))
  /\ ((fb + 432) + 8 <= ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) \/ ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) + 40 <= (fb + 432)).
Proof using LY HIok ICok ILY.
  intros s6 sm6 ax6 cr6 M1 model1 LK1 Aw1 M3 model3 LK3 Aw3 CTX G MEM BINV STK6 LEN6 LT6 V0 V8 V16 ELS DEF3 ACC3 ANN3 ACCV BASE3 HP3 MRT3 INC3 INCA3 AM3 HH3.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & _).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH).
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *.
  unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  pose proof (PMA.ly_as0 L C LY) as LYa0.
  rewrite (L5A.aly_img_lo L C LYa0), (L5A.aly_img_hi L C LYa0) in FSIMG.
  pose proof FSAPP as (FA0 & FA1 & FA2).
  pose proof G as G'. unfold bd_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 0) with 64 in *. unfold FS_BYTES in GFS2, GFLP.
  set (b6 := PNM.b_sb (PNBO.set_more s6 1)) in *. set (k6 := PNM.b_sk (PNBO.set_more s6 1)) in *.
  set (n6 := Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1)))) in *.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH3) as (WB3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  assert (INV : In (b6, PNM.BSZ * 2 ^ k6) (PNM.bvec_own b6 k6 ++ rest_own (PNBO.set_more s6 1) ++ LBX)).
  { apply in_or_app. left. unfold PNM.bvec_own. cbn [In]. left. reflexivity. }
  pose proof (WB3 _ INV) as (BR & _ & _ & _ & _ & _ & BFS). cbn [fst snd] in BR, BFS.
  unfold ablock_range, app_mem in BR. destruct BR as (B0 & BIMG & B16 & BPOS & BCEIL & BA0 & BA1 & BA2).
  rewrite (L5A.aly_img_lo L C LYa0), (L5A.aly_img_hi L C LYa0) in BIMG.
  unfold FS_BYTES in BFS.
  assert (N0 : 0 <= n6) by (unfold n6; lia).
  assert (NK : n6 + 1 <= 2 ^ k6) by (unfold n6 in *; lia).
  assert (BSZ : PNM.BSZ * 2 ^ k6 = 40 * 2 ^ k6) by (unfold PNM.BSZ; reflexivity).
  rewrite BSZ in BIMG, BPOS, BCEIL, BA1, BA2, BFS.
  assert (EIN : b6 <= b6 + 40 * n6 /\ b6 + 40 * n6 + 40 <= b6 + 40 * 2 ^ k6) by lia.
  pose proof (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ b6 (40 * 2 ^ k6) (fb + 464) 416 HH3
                ltac:(rewrite <- BSZ; exact INV)
                (PMAUAR.aobjA_push FF (fb + 464) 416 _ (PNAPAR.aobj_fbB FF fb (fb + 464) 416 FOK ltac:(lia) ltac:(lia)))) as OBJ.
  unfold BIGSHADOW_LO, BIGSHADOW_HI in BA1.
  assert (HfbF : In (fb, 5, rs) ((F, 0, sp - 160 + 32) :: FF)) by (right; exact Hfb).
  destruct (PNAEK.blk_facts L ar C HI LY HIok _ _ _ _ _ M3 _ b6 (PNM.BSZ * 2 ^ k6) HH3 INV) as (_ & _ & _ & _ & _ & _ & _ & _ & Bq8).
  pose proof (Bq8 _ HfbF) as VFB. cbn [ff_addr ff_class fst snd] in VFB. change (ff_bytes 5) with 2048 in VFB. rewrite BSZ in VFB.
  destruct VFB as [VF|VF]; repeat split; lia.
Qed.

Lemma bd_u1e_vec K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 :
  forall s6 sm6 ax6 cr6 (M1 : mem) model1 LK1 Aw1 (M3 : mem) model3 LK3 Aw3,
  bd_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  bd_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 (PNBO.set_more s6 1) sm6 ax6 cr6 ->
  PNRA.binv s6 -> PNM.b_stk s6 = PNM.b_stk s -> Z.of_nat (length (PNM.b_stk s6)) <= 1024 -> Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))) < 2 ^ PNM.b_sk (PNBO.set_more s6 1) ->
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
  L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) ((fb + 464) + 392) (PNM.b_sb (PNBO.set_more s6 1))
  /\ L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) ((fb + 464) + 400) ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1)))))
  /\ L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) ((fb + 464) + 408) ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * 2 ^ PNM.b_sk (PNBO.set_more s6 1)))
  /\ 4096 <= (PNM.b_sb (PNBO.set_more s6 1)) <= 140737488314328
  /\ PNABDP.aligned (PNM.b_sb (PNBO.set_more s6 1)) 8
  /\ 40 <= (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1)))) <= 41000
  /\ PNABDP.aligned (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1)))) 8
  /\ 40 <= (40 * 2 ^ PNM.b_sk (PNBO.set_more s6 1)) <= 81920
  /\ PNABDP.aligned (40 * 2 ^ PNM.b_sk (PNBO.set_more s6 1)) 8
  /\ PNABDP.aligned ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) 8
  /\ 4096 <= ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) <= 140737488355288.
Proof using LY HIok ICok ILY.
  intros s6 sm6 ax6 cr6 M1 model1 LK1 Aw1 M3 model3 LK3 Aw3 HC HF HM HB HS HL HLK V0 V8 V16 BS DB AC AN ACV BOK HP MR IL3 IA AMO RI.
  set (s1 := PNBO.set_more s6 1) in *.
  assert (E1 : PNM.b_stk s1 = PNM.b_stk s6) by reflexivity.
  unfold bd_ctx in HC. destruct HC as (_ & _ & _ & _ & _ & _ & _ & ((rs & Hfb) & Fal) & _).
  assert (FOK : PNRA.frame_okB ((F, 0, sp - 160 + 32) :: FF) fb) by (split; [exists rs; right; exact Hfb | exact Fal]).
  unfold bd_mem in HM. destruct HM as (_ & BRP & _).
  unfold PNRA.brun_pre in BRP. destruct BRP as (BPA & _).
  unfold PNM.bparser_at in BPA.
  destruct BPA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BV & _).
  unfold PNM.bvec_at in BV. destruct BV as (_ & _ & _ & (K0 & K11) & _ & _ & _).
  unfold PNRA.binv, PNRA.bstack_shape in HB. destruct HB as (_ & HL1 & _).
  rewrite <- E1 in HL1, HL.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ RI) as (WB & _ & _ & _ & _ & _ & _ & (CB1 & _) & (_ & ST2 & _) & ST5 & _).
  assert (Hin : In (PNM.b_sb s1, PNM.BSZ * 2 ^ PNM.b_sk s1) (PNM.bvec_own (PNM.b_sb s1) (PNM.b_sk s1) ++ rest_own s1 ++ LBX))
    by (apply in_or_app; left; left; reflexivity).
  destruct (WB _ Hin) as (AR & _). cbn [fst snd] in AR. unfold ablock_range, PNM.BSZ in AR.
  destruct AR as (AR1 & _ & AR3 & _ & AR5 & _).
  set (b := PNM.b_sb s1) in *. set (k := PNM.b_sk s1) in *. set (n := Z.of_nat (length (PNM.b_stk s1))) in *.
  assert (N1 : 1 <= n) by (unfold n; lia).
  assert (P11 : 2 ^ k <= 2 ^ 11) by (apply Z.pow_le_mono_r; lia).
  replace (2 ^ 11) with 2048 in P11 by reflexivity.
  assert (B8 : b mod 8 = 0) by exact (x11_al16_8 b AR3).
  split; [apply (PNARCK.fvis L ar C HI LY HIok _ _ _ _ _ _ _ fb _ _ RI FOK); [lia | lia | exact V0]|].
  split; [replace (fb + 464 + 400) with (fb + 464 + 392 + 8) by lia; apply (PNARCK.fvis L ar C HI LY HIok _ _ _ _ _ _ _ fb _ _ RI FOK); [lia | lia | exact V8]|].
  split; [replace (fb + 464 + 408) with (fb + 464 + 392 + 16) by lia; apply (PNARCK.fvis L ar C HI LY HIok _ _ _ _ _ _ _ fb _ _ RI FOK); [lia | lia | exact V16]|].
  split; [lia|]. split; [exact B8|]. split; [lia|]. split; [apply x11_al40|]. split; [lia|]. split; [apply x11_al40|].
  split; [apply x11_al_add; [exact B8 | apply x11_al40]|].
  lia.
Qed.

Lemma bd_u1_elem_ok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 :
  bd_u1_elem_T L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2.
Proof using LY HIok ICok ILY.
  unfold bd_u1_elem_T. intros s6 sm6 ax6 cr6 M1 model1 LK1 Aw1 M3 model3 LK3 Aw3. intros.
  pose proof (bd_u1e_vec K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 s6 sm6 ax6 cr6 M1 model1 LK1 Aw1 M3 model3 LK3 Aw3) as GV.
  pose proof (bd_u1e_zeros K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 s6 sm6 ax6 cr6 M1 model1 LK1 Aw1 M3 model3 LK3 Aw3) as GS.
  pose proof (bd_u1e_disj K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 s6 sm6 ax6 cr6 M1 model1 LK1 Aw1 M3 model3 LK3 Aw3) as GD.
  repeat (specialize (GV ltac:(assumption))). repeat (specialize (GS ltac:(assumption))). repeat (specialize (GD ltac:(assumption))).
  destruct GV as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V13 & V22).
  destruct GS as (V10 & V11 & V12 & V14 & V15 & V16 & V17).
  destruct GD as (V18 & V19 & V20 & V21 & V23 & V24 & V25 & V26).
  repeat (split; [assumption|]); assumption.
Qed.

End WithHeap.
End PNABDU1E.
