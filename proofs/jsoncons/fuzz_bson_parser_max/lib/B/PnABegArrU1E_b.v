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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnAReaderCtorKit_b.

Module PNABAU1E.
Import L5A. Import L5CA. Import L5SAR. Import PNBKA. Import PNABAK. Import PNABA.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

Lemma w9_al16_8 a : a mod 16 = 0 -> a mod 8 = 0.
Proof.
  intros H. pose proof (Z.div_mod a 16 ltac:(lia)) as D. rewrite H, Z.add_0_r in D. rewrite D.
  replace (16 * (a / 16)) with (0 + (2 * (a / 16)) * 8) by ring. rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma w9_al40 x : (40 * x) mod 8 = 0.
Proof. replace (40 * x) with (0 + (5 * x) * 8) by ring. rewrite Z.mod_add by lia. reflexivity. Qed.
Lemma w9_al_add a b : a mod 8 = 0 -> b mod 8 = 0 -> (a + b) mod 8 = 0.
Proof. intros Ha Hb. rewrite Z.add_mod by lia. rewrite Ha, Hb. reflexivity. Qed.

Lemma ba_u1e_vec K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 :
  forall s6 sm6 ax6 cr6 (M1 : mem) model1 LK1 Aw1 (M3 : mem) model3 LK3 Aw3,
  ba_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  ba_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  ba_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 (PNBO.set_more s6 1) sm6 ax6 cr6 ->
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
  /\ PNABAP.aligned (PNM.b_sb (PNBO.set_more s6 1)) 8
  /\ 40 <= (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1)))) <= 41000
  /\ PNABAP.aligned (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1)))) 8
  /\ 40 <= (40 * 2 ^ PNM.b_sk (PNBO.set_more s6 1)) <= 81920
  /\ PNABAP.aligned (40 * 2 ^ PNM.b_sk (PNBO.set_more s6 1)) 8
  /\ PNABAP.aligned ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) 8
  /\ 4096 <= ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) <= 140737488355288.
Proof using LY HIok ICok ILY.
  intros s6 sm6 ax6 cr6 M1 model1 LK1 Aw1 M3 model3 LK3 Aw3 HC HF HM HB HS HL HLK V0 V8 V16 BS DB AC AN ACV BOK HP MR IL3 IA AMO RI.
  set (s1 := PNBO.set_more s6 1) in *.
  assert (E1 : PNM.b_stk s1 = PNM.b_stk s6) by reflexivity.
  unfold ba_ctx in HC. destruct HC as (_ & _ & _ & _ & _ & _ & _ & ((rs & Hfb) & Fal) & _).
  assert (FOK : PNRA.frame_okB ((F, 0, sp - 160 + 32) :: FF) fb) by (split; [exists rs; right; exact Hfb | exact Fal]).
  unfold ba_mem in HM. destruct HM as (_ & BRP & _).
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
  assert (B8 : b mod 8 = 0) by exact (w9_al16_8 b AR3).
  split; [apply (PNARCK.fvis L ar C HI LY HIok _ _ _ _ _ _ _ fb _ _ RI FOK); [lia | lia | exact V0]|].
  split; [replace (fb + 464 + 400) with (fb + 464 + 392 + 8) by lia; apply (PNARCK.fvis L ar C HI LY HIok _ _ _ _ _ _ _ fb _ _ RI FOK); [lia | lia | exact V8]|].
  split; [replace (fb + 464 + 408) with (fb + 464 + 392 + 16) by lia; apply (PNARCK.fvis L ar C HI LY HIok _ _ _ _ _ _ _ fb _ _ RI FOK); [lia | lia | exact V16]|].
  split; [lia|]. split; [exact B8|]. split; [lia|]. split; [apply w9_al40|]. split; [lia|]. split; [apply w9_al40|].
  split; [apply w9_al_add; [exact B8 | apply w9_al40]|].
  lia.
Qed.

Lemma ba_u1_elem_ok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 :
  ba_u1_elem_P L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2.
Proof using LY HIok ICok ILY.
  unfold ba_u1_elem_P. intros s6 sm6 ax6 cr6 M1 model1 LK1 Aw1 M3 model3 LK3 Aw3. intros.
  pose proof (ba_u1e_vec K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 s6 sm6 ax6 cr6 M1 model1 LK1 Aw1 M3 model3 LK3 Aw3) as GV.
  pose proof (PNABAU1E1.ba_u1e_zeros L ar C IL HI LY HIok ICok ILY K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 s6 sm6 ax6 cr6 M1 model1 LK1 Aw1 M3 model3 LK3 Aw3) as GS.
  pose proof (PNABAU1E2.ba_u1e_disj L ar C IL HI LY HIok ICok ILY K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 s6 sm6 ax6 cr6 M1 model1 LK1 Aw1 M3 model3 LK3 Aw3) as GD.
  repeat (specialize (GV ltac:(assumption))). repeat (specialize (GS ltac:(assumption))). repeat (specialize (GD ltac:(assumption))).
  destruct GV as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V13 & V22).
  destruct GS as (V10 & V11 & V12 & V14 & V15 & V16 & V17).
  destruct GD as (V18 & V19 & V20 & V21 & V23 & V24 & V25).
  repeat (split; [assumption|]); assumption.
Qed.

End WithHeap.
End PNABAU1E.
