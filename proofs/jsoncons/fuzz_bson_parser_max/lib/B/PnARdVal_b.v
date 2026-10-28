(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5CoreSpecsA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParSpecs PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnModelFacts PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnASrcKit_b PmAUarK_b PmAUar_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrObj. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrObjA_b PnAParKit_b PnAReset1_b PnOwnerOkA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG AsanPlanSoundSums. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrKitA_b PnARvTP_b PnARvK_b PnARvKV_b PnARvE_b PnARvF_b PnARvA1_b PnARvA18_b PnARvA9_b PnARvA16_b PnARvA17_b PnARvA8_b PnARvN_b PnARvS_b PnSpecsAXD_b PnARvKD_b PnARvB_b PnARvX_b PnARvD_b PnARvO_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNARVL.
Import L5A. Import L5CA. Import L5SAR. Import PNBKA. Import PNARVK.

Lemma tsplit t : 0 <= t < 256 ->
  t = 1 \/ t = 2 \/ t = 3 \/ t = 4 \/ t = 5 \/ t = 6 \/ t = 7 \/ t = 8 \/ t = 9 \/ t = 10 \/ t = 11 \/ t = 12 \/ t = 13 \/ t = 14 \/ t = 15
  \/ t = 16 \/ t = 17 \/ t = 18 \/ t = 19 \/ t = 127 \/ t = 255 \/ t = 0 \/ (20 <= t <= 126) \/ (128 <= t <= 254).
Proof. intros Ht. Lia.lia. Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.

(* [comment removed for export] *)
Definition arm_stmt (t : Z) : Prop :=
  forall K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 (fx3 : FPState) R3 M3 model3 LK3 Aw3,
    rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax t -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
    rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s sm ax cr ->
    PNARVE.dregs R R3 sp fb t F -> PMSPA.ec_at RSEGS M3 (fb + 1024) e cat ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb016c M3 model3) K.


Theorem read_value_ok :
  PNRAa.src_read_spec L ar HI -> PNRAa.make_ec_spec L ar HI -> PNRAa.begin_document_spec L ar HI -> PNRAa.begin_array_spec L ar HI ->
  PNRAa.read_string_spec L ar HI -> PMA.validate_spec L ar HI ->
  PNRAa.read_span_v_spec L ar HI ->
  PNRAa.str_push_back_spec L ar HI ->
  PNRAa.read_cstring_spec L ar HI ->
  PMA.str_resize_spec L ar HI ->
  PNSAXD.dec128_spec RSEGS PMA.AD PMA.AN PMA.AAD L ar HI ->
  PNRAa.read_value_spec L ar HI.
Proof.
  intros SR MKE BDOC BARR RSTR VAL RSV PB RCS RSZ DECS. apply (PNARVE.rv_entry L ar C HI LY HIok).
  intros K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax t F fl LK2 M2 model2 fx3 R3 M3 model3 CTX G LM DR SPL EC3.
  pose proof CTX as (Ht & _).
  destruct (tsplit t Ht) as [Et|[Et|[Et|[Et|[Et|[Et|[Et|[Et|[Et|[Et|[Et|[Et|[Et|[Et|[Et|[Et|[Et|[Et|[Et|[Et|[Et|[Et|[Et|Et]]]]]]]]]]]]]]]]]]]]]]].
  - subst t. exact (PNARVA1.arm L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 fx3 R3 M3 model3 LK2 Aw SR MKE CTX G LM DR EC3).
  - subst t. apply (PNARVS.disp2 L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 fx3 R3 M3 model3 LK2 Aw CTX G LM DR); intros fxj Rj modelj LMj MIDj; exact (PNARVS.arm_str2 L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 2 F fl LK2 M2 model2 fxj Rj M3 modelj LK2 Aw RSTR VAL MKE CTX G LMj MIDj EC3).
  - subst t. apply (PNARVN.disp3 L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 fx3 R3 M3 model3 LK2 Aw CTX G LM DR); intros fxj Rj modelj LMj MIDj; exact (PNARVN.arm_cont3 L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 fxj Rj M3 modelj LK2 Aw BDOC CTX G LMj MIDj EC3).
  - subst t. apply (PNARVN.disp4 L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 fx3 R3 M3 model3 LK2 Aw CTX G LM DR); intros fxj Rj modelj LMj MIDj; exact (PNARVN.arm_cont4 L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 fxj Rj M3 modelj LK2 Aw BARR CTX G LMj MIDj EC3).
  - subst t. apply (PNARVB.disp5 L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 fx3 R3 M3 model3 LK2 Aw CTX G LM DR); intros fxj Rj modelj LMj MIDj; exact (PNARVB.arm_bin L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 fxj Rj M3 modelj LK2 Aw SR RSV MKE CTX G LMj MIDj EC3).
  - subst t. apply (PNARVN.disp6 L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 fx3 R3 M3 model3 LK2 Aw CTX G LM DR); intros fxj Rj modelj LMj MIDj; exact (PNARVN.arm_null6 L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 fxj Rj M3 modelj LK2 Aw CTX G LMj MIDj EC3).
  - subst t. exact (PNARVO.arm_oid L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 fx3 R3 M3 model3 LK2 Aw SR MKE RSZ CTX G LM DR EC3).
  - subst t. exact (PNARVA8.arm L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 fx3 R3 M3 model3 LK2 Aw SR MKE CTX G LM DR EC3).
  - subst t. exact (PNARVA9.arm L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 fx3 R3 M3 model3 LK2 Aw SR MKE CTX G LM DR EC3).
  - subst t. apply (PNARVN.disp10 L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 fx3 R3 M3 model3 LK2 Aw CTX G LM DR); intros fxj Rj modelj LMj MIDj; exact (PNARVN.arm_null10 L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 fxj Rj M3 modelj LK2 Aw CTX G LMj MIDj EC3).
  - subst t. apply (PNARVX.disp11 L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 fx3 R3 M3 model3 LK2 Aw CTX G LM DR); intros fxj Rj modelj LMj MIDj; exact (PNARVX.arm_rx L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 fxj Rj M3 modelj LK2 Aw PB RCS CTX G LMj MIDj EC3).
  - subst t. apply (PNARVN.disp12 L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 fx3 R3 M3 model3 LK2 Aw CTX G LM DR); intros fxj Rj modelj LMj MIDj; exact (PNARVN.arm_unk L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 12 F fl LK2 M2 model2 fxj Rj M3 modelj LK2 Aw MKE CTX G LMj MIDj EC3).
  - subst t. apply (PNARVS.disp13 L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 fx3 R3 M3 model3 LK2 Aw CTX G LM DR); intros fxj Rj modelj LMj MIDj; exact (PNARVS.arm_str13 L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 13 F fl LK2 M2 model2 fxj Rj M3 modelj LK2 Aw RSTR VAL MKE CTX G LMj MIDj EC3).
  - subst t. apply (PNARVS.disp14 L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 fx3 R3 M3 model3 LK2 Aw CTX G LM DR); intros fxj Rj modelj LMj MIDj; exact (PNARVS.arm_str2 L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 14 F fl LK2 M2 model2 fxj Rj M3 modelj LK2 Aw RSTR VAL MKE CTX G LMj MIDj EC3).
  - subst t. apply (PNARVN.disp15 L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 fx3 R3 M3 model3 LK2 Aw CTX G LM DR); intros fxj Rj modelj LMj MIDj; exact (PNARVN.arm_unk L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 15 F fl LK2 M2 model2 fxj Rj M3 modelj LK2 Aw MKE CTX G LMj MIDj EC3).
  - subst t. exact (PNARVA16.arm L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 fx3 R3 M3 model3 LK2 Aw SR MKE CTX G LM DR EC3).
  - subst t. exact (PNARVA17.arm L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 fx3 R3 M3 model3 LK2 Aw SR MKE CTX G LM DR EC3).
  - subst t. exact (PNARVA18.arm L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 fx3 R3 M3 model3 LK2 Aw SR MKE CTX G LM DR EC3).
  - subst t. apply (PNARVD.disp19 L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 fx3 R3 M3 model3 LK2 Aw CTX G LM DR); intros fxj Rj modelj LMj MIDj; exact (PNARVD.arm_dec L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 fxj Rj M3 modelj LK2 Aw SR RSZ DECS MKE CTX G LMj MIDj EC3).
  - subst t. apply (PNARVS.disp127 L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 fx3 R3 M3 model3 LK2 Aw CTX G LM DR); intros fxj Rj modelj LMj MIDj; exact (PNARVS.arm_str2 L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 127 F fl LK2 M2 model2 fxj Rj M3 modelj LK2 Aw RSTR VAL MKE CTX G LMj MIDj EC3).
  - subst t. apply (PNARVS.disp255 L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 fx3 R3 M3 model3 LK2 Aw CTX G LM DR); intros fxj Rj modelj LMj MIDj; exact (PNARVS.arm_str2 L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 255 F fl LK2 M2 model2 fxj Rj M3 modelj LK2 Aw RSTR VAL MKE CTX G LMj MIDj EC3).
  - subst t. apply (PNARVN.disp0 L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 fx3 R3 M3 model3 LK2 Aw CTX G LM DR); intros fxj Rj modelj LMj MIDj; exact (PNARVN.arm_unk L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 0 F fl LK2 M2 model2 fxj Rj M3 modelj LK2 Aw MKE CTX G LMj MIDj EC3).
  - rename Et into HR. apply (PNARVN.dispr1 L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax t F fl LK2 M2 model2 fx3 R3 M3 model3 LK2 Aw CTX G HR LM DR); intros fxj Rj modelj LMj MIDj; exact (PNARVN.arm_unk L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax t F fl LK2 M2 model2 fxj Rj M3 modelj LK2 Aw MKE CTX G LMj MIDj EC3).
  - rename Et into HR. apply (PNARVN.dispr2 L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax t F fl LK2 M2 model2 fx3 R3 M3 model3 LK2 Aw CTX G HR LM DR); intros fxj Rj modelj LMj MIDj; exact (PNARVN.arm_unk L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax t F fl LK2 M2 model2 fxj Rj M3 modelj LK2 Aw MKE CTX G LMj MIDj EC3).
Qed.

End WithHeap.
End PNARVL.
