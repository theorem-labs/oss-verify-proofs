(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PropExec CatExec CatSim SeqExec StreamSim StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5CoreSpecsA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParSpecs PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b PnStepA2_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnModelFacts PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnASrcKit_b PmAUarK_b PmAUar_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnDecFacts. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnSpecsAXD_b PnADec128Defs_b PnADec128K_b PnADec128P8_b PnADec128E_b PnADec128S_b PnADec128G_b PnADec128C1_b PnADec128C2_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.


Module PNADC3.
Import L5A. Import L5CA. Import L5SAR. Import PNADK. Import PNADC1. Import PNADC2.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation mem := (word -> option byte).

Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithHeap.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMA.EXT.
Let LYa := PMA.ly_as0 L C LY.

Theorem cold_ok : PNADS.at_b2 L ar HI -> PNADG.cold_stmt L ar HI.
Proof.
  intros B2 E X COLD fx Rc Mc modelc LKc Ac ST RG.
  pose proof (PNADC1.xgeo L ar HI E X) as (GSLO & GSHI & GSPT & GS32 & GCEIL).
  pose proof ST as (BI & _ & _ & _ & _ & BASE & ERR & _).
  pose proof BI as (HHc & AMc & _ & _ & _ & ASTKc & _). cbn [app] in HHc.
  destruct ERR as (_ & DEC & ATXc). rewrite COLD in DEC.
  cbn [PNST.bdec_ok PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj PMA.AN NADDR_A] in DEC. destruct DEC as (CGI & CGN & _ & _).
  unfold PNSTA.atexit_stA in ATXc. cbn [pa_atexit paa_atexit_f0 paa_atexit_a0 paa_at_cxa_atexit PMA.AAD AADDR_A PMA.AD ADDR_A PNL.pn_drv_call PNL.pn_drv_guard PMA.AN NADDR_A] in ATXc.
  assert (HLEN : (length (PNST.bax_list PMA.AD PMA.AN (vax E)) <= 1)%nat) by (clear - COLD; destruct (vax E); cbn in COLD |- *; first [discriminate COLD | lia]).
  (* [comment removed for export] *)
  apply (PNADC2.phase_inf L ar C IL HI LY HIok ICok ILY EXT E X LKc fx Rc Mc modelc Ac (PNST.bax_list PMA.AD PMA.AN (vax E)) HHc AMc ASTKc BASE RG CGI ATXc ltac:(clear - HLEN; lia)).
  intros fx1 R1 M1 model1 A1 HH1 AM1 RT1 IA1 ASTK1 BASE1 RG1 AG1 DK1 GI1 SI1 ATX1.
  (* [comment removed for export] *)
  assert (CGN1 : L5.img_clear M1 6759168 6759176).
  { intros i Hi. rewrite (PNADC2.xagr_stat L ar C LY E _ _ _ Mc M1 i AG1); [apply CGN; clear - Hi; lia| apply PNADC1.DX_dep; left; unfold PNADC1.DXd; clear - Hi; lia|].
    unfold PNADC2.Dph, PNADC1.DXa. clear - Hi. lia. }
  apply (PNADC2.phase_nan L ar C IL HI LY HIok ICok ILY EXT E X LKc fx1 R1 M1 model1 A1 (PNST.bax_list PMA.AD PMA.AN (vax E) ++ [(874172, 6759112)]) HH1 AM1 ASTK1 BASE1 RG1 CGN1 ATX1).
  { rewrite length_app. cbn [length]. clear - HLEN. lia. }
  intros fx2 R2 M2 model2 A2 HH2 AM2 RT2 IA2 ASTK2 BASE2 RG2 AG2 DK2 GN2 SN2 ATX2.
  assert (ND2 : forall i, 6759112 <= i < 6759144 -> ~ PNADC2.Dph 6759144 6759168 i) by (intros i Hi; unfold PNADC2.Dph, PNADC1.DXa; clear - Hi; lia).
  assert (AGI2 : forall i, 6759112 <= i < 6759144 -> M2 (Z_to_bv 64 i) = M1 (Z_to_bv 64 i)).
  { intros i Hi. apply (PNADC2.xagr_stat L ar C LY E _ _ _ M1 M2 i AG2); [apply PNADC1.DX_dep; left; unfold PNADC1.DXd; clear - Hi; lia| exact (ND2 i Hi)]. }
  apply (B2 E X fx2 R2 M2 model2 LKc A2); [| exact RG2].
  apply (PNADC1.dx_close L ar C HI LY HIok E X Mc modelc LKc Ac M2 model2 A2 ST COLD HH2 AM2).
  - eapply L5LZ.model_rt_trans; [exact RT1| exact RT2].
  - intros x Hx. apply IA2. apply IA1. exact Hx.
  - exact ASTK2.
  - apply (PNADC1.xagr_trans L ar E _ _ _ Mc M1 M2).
    + apply (PNADC1.xagr_mono L ar E _ _ _ _ _ _ Mc M1 AG1); [intros x Hx; exact Hx|]. intros a Da. unfold PNADC2.Dph in Da. unfold PNADC1.DX, PNADC1.DXd. clear - Da. destruct Da as [Y|[Y|Y]]; [left; lia| left; lia| right; exact Y].
    + apply (PNADC1.xagr_mono L ar E _ _ _ _ _ _ M1 M2 AG2); [intros x Hx; exact Hx|]. intros a Da. unfold PNADC2.Dph in Da. unfold PNADC1.DX, PNADC1.DXd. clear - Da. destruct Da as [Y|[Y|Y]]; [left; lia| left; lia| right; exact Y].
  - exact (PNADC1.xdkl_trans L ar E _ _ Mc M1 M2 DK1 DK2).
  - cbn [PNST.bdec_ok PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj PMA.AN NADDR_A].
    destruct SI1 as (SI1a & SI1b).
    split; [apply (L5C.u8_at_agree RSEGS M1 M2); [intros i Hi; apply AGI2; clear - Hi; lia| clear; lia| clear; lia| exact GI1]|].
    split; [exact GN2|]. split; [| exact SN2].
    split; [apply (L5C.u8_at_agree RSEGS M1 M2); [intros i Hi; apply AGI2; clear - Hi; lia| clear; lia| clear; lia| exact SI1a]|].
    intros i Hi. rewrite AGI2 by (clear - Hi; lia). exact (SI1b i Hi).
  - unfold PNSTA.atexit_stA. cbn [pa_atexit paa_atexit_f0 paa_atexit_a0 paa_at_cxa_atexit PMA.AAD AADDR_A PMA.AD ADDR_A PNL.pn_drv_call PNL.pn_drv_guard PMA.AN NADDR_A].
    replace (PNST.bax_list ADDR_A NADDR_A (PNST.bax_add_dec (vax E))) with ((PNST.bax_list PMA.AD PMA.AN (vax E) ++ [(874172, 6759112)]) ++ [(874172, 6759144)]); [exact ATX2|].
    clear - COLD. destruct (vax E); cbn in COLD |- *; first [discriminate COLD | reflexivity].
Qed.

End WithHeap.
End SCFG_1.
End PNADC3.
