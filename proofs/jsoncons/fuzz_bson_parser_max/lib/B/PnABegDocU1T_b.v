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

Module PNABDU1T.
Import L5A. Import L5CA. Import L5SAR. Import PNBKA. Import PNABDK. Import PNABD.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.

(* The parser's vector block [sb, sb + 40 * 2^sk) lies below 2^47 (heap block bound from ri_inv's own list). *)
Lemma u1t_vecblk K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 :
  bd_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  bd_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  PNM.b_sb s1 + 40 * 2 ^ PNM.b_sk s1 < 2 ^ 47.
Proof.
  intros CTX G LM.
  pose proof LM as (BI & _).
  pose proof BI as (HH1 & _).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (WB1 & _ & _ & _ & _ & _ & _ & (CEB1 & _) & (_ & STT & _) & STOP & _).
  assert (ISB : In (PNM.b_sb s1, PNM.BSZ * 2 ^ PNM.b_sk s1) (PNM.bparser_own s1 ++ LBX)) by (apply in_or_app; left; exact (PNBOA.PNM_own_stk s1)).
  pose proof (WB1 _ ISB) as ((Sb0 & _ & _ & _ & Sb4 & _) & _). cbn [fst snd] in Sb0, Sb4.
  clear - Sb0 Sb4 CEB1 STT STOP. unfold PNM.BSZ in Sb4. lia.
Qed.

(* Tail of the U1 arm: from abdT's pc 0xaebb4 (after abdU) with the pushed element BS 2 lenv 4 0 0, by bd_tail. *)
Lemma bd_u1_tail_ok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 :
  bd_u1_tail L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2.
Proof.
  unfold bd_u1_tail.
  intros s6 sm6 ax6 M7 model7 LK7 Aw7 cr7 fx7 R7 lenv CTX G LM ER SPL C144 X10 EC7 LENV INV6 ESTK DEPTH NFULL UNR6.
  set (c := PNM.BS 2 lenv 4 0 0) in *.
  set (s7 := set_vec (PNBO.set_more s6 1) (PNM.b_sb s6) (PNM.b_sk s6) (PNM.b_stk s6 ++ [c])) in *.
  assert (OKc : PNM.bstate_ok c) by (unfold PNM.bstate_ok, c; cbn [PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx]; clear - LENV; lia).
  assert (MCc : PNRA.bmode_cont (PNM.bs_mode c)) by (left; reflexivity).
  assert (INV7 : PNRA.binv s7).
  { destruct INV6 as (ID6 & SH6). split; [unfold s7, set_vec; cbn [PNM.b_done PNBO.set_more]; exact ID6|].
    unfold s7, set_vec. cbn [PNM.b_stk]. apply bstack_shape_push; [exact SH6| unfold PNM.MAX_DEPTH; exact DEPTH| exact OKc| exact MCc]. }
  pose proof (vecfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M7 model7 LK7 Aw7 s7 sm6 ax6 cr7 CTX G LM INV7)
    as (_ & VE7 & _ & RB41 & AL41 & _ & _ & _).
  pose proof (u1t_vecblk K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M7 model7 LK7 Aw7 s7 sm6 ax6 cr7 CTX G LM) as BTOP.
  unfold s7, set_vec in VE7, RB41, AL41, BTOP. cbn [PNM.b_sb PNM.b_sk PNM.b_stk] in VE7, RB41, AL41, BTOP.
  rewrite length_app in VE7. cbn [length] in VE7. rewrite Nat2Z.inj_add in VE7.
  assert (XV : bv_unsigned (getr R7 (reg 10)) = PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6)) + 40).
  { rewrite X10. apply bvu_small64. clear - RB41 BTOP NFULL. lia. }
  apply (bd_tail L ar C IL HI LY HIok ICok ILY K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M7 model7 LK7 Aw7 s7 sm6 ax6 cr7 fx7 R7
           CTX G LM ER SPL C144).
  - rewrite XV. clear - RB41 BTOP NFULL. lia.
  - rewrite XV.
    replace (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6)) + 40) with (PNM.b_sb s6 + (5 * Z.of_nat (length (PNM.b_stk s6)) + 5) * 8) by (clear; lia).
    rewrite Z_mod_plus_full. exact AL41.
  - rewrite XV.
    replace (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6)) + 40) with (PNM.b_sb s6 + 40 * (Z.of_nat (length (PNM.b_stk s6)) + Z.of_nat 1)) by (clear; lia).
    exact VE7.
  - right. split; [exact EC7|]. right. exists c.
    unfold s7, set_vec. cbn [PNM.b_stk PNM.b_src PNBO.set_more]. rewrite ESTK.
    split; [reflexivity|]. split; [exact OKc|]. split; [exact MCc|]. split; [reflexivity| exact UNR6].
  - exact INV7.
  - unfold s7, set_vec. cbn [PNM.b_stk]. rewrite <- ESTK. rewrite length_app. clear; lia.
Qed.

End WithHeap.
End PNABDU1T.
