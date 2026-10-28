(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation Zwf.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanSoundSums SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5CoreSpecsA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParSpecs PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b PnSpecsAX_b PnSpecsAXC_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnModelFacts PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnASrcKit_b PmAUarK_b PmAUar_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrObj. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrObjA_b PnAParKit_b PnAReset1_b PnOwnerOkA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG PmTxtKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcKitA_b PnBrKitA_b PnAParseP_b PnAParseP2_b Ba0_code_ad390_ad394_b PnAParseK_b PnAParseA_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.


Module PNAPAB.
Import L5A. Import L5CA. Import L5SAR. Import PNBKA. Import PNAPAK. Import PNAPAA.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

(* [comment removed for export] *)
Lemma unread_le R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 :
  pa_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  0 <= PM.unread (PNM.b_src s1) sm1 <= PM.unread (PNM.b_src s) sm.
Proof.
  intros (_ & RP1 & STEP1 & _). destruct RP1 as (PA1 & IA1 & _). destruct STEP1 as (_ & _ & _ & _ & LE).
  split; [exact (PNBKA.unread_nonneg _ _ _ _ _ _ _ PA1 IA1)| exact LE].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pa_mode0 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 (fx1 : FPState) R1 l c :
  PNRAa.begin_document_spec L ar HI ->
  pa_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  pa_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  PNAPAA.pa_IH L ar HI K R M model LBX FF LK Aw cr sp fb s str sm ax F (PNRA.bmu s1 sm1) ->
  pa_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  lregs R R1 sp fb F -> getr R1 (reg 17) = Z_to_bv 64 (fb + 464 + 8) -> spill M1 sp F (fb + 464) (fb + 432) (fb + 1024) -> ec_some M1 fb -> PNRA.binv s1 ->
  PNRA.bb_room s1 sm1 -> PNM.b_more s1 = 1 -> PNM.b_stk s1 = l ++ [c] -> PNM.bs_mode c = 0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xae0cc M1 model1) K.
Proof.
  intros BD CTX G IH LM ER X17 SPL ECS INV1 BBR1 MO1 ES Hm.
  pose proof CTX as (_ & _ & _ & _ & ENT & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & UNR & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof (unread_le R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 LM) as (UN0 & UNL).
  pose proof (PNAPAK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 CTX G LM) as (PF & _).
  pose proof (PNAPAA.mfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 CTX G LM) as (MOv & _ & _ & _ & _ & _ & _ & _ & _ & Q36 & Q34 & Q37).
  rewrite MO1 in MOv.
  pose proof (PNAPAA.spill_vis L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 CTX G LM SPL) as SPv.
  pose proof (PNAPAK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 l c CTX G LM INV1 ES) as (TF & PT & OKc & VIN & TB1 & TB2 & TB3 & TB4).
  pose proof (PNAPAA.hfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 l c CTX G LM INV1 ES) as HF.
  rewrite Hm in HF.
  set (MV1 := mrestrict (ahid Aw1 model1) M1) in *.
  set (b := PNM.b_sb s1) in *. set (n := Z.of_nat (length l)) in *.
  pfx PF. spx SPv. tfx TF. hfx HF. pose proof ER as ER'. lrx ER'.
  assert (Q40r : 0 <= 0 <= 0) by (clear; lia).
  (* [comment removed for export] *)
  pose proof (PNAPAP.apaH0_conc fx1 R1 MV1 (vmx R sp fb F fl 0 0 (b + 40 * n + 40) 0 0 0 0 0)) as P.
  pfeed P.
  destruct P as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & MS2 & KS2 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15).
  apply (PNAPAA.pa_piece_reg L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 fx1 fx2 R1 R2 0xae0cc 0xae13c M2v CTX G LM MS2 MG2 FRZ2).
  intros model2' LM2 HID2.
  assert (ER2 : lregs R R2 sp fb F) by (lrk ER KS2).
  assert (X172 : getr R2 (reg 17) = Z_to_bv 64 (fb + 464 + 8)) by (rewrite (KS2 17%nat) by inl; exact X17).
  assert (MVE : mrestrict (ahid Aw1 model2') M1 = MV1) by (unfold MV1; rewrite HID2; reflexivity).
  clear E2 E3 E4 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27. pose proof ER2 as ER2'. lrx ER2'.
  (* [comment removed for export] *)
  pose proof (PNAPAP.apaR_conc fx2 R2 MV1 (vmx R sp fb F fl 0 0 (b + 40 * n + 40) 0 0 0 0 0)) as P.
  pfeed P.
  destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Z1 & Z10 & Z11 & Z12 & MD3).
  rewrite <- MVE in MS3, MG3, FRZ3.
  apply (PNAPAK.pa_piece_mt L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model2' LK1 Aw1 s1 sm1 ax1 cr1 fx2 fx3 R2 R3 0xae13c 0xae924 M3v l c 1 (PNM.bs_type c)
           (fun a => b + 40 * n + 40 - 40 <= a < b + 40 * n + 40 - 40 + 4) CTX G LM2 INV1 ES MS3 MG3).
  { intros a Ha N. apply FRZ3; [exact Ha| exact N]. }
  { intros a X. left. fold b n. clear - X; lia. }
  { fold b n. replace (b + 40 * n) with (b + 40 * n + 40 - 40) by (clear; lia). exact MD3. }
  { left. split; [reflexivity| intros a X; fold b n; clear - X; lia]. }
  intros M4 model4 LM4 HID4 VIS4 FR4 MGM4 ECK4.
  set (c2 := PNM.BS 1 (PNM.bs_len c) (PNM.bs_pos c) (PNM.bs_type c) (PNM.bs_idx c)) in *.
  set (s4 := PNBO.set_stk s1 (l ++ [c2])) in *.
  pose proof INV1 as (DN1 & SH1). rewrite ES in SH1.
  pose proof (shape_bottom_nil l c SH1 ltac:(left; exact Hm)) as NIL.
  pose proof OKc as (OKm & OKl & OKp & OKt & OKi).
  assert (OKc2 : PNM.bstate_ok c2) by (unfold PNM.bstate_ok, c2; cbn [PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx]; repeat split; first [apply OKl | apply OKp | apply OKt | apply OKi | clear; lia]).
  assert (INV4 : PNRA.binv s4).
  { unfold PNRA.binv, s4. cbn [PNBO.set_stk PNM.b_done PNM.b_stk]. split; [exact DN1|].
    apply (shape_top_mode l c c2 SH1 OKc2); [intros _; right; reflexivity| intros NN; destruct (NN NIL)]. }
  destruct ECS as (e1 & c1 & He1 & EC1).
  pose proof (ECK4 _ _ EC1) as EC4.
  assert (ER3 : lregs R R3 sp fb F) by (lrk ER2 KS3).
  change 0xae924 with (PNL.pn_begin_document PMA.AN).
  apply (PNAPAK.pa_call_brun L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M4 model4 LK1 Aw1 s4 sm1 ax1 cr1 fx3 R3 0xae15c e1 c1 false (PNL.pn_begin_document PMA.AN) 7 (PNRA.bargs3 PMA.AD) PNRA.bprog_value
           BD ltac:(clear; lia) CTX G LM4 INV4 EC4 He1).
  { unfold s4. cbn [PNBO.set_stk PNM.b_src]. clear - UNL UNR; lia. }
  { unfold PNRA.bargs3, PNRA.o_p, PMSP.o_p, PNRA.o_v, PMSP.o_v, PNRA.o_ec, PMSP.o_ec. cbn [pa_off_p pa_off_v pa_off_ec PMA.AD PnLayoutA_b.ADDR_A].
    rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [exact Z10|]. split; [exact Z11| exact Z12]. }
  { exact Z1. } { unfold L5.ra_ok; clear; lia. } { rewrite (KS3 2%nat) by inl. exact E2. }
  { rewrite (KS3 3%nat) by inl. rewrite E3. exact Rgp. } { rewrite (KS3 4%nat) by inl. rewrite E4. exact Rtp. }
  intros fx5 R5 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 RP5 LM5 STEP5 AXL5 RES5 BBP5 AG5 AGF5.
  pose proof (lregs_pres R R3 R5 sp fb F ER3 RP5) as ER5.
  assert (SPL5 : spill M5 sp F (fb + 464) (fb + 432) (fb + 1024)).
  { apply (PNAPAK.spill_agree M1 M5 sp F (fb + 464) (fb + 432) (fb + 1024)); [clear - pf4; lia| clear - pf4; lia| exact SPL|].
    intros a Ha. rewrite (AG5 a ltac:(clear - Ha; lia)). apply FR4; [clear - Ha pf4; lia| clear - Ha tf9; lia]. }
  clear pf1 pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf10 pf11 pf12 pf13 pf14 pf15 pf16 pf17 pf18 pf19 pf20 pf21 pf22 pf23 pf24 pf25 pf26 pf27 pf28 pf29 pf30 pf31 pf32 pf33 pf34. clear E2 E3 E4 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27. clear sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9 sv10 sv11 sv12 sv13.
  (* [comment removed for export] *)
  pose proof (PNAPAK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 CTX G LM5) as (PF & _).
  pose proof (PNAPAA.spill_vis L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 CTX G LM5 SPL5) as SPv.
  set (MV5 := mrestrict (ahid Aw5 model5) M5) in *.
  pfx PF. spx SPv. pose proof ER5 as ER5'. lrx ER5'.
  pose proof (PNAPAP.apaJ0_conc fx5 R5 MV5 (vmx R sp fb F fl 0 0 0 0 0 0 0 0)) as P.
  pfeed P.
  destruct P as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & MS6 & KS6 & X176).
  apply (PNAPAA.pa_piece_reg L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 fx5 fx6 R5 R6 0xae15c 0xae3fc M6v CTX G LM5 MS6 MG6 FRZ6).
  intros model6 LM6 HID6.
  apply (PNAPAA.pa_tail L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 (PNRA.bmu s1 sm1) M5 model6 LK5 Aw5 s5 sm5 ax5 cr5 fx6 R6 CTX G IH LM6); [lrk ER5 KS6| exact X176| exact SPL5| |].
  - destruct RES5 as [(v & Hv & Ev & _)|(Ee & _)]; [exists v, (pa_errcat_obj PMA.AD); split; [clear - Hv; lia| exact Ev]| exists e1, c1; split; [exact He1| exact Ee]].
  - right. destruct STEP5 as (_ & _ & _ & _ & LE5). unfold s4 in LE5, BBP5. cbn [PNBO.set_stk PNM.b_src] in LE5. unfold PNRA.bb_post in BBP5. cbn [PNBO.set_stk PNM.b_bb] in BBP5.
    pose proof (unread_le R M model LBX FF LK Aw cr sp fb s str sm ax F M5 model6 LK5 Aw5 s5 sm5 ax5 cr5 LM6) as (UN5 & _).
    split; [destruct RES5 as [(v & _ & _ & _ & _ & _ & X)|(_ & X & _)]; exact X|].
    split; [intros _; exact (bb_room_keep s1 s5 sm1 sm5 BBP5 LE5 BBR1)|].
    intros MO5. destruct RES5 as [(v & _ & _ & MOv5 & _)|(_ & INV5 & PROG)]; [rewrite MOv5 in MO5; discriminate|].
    unfold PNRA.bmu. rewrite ES, bflag_app, Hm. cbn [Z.eqb Pos.eqb orb].
    pose proof (bflag_range (PNM.b_stk s5)) as FR5.
    destruct PROG as [(l3 & c3 & c3' & G1 & G2 & _ & Gm & _)|(cn & G2 & _ & Gc & _ & LT)].
    + unfold s4 in G1. cbn [PNBO.set_stk PNM.b_stk] in G1. apply app_inj_tail in G1. destruct G1 as (<- & <-). rewrite G2, bflag_app, Gm. cbn [c2 PNM.bs_mode Z.eqb Pos.eqb orb]. clear - LE5 UN5; lia.
    + unfold s4 in LT. cbn [PNBO.set_stk PNM.b_src] in LT. clear - LT FR5 UN5; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pa_mode4 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 (fx1 : FPState) R1 l c :
  PNRAa.read_value_spec L ar HI ->
  pa_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  pa_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  PNAPAA.pa_IH L ar HI K R M model LBX FF LK Aw cr sp fb s str sm ax F (PNRA.bmu s1 sm1) ->
  pa_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  lregs R R1 sp fb F -> getr R1 (reg 17) = Z_to_bv 64 (fb + 464 + 8) -> spill M1 sp F (fb + 464) (fb + 432) (fb + 1024) -> ec_some M1 fb -> PNRA.binv s1 ->
  PNRA.bb_room s1 sm1 -> PNM.b_more s1 = 1 -> PNM.b_stk s1 = l ++ [c] -> PNM.bs_mode c = 4 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xae0cc M1 model1) K.
Proof.
  intros RV CTX G IH LM ER X17 SPL ECS INV1 BBR1 MO1 ES Hm.
  pose proof CTX as (_ & _ & _ & _ & ENT & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & UNR & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof (unread_le R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 LM) as (UN0 & UNL).
  pose proof (PNAPAK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 CTX G LM) as (PF & _).
  pose proof (PNAPAA.mfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 CTX G LM) as (MOv & _ & _ & _ & _ & _ & _ & _ & _ & Q36 & Q34 & Q37).
  rewrite MO1 in MOv.
  pose proof (PNAPAA.spill_vis L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 CTX G LM SPL) as SPv.
  pose proof (PNAPAK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 l c CTX G LM INV1 ES) as (TF & PT & OKc & VIN & TB1 & TB2 & TB3 & TB4).
  pose proof (PNAPAA.hfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 l c CTX G LM INV1 ES) as HF.
  rewrite Hm in HF.
  set (MV1 := mrestrict (ahid Aw1 model1) M1) in *.
  set (b := PNM.b_sb s1) in *. set (n := Z.of_nat (length l)) in *.
  pfx PF. spx SPv. tfx TF. hfx HF. pose proof ER as ER'. lrx ER'.
  assert (Q40r : 4 <= 4 <= 4) by (clear; lia).
  (* [comment removed for export] *)
  pose proof (PNAPAP.apaH4_conc fx1 R1 MV1 (vmx R sp fb F fl 4 0 (b + 40 * n + 40) 0 (PNM.bs_type c) 0 0 0)) as P.
  pfeed P.
  destruct P as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & MS2 & KS2 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15).
  apply (PNAPAA.pa_piece_reg L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 fx1 fx2 R1 R2 0xae0cc 0xae160 M2v CTX G LM MS2 MG2 FRZ2).
  intros model2' LM2 HID2.
  assert (ER2 : lregs R R2 sp fb F) by (lrk ER KS2).
  assert (X172 : getr R2 (reg 17) = Z_to_bv 64 (fb + 464 + 8)) by (rewrite (KS2 17%nat) by inl; exact X17).
  assert (MVE : mrestrict (ahid Aw1 model2') M1 = MV1) by (unfold MV1; rewrite HID2; reflexivity).
  clear E2 E3 E4 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27. pose proof ER2 as ER2'. lrx ER2'.
  (* [comment removed for export] *)
  pose proof (PNAPAP.apaV_conc fx2 R2 MV1 (vmx R sp fb F fl 4 0 (b + 40 * n + 40) 0 (PNM.bs_type c) 0 0 0)) as P.
  pfeed P.
  destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Z1 & Z10 & Z11 & Z12 & Z13 & MD3).
  rewrite <- MVE in MS3, MG3, FRZ3.
  apply (PNAPAK.pa_piece_mt L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model2' LK1 Aw1 s1 sm1 ax1 cr1 fx2 fx3 R2 R3 0xae160 0xaff88 M3v l c 2 (PNM.bs_type c)
           (fun a => b + 40 * n + 40 - 40 <= a < b + 40 * n + 40 - 40 + 4) CTX G LM2 INV1 ES MS3 MG3).
  { intros a Ha N. apply FRZ3; [exact Ha| exact N]. }
  { intros a X. left. fold b n. clear - X; lia. }
  { fold b n. replace (b + 40 * n) with (b + 40 * n + 40 - 40) by (clear; lia). exact MD3. }
  { left. split; [reflexivity| intros a X; fold b n; clear - X; lia]. }
  intros M4 model4 LM4 HID4 VIS4 FR4 MGM4 ECK4.
  set (c2 := PNM.BS 2 (PNM.bs_len c) (PNM.bs_pos c) (PNM.bs_type c) (PNM.bs_idx c)) in *.
  set (s4 := PNBO.set_stk s1 (l ++ [c2])) in *.
  pose proof INV1 as (DN1 & SH1). rewrite ES in SH1.
  pose proof (shape_cont_cons l c SH1 ltac:(right; right; exact Hm)) as NNIL.
  pose proof OKc as (OKm & OKl & OKp & OKt & OKi).
  assert (OKc2 : PNM.bstate_ok c2) by (unfold PNM.bstate_ok, c2; cbn [PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx]; repeat split; first [apply OKl | apply OKp | apply OKt | apply OKi | clear; lia]).
  assert (INV4 : PNRA.binv s4).
  { unfold PNRA.binv, s4. cbn [PNBO.set_stk PNM.b_done PNM.b_stk]. split; [exact DN1|].
    apply (shape_top_mode l c c2 SH1 OKc2); [intros E0; destruct (NNIL E0)| intros _; left; reflexivity]. }
  assert (BBR4 : PNRA.bb_room s4 sm1) by (unfold PNRA.bb_room, s4; cbn [PNBO.set_stk PNM.b_bb PNM.b_src]; exact BBR1).
  destruct ECS as (e1 & c1 & He1 & EC1).
  pose proof (ECK4 _ _ EC1) as EC4.
  assert (ER3 : lregs R R3 sp fb F) by (lrk ER2 KS3).
  change 0xaff88 with (PNL.pn_read_value PMA.AN).
  apply (PNAPAK.pa_call_brun L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M4 model4 LK1 Aw1 s4 sm1 ax1 cr1 fx3 R3 0xae198 e1 c1 true (PNL.pn_read_value PMA.AN) 8 (PNRA.bargs_rv PMA.AD) PNRA.bprog_value
           RV ltac:(clear; lia) CTX G LM4 INV4 EC4 He1).
  { unfold s4. cbn [PNBO.set_stk PNM.b_src]. clear - UNL UNR; lia. }
  { unfold PNRA.bargs_rv, PNRA.o_p, PMSP.o_p, PNRA.o_v, PMSP.o_v, PNRA.o_ec, PMSP.o_ec. cbn [pa_off_p pa_off_v pa_off_ec PMA.AD PnLayoutA_b.ADDR_A].
    rewrite L5K.rl10, L5K.rl11, L5K.rl12, L5K.rl13. split; [exact Z10|]. split; [exact Z11|]. split; [exact Z13|].
    split; [exists (PNM.bs_type c); split; [clear - OKt; lia| exact Z12]| exact BBR4]. }
  { exact Z1. } { unfold L5.ra_ok; clear; lia. } { rewrite (KS3 2%nat) by inl. exact E2. }
  { rewrite (KS3 3%nat) by inl. rewrite E3. exact Rgp. } { rewrite (KS3 4%nat) by inl. rewrite E4. exact Rtp. }
  intros fx5 R5 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 RP5 LM5 STEP5 AXL5 RES5 BBP5 AG5 AGF5.
  pose proof (lregs_pres R R3 R5 sp fb F ER3 RP5) as ER5.
  assert (SPL5 : spill M5 sp F (fb + 464) (fb + 432) (fb + 1024)).
  { apply (PNAPAK.spill_agree M1 M5 sp F (fb + 464) (fb + 432) (fb + 1024)); [clear - pf4; lia| clear - pf4; lia| exact SPL|].
    intros a Ha. rewrite (AG5 a ltac:(clear - Ha; lia)). apply FR4; [clear - Ha pf4; lia| clear - Ha tf9; lia]. }
  clear pf1 pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf10 pf11 pf12 pf13 pf14 pf15 pf16 pf17 pf18 pf19 pf20 pf21 pf22 pf23 pf24 pf25 pf26 pf27 pf28 pf29 pf30 pf31 pf32 pf33 pf34. clear E2 E3 E4 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27. clear sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9 sv10 sv11 sv12 sv13.
  (* [comment removed for export] *)
  pose proof (PNAPAK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 CTX G LM5) as (PF & _).
  pose proof (PNAPAA.spill_vis L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 CTX G LM5 SPL5) as SPv.
  set (MV5 := mrestrict (ahid Aw5 model5) M5) in *.
  pfx PF. spx SPv. pose proof ER5 as ER5'. lrx ER5'.
  pose proof (PNAPAP.apaJ4_conc fx5 R5 MV5 (vmx R sp fb F fl 0 0 0 0 0 0 0 0)) as P.
  pfeed P.
  destruct P as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & MS6 & KS6 & X176).
  apply (PNAPAA.pa_piece_reg L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 fx5 fx6 R5 R6 0xae198 0xae3fc M6v CTX G LM5 MS6 MG6 FRZ6).
  intros model6 LM6 HID6.
  apply (PNAPAA.pa_tail L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 (PNRA.bmu s1 sm1) M5 model6 LK5 Aw5 s5 sm5 ax5 cr5 fx6 R6 CTX G IH LM6); [lrk ER5 KS6| exact X176| exact SPL5| |].
  - destruct RES5 as [(v & Hv & Ev & _)|(Ee & _)]; [exists v, (pa_errcat_obj PMA.AD); split; [clear - Hv; lia| exact Ev]| exists e1, c1; split; [exact He1| exact Ee]].
  - right. destruct STEP5 as (_ & _ & _ & _ & LE5). unfold s4 in LE5. cbn [PNBO.set_stk PNM.b_src] in LE5. unfold PNRA.bb_post in BBP5.
    pose proof (unread_le R M model LBX FF LK Aw cr sp fb s str sm ax F M5 model6 LK5 Aw5 s5 sm5 ax5 cr5 LM6) as (UN5 & _).
    split; [destruct RES5 as [(v & _ & _ & _ & _ & _ & X)|(_ & X & _)]; exact X|].
    split; [intros MO5; exact (BBP5 BBR4 MO5)|].
    intros MO5. destruct RES5 as [(v & _ & _ & MOv5 & _)|(_ & INV5 & PROG)]; [rewrite MOv5 in MO5; discriminate|].
    unfold PNRA.bmu. rewrite ES, bflag_app, Hm. cbn [Z.eqb Pos.eqb orb].
    pose proof (bflag_range (PNM.b_stk s5)) as FR5.
    destruct PROG as [(l3 & c3 & c3' & G1 & G2 & _ & Gm & _)|(cn & G2 & _ & Gc & _ & LT)].
    + unfold s4 in G1. cbn [PNBO.set_stk PNM.b_stk] in G1. apply app_inj_tail in G1. destruct G1 as (<- & <-). rewrite G2, bflag_app, Gm. cbn [c2 PNM.bs_mode Z.eqb Pos.eqb orb]. clear - LE5 UN5; lia.
    + unfold s4 in LT. cbn [PNBO.set_stk PNM.b_src] in LT. clear - LT FR5 UN5; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pa_mode1 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 (fx1 : FPState) R1 l c :
  PNSAXC.vec_clear_spec RSEGS PMA.AD L ar HI 0xab740 ->
  pa_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  pa_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  PNAPAA.pa_IH L ar HI K R M model LBX FF LK Aw cr sp fb s str sm ax F (PNRA.bmu s1 sm1) ->
  pa_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  lregs R R1 sp fb F -> getr R1 (reg 17) = Z_to_bv 64 (fb + 464 + 8) -> spill M1 sp F (fb + 464) (fb + 432) (fb + 1024) -> ec_some M1 fb -> PNRA.binv s1 ->
  PNM.b_more s1 = 1 -> PNM.b_stk s1 = l ++ [c] -> PNM.bs_mode c = 1 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xae0cc M1 model1) K.
Proof.
  intros ASH CTX G IH LM ER X17 SPL ECS INV1 MO1 ES Hm.
  pose proof CTX as (_ & _ & _ & _ & ENT & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof (PNAPAK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 CTX G LM) as (PF & _).
  pose proof (PNAPAA.mfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 CTX G LM) as (MOv & _ & _ & _ & WR400 & B392 & _ & _ & _ & Q36 & Q34 & Q37).
  rewrite MO1 in MOv.
  pose proof (PNAPAA.spill_vis L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 CTX G LM SPL) as SPv.
  pose proof (PNAPAK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 l c CTX G LM INV1 ES) as (TF & PT & OKc & VIN & TB1 & TB2 & TB3 & TB4).
  pose proof (PNAPAA.hfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 l c CTX G LM INV1 ES) as HF.
  rewrite Hm in HF.
  pose proof INV1 as (DN1 & SH1). rewrite ES in SH1.
  pose proof (shape_bottom_nil l c SH1 ltac:(right; exact Hm)) as NIL.
  set (MV1 := mrestrict (ahid Aw1 model1) M1) in *.
  set (b := PNM.b_sb s1) in *. set (n := Z.of_nat (length l)) in *.
  assert (Hn0 : n = 0) by (unfold n; rewrite NIL; reflexivity).
  pfx PF. spx SPv. tfx TF. hfx HF. pose proof ER as ER'. lrx ER'.
  assert (Q40r : 1 <= 1 <= 1) by (clear; lia).
  (* [comment removed for export] *)
  pose proof (PNAPAP.apaH1_conc fx1 R1 MV1 (vmx R sp fb F fl 1 0 (b + 40 * n + 40) 0 0 0 0 0)) as P.
  pfeed P.
  destruct P as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & MS2 & KS2 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15).
  apply (PNAPAA.pa_piece_reg L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 fx1 fx2 R1 R2 0xae0cc 0xae330 M2v CTX G LM MS2 MG2 FRZ2).
  intros model2' LM2 HID2.
  assert (ER2 : lregs R R2 sp fb F) by (lrk ER KS2).
  assert (X172 : getr R2 (reg 17) = Z_to_bv 64 (fb + 464 + 8)) by (rewrite (KS2 17%nat) by inl; exact X17).
  assert (MVE : mrestrict (ahid Aw1 model2') M1 = MV1) by (unfold MV1; rewrite HID2; reflexivity).
  clear E2 E3 E4 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27. pose proof ER2 as ER2'. lrx ER2'.
  (* [comment removed for export] *)
  assert (B392' : L5.u64_at RSEGS MV1 (fb + 464 + 392) (b + 40 * n + 40 - 40)) by (replace (b + 40 * n + 40 - 40) with b by (clear - Hn0; lia); exact B392).
  pose proof (PNAPAP.apaC1_conc fx2 R2 MV1 (vmx R sp fb F fl 1 0 (b + 40 * n + 40) 0 0 0 0 0)) as P.
  pfeed P.
  destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Z1 & Z10 & Z11 & _ & E3v).
  rewrite <- MVE in MS3, MG3, FRZ3.
  apply (PNAPAK.pa_call_shrink L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model2' LK1 Aw1 s1 sm1 ax1 cr1 fx2 fx3 R2 R3 0xae330 0xae350 M3v l c ASH CTX G LM2 ES NIL MS3 MG3).
  { intros a Ha N. apply FRZ3; [exact Ha|]. intros X. apply N. clear - X; lia. }
  { fold b n. replace (fb + 864) with (fb + 464 + 400) by (clear; lia). exact E3v. }
  { exact Z1. } { unfold L5.ra_ok; clear; lia. } { rewrite (KS3 2%nat) by inl. exact E2. }
  { rewrite (KS3 3%nat) by inl. rewrite E3. exact Rgp. } { rewrite (KS3 4%nat) by inl. rewrite E4. exact Rtp. }
  { replace (fb + 856) with (fb + 464 + 392) by (clear; lia). exact Z10. }
  intros fx4 R4 M4 model4 LK4 Aw4 RP4 LM4 AG4 ECK4.
  set (s4 := PNBO.set_stk s1 l) in *.
  assert (ER3 : lregs R R3 sp fb F) by (lrk ER2 KS3).
  pose proof (lregs_pres R R3 R4 sp fb F ER3 RP4) as ER4.
  assert (SPL4 : spill M4 sp F (fb + 464) (fb + 432) (fb + 1024)).
  { apply (PNAPAK.spill_agree M1 M4 sp F (fb + 464) (fb + 432) (fb + 1024)); [clear - pf4; lia| clear - pf4; lia| exact SPL|].
    intros a Ha. apply AG4. clear - Ha; lia. }
  clear pf1 pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf10 pf11 pf12 pf13 pf14 pf15 pf16 pf17 pf18 pf19 pf20 pf21 pf22 pf23 pf24 pf25 pf26 pf27 pf28 pf29 pf30 pf31 pf32 pf33 pf34. clear E2 E3 E4 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27. clear sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9 sv10 sv11 sv12 sv13.
  (* [comment removed for export] *)
  pose proof (PNAPAK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M4 model4 LK4 Aw4 s4 sm1 ax1 cr1 CTX G LM4) as (PF & _).
  pose proof (PNAPAA.mfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M4 model4 LK4 Aw4 s4 sm1 ax1 cr1 CTX G LM4) as (_ & _ & _ & WR2 & _).
  pose proof (PNAPAA.vfacts_of L ar C IL HI LY HIok ICok ILY K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M4 model4 LK4 Aw4 s4 sm1 ax1 cr1 CTX G LM4) as (vf1 & vf2 & vf3 & vf4 & vf5 & vf6 & vf7 & vf8 & vf9 & vf10 & vf11).
  pose proof (PNAPAA.spill_vis L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M4 model4 LK4 Aw4 s4 sm1 ax1 cr1 CTX G LM4 SPL4) as SPv.
  set (MV4 := mrestrict (ahid Aw4 model4) M4) in *.
  pfx PF. spx SPv. pose proof ER4 as ER4'. lrx ER4'.
  pose proof (PNAPAP.apaC2_conc fx4 R4 MV4 (vmx R sp fb F fl 0 0 0 0 0 0 0 0)) as P.
  pfeed P.
  destruct P as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & _ & _ & _ & X175 & DN5 & MO5).
  apply (PNAPAK.pa_piece_md L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M4 model4 LK4 Aw4 s4 sm1 ax1 cr1 fx4 fx5 R4 R5 0xae350 0xae3fc M5v 0 1
           (fun a => fb + 464 + 8 <= a < fb + 464 + 8 + 2) CTX G LM4 MS5 MG5).
  { intros a Ha N. apply FRZ5; [exact Ha| exact N]. }
  { intros a X. left. clear - X; lia. }
  { replace (fb + 472) with (fb + 464 + 8) by (clear; lia). exact MO5. }
  { left; reflexivity. }
  { right. split; [replace (fb + 473) with (fb + 464 + 9) by (clear; lia); exact DN5| right; reflexivity]. }
  intros M6 model6 LM6 HID6 VIS6 FR6 MGM6 ECK6.
  apply (PNAPAA.pa_tail L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 (PNRA.bmu s1 sm1) M6 model6 LK4 Aw4 (set_md s4 0 1) sm1 ax1 cr1 fx5 R5 CTX G IH LM6); [lrk ER4 KS5| exact X175| | |].
  - apply (PNAPAK.spill_agree M4 M6 sp F (fb + 464) (fb + 432) (fb + 1024)); [clear - pf4; lia| clear - pf4; lia| exact SPL4|].
    intros a Ha. apply FR6; [clear - Ha pf4; lia| clear - Ha pf14; lia].
  - destruct ECS as (e1 & c1 & He1 & EC1). exists e1, c1. split; [exact He1|]. exact (ECK6 _ _ (ECK4 _ _ EC1)).
  - left. reflexivity.
Qed.
End WithHeap.
End PNAPAB.
