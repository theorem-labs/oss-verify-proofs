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

Module PNABD.
Import L5A. Import L5CA. Import L5SAR. Import PNBKA. Import PNABDK.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bregs (R R4 : bvmap 5 word) (sp fb F : Z) : Prop :=
  getr R4 (reg 2) = Z_to_bv 64 (sp - 160) /\ getr R4 (reg 3) = getr R (reg 3) /\ getr R4 (reg 4) = getr R (reg 4)
  /\ getr R4 (reg 8) = Z_to_bv 64 sp /\ getr R4 (reg 9) = Z_to_bv 64 (sp - 160)
  /\ getr R4 (reg 19) = Z_to_bv 64 (fb + 464) /\ getr R4 (reg 20) = Z_to_bv 64 F /\ getr R4 (reg 21) = Z_to_bv 64 (fb + 1024)
  /\ getr R4 (reg 22) = Z_to_bv 64 ((fb + 464 + 400) / 8 + 2147450880) /\ getr R4 (reg 23) = Z_to_bv 64 (fb + 432)
  /\ getr R4 (reg 24) = Z_to_bv 64 (F + 32) /\ getr R4 (reg 25) = Z_to_bv 64 F /\ getr R4 (reg 26) = Z_to_bv 64 (F / 8 + 2147450880)
  /\ getr R4 (reg 27) = Z_to_bv 64 2147450880.

Definition bregsT (R R4 : bvmap 5 word) (sp fb F : Z) : Prop :=
  getr R4 (reg 2) = Z_to_bv 64 (sp - 160) /\ getr R4 (reg 3) = getr R (reg 3) /\ getr R4 (reg 4) = getr R (reg 4)
  /\ getr R4 (reg 8) = Z_to_bv 64 sp /\ getr R4 (reg 9) = Z_to_bv 64 (sp - 160)
  /\ getr R4 (reg 18) = Z_to_bv 64 F /\ getr R4 (reg 20) = Z_to_bv 64 F /\ getr R4 (reg 21) = Z_to_bv 64 (fb + 1024)
  /\ getr R4 (reg 22) = Z_to_bv 64 ((fb + 464 + 400) / 8 + 2147450880) /\ getr R4 (reg 23) = Z_to_bv 64 (fb + 432)
  /\ getr R4 (reg 24) = Z_to_bv 64 (F + 32) /\ getr R4 (reg 25) = Z_to_bv 64 F /\ getr R4 (reg 26) = Z_to_bv 64 (F / 8 + 2147450880)
  /\ getr R4 (reg 27) = Z_to_bv 64 2147450880.

Definition bregsE (R R4 : bvmap 5 word) (sp fb F : Z) : Prop :=
  getr R4 (reg 2) = Z_to_bv 64 (sp - 160) /\ getr R4 (reg 3) = getr R (reg 3) /\ getr R4 (reg 4) = getr R (reg 4)
  /\ getr R4 (reg 8) = Z_to_bv 64 sp /\ getr R4 (reg 9) = Z_to_bv 64 (sp - 160)
  /\ getr R4 (reg 18) = Z_to_bv 64 F /\ getr R4 (reg 19) = Z_to_bv 64 (fb + 464) /\ getr R4 (reg 20) = Z_to_bv 64 (fb + 1024)
  /\ getr R4 (reg 21) = Z_to_bv 64 ((fb + 464 + 400) / 8) /\ getr R4 (reg 22) = Z_to_bv 64 ((fb + 464 + 400) / 8 + 2147450880)
  /\ getr R4 (reg 23) = Z_to_bv 64 (fb + 432) /\ getr R4 (reg 25) = Z_to_bv 64 F /\ getr R4 (reg 26) = Z_to_bv 64 (F / 8 + 2147450880)
  /\ getr R4 (reg 27) = Z_to_bv 64 2147450880.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

(* [comment removed for export] *)
Lemma sh_le a b : a mod 8 = 0 -> b mod 8 = 0 -> a + 8 <= b -> a / 8 + 1 <= b / 8.
Proof.
  intros A8 B8 H. pose proof (Z.div_mod a 8 ltac:(clear; lia)) as Da. pose proof (Z.div_mod b 8 ltac:(clear; lia)) as Db. rewrite A8 in Da. rewrite B8 in Db.
  clear - Da Db H. lia.
Qed.
Lemma sh_le64 a b : a mod 8 = 0 -> b mod 8 = 0 -> a + 64 <= b -> a / 8 + 8 <= b / 8.
Proof.
  intros A8 B8 H. pose proof (Z.div_mod a 8 ltac:(clear; lia)) as Da. pose proof (Z.div_mod b 8 ltac:(clear; lia)) as Db. rewrite A8 in Da. rewrite B8 in Db.
  clear - Da Db H. lia.
Qed.
Lemma m32_8 a : a mod 32 = 0 -> a mod 8 = 0.
Proof. intros H. pose proof (Z.div_mod a 32 ltac:(clear; lia)) as D. rewrite H, Z.add_0_r in D. rewrite D. replace (32 * (a / 32)) with ((a / 32 * 4) * 8) by (clear; lia). apply Z_mod_mult. Qed.

(* [comment removed for export] *)
Lemma vfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 :
  bd_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  bd_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  6905856 <= fb + 432 <= 140737488355320 /\ (fb + 432) mod 8 = 0 /\ (2147446784 + 17592186048512 <= fb + 432 \/ (fb + 432) + 8 <= 2147446784)
  /\ L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) (((fb + 432) / 8) + 2147450880) 1
  /\ ((sp - 160) + 160 <= fb + 432 \/ (fb + 432) + 8 <= (sp - 160)) /\ ((fb + 464) + 416 <= fb + 432 \/ (fb + 432) + 8 <= fb + 464)
  /\ (F + 64 <= fb + 432 \/ (fb + 432) + 8 <= F) /\ (fl + 1 <= fb + 432 \/ (fb + 432) + 8 <= fl)
  /\ L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 432) 1251456
  /\ L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) 2147607320 1
  /\ ((((fb + 432) / 8) + 2147450880) + 1 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 8 <= (((fb + 432) / 8) + 2147450880)).
Proof.
  intros CTX G LM.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 7) with 26624 in *.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold bd_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 0, sp - 160 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  pose proof RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_v PMA.AD fb) with (fb + 432) in VIS1.
  pose proof (PNAPAR.ov_visB L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 fb HH1 FOK' VIS1) as VV. cbv zeta in VV.
  destruct VV as ((V1 & V8 & VNS) & VZ & VW & VCE & VU & _).
  assert (CLh : forall a, fb + 32 <= a < fb + 2040 -> aclient L ar LBX FF sp 26624 a).
  { intros a Ha. unfold aclient, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
    change (ff_bytes 5) with 2048. split; [clear - Ha; lia| intros Y; clear - Ha Y; lia]. }
  assert (APF : F + 64 <= fb + 432 \/ (fb + 432) + 8 <= F).
  { apply iv_apart; [clear; lia| clear; lia|]. intros a Ha X. apply (GNCF a); [left; exact Ha| apply CLh; clear - X; lia]. }
  pose proof (m32_8 F GF32) as F8.
  split; [exact V1|]. split; [exact V8|]. split; [exact VNS|]. split; [exact VZ|].
  split; [clear - VCE GSLO; lia|]. split; [right; clear; lia|].
  split; [exact APF|].
  split. { destruct (Z_lt_le_dec fl (fb + 432)) as [X|X]; [left; clear - X; lia|]. destruct (Z_lt_le_dec fl (fb + 432 + 8)) as [Y|Y]; [| right; clear - Y; lia].
           exfalso. apply GFLNC. apply L5SAR.aclient_cons. apply (L5SAR.aclient_00 L ar LBX FF sp 26624). apply CLh. clear - X Y; lia. }
  split; [exact VU|].
  split; [exact (PMASK.img_shz_vis L ar C HI LY IL ICok ILY _ FF' LK1 cr1 Aw1 M1 model1 0x1318c0 1 HH1 ltac:(clear; lia) ltac:(clear; lia) ltac:(reflexivity) ltac:(clear; lia) ltac:(clear; lia))|].
  destruct APF as [X|X].
  - right. pose proof (sh_le64 F (fb + 432) F8 V8 X) as Y. clear - Y. lia.
  - left. pose proof (sh_le (fb + 432) F V8 F8 X) as Y. clear - Y. lia.
Qed.


Lemma mfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 :
  bd_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  bd_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  L5.writable RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 464 + 8) 1 /\ L5.u8_at RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 464 + 10) 0.
Proof.
  intros CTX G LM.
  pose proof (PNABDK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 CTX G LM)
    as (PF & _ & _ & _ & WRop & _ & _).
  unfold pfacts in PF. destruct PF as (_ & _ & _ & _ & _ & _ & pf7 & _).
  pose proof CTX as (_ & _ & _ & _ & _ & _ & _ & FOK & _).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof LM as (BI & RP1 & _).
  pose proof BI as (HH1 & _).
  pose proof RP1 as (PA1 & _ & _ & _ & OACC1 & _).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA1, OACC1. change (PNRA.o_is PMA.AD fb) with (fb + 96) in PA1. change (PNM.PSIZE + 8) with 424 in OACC1.
  assert (FOK' : PNRA.frame_okB ((F, 0, sp - 160 + 32) :: FF) fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ _ LK1 cr1 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1 OACC1) as OPV. cbv zeta in OPV.
  destruct OPV as (_ & _ & _ & _ & OVIS & _).
  pose proof PA1 as (_ & _ & _ & _ & _ & CM & _).
  split; [apply (L5.writable_sub RSEGS _ (fb + 464) 424); [exact WRop| clear; lia| clear; lia]|].
  apply (proj2 (L5A.u8_at_vis _ M1 (fb + 464 + 10) 0 (OVIS (fb + 464 + 10) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - pf7; lia) ltac:(clear - pf7; lia))). exact CM.
Qed.

Lemma wfacts224_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 :
  bd_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  bd_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  L5.writable RSEGS (mrestrict (ahid Aw1 model1) M1) (sp - 224) 224
  /\ (sp - 224 + 224 <= fb + 464 \/ fb + 464 + 416 <= sp - 224)
  /\ (sp - 224 + 224 <= F \/ F + 64 <= sp - 224) /\ (sp - 224 + 224 <= fl \/ fl + 1 <= sp - 224)
  /\ (sp - 224 + 224 <= fb + 432 \/ fb + 432 + 8 <= sp - 224).
Proof.
  intros CTX G LM.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 7) with 26624 in *.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold bd_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 0, sp - 160 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  pose proof RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA1, OACC1. change (PNRA.o_is PMA.AD fb) with (fb + 96) in PA1. change (PNRA.o_v PMA.AD fb) with (fb + 432) in VIS1.
  change (PNM.PSIZE + 8) with 424 in OACC1.
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1 OACC1) as ((O1 & O8 & ONSH) & Zop & OWR & OCE & OVIS & AOP).
  pose proof (PNAPAR.ov_visB L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 fb HH1 FOK' VIS1) as VV. cbv zeta in VV.
  destruct VV as ((V1 & V8 & VNS) & VZ & VW & VCE & VU & _).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 sp 26624 224 HH1 ASTK1 ltac:(lia)) as (SL224 & SH224 & SWR).
  split; [exact SWR|].
  split; [clear - OCE SL224; lia|].
  split; [clear - GFCEIL GSLO; lia|].
  split; [clear - GFLR GSLO; lia|].
  clear - VCE GSLO; lia.
Qed.

Lemma vecfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 :
  bd_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  bd_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  PNRA.binv s1 ->
  L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 464 + 392) (PNM.b_sb s1)
  /\ L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 464 + 400) (PNM.b_sb s1 + 40 * Z.of_nat (length (PNM.b_stk s1)))
  /\ L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 464 + 408) (PNM.b_sb s1 + 40 * 2 ^ PNM.b_sk s1)
  /\ 4096 <= PNM.b_sb s1 <= 140737488314328 /\ PNM.b_sb s1 mod 8 = 0
  /\ 1 <= Z.of_nat (length (PNM.b_stk s1)) <= 1025 /\ 0 <= PNM.b_sk s1 <= 11
  /\ Z.of_nat (length (PNM.b_stk s1)) <= 2 ^ PNM.b_sk s1.
Proof.
  intros CTX G LM INV1.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 0, sp - 160 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  pose proof RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA1, OACC1. change (PNRA.o_is PMA.AD fb) with (fb + 96) in PA1.
  change (PNM.PSIZE + 8) with 424 in OACC1.
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1 OACC1) as ((O1 & O8 & ONSH) & Zop & OWR & OCE & OVIS & AOP).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (WB1 & _ & _ & _ & _ & _ & _ & (CEB1 & _) & (_ & STT & _) & STOP & _).
  pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SV1 & _). change PNM.OFF_STK with 392 in SV1.
  pose proof SV1 as (V0 & V8 & V16 & Hk & Hlen & Hal & DB & CB & AB & EL). change PNM.BSZ with 40 in V8, V16, Hlen, DB, CB, AB.
  pose proof INV1 as (_ & (LN1 & LN2 & _)). change (PNM.MAX_DEPTH + 1) with 1025 in LN2.
  assert (ISB : In (PNM.b_sb s1, PNM.BSZ * 2 ^ PNM.b_sk s1) (PNM.bparser_own s1 ++ LBX)) by (apply in_or_app; left; exact (PNBOA.PNM_own_stk s1)).
  pose proof (WB1 _ ISB) as ((Sb0 & _ & _ & _ & Sb4 & _) & _). cbn [fst snd] in Sb0, Sb4.
  assert (P2k : 1 <= 2 ^ PNM.b_sk s1) by (apply (Z.pow_le_mono_r 2 0 (PNM.b_sk s1)); clear - Hk; lia).
  split. { apply (proj2 (L5A.u64_at_vis _ M1 (fb + 464 + 392) _ (OVIS (fb + 464 + 392) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1; lia))). exact V0. }
  split. { apply (proj2 (L5A.u64_at_vis _ M1 (fb + 464 + 400) _ (OVIS (fb + 464 + 400) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1; lia))).
           replace (fb + 464 + 400) with (fb + 464 + 392 + 8) by (clear; lia). exact V8. }
  split. { apply (proj2 (L5A.u64_at_vis _ M1 (fb + 464 + 408) _ (OVIS (fb + 464 + 408) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1; lia))).
           replace (fb + 464 + 408) with (fb + 464 + 392 + 16) by (clear; lia). exact V16. }
  split; [clear - Sb0 Sb4 P2k CEB1 STT STOP; unfold PNM.BSZ in Sb4; lia|].
  split; [apply PMFA.mod16_8; exact Hal|].
  split; [clear - LN1 LN2; lia|].
  split; [exact Hk|].
  exact Hlen.
Qed.

Lemma vecend_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 :
  bd_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  bd_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 464 + 400) (PNM.b_sb s1 + 40 * Z.of_nat (length (PNM.b_stk s1))).
Proof.
  intros CTX G LM.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 0, sp - 160 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  pose proof RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA1, OACC1. change (PNRA.o_is PMA.AD fb) with (fb + 96) in PA1.
  change (PNM.PSIZE + 8) with 424 in OACC1.
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1 OACC1) as ((O1 & O8 & ONSH) & Zop & OWR & OCE & OVIS & AOP).
  pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SV1 & _). change PNM.OFF_STK with 392 in SV1.
  pose proof SV1 as (V0 & V8 & _). change PNM.BSZ with 40 in V8.
  apply (proj2 (L5A.u64_at_vis _ M1 (fb + 464 + 400) _ (OVIS (fb + 464 + 400) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1; lia))).
  replace (fb + 464 + 400) with (fb + 464 + 392 + 8) by (clear; lia). exact V8.
Qed.

Lemma rdn_def_hi (M : mem) : forall (n : nat) a bs, rdn RSEGS M (Z_to_bv 64 a) n = Some bs ->
  6905856 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  forall i, (i < n)%nat -> M (Z_to_bv 64 (a + Z.of_nat i)) <> None.
Proof.
  induction n as [|n IH]; intros a bs E Ha Hn i Hi; [lia|].
  cbn [rdn] in E. destruct (M (Z_to_bv 64 a)) as [x|] eqn:Ea.
  - destruct i as [|i]; [rewrite Z.add_0_r, Ea; discriminate|].
    rewrite L5C.add1_lit in E. destruct (rdn RSEGS M (Z_to_bv 64 (a + 1)) n) as [rest|] eqn:Er; [|discriminate E].
    replace (a + Z.of_nat (Datatypes.S i)) with (a + 1 + Z.of_nat i) by lia. apply (IH (a + 1) rest Er); lia.
  - exfalso. rewrite (BatByteCell_b.art_seg_rom_off (Z_to_bv 64 a)) in E; [discriminate E|].
    right. rewrite Z_to_bv_unsigned, bv_wrap_small; [lia| unfold bv_modulus; cbn; lia].
Qed.

Lemma rdn_nth_hi (M : mem) : forall (n : nat) a bs, rdn RSEGS M (Z_to_bv 64 a) n = Some bs ->
  forall i, (i < n)%nat -> M (Z_to_bv 64 (a + Z.of_nat i)) <> None -> M (Z_to_bv 64 (a + Z.of_nat i)) = nth_error bs i.
Proof.
  induction n as [|n IH]; intros a bs E i Hi D; [lia|].
  cbn [rdn] in E. destruct (M (Z_to_bv 64 a)) as [x|] eqn:Ea.
  - rewrite L5C.add1_lit in E. destruct (rdn RSEGS M (Z_to_bv 64 (a + 1)) n) as [rest|] eqn:Er; [|discriminate E].
    injection E as <-. destruct i as [|i].
    + cbn. rewrite Z.add_0_r. exact Ea.
    + cbn [nth_error]. replace (a + Z.of_nat (Datatypes.S i)) with (a + 1 + Z.of_nat i) by lia. apply (IH (a + 1) rest Er i); [lia|].
      replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (Datatypes.S i)) by lia. exact D.
  - destruct i as [|i]; [rewrite Z.add_0_r in D; exfalso; apply D; exact Ea|].
    destruct (seg_rom RSEGS (Z_to_bv 64 a)) as [y|]; [|discriminate E]. rewrite L5C.add1_lit in E.
    destruct (rdn RSEGS M (Z_to_bv 64 (a + 1)) n) as [rest|] eqn:Er; [|discriminate E].
    injection E as <-. cbn [nth_error]. replace (a + Z.of_nat (Datatypes.S i)) with (a + 1 + Z.of_nat i) by lia. apply (IH (a + 1) rest Er i); [lia|].
    replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (Datatypes.S i)) by lia. exact D.
Qed.

Lemma u64_same_hi (M M' : mem) a v i : 6905856 <= a -> a + 8 <= 2 ^ 64 ->
  L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M' a v -> a <= i < a + 8 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i).
Proof.
  intros H0 H1 U U' Hi. unfold L5.u64_at in U, U'.
  replace i with (a + Z.of_nat (Z.to_nat (i - a))) by lia.
  assert (Hj : (Z.to_nat (i - a) < 8)%nat) by Lia.lia.
  rewrite (rdn_nth_hi M' 8 a _ U' (Z.to_nat (i - a)) Hj (rdn_def_hi M' 8 a _ U' H0 ltac:(cbn; lia) (Z.to_nat (i - a)) Hj)).
  rewrite (rdn_nth_hi M 8 a _ U (Z.to_nat (i - a)) Hj (rdn_def_hi M 8 a _ U H0 ltac:(cbn; lia) (Z.to_nat (i - a)) Hj)).
  reflexivity.
Qed.


Lemma bregs_pres R R4 R5 sp fb F : bregs R R4 sp fb F -> regs_preserved R4 R5 -> bregs R R5 sp fb F.
Proof.
  intros (E2 & E3 & E4 & E8 & E9 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27) RP.
  assert (CS : forall i, In i L5SAR.cs_all -> getr R5 (reg i) = getr R4 (reg i)) by (intros i Hi; exact (L5SAR.cs_of_preserved R4 R5 i RP Hi)).
  unfold bregs. rewrite !CS by (apply L5K.In_of_mem; vm_compute; reflexivity). repeat split; assumption.
Qed.

Lemma bregsT_pres R R4 R5 sp fb F : bregsT R R4 sp fb F -> regs_preserved R4 R5 -> bregsT R R5 sp fb F.
Proof.
  intros (E2 & E3 & E4 & E8 & E9 & E18 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27) RP.
  assert (CS : forall i, In i L5SAR.cs_all -> getr R5 (reg i) = getr R4 (reg i)) by (intros i Hi; exact (L5SAR.cs_of_preserved R4 R5 i RP Hi)).
  unfold bregsT. rewrite !CS by (apply L5K.In_of_mem; vm_compute; reflexivity). repeat split; assumption.
Qed.

Lemma bregsE_pres R R4 R5 sp fb F : bregsE R R4 sp fb F -> regs_preserved R4 R5 -> bregsE R R5 sp fb F.
Proof.
  intros (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E25 & E26 & E27) RP.
  assert (CS : forall i, In i L5SAR.cs_all -> getr R5 (reg i) = getr R4 (reg i)) by (intros i Hi; exact (L5SAR.cs_of_preserved R4 R5 i RP Hi)).
  unfold bregsE. rewrite !CS by (apply L5K.In_of_mem; vm_compute; reflexivity). repeat split; assumption.
Qed.

Lemma bd_arm_err4 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 (fx6 : FPState) R6 ev ec :
  PNRAa.make_ec_spec L ar HI ->
  bd_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  bd_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 ->
  bregsE R R6 sp fb F -> spill M6 sp F ->
  PMSPA.ec_at RSEGS M6 (fb + 1024) ev ec ->
  getr R6 (reg 1) = Z_to_bv 64 0xaec90 -> getr R6 (reg 10) = Z_to_bv 64 (fb + 1024) -> getr R6 (reg 11) = Z_to_bv 64 4 ->
  PNRA.binv s6 -> (length (PNM.b_stk s) <= length (PNM.b_stk s6))%nat ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 (pa_make_ec PMA.AD) M6 model6) K.
Proof.
  intros MKE CTX G LM ER SPL EC6 X1 X10 X11 INV6 LEN6.
  pose proof CTX as (_ & _ & _ & _ & ENT & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof ER as (E2 & E3 & E4 & _).
  apply (PNABDK.bd_call_mkec L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 fx6 R6 0xaec90 4 ev ec MKE CTX G LM EC6).
  { exact X1. } { unfold L5.ra_ok; clear; lia. } { exact E2. } { rewrite E3. exact Rgp. } { rewrite E4. exact Rtp. } { exact X10. } { exact X11. } { clear; lia. }
  intros fx7 R7 M7 model7 LK7 Aw7 RP7 EC7 LM7 AG7.
  pose proof (bregsE_pres R R6 R7 sp fb F ER RP7) as ER7.
  pose proof (PNABDK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M7 model7 LK7 Aw7 s6 sm6 _ cr6 CTX G LM7)
    as (PF & OWN7 & SV7 & U8v7 & WRop7 & U8op7 & SVr7).
  pose proof (vfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M7 model7 LK7 Aw7 s6 sm6 _ cr6 CTX G LM7) as (vf1 & _).
  pose proof (mfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M7 model7 LK7 Aw7 s6 sm6 _ cr6 CTX G LM7) as (WRmo & _).
  set (MV7 := mrestrict (ahid Aw7 model7) M7) in *.
  unfold pfacts in PF. destruct PF as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32 & pf33 & pf34).
  assert (SPL7 : spill M7 sp F) by (apply (PNABDK.spill_agree M6 M7 sp F); [clear - pf4; lia| clear - pf4; lia| exact SPL| intros a Ha; apply AG7; clear - Ha; lia]).
  pose proof (SV7 (sp - 128) F ltac:(clear; lia) ltac:(clear; lia) SPL7) as SPLv.
  destruct ER7 as (E2' & E3' & E4' & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E25 & E26 & E27).
  unfold own in OWN7. destruct OWN7 as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & O12 & O13).
  assert (Q34 : 0 <= fb + 432 < 2 ^ 64) by (clear - vf1; lia).
  assert (Q36 : 0 <= fb + 1024 < 2 ^ 64) by (clear - pf7; lia).
  pose proof (bvu_rng (getr R (reg 1))) as Q60.
  pose proof (bvu_rng (getr R (reg 8))) as Q61.
  pose proof (bvu_rng (getr R (reg 9))) as Q62.
  pose proof (bvu_rng (getr R (reg 18))) as Q63.
  pose proof (bvu_rng (getr R (reg 19))) as Q64.
  pose proof (bvu_rng (getr R (reg 20))) as Q65.
  pose proof (bvu_rng (getr R (reg 21))) as Q66.
  pose proof (bvu_rng (getr R (reg 22))) as Q67.
  pose proof (bvu_rng (getr R (reg 23))) as Q68.
  pose proof (bvu_rng (getr R (reg 24))) as Q69.
  pose proof (bvu_rng (getr R (reg 25))) as Q70.
  pose proof (bvu_rng (getr R (reg 26))) as Q71.
  pose proof (bvu_rng (getr R (reg 27))) as Q72.
  LeanFeed.pfeed P (PNABDP.abdE4_conc fx7 R7 MV7 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | 60%nat => bv_unsigned (getr R (reg 1)) | 61%nat => bv_unsigned (getr R (reg 8)) | 62%nat => bv_unsigned (getr R (reg 9)) | 63%nat => bv_unsigned (getr R (reg 18)) | 64%nat => bv_unsigned (getr R (reg 19)) | 65%nat => bv_unsigned (getr R (reg 20)) | 66%nat => bv_unsigned (getr R (reg 21)) | 67%nat => bv_unsigned (getr R (reg 22)) | 68%nat => bv_unsigned (getr R (reg 23)) | 69%nat => bv_unsigned (getr R (reg 24)) | 70%nat => bv_unsigned (getr R (reg 25)) | 71%nat => bv_unsigned (getr R (reg 26)) | 72%nat => bv_unsigned (getr R (reg 27)) | _ => 0 end)) ltac:(first [assumption | unfold PNABDP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & Y1 & Y2 & Y8 & Y9 & Y10 & Y11 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27 & FL0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & MO0 & _).
  apply (PNABDK.bd_fin L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M7 model7 LK7 Aw7 s6 sm6 _ cr6
           fx7 fx9 R7 R9 0xaec90 0 M9v CTX G LM7 MS9 MG9).
  - intros a Ha N. apply FRZ9; [exact Ha| | | |]; intros X; apply N; unfold PMAUK.WretX, PMAUK.Wret; change (ff_bytes 0 / 8) with 8; unfold SB.
    + right. clear - X; lia.
    + left; left; left. clear - X; lia.
    + left; left; right. clear - X; lia.
    + left; right. clear - X; lia.
  - exact FL0.
  - replace (fb + 472) with (fb + 464 + 8) by (clear; lia). exact MO0.
  - left; reflexivity.
  - exact Y2.
  - intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [assumption|]). destruct Hk.
  - intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[]]].
    + rewrite (KS9 3%nat) by inl. exact E3'.
    + rewrite (KS9 4%nat) by inl. exact E4'.
  - left. exists 4. split; [clear; lia|]. split; [exact EC7|]. split; [reflexivity| apply bax_cat_add].
  - exact INV6.
  - exact LEN6.
Qed.


Lemma bd_arm_err1 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 (fx6 : FPState) R6 ev ec :
  PNRAa.make_ec_spec L ar HI ->
  bd_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  bd_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 ->
  bregs R R6 sp fb F -> getr R6 (reg 18) = Z_to_bv 64 4 -> spill M6 sp F ->
  PMSPA.ec_at RSEGS M6 (fb + 1024) ev ec ->
  getr R6 (reg 1) = Z_to_bv 64 0xaecb8 -> getr R6 (reg 10) = Z_to_bv 64 (fb + 1024) -> getr R6 (reg 11) = Z_to_bv 64 1 ->
  PNRA.binv s6 -> (length (PNM.b_stk s) <= length (PNM.b_stk s6))%nat ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 (pa_make_ec PMA.AD) M6 model6) K.
Proof.
  intros MKE CTX G LM ER X18 SPL EC6 X1 X10 X11 INV6 LEN6.
  pose proof CTX as (_ & _ & _ & _ & ENT & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof ER as (E2 & E3 & E4 & _).
  apply (PNABDK.bd_call_mkec L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 fx6 R6 0xaecb8 1 ev ec MKE CTX G LM EC6).
  { exact X1. } { unfold L5.ra_ok; clear; lia. } { exact E2. } { rewrite E3. exact Rgp. } { rewrite E4. exact Rtp. } { exact X10. } { exact X11. } { clear; lia. }
  intros fx7 R7 M7 model7 LK7 Aw7 RP7 EC7 LM7 AG7.
  pose proof (bregs_pres R R6 R7 sp fb F ER RP7) as ER7.
  assert (X18' : getr R7 (reg 18) = Z_to_bv 64 4) by (rewrite (L5SAR.cs_of_preserved R6 R7 18%nat RP7) by inl; exact X18).
  pose proof (PNABDK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M7 model7 LK7 Aw7 s6 sm6 _ cr6 CTX G LM7)
    as (PF & OWN7 & SV7 & U8v7 & WRop7 & U8op7 & SVr7).
  pose proof (vfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M7 model7 LK7 Aw7 s6 sm6 _ cr6 CTX G LM7) as (vf1 & _).
  pose proof (mfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M7 model7 LK7 Aw7 s6 sm6 _ cr6 CTX G LM7) as (WRmo & _).
  set (MV7 := mrestrict (ahid Aw7 model7) M7) in *.
  unfold pfacts in PF. destruct PF as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32 & pf33 & pf34).
  assert (SPL7 : spill M7 sp F) by (apply (PNABDK.spill_agree M6 M7 sp F); [clear - pf4; lia| clear - pf4; lia| exact SPL| intros a Ha; apply AG7; clear - Ha; lia]).
  pose proof (SV7 (sp - 128) F ltac:(clear; lia) ltac:(clear; lia) SPL7) as SPLv.
  destruct ER7 as (E2' & E3' & E4' & E8 & E9 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27).
  unfold own in OWN7. destruct OWN7 as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & O12 & O13).
  assert (Q34 : 0 <= fb + 432 < 2 ^ 64) by (clear - vf1; lia).
  assert (Q36 : 0 <= fb + 1024 < 2 ^ 64) by (clear - pf7; lia).
  pose proof (bvu_rng (getr R (reg 1))) as Q60.
  pose proof (bvu_rng (getr R (reg 8))) as Q61.
  pose proof (bvu_rng (getr R (reg 9))) as Q62.
  pose proof (bvu_rng (getr R (reg 18))) as Q63.
  pose proof (bvu_rng (getr R (reg 19))) as Q64.
  pose proof (bvu_rng (getr R (reg 20))) as Q65.
  pose proof (bvu_rng (getr R (reg 21))) as Q66.
  pose proof (bvu_rng (getr R (reg 22))) as Q67.
  pose proof (bvu_rng (getr R (reg 23))) as Q68.
  pose proof (bvu_rng (getr R (reg 24))) as Q69.
  pose proof (bvu_rng (getr R (reg 25))) as Q70.
  pose proof (bvu_rng (getr R (reg 26))) as Q71.
  pose proof (bvu_rng (getr R (reg 27))) as Q72.
  LeanFeed.pfeed P (PNABDP.abdE1_conc fx7 R7 MV7 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | 60%nat => bv_unsigned (getr R (reg 1)) | 61%nat => bv_unsigned (getr R (reg 8)) | 62%nat => bv_unsigned (getr R (reg 9)) | 63%nat => bv_unsigned (getr R (reg 18)) | 64%nat => bv_unsigned (getr R (reg 19)) | 65%nat => bv_unsigned (getr R (reg 20)) | 66%nat => bv_unsigned (getr R (reg 21)) | 67%nat => bv_unsigned (getr R (reg 22)) | 68%nat => bv_unsigned (getr R (reg 23)) | 69%nat => bv_unsigned (getr R (reg 24)) | 70%nat => bv_unsigned (getr R (reg 25)) | 71%nat => bv_unsigned (getr R (reg 26)) | 72%nat => bv_unsigned (getr R (reg 27)) | _ => 0 end)) ltac:(first [assumption | unfold PNABDP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & Y1 & Y2 & Y8 & Y9 & Y10 & Y11 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27 & FL0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & MO0 & _).
  apply (PNABDK.bd_fin L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M7 model7 LK7 Aw7 s6 sm6 _ cr6
           fx7 fx9 R7 R9 0xaecb8 0 M9v CTX G LM7 MS9 MG9).
  - intros a Ha N. apply FRZ9; [exact Ha| | | |]; intros X; apply N; unfold PMAUK.WretX, PMAUK.Wret; change (ff_bytes 0 / 8) with 8; unfold SB.
    + right. clear - X; lia.
    + left; left; left. clear - X; lia.
    + left; left; right. clear - X; lia.
    + left; right. clear - X; lia.
  - exact FL0.
  - replace (fb + 472) with (fb + 464 + 8) by (clear; lia). exact MO0.
  - left; reflexivity.
  - exact Y2.
  - intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [assumption|]). destruct Hk.
  - intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[]]].
    + rewrite (KS9 3%nat) by inl. exact E3'.
    + rewrite (KS9 4%nat) by inl. exact E4'.
  - left. exists 1. split; [clear; lia|]. split; [exact EC7|]. split; [reflexivity| apply bax_cat_add].
  - exact INV6.
  - exact LEN6.
Qed.


Lemma bd_tail K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 (fx6 : FPState) R6 :
  bd_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  bd_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 ->
  bregsT R R6 sp fb F -> spill M6 sp F -> L5.u64_at RSEGS M6 (sp - 144) (fb + 464 + 400) ->
  4136 <= bv_unsigned (getr R6 (reg 10)) <= 140737488355327 -> bv_unsigned (getr R6 (reg 10)) mod 8 = 0 ->
  L5.u64_at RSEGS (mrestrict (ahid Aw6 model6) M6) (fb + 464 + 400) (bv_unsigned (getr R6 (reg 10))) ->
  ( (exists v, 1 <= v <= 64 /\ PMSPA.ec_at RSEGS M6 (fb + 1024) v (pa_errcat_obj PMA.AD) /\ PNM.b_more s6 = 0 /\ PNST.bax_cat ax6 = true)
    \/ (PMSPA.ec_at RSEGS M6 (fb + 1024) e cat /\ PNRA.bpush_rel s s6 sm sm6) ) ->
  PNRA.binv s6 -> (length (PNM.b_stk s) <= length (PNM.b_stk s6))%nat ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 0xaebb4 M6 model6) K.
Proof.
  intros CTX G LM ER SPL C144 X10a X10b E400v POST INV6 LEN6.
  pose proof (PNABDK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM)
    as (PF & OWN6 & SV6 & U8v6 & WRop6 & U8op6 & SVr6).
  pose proof (vfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM) as (vf1 & _).
  set (MV6 := mrestrict (ahid Aw6 model6) M6) in *.
  unfold pfacts in PF. destruct PF as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32 & pf33 & pf34).
  pose proof (SV6 (sp - 128) F ltac:(clear; lia) ltac:(clear; lia) SPL) as SPLv.
  pose proof (SV6 (sp - 144) (fb + 464 + 400) ltac:(clear; lia) ltac:(clear; lia) C144) as C144v.
  destruct ER as (E2 & E3 & E4 & E8 & E9 & E18 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27).
  unfold own in OWN6. destruct OWN6 as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & O12 & O13).
  assert (Q34 : 0 <= fb + 432 < 2 ^ 64) by (clear - vf1; lia).
  assert (Q36 : 0 <= fb + 1024 < 2 ^ 64) by (clear - pf7; lia).
  pose proof (bvu_rng (getr R (reg 1))) as Q60.
  pose proof (bvu_rng (getr R (reg 8))) as Q61.
  pose proof (bvu_rng (getr R (reg 9))) as Q62.
  pose proof (bvu_rng (getr R (reg 18))) as Q63.
  pose proof (bvu_rng (getr R (reg 19))) as Q64.
  pose proof (bvu_rng (getr R (reg 20))) as Q65.
  pose proof (bvu_rng (getr R (reg 21))) as Q66.
  pose proof (bvu_rng (getr R (reg 22))) as Q67.
  pose proof (bvu_rng (getr R (reg 23))) as Q68.
  pose proof (bvu_rng (getr R (reg 24))) as Q69.
  pose proof (bvu_rng (getr R (reg 25))) as Q70.
  pose proof (bvu_rng (getr R (reg 26))) as Q71.
  pose proof (bvu_rng (getr R (reg 27))) as Q72.
  assert (WV6 : L5.writable RSEGS MV6 (fb + 464 + 392) 24) by (apply (L5.writable_sub RSEGS MV6 (fb + 464) 424); [exact WRop6| clear; lia| clear; lia]).
  LeanFeed.pfeed P (PNABDP.abdT_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | 60%nat => bv_unsigned (getr R (reg 1)) | 61%nat => bv_unsigned (getr R (reg 8)) | 62%nat => bv_unsigned (getr R (reg 9)) | 63%nat => bv_unsigned (getr R (reg 18)) | 64%nat => bv_unsigned (getr R (reg 19)) | 65%nat => bv_unsigned (getr R (reg 20)) | 66%nat => bv_unsigned (getr R (reg 21)) | 67%nat => bv_unsigned (getr R (reg 22)) | 68%nat => bv_unsigned (getr R (reg 23)) | 69%nat => bv_unsigned (getr R (reg 24)) | 70%nat => bv_unsigned (getr R (reg 25)) | 71%nat => bv_unsigned (getr R (reg 26)) | 72%nat => bv_unsigned (getr R (reg 27)) | _ => 0 end)) ltac:(first [assumption | unfold PNABDP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & Y1 & Y2 & Y8 & Y9 & Y10 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27 & FL0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & E400 & _).
  assert (FRZ9' : forall i, 0 <= i < 2 ^ 64 -> ~ (F + 0 <= i < F + 0 + 8) -> ~ (F / 8 + 2147450880 + 0 <= i < F / 8 + 2147450880 + 0 + 8) -> ~ (fl + 0 <= i < fl + 0 + 1) -> M9v (Z_to_bv 64 i) = MV6 (Z_to_bv 64 i)).
  { intros i Hi N1 N2 N3.
    destruct (Z_lt_le_dec i (fb + 464 + 400)) as [La|La]; [apply FRZ9; [exact Hi| exact N1| exact N2| exact N3| clear - La; lia]|].
    destruct (Z_lt_le_dec i (fb + 464 + 408)) as [Lb|Lb]; [|apply FRZ9; [exact Hi| exact N1| exact N2| exact N3| clear - Lb; lia]].
    apply (u64_same_hi MV6 M9v (fb + 464 + 400) (bv_unsigned (getr R6 (reg 10)))); [clear - pf7; lia| clear - pf7; lia| exact E400v| exact E400| clear - La Lb; lia]. }
  pose proof (fdiv_rng F pf15) as (DF1 & DF2).
  pose proof LM as (_ & RP6 & _). pose proof RP6 as (PA6 & _). change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA6.
  pose proof PA6 as (_ & _ & _ & MORE6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MB6 & _).
  apply (PNABDK.bd_fin L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6
           fx6 fx9 R6 R9 0xaebb4 (PNM.b_more s6) M9v CTX G LM MS9 MG9).
  - intros a Ha N. apply FRZ9'; [exact Ha| | |]; intros X; apply N; unfold PMAUK.WretX, PMAUK.Wret; change (ff_bytes 0 / 8) with 8; unfold SB.
    + left; left; left. clear - X; lia.
    + left; left; right. clear - X; lia.
    + left; right. clear - X; lia.
  - exact FL0.
  - replace (fb + 472) with (fb + 464 + 8) by (clear; lia).
    apply (L5C.u8_at_agree RSEGS MV6 M9v); [| clear - pf7; lia| clear - pf7; lia| exact (proj2 (U8op6 _) MORE6)].
    intros j Hj. apply FRZ9'; [clear - Hj pf7; lia| clear - Hj pf28; lia| clear - Hj pf9 DF1 DF2; lia| clear - Hj pf29; lia].
  - exact MB6.
  - exact Y2.
  - intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [assumption|]). destruct Hk.
  - intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[]]].
    + rewrite (KS9 3%nat) by inl. exact E3.
    + rewrite (KS9 4%nat) by inl. exact E4.
  - destruct POST as [(v & Hv & ECv & MO & CAT)|(EC6 & PR)].
    + left. exists v. split; [exact Hv|]. split; [exact ECv|]. split; [exact MO| exact CAT].
    + right. split; [exact EC6| exact PR].
  - exact INV6.
  - exact LEN6.
Qed.

Let base_keepW := PNBKA.base_keepW L ar C LY.
Let berr_keep := PNBKA.berr_keep L ar C LY.
Let pre_after_call := PNBKA.pre_after_call L ar.
Let blk_ceil := PNBKA.blk_ceil L ar C HI HIok.

(* [comment removed for export] *)
Lemma bd_piece_mo K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1
      (fx1 fx2 : FPState) R1 R2 (pc1 pc2 mo : Z) (M2v : mem) (W : Z -> Prop) :
  bd_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  bd_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  msteps RSEGS (st fx1 R1 pc1 (mrestrict (ahid Aw1 model1) M1)) (st fx2 R2 pc2 M2v) ->
  mem_grows (mrestrict (ahid Aw1 model1) M1) M2v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M2v (Z_to_bv 64 a) = mrestrict (ahid Aw1 model1) M1 (Z_to_bv 64 a)) ->
  (forall a, W a -> sp - 224 <= a < sp - 104 \/ fb + 472 <= a < fb + 473) ->
  L5.u8_at RSEGS M2v (fb + 472) mo -> (mo = 0 \/ mo = 1) ->
  (forall (M3 : mem) model3,
      bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK1 Aw1 (PNBO.set_more s1 mo) sm1 ax1 cr1 ->
      ahid Aw1 model3 = ahid Aw1 model1 -> mrestrict (ahid Aw1 model1) M3 = M2v ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> mem_grows M1 M3 ->
      (forall v c, PMSPA.ec_at RSEGS M1 (fb + 1024) v c -> PMSPA.ec_at RSEGS M3 (fb + 1024) v c) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 pc2 M3 model3) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M1 model1) K.
Proof.
  intros CTX G LM MS MG FRZ WP MO9 Hmo KR.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 7) with 26624 in *.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
  assert (FBI : 6905856 <= fb) by (clear - F1 FSAPP FSIMG; lia).
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold bd_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 0, sp - 160 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  pose proof RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA1, IA1, VIS1, VREF1, OACC1. change (PNRA.o_is PMA.AD fb) with (fb + 96) in PA1, IA1. change (PNRA.o_v PMA.AD fb) with (fb + 432) in VIS1, VREF1.
  change (PNM.PSIZE + 8) with 424 in OACC1.
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1 OACC1) as ((O1 & O8 & ONSH) & Zop & OWR & OCE & OVIS & AOP).
  set (op := fb + 464) in *. set (ois := fb + 96) in *.
  pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
  pose proof GFR as (GF1 & GF2 & _).
  assert (R4a : 0 <= F / 8 + 2147450880) by (clear - GF1; lia).
  assert (R4b : F / 8 + 2147450880 + 1 <= 2 ^ 64) by (clear - GF2; pose proof (Z.div_le_upper_bound F 8 17592186044408 ltac:(lia) ltac:(lia)); lia).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 sp 26624 160 HH1 ASTK1 ltac:(lia)) as (SL160 & SH160 & SWR).
  set (H1 := ahid Aw1 model1) in *.
  assert (OPS : op + 416 <= sp - 160) by (unfold op; clear - F2 FSCEIL GSLO; lia).
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF' LK1 cr1 Aw1 M1 model1 fx1 fx2 R1 pc1 R2 pc2 M2v W K HH1 AM1 MS MG FRZ).
  { intros a Ha Wa. destruct (WP a Wa) as [X|X].
    - split; [| clear - X GSLO GSHI GSPT FBI; lia].
      unfold aclientw, aclient_g. right; left. split; [clear - X GSLO GSHI GSPT; lia| intros Y; clear - Y; lia].
    - split; [| clear - X FBI; lia].
      apply (L5SAR.fframe_client L ar (PNM.bparser_own s1 ++ LBX) FF' 0 0 fb 5 rs); [right; exact Hfb| change (ff_bytes 5) with 2048; clear - X; lia]. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MG3 FR3 VV3. change (mrestrict H1 M3 = M2v) in VIS3.
  set (W8 := [(fb + 472, 1)]).
  assert (EK13 : L5SAR.ek L ar (PNM.bparser_own s1 ++ LBX) FF' (sp - 104) 120 W8 M1 M3).
  { intros a (Ha & Hc & Ho). apply FR3; [exact Ha|]. intros Wa. destruct (WP a Wa) as [X|X].
    - destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF' LK1 cr1 Aw1 M1 _ (sp - 104) 120 a HH1 GSPT Hc) as [Y|Y]; [clear - X Y; lia| clear - X Y GSLO; lia].
    - apply (Ho (fb + 472, 1)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X; lia]. }
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as FRB1. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as BRB1.
  assert (WAPP8 : PMKA.wapp W8).
  { apply PMKA.wapp_cons; [| apply PMKA.wapp_nil]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct FA1 as [Y|Y]; clear - Y F1 F2; lia. }
  assert (OUT8 : forall a n, (a + n <= op + 8 \/ op + 9 <= a) -> forall i, a <= i < a + n -> L5.outside W8 i).
  { intros a n X3 i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. unfold op in X3. clear - Hi Hr X3. lia. }
  assert (OUTB8 : forall q m, In (q, m) (PNM.bparser_own s1 ++ LBX) -> forall i, q <= i < q + m -> L5.outside W8 i).
  { intros q m Hq i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr.
    destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m op 416 HH1 Hq (PMAUAR.aobjA_push FF op 416 _ (PNAPAR.aobj_fbB FF fb op 416 FOK ltac:(unfold op; clear; lia) ltac:(unfold op; clear; lia)))) as [Z0|Z0]; unfold op in Z0; clear - Hi Hr Z0; lia. }
  assert (MOf : L5.u8_at RSEGS M3 (op + 8) mo).
  { apply (proj1 (L5A.u8_at_vis H1 M3 (op + 8) mo (OVIS (op + 8) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1; lia))). rewrite VIS3. replace (op + 8) with (fb + 472) by (unfold op; clear; lia). exact MO9. }
  set (s9 := PNBO.set_more s1 mo).
  assert (PA9 : PNM.bparser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA (pa_vp_parser PMA.AD) M3 op ois s9).
  { apply (bparser_set_moreS M1 M3 (pa_vp_parser PMA.AD) op ois s1 mo ltac:(clear - O1; lia) ltac:(clear - O1; lia)); [| | | exact MOf| exact Hmo| exact PA1].
    - intros i Hi Hn. destruct (Z_lt_le_dec i (op + 8)) as [X|X].
      + refine (proj1 (PMKA.agA_obj L ar _ FF' (sp - 104) 120 _ M1 M3 EK13 WAPP8 FRB1 op 8 _ _) i _); [| apply OUT8; clear; lia| clear - Hi X; lia].
        apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb op 8 FOK); unfold op; clear; lia.
      + refine (proj1 (PMKA.agA_obj L ar _ FF' (sp - 104) 120 _ M1 M3 EK13 WAPP8 FRB1 (op + 9) 407 _ _) i _); [| apply OUT8; clear; lia| clear - Hi X Hn; lia].
        apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb (op + 9) 407 FOK); unfold op; clear; lia.
    - intros i Hi. refine (PMKA.agsh_obj L ar _ FF' (sp - 104) 120 _ M1 M3 EK13 WAPP8 FRB1 op 416 _ i Hi). apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb op 416 FOK); unfold op; clear; lia.
    - intros q m Hq. assert (HqL : In (q, m) (PNM.bparser_own s1 ++ LBX)) by (apply in_or_app; left; exact Hq). destruct (BRB1 _ HqL) as (B0 & B1). cbn [fst snd] in B0, B1.
      split; [exact B0|]. split; [clear - B1; lia|]. apply (PMKA.agA_blk L ar _ FF' (sp - 104) 120 _ M1 M3 EK13 WAPP8 BRB1 q m HqL). apply OUTB8. exact HqL. }
  assert (IA9 : PM.iss_at RSEGS PMA.AD PMSPA.accA M3 ois str sm1).
  { apply (PMKA.iss_keepA RSEGS PMA.AD L ar _ FF' (sp - 104) 120 _ M1 M3 EK13 WAPP8 FRB1 BRB1 ois str sm1); [| | | | exact IA1].
    - apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb ois 272 FOK); unfold ois; clear; lia.
    - apply incl_appr. exact INCS.
    - apply OUT8. unfold ois, op; clear; lia.
    - intros c0 n0 p0 E0. unfold PMKA.blk_out. apply OUTB8. apply in_or_app; right. apply INCS. rewrite E0. left; reflexivity. }
  assert (BASE9 : PMSTA.base_okA RSEGS PMA.AD M3).
  { apply (PMASK.base_keep L ar C LY _ FF' (sp - 104) 120 _ M1 M3 EK13); [| exact BASE1]. intros a Ha rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Ha Hr FBI; lia. }
  assert (ERR9 : PNSTA.berr_okA RSEGS PMA.AD PMA.AAD PMA.AN M3 ax1).
  { apply (berr_keep _ FF' (sp - 104) 120 _ M1 M3 ax1 EK13); [| exact ERR1]. intros a Ha rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Ha Hr FBI; lia. }
  assert (ECK : forall v c, PMSPA.ec_at RSEGS M1 (fb + 1024) v c -> PMSPA.ec_at RSEGS M3 (fb + 1024) v c).
  { intros v0 c0 E0. apply (PMKA.ec_keepA RSEGS L ar _ FF' (sp - 104) 120 _ M1 M3 EK13 WAPP8 FRB1 (fb + 1024) v0 c0); [| | exact E0].
    - apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb (fb + 1024) 16 FOK); clear; lia.
    - apply OUT8. unfold op; clear; lia. }
  apply (KR M3 model3); [| exact HID3| exact VIS3| exact FR3| exact MG3| exact ECK].
  split.
  { pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
    unfold PMAUK.binv. split; [exact HH3|]. split; [exact AM3|]. split; [eapply L5LZ.model_rt_trans; [exact B3| exact MRT3]|].
    split; [exact B4|]. split; [exact B5|]. split; [eapply L5SAR.astk_grows; [exact B6| exact MG3]|].
    split. { eapply L5SAR.ek_trans; [exact B7|]. intros a (Ha & Hc & Ho). apply FR3; [exact Ha|]. intros Wa. destruct (WP a Wa) as [X|X].
             - destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 26624 a HH GSPT (L5SAR.aclient_appb L ar _ (PNM.bparser_own s) FF sp 26624 a Hc)) as [Y|Y];
                 [clear - X Y; lia| clear - X Y GSLO; lia].
             - apply (Ho (PNRA.o_p PMA.AD fb + 8, 8)); [unfold PNRA.W_brun; left; reflexivity| unfold L5.in_rng, PNRA.o_p, PMSP.o_p; cbn [fst snd pa_off_p PMA.AD PnLayoutA_b.ADDR_A]; clear - X; lia]. }
    split; [eapply L5SAR.dk_trans; [exact B8| apply L5SAR.dk_grows; exact MG3]|].
    split. { apply (GOWN M1 M3 B9). intros a Ha. apply FR3; [unfold ocell in Ha; clear - Ha GSPC GSHI GSPT; lia|]. intros Wa. destruct (WP a Wa) as [X|X]; unfold ocell in Ha; [clear - Ha X; lia| unfold op in OPS; clear - Ha X OPS; lia]. }
    eapply L5.defined_grows; [exact MG3| exact B10]. }
  split.
  { apply (pre_after_call (PNM.bparser_own s1 ++ LBX) FF' (sp - 104) 120 W8 M1 M3 fb s1 s9 str sm1 sm1 ax1 ax1 FRB1 EK13 WAPP8 FOK'); [| exact RP1| exact PA9| exact IA9| unfold s9; exact GR1| exact BASE9| exact ERR9].
    intros i Hi. apply (OUT8 i 1); [unfold op; clear - Hi; lia| clear; lia]. }
  split; [exact STEP1|]. split; [exact AXL1|]. split; [exact CK1|]. split; [| exact EBB1].
  apply (L5C.u8_at_agree RSEGS M1 M3); [| exact R4a| exact R4b| exact SHC1].
  intros j Hj. apply FR3; [clear - Hj R4a R4b; lia|]. intros Wj. destruct (WP _ Wj) as [X|X].
  - clear - X Hj SL160 GSPT GF2. pose proof (Z.div_le_upper_bound F 8 17592186044408 ltac:(lia) ltac:(lia)). lia.
  - destruct FA1 as [Y|Y]; clear - X Y Hj F1 F2 GF1 GF2; pose proof (Z.div_le_upper_bound F 8 17592186044408 ltac:(lia) ltac:(lia)); pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)); lia.
Qed.

(* [comment removed for export] *)
Definition set_vec (s : PNM.bpst) (b k : Z) (stk : list PNM.bstate) : PNM.bpst :=
  PNM.BPST (PNM.b_more s) (PNM.b_done s) (PNM.b_src s) (PNM.b_bb s) (PNM.b_nb s) (PNM.b_tb s) (PNM.b_ng s) (PNM.b_tg s) (PNM.b_bg s) b k stk.
Definition rest_own (s : PNM.bpst) : list (Z * Z) :=
  PM.src_own (PNM.b_src s) ++ PGV8.v8_own (PNM.b_bb s) ++ PM.vs_own (PNM.b_nb s) ++ PM.vs_own (PNM.b_tb s).
Lemma perm_stk {T} (a v b n t x : list T) : Permutation ((a ++ v ++ b ++ n ++ t) ++ x) (v ++ (a ++ b ++ n ++ t) ++ x).
Proof.
  rewrite <- !app_assoc. rewrite (app_assoc a v), (app_assoc v a). apply Permutation_app_tail. apply Permutation_app_comm.
Qed.
Lemma perm_own s LBX : Permutation (PNM.bparser_own s ++ LBX) (PNM.bvec_own (PNM.b_sb s) (PNM.b_sk s) ++ rest_own s ++ LBX).
Proof. unfold PNM.bparser_own, PNM.brest_own, rest_own. apply perm_stk. Qed.
Lemma perm_own' s b k stk LBX : Permutation (PNM.bvec_own b k ++ rest_own s ++ LBX) (PNM.bparser_own (set_vec s b k stk) ++ LBX).
Proof. apply Permutation_sym. unfold PNM.bparser_own, PNM.brest_own, rest_own, set_vec. cbn [PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk]. apply perm_stk. Qed.
Lemma rest_incl s : incl (rest_own s) (PNM.bparser_own s).
Proof. unfold rest_own, PNM.bparser_own, PNM.brest_own. intros x Hx. revert Hx. rewrite !in_app_iff. clear. tauto. Qed.

Lemma bparser_revecS (M M' : mem) vp op ois s b' k' stk' :
  0 <= op -> op + 416 <= 2 ^ 64 ->
  (forall i, op <= i < op + 392 -> PNBOA.snt M M' i) ->
  (forall i, op <= i < op + 416 -> PNBOA.sns M M' i) ->
  (forall i, op <= i < op + 416 -> M (Z_to_bv 64 i) <> None -> M' (Z_to_bv 64 i) <> None) ->
  (forall B m, In (B, m) (rest_own s) -> 0 <= B /\ B + m <= 2 ^ 64 /\ PMFA.agA M M' B m) ->
  PNM.bvec_at RSEGS PMSPA.accA PMSPA.annA M' (op + 392) b' k' stk' ->
  PNM.bparser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA vp M op ois s -> PNM.bparser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA vp M' op ois (set_vec s b' k' stk').
Proof.
  intros Ho Ho' No So Do AGb STK' PA. pose proof PA as (_ & _ & _ & H8 & H9 & _ & _ & _ & SRC & _ & _ & BB & NB & TB & STK & M01 & D01).
  unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *.
  assert (BLK : forall B m, In (B, m) (rest_own s) -> 0 <= m -> (forall i, B <= i < B + m -> PNBOA.snt M M' i) /\ (forall i, B <= i < B + m -> PNBOA.sns M M' i) /\ 0 <= B /\ B + m <= 2 ^ 64).
  { intros B m Hi Hm. destruct (AGb B m Hi) as (B0 & B1 & AG). split; [exact (PNBOA.agA_snt M M' _ _ AG)|]. split; [exact (PNBOA.agA_sns M M' _ _ AG)|]. clear - B0 B1; lia. }
  assert (BLKG : forall B m, In (B, m) (rest_own s) -> 0 <= m -> B mod 8 = 0 -> forall i, B <= i < B + PNBOA.gspan m -> PNBOA.sns M M' i).
  { intros B m Hi Hm HB. destruct (AGb B m Hi) as (B0 & B1 & [_ AG]). exact (PNBOA.agsh_gspan M M' B m HB Hm AG). }
  assert (Iq : In (PM.sr_qc (PNM.b_src s), PM.CHUNK) (rest_own s)) by (unfold rest_own, PM.src_own; left; reflexivity).
  assert (Ib : forall B m, In (B, m) (PGV8.v8_own (PNM.b_bb s)) -> In (B, m) (rest_own s)) by (intros B m X; unfold rest_own; rewrite !in_app_iff; clear - X; tauto).
  assert (In_ : forall B m, In (B, m) (PM.vs_own (PNM.b_nb s)) -> In (B, m) (rest_own s)) by (intros B m X; unfold rest_own; rewrite !in_app_iff; clear - X; tauto).
  assert (It : forall B m, In (B, m) (PM.vs_own (PNM.b_tb s)) -> In (B, m) (rest_own s)) by (intros B m X; unfold rest_own; rewrite !in_app_iff; clear - X; tauto).
  pose proof SRC as (_ & _ & _ & _ & _ & _ & _ & _ & Qr & _).
  destruct (BLK _ _ Iq ltac:(unfold PM.CHUNK; clear; lia)) as (NTq & NSq & Q0 & Q1).
  apply (PNBOA.bparser_at_xfer RSEGS PMA.AD vp M M' (PNBOA.snt M M') (fun i => M (Z_to_bv 64 i) <> None -> M' (Z_to_bv 64 i) <> None) (PNBOA.sns M M')
           (PNBOA.sAGX M M') (fun i Y => Y) (PNBOA.sSHX M M') op ois s _ Ho Ho' PA); unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK, set_vec;
    cbn [PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk PNM.b_stk].
  - exact Do.
  - exact So.
  - intros i Hi. apply No. clear - Hi; lia.
  - intros i Hi. apply No. clear - Hi; lia.
  - intros i Hi. apply No. clear - Hi; lia.
  - intros i Hi. apply No. clear - Hi; lia.
  - apply (L5C.u8_at_agree RSEGS M M'); [apply PNBOA.sAGX; [clear - Ho; lia|clear - Ho'; lia|intros i Hi; apply No; clear - Hi; lia]|clear - Ho; lia|clear - Ho'; lia|exact H8].
  - apply (L5C.u8_at_agree RSEGS M M'); [apply PNBOA.sAGX; [clear - Ho; lia|clear - Ho'; lia|intros i Hi; apply No; clear - Hi; lia]|clear - Ho; lia|clear - Ho'; lia|exact H9].
  - exact M01.
  - exact D01.
  - apply (PNBOA.src_keep_S RSEGS M M'); [clear - Ho; lia|clear - Ho'; lia|clear - Q0; lia|clear - Q1; lia| intros i Hi; apply No; clear - Hi; lia| exact NTq| intros i Hi; apply So; clear - Hi; lia| exact NSq| exact SRC].
  - apply (PNBOA.v8_keep_S RSEGS M M'); [clear - Ho; lia|clear - Ho'; lia| intros i Hi; apply No; clear - Hi; lia| intros i Hi; apply So; clear - Hi; lia| | | exact BB].
    + intros B m Hi i Hr. pose proof (Ib B m Hi) as OI. destruct (PNM.b_bb s) eqn:EBB; cbn in Hi; [destruct Hi| destruct Hi as [Hi|[]]; inversion Hi; subst].
      unfold PGV8.v8_at in BB. destruct BB as (_ & _ & _ & _ & _ & Hn & Hc & _). destruct (BLK _ _ OI ltac:(clear - Hn Hc; lia)) as (X & _). apply X. exact Hr.
    + intros B m Hi. pose proof (Ib B m Hi) as OI. destruct (PNM.b_bb s) eqn:EBB; cbn in Hi; [destruct Hi| destruct Hi as [Hi|[]]; inversion Hi; subst].
      unfold PGV8.v8_at in BB. destruct BB as (_ & _ & _ & _ & _ & Hn & Hc & _ & Hal & _). exact (BLKG _ _ OI ltac:(clear - Hn Hc; lia) (PMFA.mod16_8 _ Hal)).
  - apply (PNBOA.vstr_keep_S RSEGS M M'); [clear - Ho; lia|clear - Ho'; lia| intros i Hi; apply No; clear - Hi; lia| intros i Hi; apply No; clear - Hi; lia| intros i Hi; apply So; clear - Hi; lia| | | exact NB].
    + intros B m Hi. pose proof (In_ B m Hi) as OI. destruct (PNM.b_nb s) eqn:EVS; cbn in Hi; [destruct Hi| destruct Hi as [Hi|[]]; inversion Hi; subst].
      unfold PM.vstr_at in NB. destruct NB as (_ & _ & _ & _ & _ & Hn & Hc & _). destruct (BLK _ _ OI ltac:(clear - Hn Hc; lia)) as (X & _). exact X.
    + intros B m Hi. pose proof (In_ B m Hi) as OI. destruct (PNM.b_nb s) eqn:EVS; cbn in Hi; [destruct Hi| destruct Hi as [Hi|[]]; inversion Hi; subst].
      unfold PM.vstr_at in NB. destruct NB as (_ & _ & _ & _ & _ & Hn & Hc & _). destruct (BLK _ _ OI ltac:(clear - Hn Hc; lia)) as (_ & X & _). exact X.
  - apply (PNBOA.vstr_keep_S RSEGS M M'); [clear - Ho; lia|clear - Ho'; lia| intros i Hi; apply No; clear - Hi; lia| intros i Hi; apply No; clear - Hi; lia| intros i Hi; apply So; clear - Hi; lia| | | exact TB].
    + intros B m Hi. pose proof (It B m Hi) as OI. destruct (PNM.b_tb s) eqn:EVS; cbn in Hi; [destruct Hi| destruct Hi as [Hi|[]]; inversion Hi; subst].
      unfold PM.vstr_at in TB. destruct TB as (_ & _ & _ & _ & _ & Hn & Hc & _). destruct (BLK _ _ OI ltac:(clear - Hn Hc; lia)) as (X & _). exact X.
    + intros B m Hi. pose proof (It B m Hi) as OI. destruct (PNM.b_tb s) eqn:EVS; cbn in Hi; [destruct Hi| destruct Hi as [Hi|[]]; inversion Hi; subst].
      unfold PM.vstr_at in TB. destruct TB as (_ & _ & _ & _ & _ & Hn & Hc & _). destruct (BLK _ _ OI ltac:(clear - Hn Hc; lia)) as (_ & X & _). exact X.
  - exact STK'.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma shz_at (M : mem) lo g p : shadow_zero M lo g -> lo mod 8 = 0 -> lo <= p -> p < lo + 8 * g -> byte_at M (S p) 0.
Proof.
  intros SZ L8 H1 H2. pose proof (SZ ((p - lo) / 8) ltac:(Lia.lia)) as X. replace (S p) with (S lo + (p - lo) / 8) by (unfold S, SB; Lia.lia). exact X.
Qed.
Lemma mod4_of16 sp d : sp mod 16 = 0 -> d mod 4 = 0 -> (sp - d) mod 4 = 0.
Proof. intros A D. Lia.lia. Qed.
Lemma mod8_of16 sp d : sp mod 16 = 0 -> d mod 8 = 0 -> (sp - d) mod 8 = 0.
Proof. intros A D. Lia.lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma bd_call_push K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 (fx1 : FPState) R1 (ra m n : Z) :
  PNSAXR.push_cont_slow_spec RSEGS PMA.AD L ar HI 0xb2758 ->
  bd_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  bd_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  getr R1 (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr R1 (reg 2) = Z_to_bv 64 (sp - 160) ->
  getr R1 (reg 3) = Z_to_bv 64 (pa_gp PMA.AD) -> getr R1 (reg 4) = Z_to_bv 64 (hl_tp L) ->
  getr R1 (reg 10) = Z_to_bv 64 (fb + 464 + 392) -> getr R1 (reg 11) = Z_to_bv 64 (sp - 120) -> getr R1 (reg 12) = Z_to_bv 64 (sp - 116) -> getr R1 (reg 13) = Z_to_bv 64 (sp - 112) ->
  L5.u32_at RSEGS M1 (sp - 120) m -> 0 <= m < 2 ^ 31 -> L5.u64_at RSEGS M1 (sp - 112) n -> 0 <= n < 2 ^ 64 ->
  Z.of_nat (length (PNM.b_stk s1)) <= 1024 -> 2 ^ PNM.b_sk s1 <= Z.of_nat (length (PNM.b_stk s1)) ->
  (forall (fx2 : FPState) R2 (M3 : mem) model3 LK3 Aw3 b' lenv cr3,
      regs_preserved R1 R2 -> 0 <= lenv < 2 ^ 64 ->
      getr R2 (reg 10) = Z_to_bv 64 (b' + 40 * (Z.of_nat (length (PNM.b_stk s1)) + 1)) -> 4096 <= b' -> b' + 40 * 2 ^ (PNM.b_sk s1 + 1) < 2 ^ 47 ->
      bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 (set_vec s1 b' (PNM.b_sk s1 + 1) (PNM.b_stk s1 ++ [PNM.BS m lenv n 0 0])) sm1 ax1 cr3 ->
      (forall a, sp - 160 <= a < sp - 104 -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
      (forall v c, PMSPA.ec_at RSEGS M1 (fb + 1024) v c -> PMSPA.ec_at RSEGS M3 (fb + 1024) v c) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 ra M3 model3) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb2758 M1 model1) K.
Proof.
  intros PSH CTX G LM X1 RAok X2 X3 X4 X10 X11 X12 X13 UM Hm UN Hn DEPTH FULL KR.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 7) with 26624 in *. change (26624 / 8) with 3328 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
  assert (FBI : 6905856 <= fb) by (clear - F1 FSAPP FSIMG; lia).
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold bd_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 0, sp - 160 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  pose proof RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA1, IA1, VIS1, VREF1, OACC1. change (PNRA.o_is PMA.AD fb) with (fb + 96) in PA1, IA1. change (PNRA.o_v PMA.AD fb) with (fb + 432) in VIS1, VREF1.
  change (PNM.PSIZE + 8) with 424 in OACC1.
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1 OACC1) as ((O1 & O8 & ONSH) & Zop & OWR & OCE & OVIS & AOP).
  set (op := fb + 464) in *. set (ois := fb + 96) in *.
  set (WR := PNRA.W_brun PMA.AD PMA.AN fb) in *.
  assert (WAPPR : PMKA.wapp WR).
  { unfold WR, PNRA.W_brun, PGS.W_srcfG, PNST.berr_W, PNST.cat_W, PNST.dec_W, PNRA.o_src, PNRA.o_is, PNRA.o_bb, PNRA.o_nb, PNRA.o_tb, PNRA.o_stk, PNRA.o_ec, PNRA.o_p, PMSP.o_p, PMSP.o_is, PMSP.o_ec.
    cbn [app pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PMA.AD ADDR_A PMA.AN NADDR_A PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj].
    unfold PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK.
    pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
    repeat apply PMKA.wapp_cons; [..| apply PMKA.wapp_nil]; cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct FA1 as [FA1|FA1]; clear - FA0 FA1 FA2 F1 F2; lia. }
  pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
  pose proof GFR as (GF1 & GF2 & _).
  assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
  assert (DF2 : F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; clear - GF2; lia).
  assert (R4a : 0 <= F / 8 + 2147450880) by (clear - DF1; lia).
  assert (R4b : F / 8 + 2147450880 + 1 <= 2 ^ 64) by (clear - DF2; lia).
  assert (OPS : op + 416 <= sp - 26624) by (unfold op; clear - F2 FSCEIL SLO; lia).
  (* [comment removed for export] *)
  set (b := PNM.b_sb s1) in *. set (k := PNM.b_sk s1) in *. set (stk := PNM.b_stk s1) in *.
  set (LBc := rest_own s1 ++ LBX).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (WB1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND1 & NDF1 & _).
  assert (NDFF : base.NoDup (map ff_addr FF')) by (rewrite map_app in NDF1; apply stdpp.list_relations.list.NoDup_app in NDF1; exact (proj1 NDF1)).
  pose proof (perm_own s1 LBX) as PERM1. fold b k LBc in PERM1.
  assert (HHp : ri_inv HI (PNM.bvec_own b k ++ LBc) FF' LK1 cr1 Aw1 M1 (vml_of model1)).
  { apply (HAJ.aior_perm _ _ _ _ _ HIok _ _ FF' FF' LK1 cr1 Aw1 M1 _ HH1).
    - intros b0. split; [apply Permutation_in; exact PERM1| apply Permutation_in; apply Permutation_sym; exact PERM1].
    - apply (ln_nodup_perm (PNM.bparser_own s1 ++ LBX)); [exact PERM1| exact ND1].
    - intros f. split; intros Xf; exact Xf.
    - exact NDFF. }
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as FRB1. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as BRB1.
  assert (INCc : incl LBc (PNM.bparser_own s1 ++ LBX)).
  { unfold LBc. intros x Hx. apply in_app_or in Hx. apply in_or_app. destruct Hx as [Hx|Hx]; [left; exact (rest_incl s1 x Hx)| right; exact Hx]. }
  assert (BRBc : forall b0 : Z * Z, In b0 LBc -> 0 <= fst b0 /\ fst b0 + snd b0 <= 2 ^ 47) by (intros b0 Hb; apply BRB1; apply INCc; exact Hb).
  pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BB1 & NB1 & TB1 & SV1 & _). change (PNM.OFF_STK) with 392 in SV1. fold b k stk in SV1.
  pose proof SV1 as (V0 & V8 & V16 & Hk & Hlen & Hal & DB & CB & AB & EL).
  assert (ISB : In (b, PNM.BSZ * 2 ^ k) (PNM.bparser_own s1 ++ LBX)) by (apply in_or_app; left; exact (PNBOA.PNM_own_stk s1)).
  pose proof (WB1 _ ISB) as ((Sb0 & _) & _). cbn [fst snd] in Sb0.
  assert (AOV : PMSPA.aobjA FF' (op + 392) 24) by (apply PMAUAR.aobjA_push; apply (PNAPAR.aobj_fbB FF fb (op + 392) 24 FOK); unfold op; clear; lia).
  assert (V8m : (op + 392) mod 8 = 0) by (replace (op + 392) with (op + 49 * 8) by (clear; lia); rewrite Z.mod_add by (clear; lia); exact O8).
  set (Wc := [(op + 392, 24)]).
  assert (WAPPc : PMKA.wapp Wc).
  { apply PMKA.wapp_cons; [| apply PMKA.wapp_nil]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI, op. destruct FA1 as [Y|Y]; clear - Y F1 F2; lia. }
  assert (SZ1 : shadow_zero M1 (sp - 26624) 3328).
  { apply (PMKA.stksh_keepA L ar LBX FF sp 26624 WR M M1 EK1 WAPPR (sp - 26624) 3328); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| | clear; lia| exact STKSH].
    apply PMKA.mod16_8'. replace (sp - 26624) with (sp + (-1664) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  assert (SP8 : (sp - 26624) mod 8 = 0) by (apply PMKA.mod16_8'; replace (sp - 26624) with (sp + (-1664) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16).
  pose proof ASTK1 as (_ & _ & _ & _ & SDEF1 & _).
  (* [comment removed for export] *)
  pose proof GR1 as (GNB & GTB & GBB).
  pose proof (PMA.ly_cost L C LY) as (LCK & LCL & LCO).
  assert (P1 : forall y gy oy, PM.vstr_at RSEGS PMSPA.accA M1 oy y -> PM.tb_ok y gy -> 0 <= fst (PM.pot_text (PMSPA.HV L ar) y gy) /\ 0 <= snd (PM.pot_text (PMSPA.HV L ar) y gy)).
  { intros y gy oy (_ & _ & VSy) (Hg & _ & _). unfold PM.pot_text. cbn [fst snd HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead PMSPA.HV LibIfaceAB.heap_view]. rewrite LCK, LCO.
    assert (Cy : PM.vs_cap y <= 2 ^ 27) by (destruct y as [n0|cc n0 p]; cbn [PM.vs_cap]; [clear; lia| destruct VSy as (_ & _ & _ & _ & Hcc & _); clear - Hcc; lia]). clear - Hg Cy. lia. }
  assert (P2 : 0 <= fst (PGV8.pot_v8 (PMSPA.HV L ar) (PNM.b_bb s1) (PNM.b_bg s1)) /\ 0 <= snd (PGV8.pot_v8 (PMSPA.HV L ar) (PNM.b_bb s1) (PNM.b_bg s1))).
  { destruct BB1 as (_ & _ & VSb). pose proof (PGV8.v8_ok_cap _ _ GBB) as (Hg & _). unfold PGV8.pot_v8. cbn [fst snd HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead PMSPA.HV LibIfaceAB.heap_view]. rewrite LCK, LCO.
    assert (Cy : PGV8.v8_cap (PNM.b_bb s1) <= 2 ^ 27) by (destruct (PNM.b_bb s1) as [|b0 n0 cc]; cbn [PGV8.v8_cap]; [clear; lia| destruct VSb as (_ & _ & _ & _ & Hcc & _); clear - Hcc; lia]). clear - Hg Cy. lia. }
  pose proof (P1 _ _ _ NB1 GNB) as P4. pose proof (P1 _ _ _ TB1 GTB) as P5.
  assert (KN : PNSAX.k_next b k = k + 1) by (unfold PNSAX.k_next; destruct (Z.eqb_spec b 0) as [E0|E0]; [clear - E0 Sb0; lia| reflexivity]).
  assert (P2k : 1 <= 2 ^ k) by (apply (Z.pow_le_mono_r 2 0 k); clear - Hk; lia).
  assert (FULLk : PNSAX.full_or_empty k stk (PNM.bvec_own b k) -> k <= 10 /\ 2 * 2 ^ (k + 1) <= 2 ^ 12).
  { intros [X|X]; [discriminate X|]. destruct (Z_le_gt_dec k 10) as [Y|Y].
    - split; [exact Y|]. replace (2 * 2 ^ (k + 1)) with (2 ^ (k + 2)) by (rewrite (Z.pow_add_r 2 k 2), (Z.pow_add_r 2 k 1) by (clear - Hk; lia); clear; lia). apply Z.pow_le_mono_r; clear - Y; lia.
    - exfalso. assert (Z11 : 2 ^ 11 <= 2 ^ k) by (apply Z.pow_le_mono_r; clear - Y; lia). clear - Z11 X DEPTH. lia. }
  assert (PK1 : 2 ^ (k + 1) = 2 * 2 ^ k) by (rewrite (Z.pow_add_r 2 k 1) by (clear - Hk; lia); clear; lia).
  assert (PK2 : 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1)) by (rewrite (Z.pow_add_r 2 (k + 1) 1) by (clear - Hk; lia); clear; lia).
  assert (FE : PNSAX.full_or_empty k stk (PNM.bvec_own b k)) by (right; clear - FULL Hlen; lia).
  unfold PNSAXR.push_cont_slow_spec in PSH.
  apply (PSH fx1 R1 M1 model1 K LBc FF' LK1 Aw1 cr1 (op + 392) b k stk (PNM.bvec_own b k) (m, n) (sp - 160) ra HHp AM1 K0).
  { unfold PMSPA.entryA. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [exact RAok|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|].
    change (PMSPA.pm_scr 0) with 12288. change (12288 / 8) with 1536.
    split; [apply (L5SAR.astk_sub ar M1 M1 sp 26624 160 12288 ASTK1 (mem_grows_refl M1)); [clear; lia| clear; lia| clear; lia| replace (sp - 160) with (sp + (-10) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
    apply (PMKA.shadow_zero_sub M1 (sp - 26624) 3328); [exact SP8| | clear; lia| clear; lia| clear; lia| exact SZ1].
    apply PMKA.mod16_8'. replace (sp - 160 - 12288) with (sp + (-778) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { apply (PMAUAR.ffrsA_push FF sp (sp - 160) F 0 (sp - 160 + 32) FRS); clear; lia. }
  { rewrite L5K.rl10. exact X10. }
  { exact AOV. }
  { exact V8m. }
  { intros a Ha. apply OACC1. clear - Ha. lia. }
  { right. split; [exact SV1| reflexivity]. }
  { unfold PNSAX.dom_cont, PNM.bvec_own. discriminate. }
  { exact FE. }
  { exact (proj1 (FULLk FE)). }
  { exact BASE1. }
  { unfold PNSAX.cells_cont. exists (sp - 120), (sp - 116), (sp - 112). cbn [fst snd].
    split; [rewrite L5K.rl11; exact X11|]. split; [rewrite L5K.rl12; exact X12|]. split; [rewrite L5K.rl13; exact X13|].
    assert (AC : forall p q, sp - 160 <= p -> p + q <= sp -> 0 < q -> p mod q = 0 -> PNSAX.arg_cell ar M1 FF' (sp - 160) (op + 392) p q).
    { intros p q P1' P2' P3' P4'. unfold PNSAX.arg_cell, PNSAX.arg_ok. split; [exact P4'|].
      split; [unfold PMSPA.accA; apply (L5CBR.aacc_of_zero M1 (sp - 26624) 3328 p q SZ1 SP8); [clear - SLO SPT; lia| clear - P1'; lia| clear - P2'; lia]|].
      split; [split; [right; clear - P1' P2' P3' SLO SHI SPT; lia| right; clear - P1' OPS; lia]|].
      apply (shz_at M1 (sp - 26624) 3328); [exact SZ1| exact SP8| clear - P1'; lia| clear - P2' P3'; lia]. }
    split; [apply AC; [clear; lia| clear; lia| clear; lia| apply mod4_of16; [exact A16| reflexivity]]|].
    split; [apply AC; [clear; lia| clear; lia| clear; lia| apply mod4_of16; [exact A16| reflexivity]]|].
    split; [apply AC; [clear; lia| clear; lia| clear; lia| apply mod8_of16; [exact A16| reflexivity]]|].
    split; [exact UM|]. split; [apply (L5.defined_sub M1 (sp - 26624) 26624); [exact SDEF1| clear; lia| clear; lia]|]. split; [exact UN|].
    split; [exact Hm| exact Hn]. }
  { destruct (FULLk FE) as (K10 & K12). rewrite KN. unfold acredit_ok. rewrite LCK, LCL, LCO. unfold PNM.BSZ.
    revert CRED CK1 P2 P4 P5. unfold PMSP.credit_le, PMSP.credit_keep, PMSPA.scA, PNRA.pot_bparser, PNRA.pot_bstack, PM.credit_add, PNM.BSZ. fold k.
    cbn [fst snd HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead PMSPA.HV LibIfaceAB.heap_view]. rewrite LCK, LCL, LCO.
    clear - K10 K12 P2k PK1 Hk. intros. lia. }
  intros fx7 R7 M7 model7 LK7 Aw7 b7 lenv7 RP7 LEN7 X107 B4096 BTOP VEC7 DISJ7 ACCV7 BASE7 HP7 MRT7 INC7 IA7 AM7 HH7.
  rewrite KN in BTOP, VEC7, HH7. rewrite L5K.rl10 in X107. change PNM.BSZ with 40 in X107, BTOP.
  set (k7 := k + 1) in BTOP, VEC7, HH7. set (cr7 := adebit L cr1 (PNM.BSZ * 2 ^ k7)) in HH7.
  change (PMSPA.pm_scr 0) with 12288 in HP7. unfold PNSAX.mk_cont in VEC7. cbn [fst snd] in VEC7.
  set (stk' := stk ++ [PNM.BS m lenv7 n 0 0]) in *.
  set (s2 := set_vec s1 b7 k7 stk').
  pose proof (perm_own' s1 b7 k7 stk' LBX) as PERM2. fold LBc s2 in PERM2.
  assert (HH7' : ri_inv HI (PNM.bparser_own s2 ++ LBX) FF' LK7 cr7 Aw7 M7 (vml_of model7)).
  { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH7) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND7 & NDF7 & _).
    apply (HAJ.aior_perm _ _ _ _ _ HIok _ _ FF' FF' LK7 cr7 Aw7 M7 _ HH7).
    - intros b0. split; [apply Permutation_in; exact PERM2| apply Permutation_in; apply Permutation_sym; exact PERM2].
    - apply (ln_nodup_perm (PNM.bvec_own b7 k7 ++ LBc)); [exact PERM2| exact ND7].
    - intros f. split; intros Xf; exact Xf.
    - exact NDFF. }
  pose proof (proj1 HP7 : ek L ar LBc FF' (sp - 160) 12288 Wc M1 M7) as EK7.
  pose proof (proj2 (proj2 HP7)) as DK7.
  assert (WcR : forall rr a, In rr Wc -> L5.in_rng rr a -> op + 392 <= a < op + 416).
  { intros rr a [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hr. lia. }
  assert (OUTc : forall a n0, (a + n0 <= op + 392 \/ op + 416 <= a) -> forall i, a <= i < a + n0 -> L5.outside Wc i).
  { intros a n0 Xo i Hi rr Hin Hr. pose proof (WcR rr i Hin Hr) as Y. clear - Hi Y Xo. lia. }
  assert (OUTBc : forall q m0, In (q, m0) (PNM.bparser_own s1 ++ LBX) -> forall i, q <= i < q + m0 -> L5.outside Wc i).
  { intros q m0 Hq i Hi rr Hin Hr. pose proof (WcR rr i Hin Hr) as Y.
    destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m0 op 416 HH1 Hq (PMAUAR.aobjA_push FF op 416 _ (PNAPAR.aobj_fbB FF fb op 416 FOK ltac:(unfold op; clear; lia) ltac:(unfold op; clear; lia)))) as [Z0|Z0]; clear - Hi Y Z0; lia. }
  assert (WAV : forall rr a, In rr Wc -> L5.in_rng rr a -> ~ (sp - 160 <= a < sp) /\ ~ (F / 8 + SB <= a < F / 8 + SB + 8)).
  { intros rr a Hin Hr. unfold SB. pose proof (WcR rr a Hin Hr) as X.
    split; [clear - X OPS; lia| unfold op in X; destruct FA1 as [Y|Y]; clear - X Y DF1 DF2 F1 F2; lia]. }
  assert (WOUT : forall a, aclient L ar LBX FF sp 26624 a -> L5.outside WR a -> L5.outside Wc a).
  { intros a Hc Ho rr Hin Hr. pose proof (WcR rr a Hin Hr) as X.
    apply (Ho (PNRA.o_stk PMA.AD fb, 24)); [unfold WR, PNRA.W_brun, PGS.W_srcfG; cbn [app]; do 7 right; left; reflexivity| unfold L5.in_rng, PNRA.o_stk, PNRA.o_p, PMSP.o_p, PNM.OFF_STK; cbn [fst snd pa_off_p PMA.AD PnLayoutA_b.ADDR_A]; unfold op in X; clear - X; lia]. }
  assert (BI7 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 26624 (sp - 160) (own sp R) F 0 WR (PNM.bparser_own s2) M7 model7 LK7 cr7 Aw7).
  { apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 26624 (sp - 160) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PNM.bparser_own s) G
             WR WR (PNM.bparser_own s1) (rest_own s1) (PNM.bparser_own s2) M1 model1 LK1 cr1 Aw1 M7 model7 LK7 cr7 Aw7 12288 Wc BI HP7 HH7' AM7 MRT7 IA7 INC7);
      [clear; lia| clear; lia| intros rr a Hin Hr; destruct (WAV rr a Hin Hr) as (Y1 & Y2); split; [unfold ocell; clear - Y1; lia| exact Y2]| exact WOUT| intros a X; exact X]. }
  assert (AOP4 : PMSPA.aobjA FF' op 416) by (apply PMAUAR.aobjA_push; apply (PNAPAR.aobj_fbB FF fb op 416 FOK); unfold op; clear; lia).
  assert (PA7 : PNM.bparser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA (pa_vp_parser PMA.AD) M7 op ois s2).
  { apply (bparser_revecS M1 M7 (pa_vp_parser PMA.AD) op ois s1 b7 k7 stk' ltac:(clear - O1; lia) ltac:(clear - O1; lia)); [| | | | exact VEC7| exact PA1].
    - intros i Hi. refine (proj1 (PMKA.agA_obj L ar _ FF' (sp - 160) 12288 _ M1 M7 EK7 WAPPc FRB1 op 392 _ _) i Hi); [| apply OUTc; left; clear; lia].
      apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb op 392 FOK); unfold op; clear; lia.
    - intros i Hi. exact (PMKA.agsh_obj L ar _ FF' (sp - 160) 12288 _ M1 M7 EK7 WAPPc FRB1 op 416 AOP4 i Hi).
    - intros i Hi. apply DK7; [clear - Hi O1; lia|].
      apply (L5SAR.fframe_client L ar LBc FF' (sp - 160) 12288 fb 5 rs); [right; exact Hfb| change (ff_bytes 5) with 2048; unfold op in Hi; clear - Hi; lia].
    - intros q m0 Hq. assert (HqL : In (q, m0) (PNM.bparser_own s1 ++ LBX)) by (apply in_or_app; left; exact (rest_incl s1 _ Hq)).
      assert (HqC : In (q, m0) LBc) by (unfold LBc; apply in_or_app; left; exact Hq).
      destruct (BRB1 _ HqL) as (B0 & B1). cbn [fst snd] in B0, B1.
      split; [exact B0|]. split; [clear - B1; lia|]. apply (PMKA.agA_blk L ar _ FF' (sp - 160) 12288 _ M1 M7 EK7 WAPPc BRBc q m0 HqC). apply OUTBc. exact HqL. }
  assert (IA7' : PM.iss_at RSEGS PMA.AD PMSPA.accA M7 ois str sm1).
  { apply (PMKA.iss_keepA RSEGS PMA.AD L ar _ FF' (sp - 160) 12288 _ M1 M7 EK7 WAPPc FRB1 BRBc ois str sm1); [| | | | exact IA1].
    - apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb ois 272 FOK); unfold ois; clear; lia.
    - unfold LBc. apply incl_appr. exact INCS.
    - apply OUTc. left. unfold ois, op; clear; lia.
    - intros c0 n0 p0 E0. unfold PMKA.blk_out. apply OUTBc. apply in_or_app; right. apply INCS. rewrite E0. left; reflexivity. }
  assert (ERR7 : PNSTA.berr_okA RSEGS PMA.AD PMA.AAD PMA.AN M7 ax1).
  { apply (berr_keep _ FF' (sp - 160) 12288 Wc M1 M7 ax1 EK7); [| exact ERR1].
    intros a Ha rr Hin Hr. pose proof (WcR rr a Hin Hr) as Y. unfold op in Y. clear - Ha Y FBI; lia. }
  assert (GR7 : PNM.bgrow_ok s2) by exact GR1.
  apply (KR fx7 R7 M7 model7 LK7 Aw7 b7 lenv7 cr7 RP7 LEN7 X107 B4096 BTOP).
  - split; [exact BI7|].
    split. { apply (pre_after_call LBc FF' (sp - 160) 12288 Wc M1 M7 fb s1 s2 str sm1 sm1 ax1 ax1 FRB1 EK7 WAPPc FOK'); [| exact RP1| exact PA7| exact IA7'| exact GR7| exact BASE7| exact ERR7].
             intros i Hi. apply (OUTc i 1); [destruct Hi as [Hi|Hi]; [left| right]; unfold op; clear - Hi; lia| clear; lia]. }
    split; [exact STEP1|]. split; [exact AXL1|].
    split. { destruct (FULLk FE) as (K10 & K12).
             revert CK1. unfold PMSP.credit_keep, PMSPA.scA, PNRA.pot_bparser, PNRA.pot_bstack, PM.credit_add, cr7, adebit, s2, set_vec, k7, PNM.BSZ. fold k.
             cbn [fst snd HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead PMSPA.HV LibIfaceAB.heap_view PNM.b_sk PNM.b_tb PNM.b_tg PNM.b_nb PNM.b_ng PNM.b_bb PNM.b_bg]. rewrite LCK, LCL, LCO.
             rewrite PK2. clear - PK1. intros. lia. }
    split; [| exact EBB1].
    apply (L5C.u8_at_agree RSEGS M1 M7); [| exact R4a| exact R4b| exact SHC1].
    intros j Hj. apply EK7. split; [clear - Hj R4a R4b; lia|]. split.
    + apply (L5SAR.fframe_shadow_client L ar _ FF' (sp - 160) 12288 F 0 (sp - 160 + 32)); [left; reflexivity|]. change (ff_bytes 0) with 64.
      unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - Hj; lia.
    + intros rr Hin Hr. destruct (WAV rr _ Hin Hr) as (_ & Y). apply Y. unfold SB. clear - Hj; lia.
  - intros a Ha. apply EK7. split; [clear - Ha GSLO GSHI GSPT; lia|]. split.
    + apply (L5SAR.stack_client L ar _ FF' (sp - 160) 12288 a); clear - Ha GSLO GSHI GSPT; lia.
    + intros rr Hin Hr. destruct (WAV rr a Hin Hr) as (Y & _). apply Y. clear - Ha; lia.
  - intros v0 c0 E0. apply (PMKA.ec_keepA RSEGS L ar _ FF' (sp - 160) 12288 Wc M1 M7 EK7 WAPPc FRB1 (fb + 1024) v0 c0); [| | exact E0].
    + apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb (fb + 1024) 16 FOK); clear; lia.
    + apply OUTc. right. unfold op; clear; lia.
Qed.

Lemma bd_push_post K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 (M7 : mem) model7 LK7 Aw7 cr7 (b7 k7 : Z) (stk' : list PNM.bstate) (scr : Z) :
  0 <= scr <= 26464 -> bd_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  bd_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  PNM.bvec_at RSEGS PMSPA.accA PMSPA.annA M7 (fb + 464 + 392) b7 k7 stk' -> PMSTA.base_okA RSEGS PMA.AD M7 ->
  L5CA.ahpres L ar (rest_own s1 ++ LBX) ((F, 0, sp - 160 + 32) :: FF) (sp - 160) scr [(fb + 464 + 392, 24)] M1 M7 ->
  model_rt model1 model7 -> incl LK7 LK1 -> incl Aw1 Aw7 -> L5CA.amodel_ok Aw7 model7 ->
  ri_inv HI (PNM.bvec_own b7 k7 ++ rest_own s1 ++ LBX) ((F, 0, sp - 160 + 32) :: FF) LK7 cr7 Aw7 M7 (vml_of model7) ->
  PMSP.credit_keep cr cr7 (pot L ar s) (pot L ar (set_vec s1 b7 k7 stk')) ->
  bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M7 model7 LK7 Aw7 (set_vec s1 b7 k7 stk') sm1 ax1 cr7
  /\ (forall a, sp - 160 <= a < sp - 104 -> M7 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a))
  /\ (forall v c, PMSPA.ec_at RSEGS M1 (fb + 1024) v c -> PMSPA.ec_at RSEGS M7 (fb + 1024) v c).
Proof.
  intros HSC CTX G LM VEC7 BASE7 HP7 MRT7 INC7 IA7 AM7 HH7 CK7.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 7) with 26624 in *. change (26624 / 8) with 3328 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
  assert (FBI : 6905856 <= fb) by (clear - F1 FSAPP FSIMG; lia).
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold bd_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 0, sp - 160 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  pose proof RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA1, IA1, VIS1, VREF1, OACC1. change (PNRA.o_is PMA.AD fb) with (fb + 96) in PA1, IA1. change (PNRA.o_v PMA.AD fb) with (fb + 432) in VIS1, VREF1.
  change (PNM.PSIZE + 8) with 424 in OACC1.
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1 OACC1) as ((O1 & O8 & ONSH) & Zop & OWR & OCE & OVIS & AOP).
  set (op := fb + 464) in *. set (ois := fb + 96) in *.
  set (WR := PNRA.W_brun PMA.AD PMA.AN fb) in *.
  assert (WAPPR : PMKA.wapp WR).
  { unfold WR, PNRA.W_brun, PGS.W_srcfG, PNST.berr_W, PNST.cat_W, PNST.dec_W, PNRA.o_src, PNRA.o_is, PNRA.o_bb, PNRA.o_nb, PNRA.o_tb, PNRA.o_stk, PNRA.o_ec, PNRA.o_p, PMSP.o_p, PMSP.o_is, PMSP.o_ec.
    cbn [app pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PMA.AD ADDR_A PMA.AN NADDR_A PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj].
    unfold PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK.
    pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
    repeat apply PMKA.wapp_cons; [..| apply PMKA.wapp_nil]; cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct FA1 as [FA1|FA1]; clear - FA0 FA1 FA2 F1 F2; lia. }
  pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
  pose proof GFR as (GF1 & GF2 & _).
  assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
  assert (DF2 : F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; clear - GF2; lia).
  assert (R4a : 0 <= F / 8 + 2147450880) by (clear - DF1; lia).
  assert (R4b : F / 8 + 2147450880 + 1 <= 2 ^ 64) by (clear - DF2; lia).
  assert (OPS : op + 416 <= sp - 26624) by (unfold op; clear - F2 FSCEIL SLO; lia).
  set (b := PNM.b_sb s1) in *. set (k := PNM.b_sk s1) in *. set (stk := PNM.b_stk s1) in *.
  set (LBc := rest_own s1 ++ LBX).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (WB1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND1 & NDF1 & _).
  assert (NDFF : base.NoDup (map ff_addr FF')) by (rewrite map_app in NDF1; apply stdpp.list_relations.list.NoDup_app in NDF1; exact (proj1 NDF1)).
  pose proof (perm_own s1 LBX) as PERM1. fold b k LBc in PERM1.
  assert (HHp : ri_inv HI (PNM.bvec_own b k ++ LBc) FF' LK1 cr1 Aw1 M1 (vml_of model1)).
  { apply (HAJ.aior_perm _ _ _ _ _ HIok _ _ FF' FF' LK1 cr1 Aw1 M1 _ HH1).
    - intros b0. split; [apply Permutation_in; exact PERM1| apply Permutation_in; apply Permutation_sym; exact PERM1].
    - apply (ln_nodup_perm (PNM.bparser_own s1 ++ LBX)); [exact PERM1| exact ND1].
    - intros f. split; intros Xf; exact Xf.
    - exact NDFF. }
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as FRB1. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as BRB1.
  assert (INCc : incl LBc (PNM.bparser_own s1 ++ LBX)).
  { unfold LBc. intros x Hx. apply in_app_or in Hx. apply in_or_app. destruct Hx as [Hx|Hx]; [left; exact (rest_incl s1 x Hx)| right; exact Hx]. }
  assert (BRBc : forall b0 : Z * Z, In b0 LBc -> 0 <= fst b0 /\ fst b0 + snd b0 <= 2 ^ 47) by (intros b0 Hb; apply BRB1; apply INCc; exact Hb).
  pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BB1 & NB1 & TB1 & SV1 & _). change (PNM.OFF_STK) with 392 in SV1. fold b k stk in SV1.
  pose proof SV1 as (V0 & V8 & V16 & Hk & Hlen & Hal & DB & CB & AB & EL).
  assert (ISB : In (b, PNM.BSZ * 2 ^ k) (PNM.bparser_own s1 ++ LBX)) by (apply in_or_app; left; exact (PNBOA.PNM_own_stk s1)).
  pose proof (WB1 _ ISB) as ((Sb0 & _) & _). cbn [fst snd] in Sb0.
  assert (AOV : PMSPA.aobjA FF' (op + 392) 24) by (apply PMAUAR.aobjA_push; apply (PNAPAR.aobj_fbB FF fb (op + 392) 24 FOK); unfold op; clear; lia).
  assert (V8m : (op + 392) mod 8 = 0) by (replace (op + 392) with (op + 49 * 8) by (clear; lia); rewrite Z.mod_add by (clear; lia); exact O8).
  set (Wc := [(op + 392, 24)]).
  assert (WAPPc : PMKA.wapp Wc).
  { apply PMKA.wapp_cons; [| apply PMKA.wapp_nil]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI, op. destruct FA1 as [Y|Y]; clear - Y F1 F2; lia. }
  set (s2 := set_vec s1 b7 k7 stk').
  pose proof (perm_own' s1 b7 k7 stk' LBX) as PERM2. fold LBc s2 in PERM2.
  assert (HH7' : ri_inv HI (PNM.bparser_own s2 ++ LBX) FF' LK7 cr7 Aw7 M7 (vml_of model7)).
  { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH7) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND7 & NDF7 & _).
    apply (HAJ.aior_perm _ _ _ _ _ HIok _ _ FF' FF' LK7 cr7 Aw7 M7 _ HH7).
    - intros b0. split; [apply Permutation_in; exact PERM2| apply Permutation_in; apply Permutation_sym; exact PERM2].
    - apply (ln_nodup_perm (PNM.bvec_own b7 k7 ++ LBc)); [exact PERM2| exact ND7].
    - intros f. split; intros Xf; exact Xf.
    - exact NDFF. }
  pose proof (proj1 HP7 : ek L ar LBc FF' (sp - 160) scr Wc M1 M7) as EK7.
  pose proof (proj2 (proj2 HP7)) as DK7.
  assert (WcR : forall rr a, In rr Wc -> L5.in_rng rr a -> op + 392 <= a < op + 416).
  { intros rr a [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hr. lia. }
  assert (OUTc : forall a n0, (a + n0 <= op + 392 \/ op + 416 <= a) -> forall i, a <= i < a + n0 -> L5.outside Wc i).
  { intros a n0 Xo i Hi rr Hin Hr. pose proof (WcR rr i Hin Hr) as Y. clear - Hi Y Xo. lia. }
  assert (OUTBc : forall q m0, In (q, m0) (PNM.bparser_own s1 ++ LBX) -> forall i, q <= i < q + m0 -> L5.outside Wc i).
  { intros q m0 Hq i Hi rr Hin Hr. pose proof (WcR rr i Hin Hr) as Y.
    destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m0 op 416 HH1 Hq (PMAUAR.aobjA_push FF op 416 _ (PNAPAR.aobj_fbB FF fb op 416 FOK ltac:(unfold op; clear; lia) ltac:(unfold op; clear; lia)))) as [Z0|Z0]; clear - Hi Y Z0; lia. }
  assert (WAV : forall rr a, In rr Wc -> L5.in_rng rr a -> ~ (sp - 160 <= a < sp) /\ ~ (F / 8 + SB <= a < F / 8 + SB + 8)).
  { intros rr a Hin Hr. unfold SB. pose proof (WcR rr a Hin Hr) as X.
    split; [clear - X OPS; lia| unfold op in X; destruct FA1 as [Y|Y]; clear - X Y DF1 DF2 F1 F2; lia]. }
  assert (WOUT : forall a, aclient L ar LBX FF sp 26624 a -> L5.outside WR a -> L5.outside Wc a).
  { intros a Hc Ho rr Hin Hr. pose proof (WcR rr a Hin Hr) as X.
    apply (Ho (PNRA.o_stk PMA.AD fb, 24)); [unfold WR, PNRA.W_brun, PGS.W_srcfG; cbn [app]; do 7 right; left; reflexivity| unfold L5.in_rng, PNRA.o_stk, PNRA.o_p, PMSP.o_p, PNM.OFF_STK; cbn [fst snd pa_off_p PMA.AD PnLayoutA_b.ADDR_A]; unfold op in X; clear - X; lia]. }
  assert (BI7 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 26624 (sp - 160) (own sp R) F 0 WR (PNM.bparser_own s2) M7 model7 LK7 cr7 Aw7).
  { apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 26624 (sp - 160) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PNM.bparser_own s) G
             WR WR (PNM.bparser_own s1) (rest_own s1) (PNM.bparser_own s2) M1 model1 LK1 cr1 Aw1 M7 model7 LK7 cr7 Aw7 scr Wc BI HP7 HH7' AM7 MRT7 IA7 INC7);
      [clear - HSC; lia| clear - HSC; lia| intros rr a Hin Hr; destruct (WAV rr a Hin Hr) as (Y1 & Y2); split; [unfold ocell; clear - Y1; lia| exact Y2]| exact WOUT| intros a X; exact X]. }
  assert (AOP4 : PMSPA.aobjA FF' op 416) by (apply PMAUAR.aobjA_push; apply (PNAPAR.aobj_fbB FF fb op 416 FOK); unfold op; clear; lia).
  assert (PA7 : PNM.bparser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA (pa_vp_parser PMA.AD) M7 op ois s2).
  { apply (bparser_revecS M1 M7 (pa_vp_parser PMA.AD) op ois s1 b7 k7 stk' ltac:(clear - O1; lia) ltac:(clear - O1; lia)); [| | | | exact VEC7| exact PA1].
    - intros i Hi. refine (proj1 (PMKA.agA_obj L ar _ FF' (sp - 160) scr _ M1 M7 EK7 WAPPc FRB1 op 392 _ _) i Hi); [| apply OUTc; left; clear; lia].
      apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb op 392 FOK); unfold op; clear; lia.
    - intros i Hi. exact (PMKA.agsh_obj L ar _ FF' (sp - 160) scr _ M1 M7 EK7 WAPPc FRB1 op 416 AOP4 i Hi).
    - intros i Hi. apply DK7; [clear - Hi O1; lia|].
      apply (L5SAR.fframe_client L ar LBc FF' (sp - 160) scr fb 5 rs); [right; exact Hfb| change (ff_bytes 5) with 2048; unfold op in Hi; clear - Hi; lia].
    - intros q m0 Hq. assert (HqL : In (q, m0) (PNM.bparser_own s1 ++ LBX)) by (apply in_or_app; left; exact (rest_incl s1 _ Hq)).
      assert (HqC : In (q, m0) LBc) by (unfold LBc; apply in_or_app; left; exact Hq).
      destruct (BRB1 _ HqL) as (B0 & B1). cbn [fst snd] in B0, B1.
      split; [exact B0|]. split; [clear - B1; lia|]. apply (PMKA.agA_blk L ar _ FF' (sp - 160) scr _ M1 M7 EK7 WAPPc BRBc q m0 HqC). apply OUTBc. exact HqL. }
  assert (IA7' : PM.iss_at RSEGS PMA.AD PMSPA.accA M7 ois str sm1).
  { apply (PMKA.iss_keepA RSEGS PMA.AD L ar _ FF' (sp - 160) scr _ M1 M7 EK7 WAPPc FRB1 BRBc ois str sm1); [| | | | exact IA1].
    - apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb ois 272 FOK); unfold ois; clear; lia.
    - unfold LBc. apply incl_appr. exact INCS.
    - apply OUTc. left. unfold ois, op; clear; lia.
    - intros c0 n0 p0 E0. unfold PMKA.blk_out. apply OUTBc. apply in_or_app; right. apply INCS. rewrite E0. left; reflexivity. }
  assert (ERR7 : PNSTA.berr_okA RSEGS PMA.AD PMA.AAD PMA.AN M7 ax1).
  { apply (berr_keep _ FF' (sp - 160) scr Wc M1 M7 ax1 EK7); [| exact ERR1].
    intros a Ha rr Hin Hr. pose proof (WcR rr a Hin Hr) as Y. unfold op in Y. clear - Ha Y FBI; lia. }
  assert (GR7 : PNM.bgrow_ok s2) by exact GR1.
  split; [|split].
  - split; [exact BI7|].
    split. { apply (pre_after_call LBc FF' (sp - 160) scr Wc M1 M7 fb s1 s2 str sm1 sm1 ax1 ax1 FRB1 EK7 WAPPc FOK'); [| exact RP1| exact PA7| exact IA7'| exact GR7| exact BASE7| exact ERR7].
             intros i Hi. apply (OUTc i 1); [destruct Hi as [Hi|Hi]; [left| right]; unfold op; clear - Hi; lia| clear; lia]. }
    split; [exact STEP1|]. split; [exact AXL1|].
    split; [exact CK7|].
    split; [| exact EBB1].
    apply (L5C.u8_at_agree RSEGS M1 M7); [| exact R4a| exact R4b| exact SHC1].
    intros j Hj. apply EK7. split; [clear - Hj R4a R4b; lia|]. split.
    + apply (L5SAR.fframe_shadow_client L ar _ FF' (sp - 160) scr F 0 (sp - 160 + 32)); [left; reflexivity|]. change (ff_bytes 0) with 64.
      unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - Hj; lia.
    + intros rr Hin Hr. destruct (WAV rr _ Hin Hr) as (_ & Y). apply Y. unfold SB. clear - Hj; lia.
  - intros a Ha. apply EK7. split; [clear - Ha GSLO GSHI GSPT; lia|]. split.
    + apply (L5SAR.stack_client L ar _ FF' (sp - 160) scr a); clear - Ha GSLO GSHI GSPT; lia.
    + intros rr Hin Hr. destruct (WAV rr a Hin Hr) as (Y & _). apply Y. clear - Ha; lia.
  - intros v0 c0 E0. apply (PMKA.ec_keepA RSEGS L ar _ FF' (sp - 160) scr Wc M1 M7 EK7 WAPPc FRB1 (fb + 1024) v0 c0); [| | exact E0].
    + apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb (fb + 1024) 16 FOK); clear; lia.
    + apply OUTc. right. unfold op; clear; lia.
Qed.

Lemma bd_call_grow K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 (fx1 : FPState) R1 (ra : Z) :
  PNAECF.ann_grow_spec L ar HI 709816 ->
  bd_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  bd_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  getr R1 (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr R1 (reg 2) = Z_to_bv 64 (sp - 224) ->
  getr R1 (reg 3) = Z_to_bv 64 (pa_gp PMA.AD) -> getr R1 (reg 4) = Z_to_bv 64 (hl_tp L) ->
  getr R1 (reg 10) = Z_to_bv 64 (fb + 464 + 392) -> getr R1 (reg 11) = Z_to_bv 64 1 -> getr R1 (reg 12) = Z_to_bv 64 (-40) -> getr R1 (reg 13) = Z_to_bv 64 0 ->
  Z.of_nat (length (PNM.b_stk s1)) < 2 ^ PNM.b_sk s1 ->
  (forall (fx2 : FPState) R2 (M3 : mem) model3 LK3 Aw3,
      regs_preserved R1 R2 ->
      L5.u64_at RSEGS M3 (fb + 464 + 392) (PNM.b_sb s1) ->
      L5.u64_at RSEGS M3 (fb + 464 + 392 + 8) (PNM.b_sb s1 + 40 * Z.of_nat (length (PNM.b_stk s1))) ->
      L5.u64_at RSEGS M3 (fb + 464 + 392 + 16) (PNM.b_sb s1 + 40 * 2 ^ PNM.b_sk s1) ->
      (forall i, (i < length (PNM.b_stk s1))%nat -> PNM.bstate_at RSEGS M3 (PNM.b_sb s1 + 40 * Z.of_nat i) (nth i (PNM.b_stk s1) PNM.bs_root)) ->
      L5.defined M3 (PNM.b_sb s1) (40 * 2 ^ PNM.b_sk s1) -> PMSPA.accA M3 (PNM.b_sb s1) (40 * (Z.of_nat (length (PNM.b_stk s1)) + 1)) ->
      PMSPA.annA M3 (PNM.b_sb s1) (40 * (Z.of_nat (length (PNM.b_stk s1)) + 1)) (40 * 2 ^ PNM.b_sk s1) ->
      PMSPA.accA M3 (fb + 464 + 392) 24 -> PMSTA.base_okA RSEGS PMA.AD M3 ->
      L5CA.ahpres L ar (rest_own s1 ++ LBX) ((F, 0, sp - 160 + 32) :: FF) (sp - 224) (PMSPA.pm_scr 0) [] M1 M3 ->
      model_rt model1 model3 -> incl LK3 LK1 -> incl Aw1 Aw3 -> L5CA.amodel_ok Aw3 model3 ->
      ri_inv HI (PNM.bvec_own (PNM.b_sb s1) (PNM.b_sk s1) ++ rest_own s1 ++ LBX) ((F, 0, sp - 160 + 32) :: FF) LK3 cr1 Aw3 M3 (vml_of model3) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 ra M3 model3) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 709816 M1 model1) K.
Proof.
  intros AGR CTX G LM X1 RAok X2 X3 X4 X10 X11 X12 X13 LEN KR.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 7) with 26624 in *. change (26624 / 8) with 3328 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
  assert (FBI : 6905856 <= fb) by (clear - F1 FSAPP FSIMG; lia).
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold bd_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 0, sp - 160 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  pose proof RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA1, IA1, VIS1, VREF1, OACC1. change (PNRA.o_is PMA.AD fb) with (fb + 96) in PA1, IA1. change (PNRA.o_v PMA.AD fb) with (fb + 432) in VIS1, VREF1.
  change (PNM.PSIZE + 8) with 424 in OACC1.
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1 OACC1) as ((O1 & O8 & ONSH) & Zop & OWR & OCE & OVIS & AOP).
  set (op := fb + 464) in *. set (ois := fb + 96) in *.
  set (WR := PNRA.W_brun PMA.AD PMA.AN fb) in *.
  assert (WAPPR : PMKA.wapp WR).
  { unfold WR, PNRA.W_brun, PGS.W_srcfG, PNST.berr_W, PNST.cat_W, PNST.dec_W, PNRA.o_src, PNRA.o_is, PNRA.o_bb, PNRA.o_nb, PNRA.o_tb, PNRA.o_stk, PNRA.o_ec, PNRA.o_p, PMSP.o_p, PMSP.o_is, PMSP.o_ec.
    cbn [app pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PMA.AD ADDR_A PMA.AN NADDR_A PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj].
    unfold PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK.
    pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
    repeat apply PMKA.wapp_cons; [..| apply PMKA.wapp_nil]; cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct FA1 as [FA1|FA1]; clear - FA0 FA1 FA2 F1 F2; lia. }
  pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
  pose proof GFR as (GF1 & GF2 & _).
  assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
  assert (DF2 : F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; clear - GF2; lia).
  assert (R4a : 0 <= F / 8 + 2147450880) by (clear - DF1; lia).
  assert (R4b : F / 8 + 2147450880 + 1 <= 2 ^ 64) by (clear - DF2; lia).
  assert (OPS : op + 416 <= sp - 26624) by (unfold op; clear - F2 FSCEIL SLO; lia).
  set (b := PNM.b_sb s1) in *. set (k := PNM.b_sk s1) in *. set (stk := PNM.b_stk s1) in *.
  set (LBc := rest_own s1 ++ LBX).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (WB1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND1 & NDF1 & _).
  assert (NDFF : base.NoDup (map ff_addr FF')) by (rewrite map_app in NDF1; apply stdpp.list_relations.list.NoDup_app in NDF1; exact (proj1 NDF1)).
  pose proof (perm_own s1 LBX) as PERM1. fold b k LBc in PERM1.
  assert (HHp : ri_inv HI (PNM.bvec_own b k ++ LBc) FF' LK1 cr1 Aw1 M1 (vml_of model1)).
  { apply (HAJ.aior_perm _ _ _ _ _ HIok _ _ FF' FF' LK1 cr1 Aw1 M1 _ HH1).
    - intros b0. split; [apply Permutation_in; exact PERM1| apply Permutation_in; apply Permutation_sym; exact PERM1].
    - apply (ln_nodup_perm (PNM.bparser_own s1 ++ LBX)); [exact PERM1| exact ND1].
    - intros f. split; intros Xf; exact Xf.
    - exact NDFF. }
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as FRB1. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as BRB1.
  assert (INCc : incl LBc (PNM.bparser_own s1 ++ LBX)).
  { unfold LBc. intros x Hx. apply in_app_or in Hx. apply in_or_app. destruct Hx as [Hx|Hx]; [left; exact (rest_incl s1 x Hx)| right; exact Hx]. }
  assert (BRBc : forall b0 : Z * Z, In b0 LBc -> 0 <= fst b0 /\ fst b0 + snd b0 <= 2 ^ 47) by (intros b0 Hb; apply BRB1; apply INCc; exact Hb).
  pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BB1 & NB1 & TB1 & SV1 & _). change (PNM.OFF_STK) with 392 in SV1. fold b k stk in SV1.
  pose proof SV1 as (V0 & V8 & V16 & Hk & Hlen & Hal & DB & CB & AB & EL).
  assert (ISB : In (b, PNM.BSZ * 2 ^ k) (PNM.bparser_own s1 ++ LBX)) by (apply in_or_app; left; exact (PNBOA.PNM_own_stk s1)).
  pose proof (WB1 _ ISB) as ((Sb0 & _) & _). cbn [fst snd] in Sb0.
  assert (AOV : PMSPA.aobjA FF' (op + 392) 24) by (apply PMAUAR.aobjA_push; apply (PNAPAR.aobj_fbB FF fb (op + 392) 24 FOK); unfold op; clear; lia).
  assert (V8m : (op + 392) mod 8 = 0) by (replace (op + 392) with (op + 49 * 8) by (clear; lia); rewrite Z.mod_add by (clear; lia); exact O8).
  set (Wc := [(op + 392, 24)]).
  assert (WAPPc : PMKA.wapp Wc).
  { apply PMKA.wapp_cons; [| apply PMKA.wapp_nil]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI, op. destruct FA1 as [Y|Y]; clear - Y F1 F2; lia. }
  assert (SZ1 : shadow_zero M1 (sp - 26624) 3328).
  { apply (PMKA.stksh_keepA L ar LBX FF sp 26624 WR M M1 EK1 WAPPR (sp - 26624) 3328); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| | clear; lia| exact STKSH].
    apply PMKA.mod16_8'. replace (sp - 26624) with (sp + (-1664) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  assert (SP8 : (sp - 26624) mod 8 = 0) by (apply PMKA.mod16_8'; replace (sp - 26624) with (sp + (-1664) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16).
  pose proof ASTK1 as (_ & _ & _ & _ & SDEF1 & _).
  unfold PNAECF.ann_grow_spec in AGR.
  apply (AGR fx1 R1 M1 model1 K LBc FF' LK1 Aw1 cr1 (op + 392) b k stk (sp - 224) ra HHp AM1 K0).
  { unfold PMSPA.entryA. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [exact RAok|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|].
    change (PMSPA.pm_scr 0) with 12288. change (12288 / 8) with 1536.
    split; [apply (L5SAR.astk_sub ar M1 M1 sp 26624 224 12288 ASTK1 (mem_grows_refl M1)); [clear; lia| clear; lia| clear; lia| replace (sp - 224) with (sp + (-14) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
    apply (PMKA.shadow_zero_sub M1 (sp - 26624) 3328); [exact SP8| | clear; lia| clear; lia| clear; lia| exact SZ1].
    apply PMKA.mod16_8'. replace (sp - 224 - 12288) with (sp + (-782) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { exact X10. } { exact X11. } { exact X12. } { exact X13. }
  { exact AOV. } { exact V8m. } { intros a Ha. apply OACC1. clear - Ha. lia. }
  { exact SV1. } { exact LEN. } { exact BASE1. }
  intros fx2 R2 M3 model3 LK3 Aw3 RP2 Y0 Y8 Y16 YEL YDEF YACC YANN YACCV YBASE YHP YMRT YINCL YINCA YAM YHH.
  exact (KR fx2 R2 M3 model3 LK3 Aw3 RP2 Y0 Y8 Y16 YEL YDEF YACC YANN YACCV YBASE YHP YMRT YINCL YINCA YAM YHH).
Qed.


Lemma u32_of_defined (M : mem) a : 0 <= a -> a + 4 <= 2 ^ 64 -> L5.defined M a 4 -> exists w, 0 <= w < 2 ^ 32 /\ L5.u32_at RSEGS M a w.
Proof.
  intros Ha Hn D. destruct (PMCG.rdn_some RSEGS M 4%nat a Ha ltac:(cbn; lia) ltac:(intros i Hi; apply D; cbn in Hi; lia)) as (bs & E & Hl).
  exists (bytes_le_to_Z bs). pose proof (AX2S.bytes_le_to_Z_bound bs) as Hb. rewrite Hl in Hb. cbn in Hb.
  split; [lia|]. unfold L5.u32_at. rewrite E. f_equal. symmetry. apply APSX.word_to_le_bytes_of_bytes_n; [exact Hl| lia].
Qed.
Lemma bstack_shape_push stk c : PNRA.bstack_shape stk -> Z.of_nat (length stk) <= PNM.MAX_DEPTH -> PNM.bstate_ok c -> PNRA.bmode_cont (PNM.bs_mode c) ->
  PNRA.bstack_shape (stk ++ [c]).
Proof.
  intros (L1 & L2 & BOT & CONT & OKs) LEN OKc Mc. unfold PNRA.bstack_shape. rewrite length_app. cbn [length].
  split; [lia|]. split; [lia|].
  split; [rewrite app_nth1 by lia; exact BOT|].
  split.
  - intros i Hi. destruct (Nat.lt_ge_cases i (length stk)) as [LT|GE].
    + rewrite app_nth1 by exact LT. apply CONT. lia.
    + rewrite app_nth2 by exact GE. replace (i - length stk)%nat with 0%nat by lia. cbn [nth]. exact Mc.
  - intros i Hi. destruct (Nat.lt_ge_cases i (length stk)) as [LT|GE].
    + rewrite app_nth1 by exact LT. apply OKs. exact LT.
    + rewrite app_nth2 by exact GE. replace (i - length stk)%nat with 0%nat by lia. cbn [nth]. exact OKc.
Qed.
Lemma bregs_keep R R4 R5 sp fb F : bregs R R4 sp fb F ->
  (forall k, In k [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R5 (reg k) = getr R4 (reg k)) -> bregs R R5 sp fb F.
Proof.
  intros (E2 & E3 & E4 & E8 & E9 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27) CS.
  unfold bregs. rewrite !CS by inl. repeat split; assumption.
Qed.
Lemma bvu_small64 z : 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. clear - Hz. cbn. lia. Qed.

(* [comment removed for export] *)
Lemma bd_arm_push K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 (fx6 : FPState) R6 :
  PNSAXR.push_cont_slow_spec RSEGS PMA.AD L ar HI 0xb2758 ->
  bd_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  bd_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 ->
  bregs R R6 sp fb F -> getr R6 (reg 18) = Z_to_bv 64 4 ->
  spill M6 sp F -> L5.u64_at RSEGS M6 (sp - 112) 4 ->
  L5.u64_at RSEGS M6 (sp - 144) (fb + 464 + 400) -> L5.u64_at RSEGS M6 (sp - 136) (fb + 464 + 392) ->
  PMSPA.ec_at RSEGS M6 (fb + 1024) e cat ->
  PNRA.binv s6 -> PNM.b_stk s6 = PNM.b_stk s -> Z.of_nat (length (PNM.b_stk s6)) <= 1024 ->
  PM.unread (PNM.b_src s6) sm6 + 4 <= PM.unread (PNM.b_src s) sm ->
  2 ^ PNM.b_sk s6 <= Z.of_nat (length (PNM.b_stk s6)) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 0xaeabc M6 model6) K.
Proof.
  intros PSH CTX G LM ER X18 SPL U112 C144 C136 EC6 INV6 ESTK DEPTH UNR6 FULL6.
  pose proof CTX as (_ & _ & _ & _ & ENT & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof (PNABDK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM)
    as (PF & OWN6 & SV6 & U8v6 & WRop6 & U8op6 & SVr6).
  pose proof (vfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM) as (vf1 & vf2 & vf3 & vf4 & vf5 & vf6 & vf7 & vf8 & vf9 & vf10 & vf11).
  pose proof (mfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM) as (WRmo & CM0).
  pose proof (wfacts224_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM) as (W224 & S224o & S224F & S224fl & S224v).
  pose proof (vecfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM INV6)
    as (VB6 & VE6 & VC6 & RB41 & AL41 & Hn6 & Hk6 & Hlen6).
  set (MV6 := mrestrict (ahid Aw6 model6) M6) in *.
  unfold pfacts in PF. destruct PF as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32 & pf33 & pf34).
  pose proof (SV6 (sp - 128) F ltac:(clear; lia) ltac:(clear; lia) SPL) as SPLv.
  pose proof (SV6 (sp - 144) (fb + 464 + 400) ltac:(clear; lia) ltac:(clear; lia) C144) as C144v.
  pose proof (SV6 (sp - 136) (fb + 464 + 392) ltac:(clear; lia) ltac:(clear; lia) C136) as C136v.
  pose proof ER as (E2 & E3 & E4 & E8 & E9 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27).
  assert (Q34 : 0 <= fb + 432 < 2 ^ 64) by (clear - vf1; lia).
  assert (Q36 : 0 <= fb + 1024 < 2 ^ 64) by (clear - pf7; lia).
  destruct (u32_of_defined MV6 (F + 32) ltac:(clear - pf15; lia) ltac:(clear - pf15; lia) ltac:(apply (L5.defined_sub MV6 F 64); [exact pf17| clear; lia| clear; lia])) as (lenw & Hlenw & ULEN).
  assert (Q46 : 0 <= lenw < 2 ^ 64) by (clear - Hlenw; lia).
  assert (Q46' : 0 <= lenw <= 4294967295) by (clear - Hlenw; lia).
  assert (P2k : 1 <= 2 ^ PNM.b_sk s6) by (apply (Z.pow_le_mono_r 2 0 (PNM.b_sk s6)); clear - Hk6; lia).
  assert (P2k11 : 2 ^ PNM.b_sk s6 <= 2048) by (change 2048 with (2 ^ 11); apply (Z.pow_le_mono_r 2 (PNM.b_sk s6) 11); clear - Hk6; lia).
  assert (Q41 : 0 <= PNM.b_sb s6 < 2 ^ 64) by (clear - RB41; lia).
  assert (Q42 : 0 <= 40 * Z.of_nat (length (PNM.b_stk s6)) < 2 ^ 64) by (clear - Hn6; lia).
  assert (Q43 : 0 <= 40 * 2 ^ PNM.b_sk s6 < 2 ^ 64) by (clear - P2k P2k11; lia).
  assert (RB42 : 40 <= 40 * Z.of_nat (length (PNM.b_stk s6)) <= 41000) by (clear - Hn6; lia).
  assert (RB43 : 40 <= 40 * 2 ^ PNM.b_sk s6 <= 81920) by (clear - P2k P2k11; lia).
  assert (AL42 : PNABDP.aligned (40 * Z.of_nat (length (PNM.b_stk s6))) 8).
  { unfold PNABDP.aligned. replace (40 * Z.of_nat (length (PNM.b_stk s6))) with ((5 * Z.of_nat (length (PNM.b_stk s6))) * 8) by (clear; lia). apply Z_mod_mult. }
  assert (AL43 : PNABDP.aligned (40 * 2 ^ PNM.b_sk s6) 8).
  { unfold PNABDP.aligned. replace (40 * 2 ^ PNM.b_sk s6) with ((5 * 2 ^ PNM.b_sk s6) * 8) by (clear; lia). apply Z_mod_mult. }
  LeanFeed.pfeed P (PNABDP.abdV_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 41%nat => PNM.b_sb s6 | 42%nat => 40 * Z.of_nat (length (PNM.b_stk s6)) | 43%nat => 40 * 2 ^ PNM.b_sk s6 | 46%nat => lenw | 50%nat => F | 51%nat => fl | 60%nat => bv_unsigned (getr R (reg 1)) | 61%nat => bv_unsigned (getr R (reg 8)) | 62%nat => bv_unsigned (getr R (reg 9)) | 63%nat => bv_unsigned (getr R (reg 18)) | 64%nat => bv_unsigned (getr R (reg 19)) | 65%nat => bv_unsigned (getr R (reg 20)) | 66%nat => bv_unsigned (getr R (reg 21)) | 67%nat => bv_unsigned (getr R (reg 22)) | 68%nat => bv_unsigned (getr R (reg 23)) | 69%nat => bv_unsigned (getr R (reg 24)) | 70%nat => bv_unsigned (getr R (reg 25)) | 71%nat => bv_unsigned (getr R (reg 26)) | 72%nat => bv_unsigned (getr R (reg 27)) | _ => 0 end)) ltac:(first [assumption | unfold PNABDP.aligned; assumption]).
  destruct P as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & [(MS7 & KS7 & Y1 & Y10 & Y11 & Y12 & Y13 & Y14 & Y18 & U120 & MO1 & _)|(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LT1 & _)]).
  2: { exfalso. rewrite !Z.mod_small in LT1 by (clear - Q41 Q42 Q43 RB41 RB42 RB43; lia). clear - LT1 FULL6. lia. }
  apply (bd_piece_mo K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 fx6 fx7 R6 R7 0xaeabc 0xb2758 1 M7v
           (fun a => sp - 120 <= a < sp - 120 + 8 \/ fb + 464 + 8 <= a < fb + 464 + 8 + 1 \/ sp - 224 <= a < sp - 224 + 64) CTX G LM MS7 MG7).
  { intros a Ha N. apply FRZ7; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; left; exact X| intros X; apply N; right; right; exact X]. }
  { intros a [X|[X|X]]; [left| right| left]; clear - X; lia. }
  { replace (fb + 472) with (fb + 464 + 8) by (clear; lia). exact MO1. }
  { right; reflexivity. }
  intros M8 model8 LM8 HID8 VIS8 FR8 MG8 ECK8.
  pose proof LM8 as (BI8 & _). pose proof BI8 as (HH8 & _).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ LK6 cr6 Aw6 M8 model8 HH8) as (_ & VISs8 & _). cbv zeta in VISs8. rewrite HID8 in VISs8.
  pose proof CTX as (_ & _ & _ & _ & (_ & _ & _ & _ & _ & ASTK0 & _) & _). change (PMSPA.pm_scr 7) with 26624 in ASTK0. destruct ASTK0 as (_ & SLO & _).
  assert (U120r : L5.u32_at RSEGS M8 (sp - 120) 2).
  { apply (proj1 (L5A.u32_at_vis (ahid Aw6 model6) M8 (sp - 120) 2 (VISs8 (sp - 120) 4 ltac:(clear - SLO; lia) ltac:(clear - pf4; lia)) ltac:(clear - pf4; lia) ltac:(clear - pf4; lia))).
    rewrite VIS8. exact U120. }
  assert (U112r : L5.u64_at RSEGS M8 (sp - 112) 4).
  { apply (L5C.u64_at_agree RSEGS M6 M8 (sp - 112)); [| clear - pf4; lia| clear - pf4; lia| exact U112].
    intros j Hj. apply FR8; [clear - Hj pf4; lia|]. intros [X|[X|X]]; [clear - X Hj; lia| clear - X Hj pf14; lia| clear - X Hj; lia]. }
  assert (SPL8 : spill M8 sp F).
  { unfold spill in *. apply (L5C.u64_at_agree RSEGS M6 M8 (sp - 128)); [| clear - pf4; lia| clear - pf4; lia| exact SPL].
    intros j Hj. apply FR8; [clear - Hj pf4; lia|]. intros [X|[X|X]]; [clear - X Hj; lia| clear - X Hj pf14; lia| clear - X Hj; lia]. }
  assert (C1448 : L5.u64_at RSEGS M8 (sp - 144) (fb + 464 + 400)).
  { apply (L5C.u64_at_agree RSEGS M6 M8 (sp - 144)); [| clear - pf4; lia| clear - pf4; lia| exact C144].
    intros j Hj. apply FR8; [clear - Hj pf4; lia|]. intros [X|[X|X]]; [clear - X Hj; lia| clear - X Hj pf14; lia| clear - X Hj; lia]. }
  apply (bd_call_push K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M8 model8 LK6 Aw6 (PNBO.set_more s6 1) sm6 ax6 cr6 fx7 R7 0xaebb4 2 4 PSH CTX G LM8).
  { exact Y1. } { unfold L5.ra_ok; clear; lia. }
  { rewrite (KS7 2%nat) by inl. exact E2. }
  { rewrite (KS7 3%nat) by inl. rewrite E3. exact Rgp. }
  { rewrite (KS7 4%nat) by inl. rewrite E4. exact Rtp. }
  { exact Y10. } { exact Y11. } { exact Y12. } { exact Y13. }
  { exact U120r. } { clear; lia. } { exact U112r. } { clear; lia. }
  { cbn [PNBO.set_more PNM.b_stk]. exact DEPTH. }
  { cbn [PNBO.set_more PNM.b_sk PNM.b_stk]. exact FULL6. }
  intros fx9 R9 M9 model9 LK9 Aw9 b' lenv cr9 RP9 LEN9 X109 B4096 BTOP LM9 FRC9 ECK9.
  cbn [PNBO.set_more PNM.b_stk PNM.b_sk] in LM9, X109, BTOP.
  assert (PK1 : 2 ^ (PNM.b_sk s6 + 1) = 2 * 2 ^ PNM.b_sk s6) by (rewrite (Z.pow_add_r 2 (PNM.b_sk s6) 1) by (clear - Hk6; lia); clear; lia).
  pose proof LM9 as (_ & RP9' & _). pose proof RP9' as (PA9 & _).
  pose proof PA9 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SV9 & _).
  pose proof SV9 as (_ & _ & _ & _ & _ & Hal9 & _). unfold set_vec in Hal9. cbn [PNM.b_sb] in Hal9.
  pose proof (PMFA.mod16_8 b' Hal9) as Hal8.
  set (c := PNM.BS 2 lenv 4 0 0) in *.
  assert (OKc : PNM.bstate_ok c) by (unfold PNM.bstate_ok, c; cbn [PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx]; clear - LEN9; lia).
  assert (MCc : PNRA.bmode_cont (PNM.bs_mode c)) by (left; reflexivity).
  apply (bd_tail K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M9 model9 LK9 Aw9 _ sm6 ax6 cr9 fx9 R9 CTX G LM9).
  - apply (bregsT_pres R R7 R9 sp fb F); [| exact RP9].
    unfold bregsT. rewrite (KS7 2%nat), (KS7 3%nat), (KS7 4%nat), (KS7 8%nat), (KS7 9%nat), (KS7 20%nat), (KS7 21%nat), (KS7 22%nat), (KS7 23%nat), (KS7 24%nat), (KS7 25%nat), (KS7 26%nat), (KS7 27%nat) by inl.
    repeat split; assumption.
  - apply (PNABDK.spill_agree M8 M9 sp F); [clear - pf4; lia| clear - pf4; lia| exact SPL8| intros a Ha; apply FRC9; clear - Ha; lia].
  - apply (L5C.u64_at_agree RSEGS M8 M9 (sp - 144)); [intros j Hj; apply FRC9; clear - Hj; lia| clear - pf4; lia| clear - pf4; lia| exact C1448].
  - rewrite X109. rewrite bvu_small64 by (clear - B4096 BTOP Hlen6 P2k PK1; lia). clear - B4096 BTOP Hlen6 P2k PK1; lia.
  - rewrite X109. rewrite bvu_small64 by (clear - B4096 BTOP Hlen6 P2k PK1; lia).
    replace (b' + 40 * (Z.of_nat (length (PNM.b_stk s6)) + 1)) with (b' + (5 * (Z.of_nat (length (PNM.b_stk s6)) + 1)) * 8) by (clear; lia).
    rewrite Z_mod_plus_full. exact Hal8.
  - pose proof (vecend_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M9 model9 LK9 Aw9 _ sm6 ax6 cr9 CTX G LM9) as VE9.
    rewrite X109, bvu_small64 by (clear - B4096 BTOP Hlen6 P2k PK1; lia).
    unfold set_vec in VE9. cbn [PNM.b_sb PNM.b_stk PNBO.set_more] in VE9. rewrite length_app in VE9. cbn [length] in VE9.
    rewrite Nat2Z.inj_add in VE9. exact VE9.
  - right. split; [exact (ECK9 _ _ (ECK8 _ _ EC6))|]. right. exists c.
    unfold set_vec. cbn [PNM.b_stk PNM.b_src PNBO.set_more]. rewrite ESTK.
    split; [reflexivity|]. split; [exact OKc|]. split; [exact MCc|]. split; [reflexivity| exact UNR6].
  - destruct INV6 as (ID6 & SH6). split; [unfold set_vec; cbn [PNM.b_done PNBO.set_more]; exact ID6|].
    unfold set_vec. cbn [PNM.b_stk]. apply bstack_shape_push; [exact SH6| unfold PNM.MAX_DEPTH; exact DEPTH| exact OKc| exact MCc].
  - unfold set_vec. cbn [PNM.b_stk]. rewrite <- ESTK. rewrite length_app. clear; lia.
Qed.

Definition bd_u1K K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 : Prop :=
  forall M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 (fx6 : FPState) R6,
  bd_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  bd_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 ->
  bregs R R6 sp fb F -> getr R6 (reg 18) = Z_to_bv 64 4 ->
  spill M6 sp F -> L5.u64_at RSEGS M6 (sp - 112) 4 ->
  L5.u64_at RSEGS M6 (sp - 144) (fb + 464 + 400) -> L5.u64_at RSEGS M6 (sp - 136) (fb + 464 + 392) ->
  PMSPA.ec_at RSEGS M6 (fb + 1024) e cat ->
  PNRA.binv s6 -> PNM.b_stk s6 = PNM.b_stk s -> Z.of_nat (length (PNM.b_stk s6)) <= 1024 ->
  PM.unread (PNM.b_src s6) sm6 + 4 <= PM.unread (PNM.b_src s) sm ->
  Z.of_nat (length (PNM.b_stk s6)) < 2 ^ PNM.b_sk s6 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 0xaeabc M6 model6) K.

Definition bd_u1post K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 : Prop :=
  forall s6 sm6 ax6 cr6 (M1 : mem) model1 LK1 Aw1 (fx1 : FPState) R1 (fx2 : FPState) R2 (M3 : mem) model3 LK3 Aw3,
  bd_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  bd_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 (PNBO.set_more s6 1) sm6 ax6 cr6 ->
  getr R1 (reg 1) = Z_to_bv 64 0xb25f4 -> getr R1 (reg 2) = Z_to_bv 64 (sp - 224) -> getr R1 (reg 8) = Z_to_bv 64 (sp - 112) ->
  getr R1 (reg 9) = Z_to_bv 64 (sp - 116) -> getr R1 (reg 10) = Z_to_bv 64 (fb + 464 + 392) -> getr R1 (reg 18) = Z_to_bv 64 (sp - 120) ->
  getr R1 (reg 19) = Z_to_bv 64 2147450880 -> getr R1 (reg 3) = getr R (reg 3) -> getr R1 (reg 4) = getr R (reg 4) ->
  getr R1 (reg 20) = Z_to_bv 64 F -> getr R1 (reg 21) = Z_to_bv 64 (fb + 1024) -> getr R1 (reg 22) = Z_to_bv 64 ((fb + 464 + 400) / 8 + 2147450880) ->
  getr R1 (reg 23) = Z_to_bv 64 (fb + 432) -> getr R1 (reg 24) = Z_to_bv 64 (F + 32) -> getr R1 (reg 25) = Z_to_bv 64 F ->
  getr R1 (reg 26) = Z_to_bv 64 (F / 8 + 2147450880) -> getr R1 (reg 27) = Z_to_bv 64 2147450880 ->
  L5.u64_at RSEGS M1 (sp - 208) (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6)) + 40) ->
  L5.u64_at RSEGS M1 (sp - 216) (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6))) ->
  L5.u64_at RSEGS M1 (sp - 224) (fb + 464 + 392) ->
  L5.u64_at RSEGS M1 (sp - 200) (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6))) ->
  L5.u64_at RSEGS M1 (sp - 192) F -> L5.u64_at RSEGS M1 (sp - 184) (sp - 160) ->
  L5.u64_at RSEGS M1 (sp - 176) sp -> L5.u64_at RSEGS M1 (sp - 168) 0xaeb8c -> L5.u32_at RSEGS M1 (sp - 120) 2 ->
  L5.u64_at RSEGS M1 (sp - 112) 4 -> spill M1 sp F ->
  L5.u64_at RSEGS M1 (sp - 144) (fb + 464 + 400) -> L5.u64_at RSEGS M1 (sp - 136) (fb + 464 + 392) ->
  PMSPA.ec_at RSEGS M1 (fb + 1024) e cat ->
  PNRA.binv s6 -> PNM.b_stk s6 = PNM.b_stk s -> Z.of_nat (length (PNM.b_stk s6)) <= 1024 -> Z.of_nat (length (PNM.b_stk s6)) < 2 ^ PNM.b_sk s6 ->
  PM.unread (PNM.b_src s6) sm6 + 4 <= PM.unread (PNM.b_src s) sm ->
  regs_preserved R1 R2 ->
  L5.u64_at RSEGS M3 (fb + 464 + 392) (PNM.b_sb (PNBO.set_more s6 1)) ->
  L5.u64_at RSEGS M3 (fb + 464 + 392 + 8) (PNM.b_sb (PNBO.set_more s6 1) + 40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1)))) ->
  L5.u64_at RSEGS M3 (fb + 464 + 392 + 16) (PNM.b_sb (PNBO.set_more s6 1) + 40 * 2 ^ PNM.b_sk (PNBO.set_more s6 1)) ->
  (forall i, (i < length (PNM.b_stk (PNBO.set_more s6 1)))%nat -> PNM.bstate_at RSEGS M3 (PNM.b_sb (PNBO.set_more s6 1) + 40 * Z.of_nat i) (nth i (PNM.b_stk (PNBO.set_more s6 1)) PNM.bs_root)) ->
  L5.defined M3 (PNM.b_sb (PNBO.set_more s6 1)) (40 * 2 ^ PNM.b_sk (PNBO.set_more s6 1)) ->
  PMSPA.accA M3 (PNM.b_sb (PNBO.set_more s6 1)) (40 * (Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))) + 1)) ->
  PMSPA.annA M3 (PNM.b_sb (PNBO.set_more s6 1)) (40 * (Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))) + 1)) (40 * 2 ^ PNM.b_sk (PNBO.set_more s6 1)) ->
  PMSPA.accA M3 (fb + 464 + 392) 24 -> PMSTA.base_okA RSEGS PMA.AD M3 ->
  L5CA.ahpres L ar (rest_own (PNBO.set_more s6 1) ++ LBX) ((F, 0, sp - 160 + 32) :: FF) (sp - 224) (PMSPA.pm_scr 0) [] M1 M3 ->
  model_rt model1 model3 -> incl LK3 LK1 -> incl Aw1 Aw3 -> L5CA.amodel_ok Aw3 model3 ->
  ri_inv HI (PNM.bvec_own (PNM.b_sb (PNBO.set_more s6 1)) (PNM.b_sk (PNBO.set_more s6 1)) ++ rest_own (PNBO.set_more s6 1) ++ LBX) ((F, 0, sp - 160 + 32) :: FF) LK3 cr6 Aw3 M3 (vml_of model3) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 0xb25f4 M3 model3) K.

Definition bd_u1_tail K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 : Prop :=
  forall s6 sm6 ax6 (M7 : mem) model7 LK7 Aw7 cr7 (fx7 : FPState) R7 lenv,
  bd_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  bd_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M7 model7 LK7 Aw7 (set_vec (PNBO.set_more s6 1) (PNM.b_sb s6) (PNM.b_sk s6) (PNM.b_stk s6 ++ [PNM.BS 2 lenv 4 0 0])) sm6 ax6 cr7 ->
  bregsT R R7 sp fb F -> spill M7 sp F -> L5.u64_at RSEGS M7 (sp - 144) (fb + 464 + 400) ->
  getr R7 (reg 10) = Z_to_bv 64 (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6)) + 40) ->
  PMSPA.ec_at RSEGS M7 (fb + 1024) e cat -> 0 <= lenv < 2 ^ 64 ->
  PNRA.binv s6 -> PNM.b_stk s6 = PNM.b_stk s -> Z.of_nat (length (PNM.b_stk s6)) <= 1024 -> Z.of_nat (length (PNM.b_stk s6)) < 2 ^ PNM.b_sk s6 ->
  PM.unread (PNM.b_src s6) sm6 + 4 <= PM.unread (PNM.b_src s) sm ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx7 R7 0xaebb4 M7 model7) K.

Definition bd_u1_elem_T K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 : Prop :=
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
  /\ L5KA.zeros_at (mrestrict (ahid Aw3 model3) M3) ((sp / 8) + 2147450368) 512
  /\ L5KA.zeros_at (mrestrict (ahid Aw3 model3) M3) ((((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) / 8) + 2147450880) 5
  /\ L5.writable RSEGS (mrestrict (ahid Aw3 model3) M3) ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) 40
  /\ PNABDP.aligned ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) 8
  /\ L5KA.zeros_at (mrestrict (ahid Aw3 model3) M3) (((((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) + 8) / 8) + 2147450880) 1
  /\ L5KA.zeros_at (mrestrict (ahid Aw3 model3) M3) (((((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) + 16) / 8) + 2147450880) 1
  /\ L5KA.zeros_at (mrestrict (ahid Aw3 model3) M3) (((((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) + 24) / 8) + 2147450880) 1
  /\ L5KA.zeros_at (mrestrict (ahid Aw3 model3) M3) (((((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) + 32) / 8) + 2147450880) 1
  /\ (2147446784 + 17592186048512 <= ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) \/ ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) + 40 <= 2147446784)
  /\ ((sp - 224) + 224 <= ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) \/ ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) + 40 <= (sp - 224))
  /\ (((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) + 40 <= F \/ F + 64 <= ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))))
  /\ (((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) + 40 <= fl \/ fl + 1 <= ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))))
  /\ 4096 <= ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) <= 140737488355288
  /\ (65536 + 6840320 <= ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) \/ ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) + 40 <= 65536)
  /\ ((sp - 4096) + 4096 <= ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) \/ ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) + 40 <= (sp - 4096))
  /\ ((fb + 464) + 416 <= ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) \/ ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) + 40 <= (fb + 464))
  /\ ((fb + 432) + 8 <= ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) \/ ((PNM.b_sb (PNBO.set_more s6 1)) + (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))))) + 40 <= (fb + 432)).

Definition bd_u1_m3vis_T K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 : Prop :=
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
  pfacts (mrestrict (ahid Aw3 model3) M3) sp (fb + 464) F fl
  /\ own sp R (mrestrict (ahid Aw3 model3) M3)
  /\ (forall a v, sp - 224 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1 a v -> L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) a v)
  /\ (forall a v, sp - 224 <= a -> a + 4 <= sp -> L5.u32_at RSEGS M1 a v -> L5.u32_at RSEGS (mrestrict (ahid Aw3 model3) M3) a v)
  /\ (forall v, L5.u8_at RSEGS M1 (fb + 464 + 8) v -> L5.u8_at RSEGS (mrestrict (ahid Aw3 model3) M3) (fb + 464 + 8) v)
  /\ L5.writable RSEGS (mrestrict (ahid Aw3 model3) M3) (fb + 464) 424 /\ L5.u8_at RSEGS (mrestrict (ahid Aw3 model3) M3) (fb + 464 + 10) 0
  /\ L5.writable RSEGS (mrestrict (ahid Aw3 model3) M3) (sp - 240) 240
  /\ (sp - 240 + 240 <= fb + 464 \/ fb + 464 + 416 <= sp - 240) /\ (sp - 240 + 240 <= F \/ F + 64 <= sp - 240)
  /\ (sp - 240 + 240 <= fl \/ fl + 1 <= sp - 240) /\ (sp - 240 + 240 <= fb + 432 \/ fb + 432 + 8 <= sp - 240)
  /\ L5KA.zeros_at (mrestrict (ahid Aw3 model3) M3) (((sp - 224) / 8) + 2147450880) 1 /\ L5KA.zeros_at (mrestrict (ahid Aw3 model3) M3) (((sp - 216) / 8) + 2147450880) 1 /\ L5KA.zeros_at (mrestrict (ahid Aw3 model3) M3) (((sp - 208) / 8) + 2147450880) 1
  /\ L5KA.zeros_at (mrestrict (ahid Aw3 model3) M3) (((sp - 120) / 8) + 2147450880) 1 /\ L5KA.zeros_at (mrestrict (ahid Aw3 model3) M3) (((sp - 116) / 8) + 2147450880) 1 /\ L5KA.zeros_at (mrestrict (ahid Aw3 model3) M3) (((sp - 112) / 8) + 2147450880) 1
  /\ L5KA.zeros_at (mrestrict (ahid Aw3 model3) M3) (((fb + 432) / 8) + 2147450880) 1
  /\ L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) (fb + 432) 1251456
  /\ L5KA.zeros_at (mrestrict (ahid Aw3 model3) M3) 2147607320 1.

Local Ltac u1find := match goal with
  | H : ?a <= ?x <= ?b |- ?a <= ?x <= ?b => exact H
  | H : ?a <= ?x < ?b |- ?a <= ?x < ?b => exact H
  | H : ?a < ?b |- ?a < ?b => exact H
  | H : ?a <= ?b \/ ?c <= ?d |- ?a <= ?b \/ ?c <= ?d => exact H
  | H : ?a mod ?b = ?c |- ?a mod ?b = ?c => exact H
  | H : PNABDP.aligned ?a ?b |- PNABDP.aligned ?a ?b => exact H
  | H : getr ?R ?r = ?v |- getr ?R ?r = ?v => exact H
  | H : L5.u64_at ?s ?m ?a ?v |- L5.u64_at ?s ?m ?a ?v => exact H
  | H : L5.u32_at ?s ?m ?a ?v |- L5.u32_at ?s ?m ?a ?v => exact H
  | H : L5.u8_at ?s ?m ?a ?v |- L5.u8_at ?s ?m ?a ?v => exact H
  | H : L5.defined ?m ?a ?n |- L5.defined ?m ?a ?n => exact H
  | H : L5.writable ?s ?m ?a ?n |- L5.writable ?s ?m ?a ?n => exact H
  | H : L5KA.zeros_at ?m ?a ?n |- L5KA.zeros_at ?m ?a ?n => exact H
  | H : L5.img_clear ?m ?a ?n |- L5.img_clear ?m ?a ?n => exact H
  end.
Local Ltac u1dsp LIA := lazymatch goal with
  | |- PNABDP.aligned _ _ => first [ u1find | unfold PNABDP.aligned; u1find ]
  | |- 0 <= bv_unsigned ?x < 2 ^ 64 => exact (bvu_rng x)
  | |- _ <= _ <= _ => first [ u1find | LIA ]
  | |- _ <= _ < _ => first [ u1find | LIA ]
  | |- _ < _ => first [ u1find | LIA ]
  | |- _ \/ _ => first [ u1find | LIA ]
  | |- _ => u1find
  end.
Local Ltac u1feed P tac := lazymatch type of P with
  | ?A -> _ => let H := fresh "FD" in assert (H : A) by (first [ tac | fail 100 "feed: premise" A ]); specialize (P H); clear H; u1feed P tac
  | _ => idtac
  end.

Lemma bd_u1_abdU K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 :
  bd_u1_elem_T K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 ->
  bd_u1_m3vis_T K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 ->
  forall s6 sm6 ax6 cr6 (M1 : mem) model1 LK1 Aw1 (fx1 : FPState) R1 (fx2 : FPState) R2 (M3 : mem) model3 LK3 Aw3,
  bd_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  bd_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 (PNBO.set_more s6 1) sm6 ax6 cr6 ->
  getr R1 (reg 1) = Z_to_bv 64 0xb25f4 -> getr R1 (reg 2) = Z_to_bv 64 (sp - 224) -> getr R1 (reg 8) = Z_to_bv 64 (sp - 112) ->
  getr R1 (reg 9) = Z_to_bv 64 (sp - 116) -> getr R1 (reg 10) = Z_to_bv 64 (fb + 464 + 392) -> getr R1 (reg 18) = Z_to_bv 64 (sp - 120) ->
  getr R1 (reg 19) = Z_to_bv 64 2147450880 -> getr R1 (reg 3) = getr R (reg 3) -> getr R1 (reg 4) = getr R (reg 4) ->
  getr R1 (reg 20) = Z_to_bv 64 F -> getr R1 (reg 21) = Z_to_bv 64 (fb + 1024) -> getr R1 (reg 22) = Z_to_bv 64 ((fb + 464 + 400) / 8 + 2147450880) ->
  getr R1 (reg 23) = Z_to_bv 64 (fb + 432) -> getr R1 (reg 24) = Z_to_bv 64 (F + 32) -> getr R1 (reg 25) = Z_to_bv 64 F ->
  getr R1 (reg 26) = Z_to_bv 64 (F / 8 + 2147450880) -> getr R1 (reg 27) = Z_to_bv 64 2147450880 ->
  L5.u64_at RSEGS M1 (sp - 208) (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6)) + 40) ->
  L5.u64_at RSEGS M1 (sp - 216) (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6))) ->
  L5.u64_at RSEGS M1 (sp - 224) (fb + 464 + 392) ->
  L5.u64_at RSEGS M1 (sp - 200) (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6))) ->
  L5.u64_at RSEGS M1 (sp - 192) F -> L5.u64_at RSEGS M1 (sp - 184) (sp - 160) ->
  L5.u64_at RSEGS M1 (sp - 176) sp -> L5.u64_at RSEGS M1 (sp - 168) 0xaeb8c -> L5.u32_at RSEGS M1 (sp - 120) 2 ->
  L5.u64_at RSEGS M1 (sp - 112) 4 -> spill M1 sp F ->
  L5.u64_at RSEGS M1 (sp - 144) (fb + 464 + 400) -> L5.u64_at RSEGS M1 (sp - 136) (fb + 464 + 392) ->
  PMSPA.ec_at RSEGS M1 (fb + 1024) e cat ->
  PNRA.binv s6 -> PNM.b_stk s6 = PNM.b_stk s -> Z.of_nat (length (PNM.b_stk s6)) <= 1024 -> Z.of_nat (length (PNM.b_stk s6)) < 2 ^ PNM.b_sk s6 ->
  PM.unread (PNM.b_src s6) sm6 + 4 <= PM.unread (PNM.b_src s) sm ->
  regs_preserved R1 R2 ->
  L5.u64_at RSEGS M3 (fb + 464 + 392) (PNM.b_sb (PNBO.set_more s6 1)) ->
  L5.u64_at RSEGS M3 (fb + 464 + 392 + 8) (PNM.b_sb (PNBO.set_more s6 1) + 40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1)))) ->
  L5.u64_at RSEGS M3 (fb + 464 + 392 + 16) (PNM.b_sb (PNBO.set_more s6 1) + 40 * 2 ^ PNM.b_sk (PNBO.set_more s6 1)) ->
  (forall i, (i < length (PNM.b_stk (PNBO.set_more s6 1)))%nat -> PNM.bstate_at RSEGS M3 (PNM.b_sb (PNBO.set_more s6 1) + 40 * Z.of_nat i) (nth i (PNM.b_stk (PNBO.set_more s6 1)) PNM.bs_root)) ->
  L5.defined M3 (PNM.b_sb (PNBO.set_more s6 1)) (40 * 2 ^ PNM.b_sk (PNBO.set_more s6 1)) ->
  PMSPA.accA M3 (PNM.b_sb (PNBO.set_more s6 1)) (40 * (Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))) + 1)) ->
  PMSPA.annA M3 (PNM.b_sb (PNBO.set_more s6 1)) (40 * (Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))) + 1)) (40 * 2 ^ PNM.b_sk (PNBO.set_more s6 1)) ->
  PMSPA.accA M3 (fb + 464 + 392) 24 -> PMSTA.base_okA RSEGS PMA.AD M3 ->
  L5CA.ahpres L ar (rest_own (PNBO.set_more s6 1) ++ LBX) ((F, 0, sp - 160 + 32) :: FF) (sp - 224) (PMSPA.pm_scr 0) [] M1 M3 ->
  model_rt model1 model3 -> incl LK3 LK1 -> incl Aw1 Aw3 -> L5CA.amodel_ok Aw3 model3 ->
  ri_inv HI (PNM.bvec_own (PNM.b_sb (PNBO.set_more s6 1)) (PNM.b_sk (PNBO.set_more s6 1)) ++ rest_own (PNBO.set_more s6 1) ++ LBX) ((F, 0, sp - 160 + 32) :: FF) LK3 cr6 Aw3 M3 (vml_of model3) ->
  (forall (fx7 : FPState) R7 (M7 : mem) model7,
     ri_inv HI (PNM.bvec_own (PNM.b_sb (PNBO.set_more s6 1)) (PNM.b_sk (PNBO.set_more s6 1)) ++ rest_own (PNBO.set_more s6 1) ++ LBX) ((F, 0, sp - 160 + 32) :: FF) LK3 cr6 Aw3 M7 (vml_of model7) ->
     L5CA.amodel_ok Aw3 model7 -> model_rt model3 model7 -> ahid Aw3 model7 = ahid Aw3 model3 -> mem_grows M3 M7 ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6)) <= a < PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6)) + 40 \/ fb + 464 + 400 <= a < fb + 464 + 400 + 8 \/ sp - 240 <= a < sp - 160) -> M7 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)) ->
     L5.u32_at RSEGS M7 (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6))) 2 -> L5.u64_at RSEGS M7 (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6)) + 16) 4 -> L5.u8_at RSEGS M7 (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6)) + 24) 0 ->
     L5.u64_at RSEGS M7 (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6)) + 32) 0 -> L5.u64_at RSEGS M7 (fb + 464 + 400) (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6)) + 40) ->
     bregsT R R7 sp fb F -> getr R7 (reg 10) = Z_to_bv 64 (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6)) + 40) ->
     srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx7 R7 0xaebb4 M7 model7) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 0xb25f4 M3 model3) K.
Proof.
  intros UE UV s6 sm6 ax6 cr6 M1 model1 LK1 Aw1 fx1 R1 fx2 R2 M3 model3 LK3 Aw3 CTX G LM
    X1 X2 X8 X9 X10 X18 X19 X3 X4 X20 X21 X22 X23 X24 X25 X26 X27
    C208 C216 C224 C200 C192 C184 C176 C168 U120 U112 SPL C144 C136 EC1
    INV6 ESTK DEPTH SKB UNR RP V392 V400 V408 ELTS DEF ACC ANN ACCv BASE AHP RT3 ILK3 IAw3 AM3 RI3 KONT.
  pose proof (UE s6 sm6 ax6 cr6 M1 model1 LK1 Aw1 M3 model3 LK3 Aw3 CTX G LM INV6 ESTK DEPTH SKB V392 V400 V408 ELTS DEF ACC ANN ACCv BASE AHP RT3 ILK3 IAw3 AM3 RI3)
    as (E392 & E400 & E408 & RB41 & AL41 & RB42 & AL42 & RB43 & AL43 & ZSP & ZE0 & WRE & ALE & ZE8 & ZE16 & ZE24 & ZE32 & DE1 & DE2 & DE3 & DE4 & RBE & DE5 & DE6 & DE7 & DE8).
  pose proof (UV s6 sm6 ax6 cr6 M1 model1 LK1 Aw1 M3 model3 LK3 Aw3 CTX G LM INV6 ESTK DEPTH SKB V392 V400 V408 ELTS DEF ACC ANN ACCv BASE AHP RT3 ILK3 IAw3 AM3 RI3)
    as (PF & OWN3 & SV3 & SV3w & U8op3 & WRop3 & Z10 & W240 & D240o & D240F & D240fl & D240v & Z224 & Z216 & Z208 & Z120 & Z116 & Z112 & vz1 & vu1 & vz2).
  cbn [PNBO.set_more PNM.b_sb PNM.b_sk PNM.b_stk] in E392, E400, E408, RB41, AL41, RB42, AL42, RB43, AL43, ZE0, WRE, ALE, ZE8, ZE16, ZE24, ZE32, DE1, DE2, DE3, DE4, RBE, DE5, DE6, DE7, DE8.
  pose proof (vfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PNBO.set_more s6 1) sm6 ax6 cr6 CTX G LM)
    as (vf1 & vf2 & vf3 & _ & vf5 & vf6 & vf7 & vf8 & _ & _ & vf11).
  pose proof (wfacts224_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PNBO.set_more s6 1) sm6 ax6 cr6 CTX G LM)
    as (_ & S224o & S224F & S224fl & S224v).
  pose proof LM as (_ & RP1 & _). pose proof RP1 as (PA1 & _). change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA1.
  pose proof PA1 as (_ & _ & _ & MORE1 & _).
  pose proof CTX as (_ & _ & _ & _ & (_ & _ & _ & _ & _ & ASTK0 & _) & _). change (PMSPA.pm_scr 7) with 26624 in ASTK0. destruct ASTK0 as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof CTX as (_ & HH & _ & _ & _ & _ & _ & FOK & _). pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *.
  unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ LK3 cr6 Aw3 M3 model3 RI3) as (_ & _ & _ & VFS3 & VLB3 & _).
  assert (IN3 : In (PNM.b_sb s6, PNM.BSZ * 2 ^ PNM.b_sk s6) (PNM.bvec_own (PNM.b_sb (PNBO.set_more s6 1)) (PNM.b_sk (PNBO.set_more s6 1)) ++ rest_own (PNBO.set_more s6 1) ++ LBX)) by (apply in_or_app; left; left; reflexivity).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ RI3) as (WB3 & _).
  destruct (WB3 _ IN3) as ((BR1 & BR2 & BR3 & BR4 & BR5 & BR6) & _). cbn [fst snd] in BR1, BR2, BR5.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in BR2.
  assert (EHI : (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6))) + 40 <= ahl_ceil ar) by (unfold PNM.BSZ in BR5; clear - BR5 SKB; lia).
  set (MV3 := mrestrict (ahid Aw3 model3) M3) in *.
  unfold pfacts in PF. destruct PF as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32 & pf33 & pf34).
  unfold own in OWN3. destruct OWN3 as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & O12 & O13).
  pose proof (SV3 (sp - 144) _ ltac:(clear; lia) ltac:(clear; lia) C144) as C144v.
  pose proof (SV3 (sp - 136) _ ltac:(clear; lia) ltac:(clear; lia) C136) as C136v.
  pose proof (SV3 (sp - 208) _ ltac:(clear; lia) ltac:(clear; lia) C208) as C208v.
  pose proof (SV3 (sp - 216) _ ltac:(clear; lia) ltac:(clear; lia) C216) as C216v.
  pose proof (SV3 (sp - 224) _ ltac:(clear; lia) ltac:(clear; lia) C224) as C224v.
  pose proof (SV3 (sp - 200) _ ltac:(clear; lia) ltac:(clear; lia) C200) as C200v.
  pose proof (SV3 (sp - 192) _ ltac:(clear; lia) ltac:(clear; lia) C192) as C192v.
  pose proof (SV3 (sp - 184) _ ltac:(clear; lia) ltac:(clear; lia) C184) as C184v.
  pose proof (SV3 (sp - 176) _ ltac:(clear; lia) ltac:(clear; lia) C176) as C176v.
  pose proof (SV3 (sp - 168) _ ltac:(clear; lia) ltac:(clear; lia) C168) as C168v.
  pose proof (SV3 (sp - 112) _ ltac:(clear; lia) ltac:(clear; lia) U112) as U112v.
  pose proof (SV3 (sp - 128) _ ltac:(clear; lia) ltac:(clear; lia) SPL) as SPLv.
  pose proof (SV3w (sp - 120) 2 ltac:(clear; lia) ltac:(clear; lia) U120) as U120v.
  assert (U8v : L5.u8_at RSEGS MV3 (fb + 464 + 8) 1) by exact (U8op3 _ MORE1).
  pose proof (L5KA.zeros_at_sub MV3 _ 5 _ 1 ZE0 (Z.le_refl _) ltac:(clear; lia)) as ZE1.
  assert (ALE40 : PNABDP.aligned ((PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6))) + 40) 8) by (unfold PNABDP.aligned in ALE |- *; replace ((PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6))) + 40) with ((PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6))) + 5 * 8) by (clear; lia); rewrite Z_mod_plus_full; exact ALE).
  assert (W224 : L5.writable RSEGS MV3 (sp - 224) 224) by (apply (L5.writable_sub RSEGS MV3 (sp - 240) 240); [exact W240| clear; lia| clear; lia]).
  assert (WV8 : L5.writable RSEGS MV3 (fb + 464 + 8) 1) by (apply (L5.writable_sub RSEGS MV3 (fb + 464) 424); [exact WRop3| clear; lia| clear; lia]).
  assert (WV392 : L5.writable RSEGS MV3 (fb + 464 + 392) 24) by (apply (L5.writable_sub RSEGS MV3 (fb + 464) 424); [exact WRop3| clear; lia| clear; lia]).
  assert (Q34 : 0 <= fb + 432 < 2 ^ 64) by (clear - vf1; lia).
  assert (Q36 : 0 <= fb + 1024 < 2 ^ 64) by (clear - pf7; lia).
  destruct (u32_of_defined MV3 (F + 32) ltac:(clear - pf15; lia) ltac:(clear - pf15; lia) ltac:(apply (L5.defined_sub MV3 F 64); [exact pf17| clear; lia| clear; lia])) as (lenw & Hlenw & ULEN).
  assert (Q46 : 0 <= lenw < 2 ^ 64) by (clear - Hlenw; lia).
  assert (Q46' : 0 <= lenw <= 4294967295) by (clear - Hlenw; lia).
  pose proof (bvu_rng (getr R (reg 1))) as Q60.
  pose proof (bvu_rng (getr R (reg 8))) as Q61.
  pose proof (bvu_rng (getr R (reg 9))) as Q62.
  pose proof (bvu_rng (getr R (reg 18))) as Q63.
  pose proof (bvu_rng (getr R (reg 19))) as Q64.
  pose proof (bvu_rng (getr R (reg 20))) as Q65.
  pose proof (bvu_rng (getr R (reg 21))) as Q66.
  pose proof (bvu_rng (getr R (reg 22))) as Q67.
  pose proof (bvu_rng (getr R (reg 23))) as Q68.
  pose proof (bvu_rng (getr R (reg 24))) as Q69.
  pose proof (bvu_rng (getr R (reg 25))) as Q70.
  pose proof (bvu_rng (getr R (reg 26))) as Q71.
  pose proof (bvu_rng (getr R (reg 27))) as Q72.
  assert (Q41 : 0 <= PNM.b_sb s6 < 2 ^ 64) by (clear - RB41; lia).
  assert (Q42 : 0 <= 40 * Z.of_nat (length (PNM.b_stk s6)) < 2 ^ 64) by (clear - RB42; lia).
  assert (Q43 : 0 <= 40 * 2 ^ PNM.b_sk s6 < 2 ^ 64) by (clear - RB43; lia).
  assert (NF : (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6))) mod 2 ^ 64 < (PNM.b_sb s6 + 40 * 2 ^ PNM.b_sk s6) mod 2 ^ 64).
  { rewrite !Z.mod_small by (clear - RB41 RB42 RB43; lia). clear - SKB; lia. }
  assert (CS : forall i, In i L5SAR.cs_all -> getr R2 (reg i) = getr R1 (reg i)) by (intros i Hi; exact (L5SAR.cs_of_preserved R1 R2 i RP Hi)).
  assert (G2 : getr R2 (reg 2) = getr R1 (reg 2)) by (apply CS; (apply L5K.In_of_mem; vm_compute; reflexivity)). rewrite X2 in G2.
  assert (G3 : getr R2 (reg 3) = getr R1 (reg 3)) by (apply CS; (apply L5K.In_of_mem; vm_compute; reflexivity)). rewrite X3 in G3.
  assert (G4 : getr R2 (reg 4) = getr R1 (reg 4)) by (apply CS; (apply L5K.In_of_mem; vm_compute; reflexivity)). rewrite X4 in G4.
  assert (G8 : getr R2 (reg 8) = getr R1 (reg 8)) by (apply CS; (apply L5K.In_of_mem; vm_compute; reflexivity)). rewrite X8 in G8.
  assert (G9 : getr R2 (reg 9) = getr R1 (reg 9)) by (apply CS; (apply L5K.In_of_mem; vm_compute; reflexivity)). rewrite X9 in G9.
  assert (G18 : getr R2 (reg 18) = getr R1 (reg 18)) by (apply CS; (apply L5K.In_of_mem; vm_compute; reflexivity)). rewrite X18 in G18.
  assert (G19 : getr R2 (reg 19) = getr R1 (reg 19)) by (apply CS; (apply L5K.In_of_mem; vm_compute; reflexivity)). rewrite X19 in G19.
  assert (G20 : getr R2 (reg 20) = getr R1 (reg 20)) by (apply CS; (apply L5K.In_of_mem; vm_compute; reflexivity)). rewrite X20 in G20.
  assert (G21 : getr R2 (reg 21) = getr R1 (reg 21)) by (apply CS; (apply L5K.In_of_mem; vm_compute; reflexivity)). rewrite X21 in G21.
  assert (G22 : getr R2 (reg 22) = getr R1 (reg 22)) by (apply CS; (apply L5K.In_of_mem; vm_compute; reflexivity)). rewrite X22 in G22.
  assert (G23 : getr R2 (reg 23) = getr R1 (reg 23)) by (apply CS; (apply L5K.In_of_mem; vm_compute; reflexivity)). rewrite X23 in G23.
  assert (G24 : getr R2 (reg 24) = getr R1 (reg 24)) by (apply CS; (apply L5K.In_of_mem; vm_compute; reflexivity)). rewrite X24 in G24.
  assert (G25 : getr R2 (reg 25) = getr R1 (reg 25)) by (apply CS; (apply L5K.In_of_mem; vm_compute; reflexivity)). rewrite X25 in G25.
  assert (G26 : getr R2 (reg 26) = getr R1 (reg 26)) by (apply CS; (apply L5K.In_of_mem; vm_compute; reflexivity)). rewrite X26 in G26.
  assert (G27 : getr R2 (reg 27) = getr R1 (reg 27)) by (apply CS; (apply L5K.In_of_mem; vm_compute; reflexivity)). rewrite X27 in G27.
  pose proof (PNABDP.abdU_conc fx2 R2 MV3 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 41%nat => PNM.b_sb s6 | 42%nat => 40 * Z.of_nat (length (PNM.b_stk s6)) | 43%nat => 40 * 2 ^ PNM.b_sk s6 | 46%nat => lenw | 50%nat => F | 51%nat => fl | 60%nat => bv_unsigned (getr R (reg 1)) | 61%nat => bv_unsigned (getr R (reg 8)) | 62%nat => bv_unsigned (getr R (reg 9)) | 63%nat => bv_unsigned (getr R (reg 18)) | 64%nat => bv_unsigned (getr R (reg 19)) | 65%nat => bv_unsigned (getr R (reg 20)) | 66%nat => bv_unsigned (getr R (reg 21)) | 67%nat => bv_unsigned (getr R (reg 22)) | 68%nat => bv_unsigned (getr R (reg 23)) | 69%nat => bv_unsigned (getr R (reg 24)) | 70%nat => bv_unsigned (getr R (reg 25)) | 71%nat => bv_unsigned (getr R (reg 26)) | 72%nat => bv_unsigned (getr R (reg 27)) | _ => 0 end)) as P. cbn beta iota in P.
  u1feed P ltac:(idtac; u1dsp ltac:(idtac; first [ clear - RB41 RB42 RB43 RBE EHI SLO SHI SPT SKB pf4 pf7 pf15 pf22 Q46'; lia | clear - DE3; lia | clear - DE4; lia | clear - DE6; lia | clear - DE1; lia | clear - DE5; lia | clear - DE7; lia | clear - DE8; lia | clear - DE2; lia ])).
  destruct P as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & Y1 & Y2 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y18 & Y19 & E400x & E32 & E24 & E16 & E0).
  assert (AVe : L5A.avis (ahid Aw3 model3) (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6))) 40).
  { apply (VLB3 _ _ _ _ IN3); cbn [fst snd]; unfold PNM.BSZ; clear - SKB; lia. }
  assert (AVo : L5A.avis (ahid Aw3 model3) (fb + 464 + 400) 8).
  { apply VFS3; unfold FS_BYTES; clear - F1 F2; lia. }
  apply (L5SAR.apiece L ar C HI LYa HIok _ _ LK3 cr6 Aw3 M3 model3 fx2 fx7 R2 _ R7 _ M7v
           (fun a => (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6))) <= a < (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6))) + 40 \/ fb + 464 + 400 <= a < fb + 464 + 400 + 8 \/ sp - 240 <= a < sp - 160) K RI3 AM3 MS7 MG7).
  { intros a Ha N. apply FRZ7; [exact Ha| intros X; apply N; left; clear - X; lia| intros X; apply N; right; left; clear - X; lia| intros X; apply N; right; right; clear - X; lia]. }
  { intros a Ha [Wa|[Wa|Wa]].
    - split; [| intros X; first [clear - X Wa BR2 SKB; unfold PNM.BSZ in BR2; lia| clear - X Wa DE1; lia| clear - X Wa DE5; lia]].
      unfold aclientw, aclient_g. left. exists (PNM.b_sb s6, PNM.BSZ * 2 ^ PNM.b_sk s6). split; [exact IN3|].
      cbn [fst snd]. unfold PNM.BSZ. clear - Wa SKB; lia.
    - split; [| intros X; clear - X Wa F1 FSAPP FSIMG; lia].
      apply (L5SAR.fframe_client L ar _ _ 0 0 fb 5 rs); [right; exact Hfb| change (ff_bytes 5) with 2048; clear - Wa; lia].
    - split; [| intros X; clear - X Wa SLO F1 FSAPP FSCEIL FSIMG; lia].
      unfold aclientw, aclient_g. right; left. split; [clear - Wa SLO SHI SPT; lia| intros X; clear - X; lia]. }
  intros M7 model7 HH7 AM7 MRT7 HID7 VIS7 MGM7 FR7 VV7.
  apply (KONT fx7 R7 M7 model7 HH7 AM7 MRT7 HID7 MGM7 FR7).
  - pose proof (L5A.avis_sub (ahid Aw3 model3) (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6))) 40 (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6))) 4 AVe ltac:(clear; lia) ltac:(clear; lia)) as AVc.
    pose proof (L5A.u32_at_vis (ahid Aw3 model3) M7 (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6))) 2 AVc ltac:(clear - Q41 Q42; lia) ltac:(clear - RBE; lia)) as UVc.
    rewrite VIS7 in UVc. exact (proj1 UVc E0).
  - pose proof (L5A.avis_sub (ahid Aw3 model3) (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6))) 40 (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6)) + 16) 8 AVe ltac:(clear; lia) ltac:(clear; lia)) as AVc.
    pose proof (L5A.u64_at_vis (ahid Aw3 model3) M7 (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6)) + 16) 4 AVc ltac:(clear - Q41 Q42; lia) ltac:(clear - RBE; lia)) as UVc.
    rewrite VIS7 in UVc. exact (proj1 UVc E16).
  - pose proof (L5A.avis_sub (ahid Aw3 model3) (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6))) 40 (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6)) + 24) 1 AVe ltac:(clear; lia) ltac:(clear; lia)) as AVc.
    pose proof (L5A.u8_at_vis (ahid Aw3 model3) M7 (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6)) + 24) 0 AVc ltac:(clear - Q41 Q42; lia) ltac:(clear - RBE; lia)) as UVc.
    rewrite VIS7 in UVc. exact (proj1 UVc E24).
  - pose proof (L5A.avis_sub (ahid Aw3 model3) (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6))) 40 (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6)) + 32) 8 AVe ltac:(clear; lia) ltac:(clear; lia)) as AVc.
    pose proof (L5A.u64_at_vis (ahid Aw3 model3) M7 (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6)) + 32) 0 AVc ltac:(clear - Q41 Q42; lia) ltac:(clear - RBE; lia)) as UVc.
    rewrite VIS7 in UVc. exact (proj1 UVc E32).
  - pose proof (L5A.u64_at_vis (ahid Aw3 model3) M7 (fb + 464 + 400) ((PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6))) + 40) AVo ltac:(clear - pf34 pf7; lia) ltac:(clear - pf7; lia)) as UVc.
    rewrite VIS7 in UVc. exact (proj1 UVc E400x).
  - unfold bregsT. rewrite (KS7 3%nat), (KS7 4%nat), (KS7 20%nat), (KS7 21%nat), (KS7 22%nat), (KS7 23%nat), (KS7 24%nat), (KS7 25%nat), (KS7 26%nat), (KS7 27%nat) by (apply L5K.In_of_mem; vm_compute; reflexivity).
    repeat apply conj; u1find.
  - exact Y10.
Qed.

Definition bd_u1_push_T K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 : Prop :=
  forall s6 sm6 ax6 cr6 (M1 : mem) model1 LK1 Aw1 (M3 : mem) model3 LK3 Aw3 (M7 : mem) model7,
  bd_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  bd_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 (PNBO.set_more s6 1) sm6 ax6 cr6 ->
  PNRA.binv s6 -> Z.of_nat (length (PNM.b_stk s6)) <= 1024 -> Z.of_nat (length (PNM.b_stk s6)) < 2 ^ PNM.b_sk s6 ->
  L5.u64_at RSEGS M3 (fb + 464 + 392) (PNM.b_sb (PNBO.set_more s6 1)) ->
  L5.u64_at RSEGS M3 (fb + 464 + 392 + 8) (PNM.b_sb (PNBO.set_more s6 1) + 40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1)))) ->
  L5.u64_at RSEGS M3 (fb + 464 + 392 + 16) (PNM.b_sb (PNBO.set_more s6 1) + 40 * 2 ^ PNM.b_sk (PNBO.set_more s6 1)) ->
  (forall i, (i < length (PNM.b_stk (PNBO.set_more s6 1)))%nat -> PNM.bstate_at RSEGS M3 (PNM.b_sb (PNBO.set_more s6 1) + 40 * Z.of_nat i) (nth i (PNM.b_stk (PNBO.set_more s6 1)) PNM.bs_root)) ->
  L5.defined M3 (PNM.b_sb (PNBO.set_more s6 1)) (40 * 2 ^ PNM.b_sk (PNBO.set_more s6 1)) ->
  PMSPA.accA M3 (PNM.b_sb (PNBO.set_more s6 1)) (40 * (Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))) + 1)) ->
  PMSPA.annA M3 (PNM.b_sb (PNBO.set_more s6 1)) (40 * (Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1))) + 1)) (40 * 2 ^ PNM.b_sk (PNBO.set_more s6 1)) ->
  PMSPA.accA M3 (fb + 464 + 392) 24 -> PMSTA.base_okA RSEGS PMA.AD M3 ->
  L5CA.ahpres L ar (rest_own (PNBO.set_more s6 1) ++ LBX) ((F, 0, sp - 160 + 32) :: FF) (sp - 224) (PMSPA.pm_scr 0) [] M1 M3 ->
  model_rt model1 model3 -> incl LK3 LK1 -> incl Aw1 Aw3 -> L5CA.amodel_ok Aw3 model3 ->
  ri_inv HI (PNM.bvec_own (PNM.b_sb (PNBO.set_more s6 1)) (PNM.b_sk (PNBO.set_more s6 1)) ++ rest_own (PNBO.set_more s6 1) ++ LBX) ((F, 0, sp - 160 + 32) :: FF) LK3 cr6 Aw3 M3 (vml_of model3) ->
  ri_inv HI (PNM.bvec_own (PNM.b_sb (PNBO.set_more s6 1)) (PNM.b_sk (PNBO.set_more s6 1)) ++ rest_own (PNBO.set_more s6 1) ++ LBX) ((F, 0, sp - 160 + 32) :: FF) LK3 cr6 Aw3 M7 (vml_of model7) ->
  L5CA.amodel_ok Aw3 model7 -> model_rt model3 model7 -> mem_grows M3 M7 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6)) <= a < PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6)) + 40 \/ fb + 464 + 400 <= a < fb + 464 + 400 + 8 \/ sp - 240 <= a < sp - 160) -> M7 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)) ->
  L5.u32_at RSEGS M7 (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6))) 2 -> L5.u64_at RSEGS M7 (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6)) + 16) 4 -> L5.u8_at RSEGS M7 (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6)) + 24) 0 ->
  L5.u64_at RSEGS M7 (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6)) + 32) 0 -> L5.u64_at RSEGS M7 (fb + 464 + 400) (PNM.b_sb s6 + 40 * Z.of_nat (length (PNM.b_stk s6)) + 40) ->
  exists lenv, 0 <= lenv < 2 ^ 64
  /\ bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M7 model7 LK3 Aw3 (set_vec (PNBO.set_more s6 1) (PNM.b_sb s6) (PNM.b_sk s6) (PNM.b_stk s6 ++ [PNM.BS 2 lenv 4 0 0])) sm6 ax6 cr6
  /\ (forall a, sp - 160 <= a < sp - 104 -> M7 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a))
  /\ (forall v c, PMSPA.ec_at RSEGS M1 (fb + 1024) v c -> PMSPA.ec_at RSEGS M7 (fb + 1024) v c).

Lemma bd_u1post_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 :
  bd_u1_elem_T K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 -> bd_u1_m3vis_T K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 -> bd_u1_push_T K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 -> bd_u1_tail K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 -> bd_u1post K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2.
Proof.
  intros UE UV UP UT. unfold bd_u1post.
  intros s6 sm6 ax6 cr6 M1 model1 LK1 Aw1 fx1 R1 fx2 R2 M3 model3 LK3 Aw3 CTX G LM.
  intros.
  apply (bd_u1_abdU K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 UE UV s6 sm6 ax6 cr6 M1 model1 LK1 Aw1 fx1 R1 fx2 R2 M3 model3 LK3 Aw3 CTX G LM); try assumption.
  intros fx7 R7 M7 model7 HH7 AM7 MRT7 HID7 MG7 FRZ7 E0 E16 E24 E32 E400 ER7 X10.
  pose proof (UP s6 sm6 ax6 cr6 M1 model1 LK1 Aw1 M3 model3 LK3 Aw3 M7 model7 CTX G LM) as PP.
  repeat (specialize (PP ltac:(assumption))).
  destruct PP as (lenv & LV & LM7 & FR7 & ECK7).
  pose proof (PNABDK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PNBO.set_more s6 1) sm6 ax6 cr6 CTX G LM) as (PF & _).
  unfold pfacts in PF. destruct PF as (_ & _ & _ & pf4 & _).
  apply (UT s6 sm6 ax6 M7 model7 LK3 Aw3 cr6 fx7 R7 lenv CTX G LM7 ER7).
  - apply (PNABDK.spill_agree M1 M7 sp F); [clear - pf4; lia| clear - pf4; lia| assumption| intros a Ha; apply FR7; clear - Ha; lia].
  - apply (L5C.u64_at_agree RSEGS M1 M7 (sp - 144)); [| clear - pf4; lia| clear - pf4; lia| eassumption]. intros j Hj. apply FR7. clear - Hj; lia.
  - exact X10.
  - apply ECK7. assumption.
  - exact LV.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
Qed.

Lemma bd_arm_u1 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 :
  PNAECF.ann_grow_spec L ar HI 0xad4b8 ->
  bd_u1post K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 ->
  bd_u1K K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2.
Proof.
  intros AGR PK1. unfold bd_u1K.
  intros M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 fx6 R6 CTX G LM ER X18 SPL U112 C144 C136 EC6 INV6 ESTK DEPTH UNR6 NFULL.
  pose proof CTX as (_ & _ & _ & _ & ENT & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof (PNABDK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM)
    as (PF & OWN6 & SV6 & U8v6 & WRop6 & U8op6 & SVr6).
  pose proof (vfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM) as (vf1 & vf2 & vf3 & vf4 & vf5 & vf6 & vf7 & vf8 & vf9 & vf10 & vf11).
  pose proof (mfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM) as (WRmo & CM0).
  pose proof (wfacts224_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM) as (W224 & S224o & S224F & S224fl & S224v).
  pose proof (vecfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM INV6)
    as (VB6 & VE6 & VC6 & RB41 & AL41 & Hn6 & Hk6 & Hlen6).
  set (MV6 := mrestrict (ahid Aw6 model6) M6) in *.
  unfold pfacts in PF. destruct PF as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32 & pf33 & pf34).
  pose proof (SV6 (sp - 128) F ltac:(clear; lia) ltac:(clear; lia) SPL) as SPLv.
  pose proof (SV6 (sp - 144) (fb + 464 + 400) ltac:(clear; lia) ltac:(clear; lia) C144) as C144v.
  pose proof (SV6 (sp - 136) (fb + 464 + 392) ltac:(clear; lia) ltac:(clear; lia) C136) as C136v.
  pose proof ER as (E2 & E3 & E4 & E8 & E9 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27).
  assert (Q34 : 0 <= fb + 432 < 2 ^ 64) by (clear - vf1; lia).
  assert (Q36 : 0 <= fb + 1024 < 2 ^ 64) by (clear - pf7; lia).
  destruct (u32_of_defined MV6 (F + 32) ltac:(clear - pf15; lia) ltac:(clear - pf15; lia) ltac:(apply (L5.defined_sub MV6 F 64); [exact pf17| clear; lia| clear; lia])) as (lenw & Hlenw & ULEN).
  assert (Q46 : 0 <= lenw < 2 ^ 64) by (clear - Hlenw; lia).
  assert (Q46' : 0 <= lenw <= 4294967295) by (clear - Hlenw; lia).
  assert (P2k : 1 <= 2 ^ PNM.b_sk s6) by (apply (Z.pow_le_mono_r 2 0 (PNM.b_sk s6)); clear - Hk6; lia).
  assert (P2k11 : 2 ^ PNM.b_sk s6 <= 2048) by (change 2048 with (2 ^ 11); apply (Z.pow_le_mono_r 2 (PNM.b_sk s6) 11); clear - Hk6; lia).
  assert (Q41 : 0 <= PNM.b_sb s6 < 2 ^ 64) by (clear - RB41; lia).
  assert (Q42 : 0 <= 40 * Z.of_nat (length (PNM.b_stk s6)) < 2 ^ 64) by (clear - Hn6; lia).
  assert (Q43 : 0 <= 40 * 2 ^ PNM.b_sk s6 < 2 ^ 64) by (clear - P2k P2k11; lia).
  assert (RB42 : 40 <= 40 * Z.of_nat (length (PNM.b_stk s6)) <= 41000) by (clear - Hn6; lia).
  assert (RB43 : 40 <= 40 * 2 ^ PNM.b_sk s6 <= 81920) by (clear - P2k P2k11; lia).
  assert (AL42 : PNABDP.aligned (40 * Z.of_nat (length (PNM.b_stk s6))) 8).
  { unfold PNABDP.aligned. replace (40 * Z.of_nat (length (PNM.b_stk s6))) with ((5 * Z.of_nat (length (PNM.b_stk s6))) * 8) by (clear; lia). apply Z_mod_mult. }
  assert (AL43 : PNABDP.aligned (40 * 2 ^ PNM.b_sk s6) 8).
  { unfold PNABDP.aligned. replace (40 * 2 ^ PNM.b_sk s6) with ((5 * 2 ^ PNM.b_sk s6) * 8) by (clear; lia). apply Z_mod_mult. }
  LeanFeed.pfeed P (PNABDP.abdV_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 41%nat => PNM.b_sb s6 | 42%nat => 40 * Z.of_nat (length (PNM.b_stk s6)) | 43%nat => 40 * 2 ^ PNM.b_sk s6 | 46%nat => lenw | 50%nat => F | 51%nat => fl | 60%nat => bv_unsigned (getr R (reg 1)) | 61%nat => bv_unsigned (getr R (reg 8)) | 62%nat => bv_unsigned (getr R (reg 9)) | 63%nat => bv_unsigned (getr R (reg 18)) | 64%nat => bv_unsigned (getr R (reg 19)) | 65%nat => bv_unsigned (getr R (reg 20)) | 66%nat => bv_unsigned (getr R (reg 21)) | 67%nat => bv_unsigned (getr R (reg 22)) | 68%nat => bv_unsigned (getr R (reg 23)) | 69%nat => bv_unsigned (getr R (reg 24)) | 70%nat => bv_unsigned (getr R (reg 25)) | 71%nat => bv_unsigned (getr R (reg 26)) | 72%nat => bv_unsigned (getr R (reg 27)) | _ => 0 end)) ltac:(first [assumption | unfold PNABDP.aligned; assumption]).
  destruct P as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & [(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LT0)|(MS7 & KS7 & Z1 & Z2 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z18 & Z19 & LT1 & C208 & C216 & C224 & C200 & C192 & C184 & C176 & C168 & U120 & MO1)]).
  1: { exfalso. rewrite !Z.mod_small in LT0 by (clear - Q41 Q42 Q43 RB41 RB42 RB43; lia). clear - LT0 NFULL. lia. }
  apply (bd_piece_mo K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 fx6 fx7 R6 R7 0xaeabc 0xad4b8 1 M7v
           (fun a => sp - 120 <= a < sp - 120 + 8 \/ fb + 464 + 8 <= a < fb + 464 + 8 + 1 \/ sp - 224 <= a < sp - 224 + 64) CTX G LM MS7 MG7).
  { intros a Ha N. apply FRZ7; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; left; exact X| intros X; apply N; right; right; exact X]. }
  { intros a [X|[X|X]]; [left| right| left]; clear - X; lia. }
  { replace (fb + 472) with (fb + 464 + 8) by (clear; lia). exact MO1. }
  { right; reflexivity. }
  intros M8 model8 LM8 HID8 VIS8 FR8 MG8 ECK8.
  pose proof LM8 as (BI8 & _). pose proof BI8 as (HH8 & _).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ LK6 cr6 Aw6 M8 model8 HH8) as (_ & VISs8 & _). cbv zeta in VISs8. rewrite HID8 in VISs8.
  pose proof CTX as (_ & _ & _ & _ & (_ & _ & _ & _ & _ & ASTK0 & _) & _). change (PMSPA.pm_scr 7) with 26624 in ASTK0. destruct ASTK0 as (_ & SLO & _).
  assert (SVf : forall a v, sp - 224 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M7v a v -> L5.u64_at RSEGS M8 a v).
  { intros a v Ha1 Ha2 X. apply (proj1 (L5A.u64_at_vis (ahid Aw6 model6) M8 a v (VISs8 a 8 ltac:(clear - Ha1 SLO; lia) ltac:(clear - Ha2 pf4; lia)) ltac:(clear - Ha1 pf4; lia) ltac:(clear - Ha2 pf4; lia))).
    rewrite VIS8. exact X. }
  assert (U120r : L5.u32_at RSEGS M8 (sp - 120) 2).
  { apply (proj1 (L5A.u32_at_vis (ahid Aw6 model6) M8 (sp - 120) 2 (VISs8 (sp - 120) 4 ltac:(clear - SLO; lia) ltac:(clear - pf4; lia)) ltac:(clear - pf4; lia) ltac:(clear - pf4; lia))).
    rewrite VIS8. exact U120. }
  assert (U112r : L5.u64_at RSEGS M8 (sp - 112) 4).
  { apply (L5C.u64_at_agree RSEGS M6 M8 (sp - 112)); [| clear - pf4; lia| clear - pf4; lia| exact U112].
    intros j Hj. apply FR8; [clear - Hj pf4; lia|]. intros [X|[X|X]]; [clear - X Hj; lia| clear - X Hj pf14; lia| clear - X Hj; lia]. }
  assert (SPL8 : spill M8 sp F).
  { unfold spill in *. apply (L5C.u64_at_agree RSEGS M6 M8 (sp - 128)); [| clear - pf4; lia| clear - pf4; lia| exact SPL].
    intros j Hj. apply FR8; [clear - Hj pf4; lia|]. intros [X|[X|X]]; [clear - X Hj; lia| clear - X Hj pf14; lia| clear - X Hj; lia]. }
  assert (C1448 : L5.u64_at RSEGS M8 (sp - 144) (fb + 464 + 400)).
  { apply (L5C.u64_at_agree RSEGS M6 M8 (sp - 144)); [| clear - pf4; lia| clear - pf4; lia| exact C144].
    intros j Hj. apply FR8; [clear - Hj pf4; lia|]. intros [X|[X|X]]; [clear - X Hj; lia| clear - X Hj pf14; lia| clear - X Hj; lia]. }
  assert (C1368 : L5.u64_at RSEGS M8 (sp - 136) (fb + 464 + 392)).
  { apply (L5C.u64_at_agree RSEGS M6 M8 (sp - 136)); [| clear - pf4; lia| clear - pf4; lia| exact C136].
    intros j Hj. apply FR8; [clear - Hj pf4; lia|]. intros [X|[X|X]]; [clear - X Hj; lia| clear - X Hj pf14; lia| clear - X Hj; lia]. }
  apply (bd_call_grow K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M8 model8 LK6 Aw6 (PNBO.set_more s6 1) sm6 ax6 cr6 fx7 R7 0xb25f4 AGR CTX G LM8).
  { exact Z1. } { unfold L5.ra_ok; clear; lia. } { exact Z2. }
  { rewrite (KS7 3%nat) by inl. rewrite E3. exact Rgp. }
  { rewrite (KS7 4%nat) by inl. rewrite E4. exact Rtp. }
  { exact Z10. } { exact Z11. } { rewrite Z12. apply bv_eq. reflexivity. } { exact Z13. }
  { cbn [PNBO.set_more PNM.b_stk PNM.b_sk]. exact NFULL. }
  intros fx12 R12 M12 model12 LK12 Aw12 RP12 Y0 Y8 Y16 YEL YDEF YACC YANN YACCV YBASE YHP YMRT YINCL YINCA YAM YHH.
  apply (PK1 s6 sm6 ax6 cr6 M8 model8 LK6 Aw6 fx7 R7 fx12 R12 M12 model12 LK12 Aw12 CTX G LM8 Z1 Z2 Z8 Z9 Z10 Z18 Z19).
  - rewrite (KS7 3%nat) by inl. exact E3.
  - rewrite (KS7 4%nat) by inl. exact E4.
  - rewrite (KS7 20%nat) by inl. exact E20.
  - rewrite (KS7 21%nat) by inl. exact E21.
  - rewrite (KS7 22%nat) by inl. exact E22.
  - rewrite (KS7 23%nat) by inl. exact E23.
  - rewrite (KS7 24%nat) by inl. exact E24.
  - rewrite (KS7 25%nat) by inl. exact E25.
  - rewrite (KS7 26%nat) by inl. exact E26.
  - rewrite (KS7 27%nat) by inl. exact E27.
  - apply SVf; [clear; lia| clear; lia| exact C208].
  - apply SVf; [clear; lia| clear; lia| exact C216].
  - apply SVf; [clear; lia| clear; lia| exact C224].
  - apply SVf; [clear; lia| clear; lia| exact C200].
  - apply SVf; [clear; lia| clear; lia| exact C192].
  - apply SVf; [clear; lia| clear; lia| exact C184].
  - apply SVf; [clear; lia| clear; lia| exact C176].
  - apply SVf; [clear; lia| clear; lia| exact C168].
  - exact U120r.
  - exact U112r.
  - exact SPL8.
  - exact C1448.
  - exact C1368.
  - exact (ECK8 _ _ EC6).
  - exact INV6.
  - exact ESTK.
  - exact DEPTH.
  - exact NFULL.
  - exact UNR6.
  - exact RP12.
  - exact Y0.
  - exact Y8.
  - exact Y16.
  - exact YEL.
  - exact YDEF.
  - exact YACC.
  - exact YANN.
  - exact YACCV.
  - exact YBASE.
  - exact YHP.
  - exact YMRT.
  - exact YINCL.
  - exact YINCA.
  - exact YAM.
  - exact YHH.
Qed.


(* [comment removed for export] *)
Lemma bd_after_read K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 (fx6 : FPState) R6 d :
  PNRAa.make_ec_spec L ar HI -> PNSAXR.push_cont_slow_spec RSEGS PMA.AD L ar HI 0xb2758 ->
  bd_u1K K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 ->
  bd_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  bd_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 ->
  bregs R R6 sp fb F -> getr R6 (reg 10) = Z_to_bv 64 d -> 0 <= d <= 4 ->
  getr R6 (reg 18) = Z_to_bv 64 4 ->
  spill M6 sp F -> L5.u64_at RSEGS M6 (sp - 144) (fb + 464 + 400) -> L5.u64_at RSEGS M6 (sp - 136) (fb + 464 + 392) ->
  PMSPA.ec_at RSEGS M6 (fb + 1024) e cat ->
  PNRA.binv s6 -> PNM.b_stk s6 = PNM.b_stk s -> Z.of_nat (length (PNM.b_stk s6)) <= 1024 ->
  PM.unread (PNM.b_src s6) sm6 = PM.unread (PNM.b_src s) sm - d ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 0xaeab4 M6 model6) K.
Proof.
  intros MKE PSH U1K CTX G LM ER X10 Hd X18 SPL C144 C136 EC6 INV6 ESTK DEPTH UNR6.
  pose proof (PNABDK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM)
    as (PF & OWN6 & SV6 & U8v6 & WRop6 & U8op6 & SVr6).
  pose proof (vfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM) as (vf1 & _).
  set (MV6 := mrestrict (ahid Aw6 model6) M6) in *.
  unfold pfacts in PF. destruct PF as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32 & pf33 & pf34).
  pose proof ER as (E2 & E3 & E4 & E8 & E9 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27).
  assert (Q34 : 0 <= fb + 432 < 2 ^ 64) by (clear - vf1; lia).
  assert (Q36 : 0 <= fb + 1024 < 2 ^ 64) by (clear - pf7; lia).
  assert (Q45 : 0 <= d < 2 ^ 64) by (clear - Hd; lia).
  LeanFeed.pfeed P (PNABDP.abdR_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 45%nat => d | 50%nat => F | 51%nat => fl | 60%nat => bv_unsigned (getr R (reg 1)) | 61%nat => bv_unsigned (getr R (reg 8)) | 62%nat => bv_unsigned (getr R (reg 9)) | 63%nat => bv_unsigned (getr R (reg 18)) | 64%nat => bv_unsigned (getr R (reg 19)) | 65%nat => bv_unsigned (getr R (reg 20)) | 66%nat => bv_unsigned (getr R (reg 21)) | 67%nat => bv_unsigned (getr R (reg 22)) | 68%nat => bv_unsigned (getr R (reg 23)) | 69%nat => bv_unsigned (getr R (reg 24)) | 70%nat => bv_unsigned (getr R (reg 25)) | 71%nat => bv_unsigned (getr R (reg 26)) | 72%nat => bv_unsigned (getr R (reg 27)) | _ => 0 end)) ltac:(first [assumption | unfold PNABDP.aligned; assumption]).
  destruct P as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & [(MS7 & KS7 & Y1 & Y10 & Y11 & PC & U112)|(MS7 & KS7 & PC & U112)]).
  - (* [comment removed for export] *)
    apply (PNABDK.bd_piece_fr L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 fx6 fx7 R6 R7 0xaeab4 0xae848 M7v
             (fun a => sp - 112 <= a < sp - 112 + 8) CTX G LM MS7 MG7 FRZ7).
    { intros a X. clear - X; lia. }
    intros M8 model8 LM8 HID8 VIS8 FR8 MG8 ECK8.
    apply (bd_arm_err1 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M8 model8 LK6 Aw6 s6 sm6 ax6 cr6 fx7 R7 e cat MKE CTX G LM8).
    + apply (bregs_keep R R6 R7 sp fb F ER). intros k0 Hk0. apply KS7. revert k0 Hk0; apply (L5K.incl_b [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat); vm_compute; reflexivity.
    + rewrite (KS7 18%nat) by inl. exact X18.
    + unfold spill in *. apply (L5C.u64_at_agree RSEGS M6 M8 (sp - 128)); [| clear - pf4; lia| clear - pf4; lia| exact SPL].
      intros j Hj. apply FR8; [clear - Hj pf4; lia|]. intros X. clear - X Hj; lia.
    + exact (ECK8 _ _ EC6).
    + exact Y1.
    + exact Y10.
    + exact Y11.
    + exact INV6.
    + rewrite ESTK. apply Nat.le_refl.
  - (* [comment removed for export] *)
    assert (D4 : d = 4).
    { destruct (Z.eq_dec d 4) as [X|X]; [exact X| exfalso].
      replace ((d - 4) mod 2 ^ 64) with (d - 4 + 2 ^ 64) in PC; [clear - PC Hd X; lia|].
      apply (Z.mod_unique_pos (d - 4) (2 ^ 64) (-1) (d - 4 + 2 ^ 64)); clear - Hd X; lia. }
    subst d.
    apply (PNABDK.bd_piece_fr L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 fx6 fx7 R6 R7 0xaeab4 0xaeabc M7v
             (fun a => sp - 112 <= a < sp - 112 + 8) CTX G LM MS7 MG7 FRZ7).
    { intros a X. clear - X; lia. }
    intros M8 model8 LM8 HID8 VIS8 FR8 MG8 ECK8.
    pose proof (PNABDK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M8 model8 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM8) as (_ & _ & _ & _ & _ & _ & SVr8).
    assert (ER7 : bregs R R7 sp fb F).
    { apply (bregs_keep R R6 R7 sp fb F ER). intros k0 Hk0. apply KS7. revert k0 Hk0; apply (L5K.incl_b [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat); vm_compute; reflexivity. }
    assert (X187 : getr R7 (reg 18) = Z_to_bv 64 4) by (rewrite (KS7 18%nat) by inl; exact X18).
    assert (SPL8 : spill M8 sp F).
    { unfold spill in *. apply (L5C.u64_at_agree RSEGS M6 M8 (sp - 128)); [| clear - pf4; lia| clear - pf4; lia| exact SPL].
      intros j Hj. apply FR8; [clear - Hj pf4; lia|]. intros X. clear - X Hj; lia. }
    assert (U1128 : L5.u64_at RSEGS M8 (sp - 112) 4).
    { apply (SVr8 (sp - 112) 4 ltac:(clear; lia) ltac:(clear; lia)). rewrite HID8. rewrite VIS8. exact U112. }
    assert (C1448 : L5.u64_at RSEGS M8 (sp - 144) (fb + 464 + 400)).
    { apply (L5C.u64_at_agree RSEGS M6 M8 (sp - 144)); [| clear - pf4; lia| clear - pf4; lia| exact C144].
      intros j Hj. apply FR8; [clear - Hj pf4; lia|]. intros X. clear - X Hj; lia. }
    assert (C1368 : L5.u64_at RSEGS M8 (sp - 136) (fb + 464 + 392)).
    { apply (L5C.u64_at_agree RSEGS M6 M8 (sp - 136)); [| clear - pf4; lia| clear - pf4; lia| exact C136].
      intros j Hj. apply FR8; [clear - Hj pf4; lia|]. intros X. clear - X Hj; lia. }
    assert (UNR6' : PM.unread (PNM.b_src s6) sm6 + 4 <= PM.unread (PNM.b_src s) sm) by (rewrite UNR6; clear; lia).
    destruct (Z_le_gt_dec (2 ^ PNM.b_sk s6) (Z.of_nat (length (PNM.b_stk s6)))) as [FULL|NFULL].
    + exact (bd_arm_push K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M8 model8 LK6 Aw6 s6 sm6 ax6 cr6 fx7 R7 PSH CTX G LM8
               ER7 X187 SPL8 U1128 C1448 C1368 (ECK8 _ _ EC6) INV6 ESTK DEPTH UNR6' FULL).
    + exact (U1K M8 model8 LK6 Aw6 s6 sm6 ax6 cr6 fx7 R7 CTX G LM8 ER7 X187 SPL8 U1128 C1448 C1368 (ECK8 _ _ EC6) INV6 ESTK DEPTH UNR6' ltac:(clear - NFULL; lia)).
Qed.


(* [comment removed for export] *)
Definition sz32a (m : Z) : Z :=
  bv_unsigned (sext 64 (mul_div Instr.M_MUL (low32 (alu64 Instr.ALU_SRA (Z_to_bv 64 m) (Z_to_bv 64 3))) (low32 (Z_to_bv 64 14757395258967641293)))).
Lemma sz32a_tab : forallb (fun n => Z.eqb (sz32a (40 * Z.of_nat n)) (Z.of_nat n)) (seq 0 1026) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma sz32a_ok n : 0 <= n <= 1025 -> sz32a (40 * n) = n.
Proof.
  intros Hn. pose proof sz32a_tab as T. rewrite forallb_forall in T.
  specialize (T (Z.to_nat n) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in T by lia. apply Z.eqb_eq in T. exact T.
Qed.

(* [comment removed for export] *)
Lemma pfacts_of0 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 :
  bd_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  bd_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  PMAUK.binv L ar HI M model LBX FF LK Aw sp 26624 (sp - 160) (own sp R) F 0 (PNRA.W_brun PMA.AD PMA.AN fb) (PNM.bparser_own s1) M1 model1 LK1 cr1 Aw1 ->
  PNRA.brun_pre RSEGS PMA.AD PMA.AN PMA.AAD M1 fb s1 str sm1 ax1 ->
  pfacts (mrestrict (ahid Aw1 model1) M1) sp (fb + 464) F fl
  /\ own sp R (mrestrict (ahid Aw1 model1) M1)
  /\ (forall a v, sp - 160 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1 a v -> L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) a v)
  /\ (forall v, L5.u8_at RSEGS M1 (F + 32) v -> L5.u8_at RSEGS (mrestrict (ahid Aw1 model1) M1) (F + 32) v)
  /\ L5.writable RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 464) 424
  /\ (forall v, L5.u8_at RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 464 + 8) v <-> L5.u8_at RSEGS M1 (fb + 464 + 8) v)
  /\ (forall a v, sp - 160 <= a -> a + 8 <= sp -> L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) a v -> L5.u64_at RSEGS M1 a v).
Proof.
  intros CTX G BI RP1.
  destruct CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 7) with 26624 in *.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, F1, F2.
  pose proof G as G'. unfold bd_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 0, sp - 160 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  destruct RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in *. change (PNRA.o_is PMA.AD fb) with (fb + 96) in *. change (PNRA.o_v PMA.AD fb) with (fb + 432) in *.
  change (PNM.PSIZE + 8) with 424 in OACC1.
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1 OACC1) as ((O1 & O8 & ONSH) & Zop & OWR & OCE & OVIS & AOP).
  pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 HH1 BASE1) as (VM0 & VM1 & VM2).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 sp 26624 160 HH1 ASTK1 ltac:(lia)) as (SL160 & SH160 & SWR).
  destruct (PMAUK.vis_facts L ar C HI LYa HIok M model LBX FF LK Aw sp 26624 (sp - 160) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PNM.bparser_own s) G
              _ (PNM.bparser_own s1) M1 model1 LK1 cr1 Aw1 BI) as ((WS1 & _ & _ & _ & _) & OWNv & (FD1 & FW1 & FSW1 & FLC1 & FLW1) & (FLCc1 & FLV1 & VF1 & VS1 & VSH1)).
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *. replace (F + 64 - 8) with (F + 56) in FLC1 by (clear; lia).
  set (op := fb + 464) in *.
  set (MV := mrestrict (ahid Aw1 model1) M1) in *.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ LK1 cr1 Aw1 M1 model1 HH1) as (_ & VISs & _).
  (* [comment removed for export] *)
  assert (CLo : forall a, fb + 32 <= a < fb + 2040 -> aclient L ar LBX FF sp 26624 a).
  { intros a Ha. unfold aclient, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
    change (ff_bytes 5) with 2048. split; [clear - Ha; lia| intros Y; clear - Ha Y; lia]. }
  assert (CLs : forall a, fb / 8 + SB <= a < fb / 8 + SB + 256 -> aclient L ar LBX FF sp 26624 a).
  { intros a Ha. unfold aclient, aclient_g. do 5 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
    change (ff_bytes 5) with 2048. unfold in_shadow_of, S. unfold SB in *.
    assert (D1 : (fb + 2048 - 1) / 8 = fb / 8 + 255).
    { pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
      replace (2048 * (fb / 2048) + 2048 - 1) with (7 + (256 * (fb / 2048) + 255) * 8) by (clear; lia). rewrite Z.div_add by lia.
      replace (2048 * (fb / 2048)) with ((256 * (fb / 2048)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
    rewrite D1. clear - Ha. lia. }
  assert (SHop : op / 8 + SB = fb / 8 + SB + 58).
  { unfold op. pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
    replace (2048 * (fb / 2048) + 464) with ((256 * (fb / 2048) + 58) * 8) by (clear; lia). rewrite Z.div_mul by lia.
    replace (2048 * (fb / 2048)) with ((256 * (fb / 2048)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
  assert (SF1 : S (F + 64 - 1) = F / 8 + SB + 7).
  { unfold S. destruct GF8 as (X1 & X2 & X3). rewrite X2. clear; lia. }
  assert (NF : forall a, fb + 32 <= a < fb + 2040 -> ~ (F <= a < F + 64)).
  { intros a Ha X. apply (GNCF a); [left; exact X| exact (CLo a Ha)]. }
  assert (NFS : forall a, fb / 8 + SB <= a < fb / 8 + SB + 256 -> ~ (F / 8 + SB <= a < F / 8 + SB + 8)).
  { intros a Ha X. apply (GNCF a); [right; unfold S at 1; rewrite SF1; clear - X; lia| exact (CLs a Ha)]. }
  assert (NFL : forall a, fb + 32 <= a < fb + 2040 -> a <> fl).
  { intros a Ha X. subst a. apply GFLNC. apply L5SAR.aclient_cons. apply (L5SAR.aclient_00 L ar LBX FF sp 26624 fl). exact (CLo fl Ha). }
  assert (ApF : op + 416 <= F \/ F + 64 <= op) by (apply iv_apart; [clear; lia| clear; lia| intros a Ha; apply NF; clear - Ha; unfold op in Ha; lia]).
  assert (ApFL : op + 416 <= fl \/ fl + 1 <= op).
  { destruct (Z_lt_le_dec fl op) as [X|X]; [right; clear - X; lia|]. destruct (Z_lt_le_dec fl (op + 416)) as [Y|Y]; [exfalso; apply (NFL fl); [clear - X Y; unfold op in X, Y; lia| reflexivity]| left; exact Y]. }
  assert (ApS : ((op / 8) + 2147450880) + 52 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 8 <= ((op / 8) + 2147450880)).
  { change 2147450880 with SB. apply iv_apart; [clear; lia| clear; lia| intros a Ha; apply NFS; clear - Ha SHop; lia]. }
  (* [comment removed for export] *)
  assert (SVV : forall a v0, sp - 160 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1 a v0 -> L5.u64_at RSEGS MV a v0).
  { intros a v0 Ha1 Ha2 X. apply (proj2 (L5A.u64_at_vis _ M1 a v0 (VISs a 8 ltac:(clear - Ha1 SL160 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SL160 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))). exact X. }
  assert (CV : forall v, L5.u8_at RSEGS M1 (F + 32) v -> L5.u8_at RSEGS MV (F + 32) v).
  { intros v X. apply (proj2 (L5A.u8_at_vis _ M1 (F + 32) v (L5A.avis_sub _ F 64 (F + 32) 1 VF1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - GFR; lia) ltac:(clear - GFR; lia))). exact X. }
  assert (Zz0 : L5KA.zeros_at MV (op / 8 + 2147450880) 2). { intros i Hi. apply Zop. clear - Hi; lia. }
  assert (Zz1 : L5KA.zeros_at MV ((op + 10) / 8 + 2147450880) 1).
  { intros i Hi. replace ((op + 10) / 8 + 2147450880 + i) with (op / 8 + SB + (1 + i)) by (unfold SB; rewrite (div8_add op 10 O8 ltac:(clear; lia)); change (10 / 8) with 1; clear; lia).
    apply Zop. clear - Hi; lia. }
  assert (Zz2 : L5KA.zeros_at MV ((op + 312) / 8 + 2147450880) 1).
  { intros i Hi. replace ((op + 312) / 8 + 2147450880 + i) with (op / 8 + SB + (39 + i)) by (unfold SB; rewrite (div8_add op 312 O8 ltac:(clear; lia)); change (312 / 8) with 39; clear; lia).
    apply Zop. clear - Hi; lia. }
  assert (Zz3 : L5KA.zeros_at MV ((op + 392) / 8 + 2147450880) 3).
  { intros i Hi. replace ((op + 392) / 8 + 2147450880 + i) with (op / 8 + SB + (49 + i)) by (unfold SB; rewrite (div8_add op 392 O8 ltac:(clear; lia)); change (392 / 8) with 49; clear; lia).
    apply Zop. clear - Hi; lia. }
  assert (Z3 : L5KA.zeros_at MV ((op + 392) / 8 + 2147450880) 3).
  { intros i Hi. replace ((op + 392) / 8 + 2147450880 + i) with (op / 8 + SB + (49 + i)).
    - apply Zop. clear - Hi; lia.
    - unfold SB. replace (op + 392) with (op + 49 * 8) by (clear; lia). rewrite Z.div_add by (clear; lia). clear; lia. }
  assert (SVR : forall a v0, sp - 160 <= a -> a + 8 <= sp -> L5.u64_at RSEGS MV a v0 -> L5.u64_at RSEGS M1 a v0).
  { intros a v0 Ha1 Ha2 X. apply (proj1 (L5A.u64_at_vis _ M1 a v0 (VISs a 8 ltac:(clear - Ha1 SL160 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SL160 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))). exact X. }
  split; [| split; [exact OWNv| split; [exact SVV| split; [exact CV| split; [exact OWR| split; [intros v; apply (L5A.u8_at_vis _ M1 (op + 8) v (OVIS (op + 8) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1; lia))| exact SVR]]]]]].
  unfold pfacts. unfold SB in FSW1.
  split; [exact VM0|]. split; [exact VM1|]. split; [exact VM2|].
  split; [clear - SL160 SHI SPT; lia|]. split; [exact SP32|]. split; [exact SWR|].
  split; [clear - O1; lia|]. split; [exact O8|]. split; [clear - ONSH; lia|]. split; [exact Zz0|]. split; [exact Zz1|]. split; [exact Zz2|]. split; [exact Zz3|]. split; [clear - OCE SL160; lia|].
  split; [clear - GFR; lia|]. split; [exact GF32|]. split; [exact FD1|]. split; [exact FW1|]. split; [exact GFBIG|]. split; [exact FSW1|].
  split; [exact FLC1|]. split; [clear - GFLR; lia|]. split; [exact FLW1|]. split; [exact GFLBIG|]. split; [exact GFLA|].
  split; [clear - GFCEIL GSLO; lia|]. split; [clear - GFLR GSLO; lia|].
  split; [exact ApF|]. split; [exact ApFL|]. split; [exact ApS|].
  clear - SL160 SHI SPT O1 GFR GFLR. lia.
Qed.

(* [comment removed for export] *)
Theorem begin_document_ok :
  PNRAa.src_read_spec L ar HI -> PNRAa.make_ec_spec L ar HI -> PNSAXR.push_cont_slow_spec RSEGS PMA.AD L ar HI 0xb2758 ->
  PNAECF.ann_grow_spec L ar HI 0xad4b8 ->
  (forall K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2, bd_u1_elem_T K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2) ->
  (forall K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2, bd_u1_m3vis_T K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2) ->
  (forall K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2, bd_u1_push_T K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2) ->
  (forall K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2, bd_u1_tail K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2) ->
  PNRAa.begin_document_spec L ar HI.
Proof.
  intros SRD MKE PSH AGR UE UMV UP U1. unfold PNRAa.begin_document_spec, PNRA.begin_document_spec, PNRA.brun_spec.
  set (w := 0). assert (Hw : w = 0 \/ w = 1) by (left; reflexivity).
  intros fx R M model K LBX FF LK Aw cr sp r fb cat e s str sm ax HH AM K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC HE UNR CRED KONT.
  assert (CTX : bd_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w).
  { exact (conj Hw (conj HH (conj AM (conj K0 (conj ENT (conj FRM (conj FRS (conj FOK (conj SP32 (conj ARGS (conj RPRE (conj INCS (conj INV (conj EC (conj HE (conj UNR (conj CRED KONT))))))))))))))))). }
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 7) with 26624 in *. change (26624 / 8) with 3328 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  destruct ARGS as (A10 & A11 & A12).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12.
  pose proof RPRE as (PA & IA & VIS & VREF & OACC & BASE & ERR & GROW).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & (CEB1 & _) & (_ & STT & _) & STOP & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, F1, F2.
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in *. change (PNRA.o_ec PMA.AD fb) with (fb + 1024) in *.
  change (PNRA.o_v PMA.AD fb) with (fb + 432) in *. change (PNRA.o_is PMA.AD fb) with (fb + 96) in *.
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ FF LK cr Aw M model fb _ s HH FOK PA OACC) as ((O1 & O8 & ONSH) & Zop & OWR & OCE & OVIS & AOP).
  pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF LK cr Aw M model HH BASE) as (VM0 & VM1 & VM2).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 26624 160 HH ASTK ltac:(lia)) as (SL160 & SH160 & SWR).
  set (op := fb + 464) in *. set (ov := fb + 432) in *. set (oec := fb + 1024) in *. set (ois := fb + 96) in *.
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (_ & VISs & _).
  assert (Q0 : 0 <= sp < 2 ^ 64 /\ 0 <= op < 2 ^ 64 /\ 0 <= oec < 2 ^ 64 /\ 0 <= ov < 2 ^ 64)
    by (clear - SL160 SHI SPT O1 F1 F2 FSAPP FSCEIL SLO; unfold oec, op, ov in *; lia).
  destruct Q0 as (Q0a & Q0b & Q0d & Q0h).
  assert (Q1 : 140735332487296 <= sp <= 140737488355328) by (clear - SL160 SHI SPT; lia).
  LeanFeed.pfeed P (PNABDP.abdA_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => op | 34%nat => ov | 36%nat => oec | _ => 0 end)) ltac:(first [assumption | unfold PNABDP.aligned; assumption]).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T12 & T19 & T20 & T23 & T27
                 & C104 & C96 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8 & C128).
  unfold PMSP.cfg. change (PNL.pn_begin_document PMA.AN) with 0xae924.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xae924 R1 0x5dc2c M1v (fun a => sp - 160 <= a < sp - 160 + 160) K HH AM MS1 MG1).
  { intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
  { intros a Ha Wa. split; [|intros X; clear - X Wa SL160 FSAPP FSCEIL; lia]. unfold aclientw, aclient_g. right; left. split; [clear - Wa SL160 SHI SPT; lia| intros X; clear - X; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
  set (LB := PNM.bparser_own s ++ LBX) in *.
  assert (INCX : incl LBX LB) by (unfold LB; apply incl_appr; apply incl_refl).
  assert (NCS0 : forall a, sp - 160 <= a < sp -> ~ aclient L ar LB FF sp 26624 a).
  { intros a Xa Hc. destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 26624 a HH SPT Hc) as [Y|Y].
    - clear - Xa Y; lia.
    - clear - Xa Y SL160; lia. }
  assert (EK01f : L5SAR.ek L ar LB FF sp 26624 [] M M1).
  { apply (L5SAR.ek_piece L ar LB FF sp 26624 [] M M1 (fun a => sp - 160 <= a < sp - 160 + 160) FR1). intros a Ha Hc _ X. apply (NCS0 a); [clear - X; lia| exact Hc]. }
  assert (DK01f : L5SAR.dk L ar LB FF sp 26624 M M1) by (apply L5SAR.dk_grows; exact MGM1).
  pose proof (PMKA.ek_sublb L ar LB LBX FF sp 26624 [] M M1 INCX EK01f) as EK01.
  pose proof (PMKA.dk_sublb L ar LB LBX FF sp 26624 M M1 INCX DK01f) as DK01.
  assert (SV1 : forall a v, sp - 160 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
  { intros a v Ha1 Ha2 X. apply (proj1 (L5A.u64_at_vis H M1 a v (VISs a 8 ltac:(clear - Ha1 SL160 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SL160 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))).
    rewrite VIS1. exact X. }
  assert (OWN1 : own sp R M1).
  { unfold own. repeat split; (apply SV1; [clear; lia| clear; lia| assumption]). }
  clear C104 C96 C88 C80 C72 C64 C56 C48 C40 C32 C24 C16 C8 SV1.
  (* [comment removed for export] *)
  assert (FRk0 : ff_room 0 FF LK) by (apply (PMAUAR.ff_room_ofB PNRA.FCB 7 FF LK 0 FRM); [clear; lia| left; reflexivity]).
  change 0x5dc2c with (PMA.SM_PC 0).
  apply (PMAUAR.uar_sm L ar C HI LY HIok 0 LBX (PNM.bparser_own s) FF LK cr Aw sp 26624 (sp - 160) (sp - 104) sp (ocell sp) (own sp R)
           fx1 R1 M M1 model model1 K 0xae99c ltac:(left; reflexivity) HH HH1 AM1 K0 ASTK MGM1 EK01 DK01).
  { rewrite L5K.rl2. exact T2. }
  { rewrite L5K.rl4. rewrite (KS1 4%nat) by inl. rewrite <- L5K.rl4. exact Rtp. }
  { rewrite L5K.rl1. exact T1. }
  { reflexivity. }
  { clear; lia. }
  { replace (sp - 160) with (sp + (-10) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { clear; lia. } { clear; lia. } { clear; lia. } { clear; lia. }
  { intros a Ha. exact Ha. }
  { intros Ma Mb OW AG. apply (own_agree sp R Ma Mb ltac:(clear - SL160 SPT; lia) ltac:(clear - SHI SPT; lia) OW AG). }
  { exact FRk0. }
  { intros f Hf. specialize (FRS f Hf). clear - FRS; lia. }
  intros R2 M2 model2 F fl LK2 G G10 RP2 AM2 MRT2 ASTK2 EK02 DK02 EK12f DK12f AGF FW FSHW FSHZ FLC FLW FDEF VF VSH VFL APART.
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *. change (64 - 8) with 56 in *.
  pose proof G as G'. destruct G' as [_ _ _ _ _ _ _ GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 0) with 64 in *.
  pose proof (L5SAR.ek_trans L ar LB FF sp 26624 [] M M1 M2 EK01f EK12f) as EK02f.
  pose proof (L5SAR.dk_trans L ar LB FF sp 26624 M M1 M2 DK01f DK12f) as DK02f.
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
  assert (HH2 : ri_inv HI LB ((F, 0, sp - 160 + 32) :: FF) LK2 cr Aw M2 (vml_of model2)) by exact GHH2.
  set (FF' := (F, 0, sp - 160 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  set (H2 := ahid Aw model2) in *. set (MV2 := mrestrict H2 M2) in *.
  assert (WAPPR : PMKA.wapp (PNRA.W_brun PMA.AD PMA.AN fb)).
  { unfold PNRA.W_brun, PGS.W_srcfG, PNST.berr_W, PNST.cat_W, PNST.dec_W, PNRA.o_src, PNRA.o_is, PNRA.o_bb, PNRA.o_nb, PNRA.o_tb, PNRA.o_stk, PNRA.o_ec, PNRA.o_p, PMSP.o_p, PMSP.o_is, PMSP.o_ec.
    cbn [app pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PMA.AD ADDR_A PMA.AN NADDR_A PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj].
    unfold PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK.
    pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
    repeat apply PMKA.wapp_cons; [..| apply PMKA.wapp_nil]; cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct FA1 as [FA1|FA1]; clear - FA0 FA1 FA2 F1 F2; lia. }
  set (WR := PNRA.W_brun PMA.AD PMA.AN fb) in *.
  (* [comment removed for export] *)
  assert (OWN2 : own sp R M2).
  { apply (own_agree sp R M1 M2 ltac:(clear - SL160 SPT; lia) ltac:(clear - SHI SPT; lia) OWN1). intros a Ha. unfold ocell in Ha. apply AGF. clear - Ha; lia. }
  assert (BI2 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 26624 (sp - 160) (own sp R) F 0 WR (PNM.bparser_own s) M2 model2 LK2 cr Aw).
  { unfold PMAUK.binv. split; [exact HH2|]. split; [exact AM2|].
    split; [eapply L5LZ.model_rt_trans; [exact MRT1| exact MRT2]|].
    split; [apply incl_refl|]. split; [exact GLKI2|]. split; [exact ASTK2|].
    split; [apply (L5SAR.ek_W L ar LBX FF sp 26624 WR [] M M2 (PMKA.ek_sublb L ar LB LBX FF sp 26624 [] M M2 INCX EK02f)); intros a _ r0 []|].
    split; [exact DK02|].
    split; [exact OWN2|].
    change (ff_bytes 0 / 8) with 8.
    apply (proj1 (L5A.defined_vis H2 M2 (F / 8 + SB) 8 VSH)). intros i Hi. pose proof (FSHZ i Hi) as Z0. unfold MV2 in Z0. rewrite Z0. discriminate. }
  assert (AOPp : PMSPA.aobjA FF op PNM.PSIZE) by (apply (PNAPAR.aobj_fbB FF fb op PNM.PSIZE FOK); unfold op, PNM.PSIZE; clear; lia).
  assert (KEEP : forall Mx, L5SAR.ek L ar LB FF sp 26624 [] M Mx ->
            PNRA.brun_pre RSEGS PMA.AD PMA.AN PMA.AAD Mx fb s str sm ax /\ PMSPA.ec_at RSEGS Mx oec e cat).
  { intros Mx EKx.
    assert (PAx : PNM.bparser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA (pa_vp_parser PMA.AD) Mx op ois s).
    { apply (PNAPAR.bparser_keepA L ar C HI HIok LB FF LK cr Aw (vml_of model) [] sp 26624 M Mx op ois s HH EKx PMKA.wapp_nil AOPp);
        [unfold LB; apply incl_appl; apply incl_refl| intros i _ r0 []| intros B m _ i _ r0 []| exact PA]. }
    assert (IAx : PM.iss_at RSEGS PMA.AD PMSPA.accA Mx ois str sm).
    { apply (PMKA.iss_keepA RSEGS PMA.AD L ar LB FF sp 26624 [] M Mx EKx PMKA.wapp_nil FRB BRB ois str sm); [| | intros i _ r0 []| intros c n p _ i _ r0 []| exact IA].
      - apply (PNAPAR.aobj_fbB FF fb ois 272 FOK); unfold ois; clear; lia.
      - unfold LB. apply incl_appr. exact INCS. }
    assert (BASEx : PMSTA.base_okA RSEGS PMA.AD Mx) by (apply (PMASK.base_keep L ar C LY LB FF sp 26624 [] M Mx EKx); [intros a _ r0 []| exact BASE]).
    assert (ERRx : PNSTA.berr_okA RSEGS PMA.AD PMA.AAD PMA.AN Mx ax).
    { apply (PNSTA.berr_okA_frame RSEGS PMA.AD PMA.AAD PMA.AN PMA.addrs_wf_B M Mx); [| exact ERR].
      intros a Ha D. apply EKx. split; [exact Ha|]. split; [| intros r0 []]. unfold aclient, aclient_g. right; right; left.
      pose proof (depA_img a D). rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia| exact (PMA.ly_static L C LY a D)]. }
    split.
    - refine (PNBKA.pre_after_call L ar LB FF sp 26624 [] M Mx fb s s str sm sm ax ax FRB EKx PMKA.wapp_nil FOK _ RPRE PAx IAx GROW BASEx ERRx). intros i _ rr [].
    - apply (PMKA.ec_keepA RSEGS L ar LB FF sp 26624 [] M Mx EKx PMKA.wapp_nil FRB oec e cat); [| intros i _ r0 []| exact EC].
      apply (PNAPAR.aobj_fbB FF fb oec 16 FOK); unfold oec; clear; lia. }
  destruct (KEEP M2 EK02f) as (PRE2 & _).
  pose proof (pfacts_of0 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M2 model2 LK2 Aw s sm ax cr CTX G BI2 PRE2)
    as (PF & OWNv2 & SV2 & _ & WRop2 & _ & SVr2).
  fold H2 MV2 in PF, OWNv2, SV2, WRop2, SVr2. fold op in PF, WRop2.
  unfold pfacts in PF. destruct PF as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32 & pf33 & pf34).
  (* [comment removed for export] *)
  assert (R2c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (reg j) = getr R1 (reg j)).
  { intros j Hj. apply (L5SAR.cs_of_preserved R1 R2 j RP2 Hj). }
  assert (B2R : getr R2 (reg 2) = Z_to_bv 64 (sp - 160)) by (rewrite (R2c 2%nat) by inl; exact T2).
  assert (B8R : getr R2 (reg 8) = Z_to_bv 64 sp) by (rewrite (R2c 8%nat) by inl; exact T8).
  assert (B9R : getr R2 (reg 9) = Z_to_bv 64 (sp - 160)) by (rewrite (R2c 9%nat) by inl; exact T9).
  assert (B19R : getr R2 (reg 19) = Z_to_bv 64 op) by (rewrite (R2c 19%nat) by inl; exact T19).
  assert (B20R : getr R2 (reg 20) = Z_to_bv 64 oec) by (rewrite (R2c 20%nat) by inl; exact T20).
  assert (B23R : getr R2 (reg 23) = Z_to_bv 64 ov) by (rewrite (R2c 23%nat) by inl; exact T23).
  assert (B27R : getr R2 (reg 27) = Z_to_bv 64 2147450880) by (rewrite (R2c 27%nat) by inl; exact T27).
  assert (B10R : getr R2 (reg 10) = Z_to_bv 64 F) by (rewrite <- L5K.rl10; exact G10).
  assert (R1c : forall j, In j [3; 4]%nat -> getr R1 (reg j) = getr R (reg j)).
  { intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity. }
  assert (Q50 : 0 <= F < 2 ^ 64) by (clear - pf15; lia).
  assert (Q51 : 0 <= fl < 2 ^ 64) by (clear - pf22; lia).
  (* [comment removed for export] *)
  pose proof PRE2 as (PA2 & _ & _ & _ & OACC2 & _).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA2, OACC2. change (PNRA.o_is PMA.AD fb) with (fb + 96) in PA2. change (PNM.PSIZE + 8) with 424 in OACC2. fold op ois in PA2, OACC2.
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ FF' LK2 cr Aw M2 model2 fb _ s HH2 FOK' PA2 OACC2) as (_ & _ & _ & _ & OVIS2 & _). fold op H2 in OVIS2.
  pose proof PA2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & MD2 & _ & _ & _ & _ & SV0 & _). change PNM.OFF_STK with 392 in SV0. change PNM.MAX_DEPTH with 1024 in MD2.
  pose proof SV0 as (V0 & V8 & V16 & Hk & Hlen & Hal & DB & CB & AB & EL). change PNM.BSZ with 40 in V8, V16, Hlen, DB, CB, AB.
  set (b := PNM.b_sb s) in *. set (n := Z.of_nat (length (PNM.b_stk s))) in *.
  pose proof INV as (_ & (LN1 & LN2 & _)). change (PNM.MAX_DEPTH + 1) with 1025 in LN2. fold n in LN2.
  assert (Hn1 : 1 <= n) by (unfold n; clear - LN1; lia).
  assert (ISB : In (b, PNM.BSZ * 2 ^ PNM.b_sk s) LB) by (unfold LB; apply in_or_app; left; exact (PNBOA.PNM_own_stk s)).
  pose proof (WB _ ISB) as ((Sb0 & _ & _ & _ & Sb4 & _) & _). cbn [fst snd] in Sb0, Sb4.
  assert (P2k : 1 <= 2 ^ PNM.b_sk s) by (apply (Z.pow_le_mono_r 2 0 (PNM.b_sk s)); clear - Hk; lia).
  assert (Q41 : 0 <= b < 2 ^ 64) by (clear - Sb0 Sb4 P2k CEB1 STT STOP; unfold PNM.BSZ in Sb4; lia).
  assert (Q42 : 0 <= 40 * n < 2 ^ 64) by (clear - Hn1 LN2; lia).
  assert (VBv : L5.u64_at RSEGS MV2 (op + 392) b).
  { apply (proj2 (L5A.u64_at_vis H2 M2 (op + 392) b (OVIS2 (op + 392) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1; lia))). exact V0. }
  assert (VEv : L5.u64_at RSEGS MV2 (op + 400) (b + 40 * n)).
  { apply (proj2 (L5A.u64_at_vis H2 M2 (op + 400) (b + 40 * n) (OVIS2 (op + 400) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1; lia))).
    replace (op + 400) with (op + 392 + 8) by (clear; lia). exact V8. }
  assert (RB41 : 4096 <= b <= 140737488314328) by (clear - Sb0 Sb4 P2k CEB1 STT STOP; unfold PNM.BSZ in Sb4; lia).
  assert (AL41 : PNABDP.aligned b 8) by (unfold PNABDP.aligned; apply PMFA.mod16_8; exact Hal).
  assert (RB42 : 40 <= 40 * n <= 41000) by (clear - Hn1 LN2; lia).
  assert (AL42 : PNABDP.aligned (40 * n) 8) by (unfold PNABDP.aligned; replace (40 * n) with ((5 * n) * 8) by (clear; lia); apply Z_mod_mult).
  assert (MDv : L5.u32_at RSEGS MV2 (op + 312) 1024).
  { apply (proj2 (L5A.u32_at_vis H2 M2 (op + 312) 1024 (OVIS2 (op + 312) 4 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1; lia))). exact MD2. }
  assert (FLCv : L5.u64_at RSEGS MV2 (F + 56) fl) by (replace (F + 56) with (F + 64 - 8) by (clear; lia); exact FLC).
  (* [comment removed for export] *)
  assert (SETUP : forall (fx3 : FPState) R3 pc3 (M3v : mem),
             msteps RSEGS (st fx1 R2 0xae99c MV2) (st fx3 R3 pc3 M3v) -> mem_grows MV2 M3v ->
             (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (F + 0 <= i < F + 0 + 24) -> ~ (F / 8 + 2147450880 + 0 <= i < F / 8 + 2147450880 + 0 + 8) -> ~ (sp - 128 <= i < sp - 128 + 8) -> ~ (sp - 144 <= i < sp - 144 + 16) ->
                          M3v (Z_to_bv 64 i) = MV2 (Z_to_bv 64 i)) ->
             L5.u8_at RSEGS M3v (F / 8 + 2147450880) 241 -> L5.u64_at RSEGS M3v (sp - 128) F ->
             (forall (M3 : mem) model3,
                 bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK2 Aw s sm ax cr ->
                 spill M3 sp F -> PMSPA.ec_at RSEGS M3 (fb + 1024) e cat -> mrestrict H2 M3 = M3v ->
                 (forall a v, sp - 160 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS M3 a v) ->
                 srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 pc3 M3 model3) K) ->
             srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R2 0xae99c M2 model2) K).
  { intros fx3 R3 pc3 M3v MS3 MG3 FRZ3 SH0 SPL3v KR.
    set (W3 := fun a => (F <= a < F + 24) \/ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 8) \/ (sp - 128 <= a < sp - 128 + 8) \/ (sp - 144 <= a < sp - 144 + 16)).
    apply (L5SAR.apiece L ar C HI LYa HIok LB FF' LK2 cr Aw M2 model2 fx1 fx3 R2 0xae99c R3 pc3 M3v W3 K HH2 AM2 MS3 MG3).
    { intros a Ha Hn. apply FRZ3; [exact Ha| intros X; apply Hn; left; clear - X; lia| intros X; apply Hn; right; left; clear - X; lia| intros X; apply Hn; right; right; left; exact X| intros X; apply Hn; right; right; right; exact X]. }
    { intros a Ha Wa. split.
      - destruct Wa as [X|[X|[X|X]]].
        + apply (L5SAR.fframe_client L ar LB FF' 0 0 F 0 (sp - 160 + 32)); [left; reflexivity| change (ff_bytes 0) with 64; clear - X; lia].
        + apply (L5SAR.fframe_shadow_client L ar LB FF' 0 0 F 0 (sp - 160 + 32)); [left; reflexivity|]. change (ff_bytes 0) with 64.
          unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - X; lia.
        + unfold aclientw, aclient_g. right; left. split; [clear - X SL160 SHI SPT; lia| intros Y; clear - Y; lia].
        + unfold aclientw, aclient_g. right; left. split; [clear - X SL160 SHI SPT; lia| intros Y; clear - Y; lia].
      - destruct Wa as [X|[X|[X|X]]]; clear - X GFR SL160 SPT FSAPP FSCEIL; lia. }
    intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3. change (mrestrict H2 M3 = M3v) in VIS3.
    assert (EK23f : L5SAR.ek L ar LB FF sp 26624 [] M2 M3).
    { apply (L5SAR.ek_piece L ar LB FF sp 26624 [] M2 M3 W3 FR3). intros a Ha Hc _ X. destruct X as [X|[X|[X|X]]].
      - destruct (APART a 1 sp 26624 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (Y & _). clear - X Y; lia.
      - destruct (APART a 1 sp 26624 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (_ & Y & _). unfold SB in Y. clear - X Y; lia.
      - apply (NCS0 a); [clear - X; lia| exact Hc].
      - apply (NCS0 a); [clear - X; lia| exact Hc]. }
    pose proof (L5SAR.ek_trans L ar LB FF sp 26624 [] M M2 M3 EK02f EK23f) as EK03f.
    destruct (KEEP M3 EK03f) as (PRE3 & EC3).
    assert (BI3 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 26624 (sp - 160) (own sp R) F 0 WR (PNM.bparser_own s) M3 model3 LK2 cr Aw).
    { apply (PMAUK.binv_piece L ar HI M model LBX FF LK Aw sp 26624 (sp - 160) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PNM.bparser_own s) G
               WR (PNM.bparser_own s) M2 model2 LK2 cr Aw M3 model3 W3 BI2 HH3 AM3 MRT3 MGM3 FR3).
      intros a [X|[X|[X|X]]].
      - right; left. change (ff_bytes 0) with 64. clear - X; lia.
      - right; right. change (ff_bytes 0 / 8) with 8. unfold SB. clear - X; lia.
      - left. split; [clear - X; lia| unfold ocell; clear - X; lia].
      - left. split; [clear - X; lia| unfold ocell; clear - X; lia]. }
    assert (AV4 : avis H2 (F / 8 + 2147450880) 1) by (apply (L5A.avis_sub H2 (F / 8 + SB) 8); [exact VSH| unfold SB; clear; lia| unfold SB; clear; lia]).
    assert (R4a : 0 <= F / 8 + 2147450880) by (clear - pf15; pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)); lia).
    assert (R4b : F / 8 + 2147450880 + 1 <= 2 ^ 64) by (clear - pf15; pose proof (Z.div_le_upper_bound F 8 17592186044408 ltac:(lia) ltac:(lia)); lia).
    pose proof (L5A.u8_at_vis H2 M3 (F / 8 + 2147450880) 241 AV4 R4a R4b) as UV. rewrite VIS3 in UV.
    assert (U8c : L5.u8_at RSEGS M3 (F / 8 + 2147450880) 241) by (apply (proj1 UV); exact SH0). clear UV.
    pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ LK2 cr Aw M3 model3 HH3) as (_ & VISs3 & _). cbv zeta in VISs3. rewrite HID3 in VISs3. fold H2 in VISs3.
    assert (SVR3 : forall a v, sp - 160 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS M3 a v).
    { intros a v Ha1 Ha2 X.
      apply (proj1 (L5A.u64_at_vis H2 M3 a v (VISs3 a 8 ltac:(clear - Ha1 SLO; lia) ltac:(clear - Ha2 Q1; lia)) ltac:(clear - Ha1 Q1; lia) ltac:(clear - Ha2 Q1; lia))).
      rewrite VIS3. exact X. }
    assert (SPL3 : spill M3 sp F) by (unfold spill; apply (SVR3 (sp - 128) F ltac:(clear; lia) ltac:(clear; lia) SPL3v)).
    apply (KR M3 model3); [| exact SPL3| exact EC3| exact VIS3| exact SVR3].
    unfold bd_mem. split; [exact BI3|]. split; [exact PRE3|]. split; [apply PNBKA.src_step_refl|]. split; [apply PNST.bax_le_refl|].
    split; [apply PNBKA.credit_keep_refl|]. split; [exact U8c| reflexivity]. }
  assert (R3gpF : forall R3, (forall x, In x [3; 4]%nat -> getr R3 (reg x) = getr R2 (reg x)) -> getr R3 (reg 3) = getr R (reg 3) /\ getr R3 (reg 4) = getr R (reg 4)).
  { intros R3 KS3. split; [rewrite (KS3 3%nat) by inl; rewrite (R2c 3%nat) by inl; apply R1c; inl| rewrite (KS3 4%nat) by inl; rewrite (R2c 4%nat) by inl; apply R1c; inl]. }
  destruct (Z_le_gt_dec n 1024) as [DEP|DEP].
  - (* [comment removed for export] *)
    assert (DEPv : 1 <= sz32a (40 * n) <= 1024) by (rewrite (sz32a_ok n ltac:(clear - Hn1 DEP; lia)); clear - Hn1 DEP; lia).
    unfold sz32a in DEPv.
    LeanFeed.pfeed P (PNABDP.abdB_conc fx1 R2 MV2 (fun j => match j with 2%nat => sp | 33%nat => op | 34%nat => ov | 36%nat => oec | 41%nat => b | 42%nat => 40 * n | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNABDP.aligned; assumption]).
    destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11 & Y12 & Y13 & Y14 & Y18 & Y22 & Y23 & Y24 & Y25 & Y27 & Y20 & Y21 & Y26
                   & SH4 & SPLv & C144v & C136v & SH3 & SH2 & SH1 & SH0 & SH7 & SH6 & SH5 & HPC & HDESC & HMAG & D24).
    apply (SETUP fx3 R3 0xaed4c M3v MS3 MG3 FRZ3 SH0 SPLv).
    intros M3 model3 LM3 SPL3 EC3 VIS3 SVR3.
    assert (C1443 : L5.u64_at RSEGS M3 (sp - 144) (fb + 464 + 400)) by (apply (SVR3 (sp - 144) _ ltac:(clear; lia) ltac:(clear; lia)); exact C144v).
    assert (C1363 : L5.u64_at RSEGS M3 (sp - 136) (fb + 464 + 392)) by (apply (SVR3 (sp - 136) _ ltac:(clear; lia) ltac:(clear; lia)); exact C136v).
    assert (KS3' : forall x, In x [2; 3; 4; 8; 9; 19]%nat -> getr R3 (reg x) = getr R2 (reg x)).
    { intros x Hx. apply KS3. revert x Hx. apply (L5K.incl_b [2; 3; 4; 8; 9; 19]%nat); vm_compute; reflexivity. }
    destruct (R3gpF R3 ltac:(intros x Hx; apply KS3'; revert x Hx; apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity)) as (R3gp & R3tp).
    assert (ER3 : bregs R R3 sp fb F).
    { unfold bregs. rewrite (KS3' 2%nat), (KS3' 3%nat), (KS3' 4%nat), (KS3' 8%nat), (KS3' 9%nat), (KS3' 19%nat) by inl. unfold op, ov, oec in *.
      split; [exact B2R|]. split; [rewrite (R2c 3%nat) by inl; apply R1c; inl|]. split; [rewrite (R2c 4%nat) by inl; apply R1c; inl|].
      split; [exact B8R|]. split; [exact B9R|]. split; [exact B19R|]. split; [exact Y20|]. split; [exact Y21|]. split; [exact Y22|].
      split; [exact Y23|]. split; [exact Y24|]. split; [exact Y25|]. split; [exact Y26| exact Y27]. }
    unfold op, ov, oec, ois in *. clear op ov oec ois.
    (* [comment removed for export] *)
    pose proof LM3 as (BI3 & _). pose proof BI3 as (HH3 & _).
    assert (AV44 : avis H2 (F / 8 + 2147450884) 1) by (apply (L5A.avis_sub H2 (F / 8 + SB) 8); [exact VSH| unfold SB; clear; lia| unfold SB; clear; lia]).
    assert (R4a : 0 <= F / 8 + 2147450884) by (clear - pf15; pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)); lia).
    assert (R4b : F / 8 + 2147450884 + 1 <= 2 ^ 64) by (clear - pf15; pose proof (Z.div_le_upper_bound F 8 17592186044408 ltac:(lia) ltac:(lia)); lia).
    pose proof (L5A.u8_at_vis H2 M3 (F / 8 + 2147450884) 4 AV44 R4a R4b) as UV. rewrite VIS3 in UV.
    assert (U84 : L5.u8_at RSEGS M3 (F / 8 + 2147450884) 4) by (apply (proj1 UV); exact SH4). clear UV.
    assert (ACC4 : aacc M3 (F + 32) 4).
    { apply (aacc_local M3 F 32 4 4 (proj1 GF8) ltac:(reflexivity) ltac:(clear; lia) ltac:(clear - pf15; lia) ltac:(right; split; [clear; lia| reflexivity])).
      change (32 / 8) with 4. replace (F / 8 + 4 + 2147450880) with (F / 8 + 2147450884) by (clear; lia). unfold byte_at.
      apply (L5ADHR.byte_of_u8 M3 (F / 8 + 2147450884) 4 U84); [right; pose proof (Z.div_pos F 8 ltac:(clear - pf15; lia) ltac:(clear; lia)) as DF0; clear - DF0; lia| clear - R4a R4b; lia]. }
    apply (PNABDK.bd_call_read L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK2 Aw s sm ax cr fx3 R3 0xaeab4 32 4
             SRD CTX G LM3 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ACC4).
    { exact Y1. } { unfold L5.ra_ok; clear; lia. }
    { rewrite (KS3' 2%nat) by inl. exact B2R. }
    { rewrite R3gp. exact Rgp. } { rewrite R3tp. exact Rtp. }
    { exact Y10. } { exact Y11. } { exact Y12. }
    intros fx5 R5 M5 model5 LK5 Aw5 src5 sm5 d RP5 Z10 Hd UN5 _ _ DEF5 QC5 LM5 FRC5 ECK5 _.
    apply (bd_after_read K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 (PNM.with_srcB s src5) sm5 ax cr fx5 R5 d MKE PSH
             (bd_arm_u1 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 AGR (bd_u1post_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 (UE K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2) (UMV K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2) (UP K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2) (U1 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2))) CTX G LM5).
    + exact (bregs_pres R R3 R5 sp fb F ER3 RP5).
    + exact Z10.
    + exact Hd.
    + rewrite (L5SAR.cs_of_preserved R3 R5 18%nat RP5) by inl. exact Y18.
    + apply (PNABDK.spill_agree M3 M5 sp F); [clear - Q1; lia| clear - Q1; lia| exact SPL3| intros a Ha; apply FRC5; clear - Ha; lia].
    + apply (L5C.u64_at_agree RSEGS M3 M5 (sp - 144)); [intros j Hj; apply FRC5; clear - Hj; lia| clear - Q1; lia| clear - Q1; lia| exact C1443].
    + apply (L5C.u64_at_agree RSEGS M3 M5 (sp - 136)); [intros j Hj; apply FRC5; clear - Hj; lia| clear - Q1; lia| clear - Q1; lia| exact C1363].
    + exact (ECK5 _ _ EC3).
    + exact INV.
    + reflexivity.
    + cbn [PNM.with_srcB PNM.b_stk]. exact DEP.
    + cbn [PNM.with_srcB PNM.b_src]. exact UN5.
  - (* [comment removed for export] *)
    assert (N1025 : n = 1025) by (clear - DEP LN2; lia).
    assert (DEPv : 1025 <= sz32a (40 * n) <= 1025) by (rewrite (sz32a_ok n ltac:(clear - N1025; lia)); clear - N1025; lia).
    unfold sz32a in DEPv.
    LeanFeed.pfeed P (PNABDP.abdBx_conc fx1 R2 MV2 (fun j => match j with 2%nat => sp | 33%nat => op | 34%nat => ov | 36%nat => oec | 41%nat => b | 42%nat => 40 * n | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNABDP.aligned; assumption]).
    destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11 & Y13 & Y14 & Y18 & Y22 & Y25 & Y21 & Y26
                   & SPLv & SH3 & SH2 & SH1 & SH0 & SH7 & SH6 & SH5 & SH4 & HPC & HDESC & HMAG & D24).
    apply (SETUP fx3 R3 0xae848 M3v MS3 MG3 (fun i Hi N1 N2 N3 _ => FRZ3 i Hi N1 N2 N3) SH0 SPLv).
    intros M3 model3 LM3 SPL3 EC3 VIS3 _.
    assert (KS3' : forall x, In x [2; 3; 4; 8; 9; 19; 20; 23; 27]%nat -> getr R3 (reg x) = getr R2 (reg x)).
    { intros x Hx. apply KS3. revert x Hx. apply (L5K.incl_b [2; 3; 4; 8; 9; 19; 20; 23; 27]%nat); vm_compute; reflexivity. }
    assert (ER3 : bregsE R R3 sp fb F).
    { unfold bregsE. rewrite (KS3' 2%nat), (KS3' 3%nat), (KS3' 4%nat), (KS3' 8%nat), (KS3' 9%nat), (KS3' 19%nat), (KS3' 20%nat), (KS3' 23%nat), (KS3' 27%nat) by inl. unfold op, ov, oec in *.
      split; [exact B2R|]. split; [rewrite (R2c 3%nat) by inl; apply R1c; inl|]. split; [rewrite (R2c 4%nat) by inl; apply R1c; inl|].
      split; [exact B8R|]. split; [exact B9R|]. split; [exact Y18|]. split; [exact B19R|]. split; [exact B20R|]. split; [exact Y21|].
      split; [exact Y22|]. split; [exact B23R|]. split; [exact Y25|]. split; [exact Y26| exact B27R]. }
    unfold op, ov, oec, ois in *. clear op ov oec ois.
    apply (bd_arm_err4 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK2 Aw s sm ax cr fx3 R3 e cat MKE CTX G LM3 ER3 SPL3 EC3 Y1 Y10 Y11 INV).
    apply Nat.le_refl.
Qed.

End WithHeap.
End PNABD.
