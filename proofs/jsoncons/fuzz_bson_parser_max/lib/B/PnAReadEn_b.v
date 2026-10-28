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
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5CoreSpecsA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParSpecs PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnModelFacts PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnASrcKit_b PnASrcRead1_b PmAUarK_b PmAUar_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrObj. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrObjA_b PnAParKit_b PnAReset1_b PnOwnerOkA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrKitA_b PnAReadEnP_b Ba0_code_ae2e8_ae2ec_b PnAReadEnK_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNACEN.
Import L5A. Import L5CA. Import L5SAR. Import PNBKA. Import PNAENK.

(* [comment removed for export] *)
Definition eregs (R R4 : bvmap 5 word) (sp fb F ty : Z) : Prop :=
  getr R4 (reg 2) = Z_to_bv 64 (sp - 128) /\ getr R4 (reg 3) = getr R (reg 3) /\ getr R4 (reg 4) = getr R (reg 4)
  /\ getr R4 (reg 8) = Z_to_bv 64 sp /\ getr R4 (reg 9) = Z_to_bv 64 (sp - 128)
  /\ getr R4 (reg 18) = Z_to_bv 64 F /\ getr R4 (reg 19) = Z_to_bv 64 (fb + 464) /\ getr R4 (reg 20) = Z_to_bv 64 (fb + 1024)
  /\ getr R4 (reg 21) = Z_to_bv 64 (fb + 432) /\ getr R4 (reg 22) = Z_to_bv 64 (fb + 464 + 344) /\ getr R4 (reg 23) = Z_to_bv 64 ty
  /\ getr R4 (reg 24) = Z_to_bv 64 F /\ getr R4 (reg 25) = Z_to_bv 64 2147450880 /\ getr R4 (reg 26) = Z_to_bv 64 (F / 8 + 2147450880)
  /\ getr R4 (reg 27) = Z_to_bv 64 ((fb + 464 + 344) / 8 + 2147450880).

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
  en_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  en_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  en_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  6905856 <= fb + 432 <= 140737488355320 /\ (fb + 432) mod 8 = 0 /\ (2147446784 + 17592186048512 <= fb + 432 \/ (fb + 432) + 8 <= 2147446784)
  /\ L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) (((fb + 432) / 8) + 2147450880) 1
  /\ ((sp - 128) + 128 <= fb + 432 \/ (fb + 432) + 8 <= (sp - 128)) /\ ((fb + 464) + 416 <= fb + 432 \/ (fb + 432) + 8 <= fb + 464)
  /\ (F + 64 <= fb + 432 \/ (fb + 432) + 8 <= F) /\ (fl + 1 <= fb + 432 \/ (fb + 432) + 8 <= fl)
  /\ L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 432) 1251456
  /\ L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) 2147607324 1
  /\ ((((fb + 432) / 8) + 2147450880) + 1 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 8 <= (((fb + 432) / 8) + 2147450880)).
Proof.
  intros CTX G LM.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 6) with 24576 in *.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold en_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 0, sp - 128 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  pose proof RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_v PMA.AD fb) with (fb + 432) in VIS1.
  pose proof (PNAPAR.ov_visB L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 fb HH1 FOK' VIS1) as VV. cbv zeta in VV.
  destruct VV as ((V1 & V8 & VNS) & VZ & VW & VCE & VU & _).
  assert (CLh : forall a, fb + 32 <= a < fb + 2040 -> aclient L ar LBX FF sp 24576 a).
  { intros a Ha. unfold aclient, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
    change (ff_bytes 5) with 2048. split; [clear - Ha; lia| intros Y; clear - Ha Y; lia]. }
  assert (APF : F + 64 <= fb + 432 \/ (fb + 432) + 8 <= F).
  { apply iv_apart; [clear; lia| clear; lia|]. intros a Ha X. apply (GNCF a); [left; exact Ha| apply CLh; clear - X; lia]. }
  pose proof (m32_8 F GF32) as F8.
  split; [exact V1|]. split; [exact V8|]. split; [exact VNS|]. split; [exact VZ|].
  split; [clear - VCE GSLO; lia|]. split; [right; clear; lia|].
  split; [exact APF|].
  split. { destruct (Z_lt_le_dec fl (fb + 432)) as [X|X]; [left; clear - X; lia|]. destruct (Z_lt_le_dec fl (fb + 432 + 8)) as [Y|Y]; [| right; clear - Y; lia].
           exfalso. apply GFLNC. apply L5SAR.aclient_cons. apply (L5SAR.aclient_00 L ar LBX FF sp 24576). apply CLh. clear - X Y; lia. }
  split; [exact VU|].
  split; [exact (PMASK.img_shz_vis L ar C HI LY IL ICok ILY _ FF' LK1 cr1 Aw1 M1 model1 0x1318e0 1 HH1 ltac:(clear; lia) ltac:(clear; lia) ltac:(reflexivity) ltac:(clear; lia) ltac:(clear; lia))|].
  destruct APF as [X|X].
  - right. pose proof (sh_le64 F (fb + 432) F8 V8 X) as Y. clear - Y. lia.
  - left. pose proof (sh_le (fb + 432) F V8 F8 X) as Y. clear - Y. lia.
Qed.

(* [comment removed for export] *)
Definition nfacts (MV : mem) (sp op F fl : Z) (x : PM.vstr) : Prop :=
  match x with
  | PM.VShort n => 0 <= n <= 22 /\ L5.u8_at RSEGS MV (op + 344) (2 * n)
  | PM.VLong c n p =>
      L5.u8_at RSEGS MV (op + 344) ((c + 1) mod 256) /\ L5.u64_at RSEGS MV (op + 360) p
      /\ 4096 <= p <= 140737488355296 /\ (2147446784 + 17592186048512 <= p \/ p + 1 <= 2147446784)
      /\ L5KA.zeros_at MV ((p / 8) + 2147450880) 1
      /\ (((p / 8) + 2147450880) + 1 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 8 <= ((p / 8) + 2147450880))
      /\ L5.u64_at RSEGS MV (op + 352) n
      /\ L5.writable RSEGS MV p 1 /\ ((sp - 128) + 128 <= p \/ p + 1 <= (sp - 128))
      /\ (p + 1 <= op \/ op + 416 <= p) /\ (p + 1 <= F \/ F + 64 <= p) /\ (p + 1 <= fl \/ fl + 1 <= p)
      /\ 0 <= n < c /\ 26 <= c <= 2 ^ 27 /\ c mod 2 = 0 /\ p + c <= 2 ^ 47
  end.
Lemma nfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 :
  en_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  en_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  en_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  nfacts (mrestrict (ahid Aw1 model1) M1) sp (fb + 464) F fl (PNM.b_nb s1)
  /\ (let p := PM.vs_data (fb + 464 + 344) (PNM.b_nb s1) in let n := PM.vs_size (PNM.b_nb s1) in
      0 <= n /\ 0 < p /\ p + n <= 2 ^ 47 /\ L5.defined M1 p n /\ aacc M1 p n
      /\ (forall a, p <= a < p + n -> ahid Aw1 model1 (Z_to_bv 64 a) = false /\ ahid Aw1 model1 (Z_to_bv 64 (S a)) = false)
      /\ p + n <= sp - 128 - 12288).
Proof.
  intros CTX G LM.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 6) with 24576 in *.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold en_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 0, sp - 128 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  pose proof RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in *. change (PNRA.o_is PMA.AD fb) with (fb + 96) in *.
  change (PNM.PSIZE + 8) with 424 in OACC1.
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1 OACC1) as OPV. cbv zeta in OPV.
  destruct OPV as ((O1 & O8 & ONSH) & Zop & OWR & OCE & OVIS & AOP).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (WB1 & WF1 & FSAPP1 & FSCEIL1 & _).
  assert (Hfb' : In (fb, 5, rs) FF') by (right; exact Hfb).
  pose proof (WF1 _ Hfb') as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP1, FSCEIL1, F1, F2.
  pose proof (m32_8 F GF32) as F8.
  pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NB1 & _). change (fb + 464 + PNM.OFF_NB) with (fb + 464 + 344) in NB1.
  set (MV := mrestrict (ahid Aw1 model1) M1) in *.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ LK1 cr1 Aw1 M1 model1 HH1) as VP; cbv zeta in VP; destruct VP as (_ & _ & _ & VFS & VB & _).
  assert (VINI : forall q m, In (q, m) (PM.vs_own (PNM.b_nb s1)) -> In (q, m) (PNM.bparser_own s1 ++ LBX)).
  { intros q m Hq. apply in_or_app. left. unfold PNM.bparser_own, PNM.brest_own. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hq. }
  destruct (PNM.b_nb s1) as [n|c n p] eqn:ENB; cbn [PM.vs_data PM.vs_size nfacts PM.vs_own] in *.
  - destruct NB1 as (Dnb & Anb & (Hn & U8n)).
    split.
    { split; [exact Hn|].
      apply (proj2 (L5A.u8_at_vis _ M1 (fb + 464 + 344) (2 * n) (OVIS (fb + 464 + 344) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1; lia))). exact U8n. }
    split; [clear - Hn; lia|]. split; [clear - O1; lia|]. split; [clear - O1 Hn; lia|].
    split; [apply (L5.defined_sub M1 (fb + 464 + 344) 24); [exact Dnb| clear; lia| clear - Hn; lia]|].
    split. { intros a Ha. apply Anb. clear - Ha Hn. lia. }
    split. { apply (PMASR1.vis_scan L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 (fb + 464 + 344 + 1) n HH1). right; left. unfold FS_BYTES. clear - F1 F2 Hn. lia. }
    clear - OCE GSLO Hn. lia.
  - destruct NB1 as (Dnb & Anb & (U0 & U8 & U16 & Hn & Hc & He & Dp & Ap)).
    pose proof (VINI p c ltac:(left; reflexivity)) as VINL.
    destruct (WB1 _ VINL) as ((B0 & BI0 & B16 & _ & B4 & BAPP) & _ & _ & _ & _ & BFA & BFS). cbn [fst snd] in B0, BI0, B16, B4, BAPP, BFA, BFS.
    unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in BAPP. unfold FS_BYTES in BFS.
    pose proof (BFA (F, 0, sp - 128 + 32) (in_or_app FF' LK1 _ (or_introl (or_introl eq_refl)))) as Z1. cbn [ff_addr ff_class fst snd] in Z1. change (ff_bytes 0) with 64 in Z1.
    pose proof (BFA (fb, 5, rs) (in_or_app FF' LK1 (fb, 5, rs) (or_introl (or_intror Hfb)))) as Z2. cbn [ff_addr ff_class fst snd] in Z2. change (ff_bytes 5) with 2048 in Z2.
    pose proof (PMKA.mod16_8' p B16) as P8.
    pose proof GFLP as GFLP'. unfold FS_BYTES in GFLP'.
    assert (PV : L5A.avis (ahid Aw1 model1) p c) by (apply (VB p c p c VINL); clear; lia).
    split.
    { split. { apply (proj2 (L5A.u8_at_vis _ M1 (fb + 464 + 344) _ (OVIS (fb + 464 + 344) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1; lia))).
               apply (PMF.u8_of_u64 RSEGS M1 _ (c + 1) ltac:(clear - Hc; lia) U0). }
      split. { apply (proj2 (L5A.u64_at_vis _ M1 (fb + 464 + 360) _ (OVIS (fb + 464 + 360) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1; lia))).
               replace (fb + 464 + 360) with (fb + 464 + 344 + 16) by (clear; lia). exact U16. }
      split; [clear - B0 B4 GSLO GSHI GSPT Hc; lia|].
      split; [destruct BAPP as (_ & [X|X] & _); [right| left]; clear - X Hc; lia|].
      split. { change 2147450880 with SB. replace 1 with (8 / 8) at 2 by reflexivity.
               apply (PMKA.blk_shadow_vis L ar C HI LYa HIok _ _ LK1 cr1 Aw1 M1 model1 p c p 8 HH1 VINL); [clear; lia| clear - Hc; lia| exact P8| clear; lia| reflexivity|].
               intros a Ha. apply Ap. clear - Ha Hc; lia. }
      split. { destruct Z1 as [X|X].
               - left. pose proof (sh_le p F P8 F8 ltac:(clear - X Hc; lia)) as Y. clear - Y. lia.
               - right. pose proof (sh_le64 F p F8 P8 X) as Y. clear - Y. lia. }
      split. { apply (proj2 (L5A.u64_at_vis _ M1 (fb + 464 + 352) _ (OVIS (fb + 464 + 352) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1; lia))).
               replace (fb + 464 + 352) with (fb + 464 + 344 + 8) by (clear; lia). exact U8. }
      split. { apply (proj2 (L5A.writable_vis _ M1 p 1 ltac:(eapply L5A.avis_sub; [exact PV| clear; lia| clear - Hc; lia]) ltac:(clear - B0; lia) ltac:(clear - B4 Hc GSLO GSHI GSPT; lia))).
               apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M1 p c); [exact Dp| clear; lia| clear - Hc; lia]| clear - B0; lia| clear - B4 Hc GSLO GSHI GSPT; lia]. }
      split; [right; clear - B4 Hc GSLO; lia|].
      split; [clear - Z2 Hc; lia|].
      split; [clear - Z1 Hc; lia|].
      split; [clear - BFS Hc GFLP'; lia|].
      split; [exact Hn|]. split; [exact Hc|]. split; [exact He|]. clear - B4 GSLO GSHI GSPT. lia. }
    split; [clear - Hn; lia|]. split; [clear - B0; lia|]. split; [clear - B4 Hn GSLO GSHI GSPT; lia|].
    split; [apply (L5.defined_sub M1 p c); [exact Dp| clear; lia| clear - Hn; lia]|].
    split. { intros a Ha. apply Ap. clear - Ha Hn. lia. }
    split. { apply (PMASR1.vis_scan L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 p n HH1). right; right. exists p, c. split; [exact VINL|]. clear - Hn. lia. }
    clear - B4 Hn GSLO. lia.
Qed.

(* [comment removed for export] *)
Lemma en_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1
      (fx1 fx2 : FPState) R1 R2 (pc1 pc2 : Z) (M2v : mem) :
  en_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w -> en_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  en_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  msteps RSEGS (st fx1 R1 pc1 (mrestrict (ahid Aw1 model1) M1)) (st fx2 R2 pc2 M2v) ->
  mem_grows (mrestrict (ahid Aw1 model1) M1) M2v ->
  (forall a, 0 <= a < 2 ^ 64 -> M2v (Z_to_bv 64 a) = mrestrict (ahid Aw1 model1) M1 (Z_to_bv 64 a)) ->
  (forall model3,
      en_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model3 LK1 Aw1 s1 sm1 ax1 cr1 ->
      ahid Aw1 model3 = ahid Aw1 model1 ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 pc2 M1 model3) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M1 model1) K.
Proof.
  intros CTX G LM MS MG FRZ KR.
  apply (PNAENK.en_piece_fr L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1
           fx1 fx2 R1 R2 pc1 pc2 M2v (fun _ => False) CTX G LM MS MG).
  - intros a Ha _. exact (FRZ a Ha).
  - intros a [].
  - intros M3 model3 LM3 HID3 VIS3 FR3 MG3 ECK3.
    assert (EM31 : M3 = M1) by (apply PNBKA.mem_eq_of_agree; exact FR3). subst M3.
    exact (KR model3 LM3 HID3).
Qed.

Lemma eregs_keep R R4 R5 sp fb F ty :
  eregs R R4 sp fb F ty -> (forall k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R5 (reg k) = getr R4 (reg k)) -> eregs R R5 sp fb F ty.
Proof.
  intros (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27) RK. unfold eregs.
  rewrite (RK 2%nat) by inl. rewrite (RK 3%nat) by inl. rewrite (RK 4%nat) by inl. rewrite (RK 8%nat) by inl. rewrite (RK 9%nat) by inl.
  rewrite (RK 18%nat) by inl. rewrite (RK 19%nat) by inl. rewrite (RK 20%nat) by inl. rewrite (RK 21%nat) by inl. rewrite (RK 22%nat) by inl.
  rewrite (RK 23%nat) by inl. rewrite (RK 24%nat) by inl. rewrite (RK 25%nat) by inl. rewrite (RK 26%nat) by inl. rewrite (RK 27%nat) by inl.
  repeat split; assumption.
Qed.
Lemma eregs_pres R R4 R5 sp fb F ty : eregs R R4 sp fb F ty -> regs_preserved R4 R5 -> eregs R R5 sp fb F ty.
Proof. intros ER RP. apply (eregs_keep R R4 R5 sp fb F ty ER). intros k Hk. exact (L5SAR.cs_of_preserved R4 R5 k RP Hk). Qed.


(* [comment removed for export] *)
Lemma en_tail K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 (fx6 : FPState) R6 ty :
  en_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  en_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  en_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 ->
  0 <= ty <= 1 -> eregs R R6 sp fb F ty ->
  ( (exists v, 1 <= v <= 64 /\ PMSPA.ec_at RSEGS M6 (fb + 1024) v (pa_errcat_obj PMA.AD) /\ PNM.b_more s6 = 0 /\ PNST.bax_cat ax6 = true)
    \/ (PMSPA.ec_at RSEGS M6 (fb + 1024) e cat /\ PNRA.bprog_name R6 M6 s s6 sm sm6) ) ->
  PNRA.binv s6 -> (length (PNM.b_stk s) <= length (PNM.b_stk s6))%nat ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 0xaf854 M6 model6) K.
Proof.
  intros CTX G LM Hty ER POST INV6 LEN6.
  pose proof (PNAENK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM)
    as (PF & OWN6 & SV6 & U8v6 & WRop6 & U8op6 & SVr6).
  pose proof (vfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM) as (vf1 & _).
  set (MV6 := mrestrict (ahid Aw6 model6) M6) in *.
  unfold pfacts in PF. destruct PF as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32 & pf33 & pf34).
  destruct ER as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27).
  unfold own in OWN6. destruct OWN6 as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & O12 & O13).
  assert (Q34 : 0 <= fb + 432 < 2 ^ 64) by (clear - vf1; lia).
  assert (Q35 : 0 <= ty < 2 ^ 64) by (clear - Hty; lia).
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
  LeanFeed.pfeed P (PNAENP.aenT_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 35%nat => ty | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | 60%nat => bv_unsigned (getr R (reg 1)) | 61%nat => bv_unsigned (getr R (reg 8)) | 62%nat => bv_unsigned (getr R (reg 9)) | 63%nat => bv_unsigned (getr R (reg 18)) | 64%nat => bv_unsigned (getr R (reg 19)) | 65%nat => bv_unsigned (getr R (reg 20)) | 66%nat => bv_unsigned (getr R (reg 21)) | 67%nat => bv_unsigned (getr R (reg 22)) | 68%nat => bv_unsigned (getr R (reg 23)) | 69%nat => bv_unsigned (getr R (reg 24)) | 70%nat => bv_unsigned (getr R (reg 25)) | 71%nat => bv_unsigned (getr R (reg 26)) | 72%nat => bv_unsigned (getr R (reg 27)) | _ => 0 end)) ltac:(first [assumption | unfold PNAENP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & Y1 & Y2 & Y8 & Y9 & Y10 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27 & FL0 & _).
  pose proof (fdiv_rng F pf15) as (DF1 & DF2).
  pose proof LM as (_ & RP6 & _). pose proof RP6 as (PA6 & _). change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA6.
  pose proof PA6 as (_ & _ & _ & MORE6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MB6 & _).
  apply (PNAENK.en_fin L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6
           fx6 fx9 R6 R9 0xaf854 (PNM.b_more s6) M9v CTX G LM MS9 MG9).
  - intros a Ha N. apply FRZ9; [exact Ha| | |]; intros X; apply N; unfold PMAUK.WretX, PMAUK.Wret; change (ff_bytes 0 / 8) with 8; unfold SB.
    + left; left; left. clear - X; lia.
    + left; left; right. clear - X; lia.
    + left; right. clear - X; lia.
  - exact FL0.
  - replace (fb + 472) with (fb + 464 + 8) by (clear; lia).
    apply (L5C.u8_at_agree RSEGS MV6 M9v); [| clear - pf7; lia| clear - pf7; lia| exact (proj2 (U8op6 _) MORE6)].
    intros j Hj. apply FRZ9; [clear - Hj pf7; lia| clear - Hj pf28; lia| clear - Hj pf9 DF1 DF2; lia| clear - Hj pf29; lia].
  - exact MB6.
  - exact Y2.
  - intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [assumption|]). destruct Hk.
  - intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[]]].
    + rewrite (KS9 3%nat) by inl. exact E3.
    + rewrite (KS9 4%nat) by inl. exact E4.
  - destruct POST as [(v & Hv & ECv & MO & CAT)|(EC6 & TP & UN)].
    + left. exists v. split; [exact Hv|]. split; [exact ECv|]. split; [exact MO| exact CAT].
    + right. split; [exact EC6|]. split; [exact TP| exact UN].
  - exact INV6.
  - exact LEN6.
Qed.

(* [comment removed for export] *)
Lemma mfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 :
  en_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  en_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  en_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  L5.writable RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 464 + 8) 1 /\ L5.u8_at RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 464 + 10) 0.
Proof.
  intros CTX G LM.
  pose proof (PNAENK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 CTX G LM)
    as (PF & _ & _ & _ & WRop & _ & _).
  unfold pfacts in PF. destruct PF as (_ & _ & _ & _ & _ & _ & pf7 & _).
  pose proof CTX as (_ & _ & _ & _ & _ & _ & _ & FOK & _).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof LM as (BI & RP1 & _).
  pose proof BI as (HH1 & _).
  pose proof RP1 as (PA1 & _ & _ & _ & OACC1 & _).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA1, OACC1. change (PNRA.o_is PMA.AD fb) with (fb + 96) in PA1. change (PNM.PSIZE + 8) with 424 in OACC1.
  assert (FOK' : PNRA.frame_okB ((F, 0, sp - 128 + 32) :: FF) fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ _ LK1 cr1 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1 OACC1) as OPV. cbv zeta in OPV.
  destruct OPV as (_ & _ & _ & _ & OVIS & _).
  pose proof PA1 as (_ & _ & _ & _ & _ & CM & _).
  split; [apply (L5.writable_sub RSEGS _ (fb + 464) 424); [exact WRop| clear; lia| clear; lia]|].
  apply (proj2 (L5A.u8_at_vis _ M1 (fb + 464 + 10) 0 (OVIS (fb + 464 + 10) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - pf7; lia) ltac:(clear - pf7; lia))). exact CM.
Qed.

Lemma tb0_long c : 0 <= c -> c mod 2 = 0 -> Z.testbit ((c + 1) mod 256) 0 = true.
Proof.
  intros Hc He. rewrite Z.bit0_odd. change 256 with (2 ^ 8). rewrite <- Z.land_ones by (clear; lia). rewrite <- Z.bit0_odd. rewrite Z.land_spec. rewrite Z.bit0_odd.
  change (Z.testbit (Z.ones 8) 0) with true. rewrite Bool.andb_true_r. rewrite Z.odd_add. change (Z.odd 1) with true.
  rewrite <- Z.negb_even. rewrite (proj2 (Z.even_spec c)); [reflexivity|]. exists (c / 2). pose proof (Z.div_mod c 2 ltac:(clear; lia)) as D. rewrite He in D. clear - D. lia.
Qed.

(* [comment removed for export] *)
Lemma en_arm_err K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 (fx6 : FPState) R6 ty ev ec :
  PNRAa.make_ec_spec L ar HI ->
  en_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  en_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  en_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 ->
  0 <= ty <= 1 -> eregs R R6 sp fb F ty -> spill M6 sp F ->
  PMSPA.ec_at RSEGS M6 (fb + 1024) ev ec ->
  getr R6 (reg 1) = Z_to_bv 64 0xaf900 -> getr R6 (reg 10) = Z_to_bv 64 (fb + 1024) -> getr R6 (reg 11) = Z_to_bv 64 3 ->
  PNRA.binv s6 -> (length (PNM.b_stk s) <= length (PNM.b_stk s6))%nat ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 (pa_make_ec PMA.AD) M6 model6) K.
Proof.
  intros MKE CTX G LM Hty ER SPL EC6 X1 X10 X11 INV6 LEN6.
  pose proof CTX as (_ & _ & _ & _ & ENT & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof ER as (E2 & E3 & E4 & _).
  apply (PNAENK.en_call_mkec L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 fx6 R6 0xaf900 3 ev ec MKE CTX G LM EC6).
  { exact X1. } { unfold L5.ra_ok; clear; lia. } { exact E2. } { rewrite E3. exact Rgp. } { rewrite E4. exact Rtp. } { exact X10. } { exact X11. } { clear; lia. }
  intros fx7 R7 M7 model7 LK7 Aw7 RP7 EC7 LM7 AG7.
  pose proof (eregs_pres R R6 R7 sp fb F ty ER RP7) as ER7.
  pose proof (PNAENK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M7 model7 LK7 Aw7 s6 sm6 _ cr6 CTX G LM7)
    as (PF & OWN7 & SV7 & U8v7 & WRop7 & U8op7 & SVr7).
  pose proof (vfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M7 model7 LK7 Aw7 s6 sm6 _ cr6 CTX G LM7) as (vf1 & _).
  pose proof (mfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M7 model7 LK7 Aw7 s6 sm6 _ cr6 CTX G LM7) as (WRmo & _).
  set (MV7 := mrestrict (ahid Aw7 model7) M7) in *.
  unfold pfacts in PF. destruct PF as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32 & pf33 & pf34).
  assert (SPL7 : spill M7 sp F) by (apply (PNAENK.spill_agree M6 M7 sp F); [clear - pf4; lia| clear - pf4; lia| exact SPL| intros a Ha; apply AG7; clear - Ha; lia]).
  pose proof (SV7 (sp - 112) F ltac:(clear; lia) ltac:(clear; lia) SPL7) as SPLv.
  destruct ER7 as (E2' & E3' & E4' & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27).
  unfold own in OWN7. destruct OWN7 as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & O12 & O13).
  assert (Q34 : 0 <= fb + 432 < 2 ^ 64) by (clear - vf1; lia).
  assert (Q35 : 0 <= ty < 2 ^ 64) by (clear - Hty; lia).
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
  LeanFeed.pfeed P (PNAENP.aenE_conc fx7 R7 MV7 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 35%nat => ty | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | 60%nat => bv_unsigned (getr R (reg 1)) | 61%nat => bv_unsigned (getr R (reg 8)) | 62%nat => bv_unsigned (getr R (reg 9)) | 63%nat => bv_unsigned (getr R (reg 18)) | 64%nat => bv_unsigned (getr R (reg 19)) | 65%nat => bv_unsigned (getr R (reg 20)) | 66%nat => bv_unsigned (getr R (reg 21)) | 67%nat => bv_unsigned (getr R (reg 22)) | 68%nat => bv_unsigned (getr R (reg 23)) | 69%nat => bv_unsigned (getr R (reg 24)) | 70%nat => bv_unsigned (getr R (reg 25)) | 71%nat => bv_unsigned (getr R (reg 26)) | 72%nat => bv_unsigned (getr R (reg 27)) | _ => 0 end)) ltac:(first [assumption | unfold PNAENP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & Y1 & Y2 & Y8 & Y9 & Y10 & Y11 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27 & FL0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & MO0 & _).
  apply (PNAENK.en_fin L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M7 model7 LK7 Aw7 s6 sm6 _ cr6
           fx7 fx9 R7 R9 0xaf900 0 M9v CTX G LM7 MS9 MG9).
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
  - left. exists 3. split; [clear; lia|]. split; [exact EC7|]. split; [reflexivity| apply bax_cat_add].
  - exact INV6.
  - exact LEN6.
Qed.

(* [comment removed for export] *)
Lemma en_arm_key K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 (fx6 : FPState) R6 ty :
  en_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  en_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  en_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 ->
  0 <= ty <= 1 -> eregs R R6 sp fb F ty -> spill M6 sp F ->
  PMSPA.ec_at RSEGS M6 (fb + 1024) e cat -> PNRA.bprog_name R6 M6 s s6 sm sm6 ->
  PNRA.binv s6 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 0xaf768 M6 model6) K.
Proof.
  intros CTX G LM Hty ER SPL EC6 PROG INV6.
  pose proof (PNAENK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM)
    as (PF & OWN6 & SV6 & U8v6 & WRop6 & U8op6 & SVr6).
  pose proof (vfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM)
    as (vf1 & vf2 & vf3 & vf4 & vf5 & vf6 & vf7 & vf8 & vf9 & vf10 & vf11).
  pose proof (mfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM) as (WRmo & CM0).
  pose proof (nfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM) as (NF & _).
  pose proof (PNAENK.efacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 e cat CTX G LM EC6) as (ef1 & _).
  set (MV6 := mrestrict (ahid Aw6 model6) M6) in *.
  unfold pfacts in PF. destruct PF as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32 & pf33 & pf34).
  pose proof (SV6 (sp - 112) F ltac:(clear; lia) ltac:(clear; lia) SPL) as SPLv.
  destruct ER as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27).
  unfold own in OWN6. destruct OWN6 as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & O12 & O13).
  assert (Q34 : 0 <= fb + 432 < 2 ^ 64) by (clear - vf1; lia).
  assert (Q35 : 0 <= ty < 2 ^ 64) by (clear - Hty; lia).
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
  assert (FIN : forall (fx9 : FPState) R9 M9v,
             msteps RSEGS (st fx6 R6 0xaf768 MV6) (st fx9 R9 0xaf8f0 M9v) -> mem_grows MV6 M9v ->
             (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (F / 8 + 2147450880 + 0 <= i < F / 8 + 2147450880 + 0 + 8) -> ~ (F + 32 <= i < F + 32 + 16) -> ~ (fb + 464 + 8 <= i < fb + 464 + 8 + 1)
                            -> ~ (F + 0 <= i < F + 0 + 8) -> ~ (fl + 0 <= i < fl + 0 + 1) -> M9v (Z_to_bv 64 i) = MV6 (Z_to_bv 64 i)) ->
             (forall k, In k [3; 4]%nat -> getr R9 (reg k) = getr R6 (reg k)) ->
             getr R9 (reg 2) = Z_to_bv 64 sp ->
             (forall k, In k [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R9 (reg k) = Z_to_bv 64 (bv_unsigned (getr R (reg k)))) ->
             L5.u8_at RSEGS M9v fl 0 -> L5.u8_at RSEGS M9v (fb + 464 + 8) 1 ->
             srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 0xaf768 M6 model6) K).
  { intros fx9 R9 M9v MS9 MG9 FRZ9 K34 Y2 YK FL0 MO1.
    apply (PNAENK.en_finF L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6
             fx6 fx9 R6 R9 0xaf768 1 M9v CTX G LM MS9 MG9).
    - intros a Ha N. apply FRZ9; [exact Ha| | | | |]; intros X; apply N; unfold PMAUK.WretX, PMAUK.Wret; change (ff_bytes 0 / 8) with 8; unfold SB.
      + left; left; right. clear - X; lia.
      + right; right. clear - X; lia.
      + right; left. clear - X; lia.
      + left; left; left. clear - X; lia.
      + left; right. clear - X; lia.
    - exact FL0.
    - replace (fb + 472) with (fb + 464 + 8) by (clear; lia). exact MO1.
    - right; reflexivity.
    - exact Y2.
    - exact YK.
    - intros k Hk. rewrite (K34 k Hk). cbn [In] in Hk. destruct Hk as [<-|[<-|[]]]; [exact E3| exact E4].
    - right. split; [exact EC6|]. destruct PROG as (TP & UN). split; [exact TP| exact UN].
    - exact INV6.
    - destruct PROG as (TP & _). exact (btop_len s s6 TP). }
  destruct (PNM.b_nb s6) as [n|c n p] eqn:ENB; cbn [nfacts] in NF.
  - (* [comment removed for export] *)
    destruct NF as (Hn & U8n).
    assert (Q42 : 0 <= 2 * n < 2 ^ 64) by (clear - Hn; lia).
    assert (Q42' : 0 <= 2 * n <= 255) by (clear - Hn; lia).
    assert (TB0 : Z.testbit (2 * n) 0 = false) by (apply Z.testbit_even_0).
    LeanFeed.pfeed P (PNAENP.aenKS_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 35%nat => ty | 36%nat => fb + 1024 | 42%nat => 2 * n | 50%nat => F | 51%nat => fl | 60%nat => bv_unsigned (getr R (reg 1)) | 61%nat => bv_unsigned (getr R (reg 8)) | 62%nat => bv_unsigned (getr R (reg 9)) | 63%nat => bv_unsigned (getr R (reg 18)) | 64%nat => bv_unsigned (getr R (reg 19)) | 65%nat => bv_unsigned (getr R (reg 20)) | 66%nat => bv_unsigned (getr R (reg 21)) | 67%nat => bv_unsigned (getr R (reg 22)) | 68%nat => bv_unsigned (getr R (reg 23)) | 69%nat => bv_unsigned (getr R (reg 24)) | 70%nat => bv_unsigned (getr R (reg 25)) | 71%nat => bv_unsigned (getr R (reg 26)) | 72%nat => bv_unsigned (getr R (reg 27)) | _ => 0 end)) ltac:(first [assumption | unfold PNAENP.aligned; assumption]).
    destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & Y1 & Y2 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27 & FL0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & MO1 & _).
    apply (FIN fx9 R9 M9v MS9 MG9 FRZ9); [| exact Y2| | exact FL0| exact MO1].
    + intros k Hk. apply KS9. revert k Hk. apply (L5K.incl_b [3; 4]%nat). vm_compute. reflexivity.
    + intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [assumption|]). destruct Hk.
  - (* [comment removed for export] *)
    destruct NF as (nf1 & nf2 & nf3 & nf4 & nf5 & nf6 & nf7 & nf8 & nf9 & nf10 & nf11 & nf12 & Hn & Hc & He & Hpc).
    pose proof (Z.mod_pos_bound (c + 1) 256 ltac:(clear; lia)) as MB.
    assert (Q42 : 0 <= (c + 1) mod 256 < 2 ^ 64) by (clear - MB; lia).
    assert (Q42' : 0 <= (c + 1) mod 256 <= 255) by (clear - MB; lia).
    assert (TB0 : Z.testbit ((c + 1) mod 256) 0 = true) by (apply tb0_long; [clear - Hc; lia| exact He]).
    assert (Q43 : 0 <= p < 2 ^ 64) by (clear - nf3; lia).
    assert (Q45 : 0 <= n < 2 ^ 64) by (clear - Hn Hc; lia).
    LeanFeed.pfeed P (PNAENP.aenKL_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 35%nat => ty | 36%nat => fb + 1024 | 42%nat => (c + 1) mod 256 | 43%nat => p | 45%nat => n | 50%nat => F | 51%nat => fl | 60%nat => bv_unsigned (getr R (reg 1)) | 61%nat => bv_unsigned (getr R (reg 8)) | 62%nat => bv_unsigned (getr R (reg 9)) | 63%nat => bv_unsigned (getr R (reg 18)) | 64%nat => bv_unsigned (getr R (reg 19)) | 65%nat => bv_unsigned (getr R (reg 20)) | 66%nat => bv_unsigned (getr R (reg 21)) | 67%nat => bv_unsigned (getr R (reg 22)) | 68%nat => bv_unsigned (getr R (reg 23)) | 69%nat => bv_unsigned (getr R (reg 24)) | 70%nat => bv_unsigned (getr R (reg 25)) | 71%nat => bv_unsigned (getr R (reg 26)) | 72%nat => bv_unsigned (getr R (reg 27)) | _ => 0 end)) ltac:(first [assumption | unfold PNAENP.aligned; assumption]).
    destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & Y1 & Y2 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27 & FL0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & MO1 & _).
    apply (FIN fx9 R9 M9v MS9 MG9 FRZ9); [| exact Y2| | exact FL0| exact MO1].
    + intros k Hk. apply KS9. revert k Hk. apply (L5K.incl_b [3; 4]%nat). vm_compute. reflexivity.
    + intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [assumption|]). destruct Hk.
Qed.

(* [comment removed for export] *)
Lemma en_after_val K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 (fx6 : FPState) R6 ty :
  PNRAa.make_ec_spec L ar HI ->
  en_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  en_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  en_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 ->
  0 <= ty <= 1 -> eregs R R6 sp fb F ty -> spill M6 sp F ->
  PMSPA.ec_at RSEGS M6 (fb + 1024) e cat -> PNRA.btop_pos s s6 -> PM.unread (PNM.b_src s6) sm6 < PM.unread (PNM.b_src s) sm ->
  PNRA.binv s6 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 0xaf760 M6 model6) K.
Proof.
  intros MKE CTX G LM Hty ER SPL EC6 TP6 UN6 INV6.
  pose proof (PNAENK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM)
    as (PF & _).
  pose proof (vfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM) as (vf1 & _).
  set (MV6 := mrestrict (ahid Aw6 model6) M6) in *.
  unfold pfacts in PF. destruct PF as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32 & pf33 & pf34).
  pose proof ER as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27).
  assert (Q34 : 0 <= fb + 432 < 2 ^ 64) by (clear - vf1; lia).
  assert (Q35 : 0 <= ty < 2 ^ 64) by (clear - Hty; lia).
  assert (Q36 : 0 <= fb + 1024 < 2 ^ 64) by (clear - pf7; lia).
  pose proof (bvu_rng (getr R6 (reg 11))) as Q46.
  assert (E11 : getr R6 (reg 11) = Z_to_bv 64 (bv_unsigned (getr R6 (reg 11)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  LeanFeed.pfeed P (PNAENP.aenC_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 35%nat => ty | 36%nat => fb + 1024 | 46%nat => bv_unsigned (getr R6 (reg 11)) | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNAENP.aligned; assumption]).
  destruct P as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & [(MS7 & KS7 & Y1 & Y10 & Y11)|(MS7 & KS7)]).
  - (* [comment removed for export] *)
    apply (en_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 fx6 fx7 R6 R7 0xaf760 0xae848 M7v CTX G LM MS7 MG7 FRZ7).
    intros model7 LM7 HID7.
    assert (RK : forall k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R7 (reg k) = getr R6 (reg k)).
    { intros k Hk. apply KS7. revert k Hk. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
    change 0xae848 with (pa_make_ec PMA.AD).
    apply (en_arm_err K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model7 LK6 Aw6 s6 sm6 ax6 cr6 fx7 R7 ty e cat MKE CTX G LM7 Hty
             (eregs_keep R R6 R7 sp fb F ty ER RK) SPL EC6 Y1 Y10 Y11 INV6 (btop_len s s6 TP6)).
  - (* [comment removed for export] *)
    apply (en_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 fx6 fx7 R6 R7 0xaf760 0xaf768 M7v CTX G LM MS7 MG7 FRZ7).
    intros model7 LM7 HID7.
    assert (RK : forall k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R7 (reg k) = getr R6 (reg k)).
    { intros k Hk. apply KS7. revert k Hk. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
    apply (en_arm_key K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model7 LK6 Aw6 s6 sm6 ax6 cr6 fx7 R7 ty CTX G LM7 Hty
             (eregs_keep R R6 R7 sp fb F ty ER RK) SPL EC6 (conj TP6 UN6) INV6).
Qed.

(* [comment removed for export] *)
Lemma en_arm_val K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 (fx6 : FPState) R6 ty :
  PMA.validate_spec L ar HI -> PNRAa.make_ec_spec L ar HI ->
  en_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  en_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  en_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 ->
  0 <= ty <= 1 -> eregs R R6 sp fb F ty -> spill M6 sp F ->
  PMSPA.ec_at RSEGS M6 (fb + 1024) e cat -> PNRA.btop_pos s s6 -> PM.unread (PNM.b_src s6) sm6 < PM.unread (PNM.b_src s) sm ->
  PNRA.binv s6 -> PM.vs_size (PNM.b_nb s6) < 2 ^ 26 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 0xaf70c M6 model6) K.
Proof.
  intros VAL MKE CTX G LM Hty ER SPL EC6 TP6 UN6 INV6 SZ6.
  pose proof CTX as (_ & _ & _ & _ & ENT & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof (PNAENK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM)
    as (PF & _).
  pose proof (vfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM) as (vf1 & _).
  pose proof (nfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM) as (NF & VP).
  cbv zeta in VP.
  set (MV6 := mrestrict (ahid Aw6 model6) M6) in *.
  unfold pfacts in PF. destruct PF as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32 & pf33 & pf34).
  pose proof ER as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27).
  assert (Q34 : 0 <= fb + 432 < 2 ^ 64) by (clear - vf1; lia).
  assert (Q35 : 0 <= ty < 2 ^ 64) by (clear - Hty; lia).
  assert (Q36 : 0 <= fb + 1024 < 2 ^ 64) by (clear - pf7; lia).
  (* [comment removed for export] *)
  assert (VCALL : forall (fx7 : FPState) R7 M7v p n,
             msteps RSEGS (st fx6 R6 0xaf70c MV6) (st fx7 R7 0xb2f54 M7v) -> mem_grows MV6 M7v ->
             (forall i : Z, 0 <= i < 2 ^ 64 -> M7v (Z_to_bv 64 i) = MV6 (Z_to_bv 64 i)) ->
             (forall k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R7 (reg k) = getr R6 (reg k)) ->
             getr R7 (reg 1) = Z_to_bv 64 718688 -> getr R7 (reg 10) = Z_to_bv 64 p -> getr R7 (reg 11) = Z_to_bv 64 n ->
             p = PM.vs_data (fb + 464 + 344) (PNM.b_nb s6) -> n = PM.vs_size (PNM.b_nb s6) ->
             srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 0xaf70c M6 model6) K).
  { intros fx7 R7 M7v p n MS7 MG7 FRZ7 RK Y1 Y10 Y11 Ep En.
    destruct VP as (V1 & V2 & V3 & V4 & V5 & V6 & V7). subst p n.
    apply (en_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 fx6 fx7 R6 R7 0xaf70c 0xb2f54 M7v CTX G LM MS7 MG7 FRZ7).
    intros model7 LM7 HID7.
    pose proof (eregs_keep R R6 R7 sp fb F ty ER RK) as ER7.
    pose proof ER7 as (E2' & E3' & E4' & _).
    change 0xb2f54 with (pa_validate PMA.AD).
    apply (PNAENK.en_call_val L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model7 LK6 Aw6 s6 sm6 ax6 cr6 fx7 R7 0xaf760 (PM.vs_data (fb + 464 + 344) (PNM.b_nb s6)) (PM.vs_size (PNM.b_nb s6)) VAL CTX G LM7).
    { exact Y1. } { unfold L5.ra_ok; clear; lia. } { exact E2'. } { rewrite E3'. exact Rgp. } { rewrite E4'. exact Rtp. } { exact Y10. } { exact Y11. }
    { clear - V1 SZ6. lia. } { clear - V2. lia. } { right. exact V2. } { exact V3. } { exact V4. } { exact V5. }
    { rewrite HID7. exact V6. }
    { right; right. exact V7. }
    intros fx8 R8 M8 model8 RP8 LM8 AG8 ECK8.
    apply (en_after_val K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M8 model8 LK6 Aw6 s6 sm6 ax6 cr6 fx8 R8 ty MKE CTX G LM8 Hty
             (eregs_pres R R7 R8 sp fb F ty ER7 RP8)); [| exact (ECK8 _ _ EC6)| exact TP6| exact UN6| exact INV6].
    apply (PNAENK.spill_agree M6 M8 sp F); [clear - pf4; lia| clear - pf4; lia| exact SPL|].
    intros a Ha. apply AG8; [clear - Ha pf4; lia| clear - Ha; lia]. }
  destruct (PNM.b_nb s6) as [n|c n p] eqn:ENB; cbn [nfacts PM.vs_data PM.vs_size] in NF, VCALL.
  - (* [comment removed for export] *)
    destruct NF as (Hn & U8n).
    assert (Q42 : 0 <= 2 * n < 2 ^ 64) by (clear - Hn; lia).
    assert (Q42' : 0 <= 2 * n <= 255) by (clear - Hn; lia).
    assert (TB0 : Z.testbit (2 * n) 0 = false) by (apply Z.testbit_even_0).
    LeanFeed.pfeed P (PNAENP.aenVS_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 35%nat => ty | 36%nat => fb + 1024 | 42%nat => 2 * n | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNAENP.aligned; assumption]).
    destruct P as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & Y1 & Y10 & Y11).
    rewrite (Z.mul_comm 2 n), Z.div_mul in Y11 by (clear; lia).
    apply (VCALL fx7 R7 M7v (fb + 464 + 345) n MS7 MG7 FRZ7); [| exact Y1| exact Y10| exact Y11| clear; lia| reflexivity].
    intros k Hk. apply KS7. revert k Hk. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat). vm_compute. reflexivity.
  - (* [comment removed for export] *)
    destruct NF as (nf1 & nf2 & nf3 & nf4 & nf5 & nf6 & nf7 & nf8 & nf9 & nf10 & nf11 & nf12 & Hn & Hc & He & Hpc).
    pose proof (Z.mod_pos_bound (c + 1) 256 ltac:(clear; lia)) as MB.
    assert (Q42 : 0 <= (c + 1) mod 256 < 2 ^ 64) by (clear - MB; lia).
    assert (Q42' : 0 <= (c + 1) mod 256 <= 255) by (clear - MB; lia).
    assert (TB0 : Z.testbit ((c + 1) mod 256) 0 = true) by (apply tb0_long; [clear - Hc; lia| exact He]).
    assert (Q43 : 0 <= p < 2 ^ 64) by (clear - nf3; lia).
    assert (Q45 : 0 <= n < 2 ^ 64) by (clear - Hn Hc; lia).
    LeanFeed.pfeed P (PNAENP.aenVL_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 35%nat => ty | 36%nat => fb + 1024 | 42%nat => (c + 1) mod 256 | 43%nat => p | 45%nat => n | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNAENP.aligned; assumption]).
    destruct P as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & Y1 & Y10 & Y11).
    apply (VCALL fx7 R7 M7v p n MS7 MG7 FRZ7); [| exact Y1| exact Y10| exact Y11| reflexivity| reflexivity].
    intros k Hk. apply KS7. revert k Hk. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat). vm_compute. reflexivity.
Qed.

Lemma lor_small a b : 0 <= a <= 64 -> 0 <= b <= 1 -> 0 <= Z.lor a b <= 65 /\ (Z.lor a b = 0 -> a = 0 /\ b = 0).
Proof.
  intros Ha Hb. split.
  - assert (X : Z.lor a b < 2 ^ 7).
    { destruct (Z.eq_dec (Z.lor a b) 0) as [E0|N0]; [rewrite E0; clear; lia|]. apply Z.log2_lt_pow2; [pose proof (Z.lor_nonneg a b); clear - H Ha Hb N0; lia|].
      rewrite Z.log2_lor by (clear - Ha Hb; lia). apply Z.max_lub_lt.
      - destruct (Z.eq_dec a 0) as [->|Na]; [cbn; clear; lia|]. apply Z.log2_lt_pow2; clear - Ha Na; lia.
      - destruct (Z.eq_dec b 0) as [->|Nb]; [cbn; clear; lia|]. apply Z.log2_lt_pow2; clear - Hb Nb; lia. }
    pose proof (proj2 (Z.lor_nonneg a b) ltac:(clear - Ha Hb; lia)) as Y.
    assert (B : b = 0 \/ b = 1) by (clear - Hb; lia). destruct B as [->| ->].
    + rewrite Z.lor_0_r. clear - Ha. lia.
    + assert (LE : Z.lor a 1 <= a + 1).
      { destruct (Z.odd a) eqn:OD.
        - replace (Z.lor a 1) with a; [clear; lia|]. apply Z.bits_inj'. intros k Hk. rewrite Z.lor_spec. destruct (Z.eq_dec k 0) as [->|Nk].
          + rewrite Z.bit0_odd, OD. reflexivity.
          + rewrite (Z.bits_above_log2 1 k) by (cbn; clear - Hk Nk; lia). rewrite Bool.orb_false_r. reflexivity.
        - replace (Z.lor a 1) with (a + 1); [clear; lia|]. rewrite <- Z.add_nocarry_lor; [reflexivity|].
          apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.bits_0. destruct (Z.eq_dec k 0) as [->|Nk].
          + rewrite Z.bit0_odd, OD. reflexivity.
          + rewrite (Z.bits_above_log2 1 k) by (cbn; clear - Hk Nk; lia). apply Bool.andb_false_r. }
      clear - LE Y Ha. lia.
  - intros E0. apply Z.lor_eq_0_iff in E0. exact E0.
Qed.

(* [comment removed for export] *)
Lemma en_body K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 (fx4 : FPState) R4 ty :
  PNRAa.read_cstring_spec L ar HI -> PMA.validate_spec L ar HI -> PNRAa.make_ec_spec L ar HI ->
  en_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  en_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  en_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 ->
  PNRA.binv s5 -> PMSPA.ec_at RSEGS M5 (fb + 1024) e cat -> PNRA.btop_pos s s5 ->
  PM.vs_size (PNM.b_nb s5) = 0 -> PM.unread (PNM.b_src s5) sm5 = PM.unread (PNM.b_src s) sm ->
  spill M5 sp F -> 0 <= ty <= 1 -> eregs R R4 sp fb F ty ->
  getr R4 (reg 1) = Z_to_bv 64 0xaf6f0 -> getr R4 (reg 10) = Z_to_bv 64 (fb + 464) -> getr R4 (reg 11) = Z_to_bv 64 (fb + 464 + 344) -> getr R4 (reg 12) = Z_to_bv 64 (fb + 1024) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx4 R4 (PNL.pn_read_cstring PMA.AN) M5 model5) K.
Proof.
  intros RCS VAL MKE CTX G LM5 INV5 EC5 TP5 SZ5 UN5 SPL5 Hty ER X1 X10 X11 X12.
  pose proof CTX as (Hw & _ & _ & _ & ENT & _ & _ & _ & _ & _ & _ & _ & _ & _ & HE & UNR & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof ER as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27).
  (* [comment removed for export] *)
  apply (PNAENK.en_call_cs L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 fx4 R4 0xaf6f0 e cat RCS CTX G LM5 INV5 EC5 HE).
  { rewrite UN5. exact UNR. }
  { rewrite SZ5, UN5. clear - UNR. lia. }
  { exact X1. } { unfold L5.ra_ok; clear; lia. } { exact E2. } { rewrite E3. exact Rgp. } { rewrite E4. exact Rtp. } { exact X10. } { exact X11. } { exact X12. }
  intros fx6 R6 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 RP6 LM6 STEP6 AXL6 RES6 AG6.
  pose proof (eregs_pres R R4 R6 sp fb F ty ER RP6) as ER6.
  pose proof (PNAENK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM6)
    as (PF & _).
  pose proof (vfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM6) as (vf1 & _).
  unfold pfacts in PF. destruct PF as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32 & pf33 & pf34).
  assert (SPL6 : spill M6 sp F).
  { apply (PNAENK.spill_agree M5 M6 sp F); [clear - pf4; lia| clear - pf4; lia| exact SPL5| intros a Ha; apply AG6; clear - Ha; lia]. }
  (* [comment removed for export] *)
  assert (ECV : exists ecv ecc, 0 <= ecv <= 64 /\ PMSPA.ec_at RSEGS M6 (fb + 1024) ecv ecc
            /\ (ecv = 0 -> PMSPA.ec_at RSEGS M6 (fb + 1024) e cat /\ PNRA.binv s6 /\ PNRA.bprog_cs 0 R6 M6 s5 s6 sm5 sm6)).
  { destruct RES6 as [(v & Hv & E1 & _)|(E0 & INV & PROG)].
    - exists v, (pa_errcat_obj PMA.AD). split; [clear - Hv; lia|]. split; [exact E1|]. intros ->. exfalso. clear - Hv. lia.
    - exists e, cat. split; [exact HE|]. split; [exact E0|]. intros _. split; [exact E0|]. split; [exact INV| exact PROG]. }
  destruct ECV as (ecv & ecc & Hecv & ECv & OKP).
  pose proof (lor_small ecv ty Hecv Hty) as (LOR1 & LOR2).
  pose proof (PNAENK.efacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 ecv ecc CTX G LM6 ECv)
    as (ef1 & ef2 & ef3 & ef4 & ef5 & ef6 & ef7 & ef8 & ef9 & ef10).
  set (MV6 := mrestrict (ahid Aw6 model6) M6) in *.
  pose proof ER6 as (F2 & F3 & F4 & F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27).
  assert (Q34 : 0 <= fb + 432 < 2 ^ 64) by (clear - vf1; lia).
  assert (Q35 : 0 <= ty < 2 ^ 64) by (clear - Hty; lia).
  assert (Q36 : 0 <= fb + 1024 < 2 ^ 64) by (clear - pf7; lia).
  assert (Q44 : 0 <= ecv < 2 ^ 64) by (clear - Hecv; lia).
  LeanFeed.pfeed P (PNAENP.aenR_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 35%nat => ty | 36%nat => fb + 1024 | 44%nat => ecv | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNAENP.aligned; assumption]).
  destruct P as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & [(MS7 & KS7 & Y10 & PATH)|(MS7 & KS7 & Y10 & PATH)]).
  - (* [comment removed for export] *)
    apply (en_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 fx6 fx7 R6 R7 0xaf6f0 0xaf854 M7v CTX G LM6 MS7 MG7 FRZ7).
    intros model7 LM7 HID7.
    assert (RK : forall k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R7 (reg k) = getr R6 (reg k)).
    { intros k Hk. apply KS7. revert k Hk. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
    apply (en_tail K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model7 LK6 Aw6 s6 sm6 ax6 cr6 fx7 R7 ty CTX G LM7 Hty (eregs_keep R R6 R7 sp fb F ty ER6 RK)).
    + destruct RES6 as [(v & Hv & E1 & MO & CAT & LEN & INV')|(E0 & INV & (TP56 & LT56 & _))].
      * left. exists v. split; [exact Hv|]. split; [exact E1|]. split; [exact MO| exact CAT].
      * right. split; [exact E0|]. unfold PNRA.bprog_name. split; [exact (PNBKA.btop_pos_trans s s5 s6 TP5 TP56)| rewrite <- UN5; exact LT56].
    + destruct RES6 as [(v & Hv & E1 & MO & CAT & LEN & INV')|(E0 & INV & _)]; [exact INV'| exact INV].
    + destruct RES6 as [(v & Hv & E1 & MO & CAT & LEN & INV')|(E0 & INV & (TP56 & _))].
      * pose proof (btop_len s s5 TP5) as L1. clear - L1 LEN. lia.
      * exact (btop_len s s6 (PNBKA.btop_pos_trans s s5 s6 TP5 TP56)).
  - (* [comment removed for export] *)
    rewrite Z.sub_0_r, Z.mod_small in PATH by (clear - LOR1; lia).
    destruct (LOR2 ltac:(clear - PATH LOR1; lia)) as (Eecv & Ety).
    destruct (OKP Eecv) as (EC6 & INV6 & (TP56 & LT56 & SZ56)). clear OKP.
    unfold PNRA.bcs_str in SZ56. cbn [Z.eqb] in SZ56.
    apply (en_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 fx6 fx7 R6 R7 0xaf6f0 0xaf70c M7v CTX G LM6 MS7 MG7 FRZ7).
    intros model7 LM7 HID7.
    assert (RK : forall k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R7 (reg k) = getr R6 (reg k)).
    { intros k Hk. apply KS7. revert k Hk. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
    apply (en_arm_val K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model7 LK6 Aw6 s6 sm6 ax6 cr6 fx7 R7 ty VAL MKE CTX G LM7 Hty
             (eregs_keep R R6 R7 sp fb F ty ER6 RK) SPL6 EC6 (PNBKA.btop_pos_trans s s5 s6 TP5 TP56)).
    + rewrite <- UN5. exact LT56.
    + exact INV6.
    + pose proof LM6 as (_ & RPx & _). pose proof RPx as (PAx & IAx & _). pose proof (PNBKA.unread_nonneg _ M6 _ _ s6 str sm6 PAx IAx) as U0. clear - SZ56 SZ5 UN5 UNR U0. lia.
Qed.

Theorem read_e_name_ok : PNRAa.read_cstring_spec L ar HI -> PMA.validate_spec L ar HI -> PNRAa.make_ec_spec L ar HI -> PNRAa.read_e_name_spec L ar HI.
Proof.
  intros RCS VAL MKE. unfold PNRAa.read_e_name_spec, PNRA.read_e_name_spec, PNRA.brun_spec.
  set (w := 0). assert (Hw : w = 0 \/ w = 1) by (left; reflexivity).
  intros fx R M model K LBX FF LK Aw cr sp r fb cat e s str sm ax HH AM K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC HE UNR CRED KONT.
  assert (CTX : en_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w).
  { exact (conj Hw (conj HH (conj AM (conj K0 (conj ENT (conj FRM (conj FRS (conj FOK (conj SP32 (conj ARGS (conj RPRE (conj INCS (conj INV (conj EC (conj HE (conj UNR (conj CRED KONT))))))))))))))))). }
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 6) with 24576 in *. change (24576 / 8) with 3072 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  destruct ARGS as (A10 & A11 & A13 & A12).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl13 in A13. rewrite L5K.rl12 in A12.
  assert (TY : exists ty, 0 <= ty <= 1 /\ getr R (reg 12) = Z_to_bv 64 ty) by (destruct A12 as [X|X]; [exists 0| exists 1]; (split; [clear; lia| exact X])).
  destruct TY as (ty & Hty & A12t).
  pose proof RPRE as (PA & IA & VIS & VREF & OACC & BASE & ERR & GROW).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & STOP & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, F1, F2.
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in *. change (PNRA.o_ec PMA.AD fb) with (fb + 1024) in *.
  change (PNRA.o_v PMA.AD fb) with (fb + 432) in *. change (PNRA.o_is PMA.AD fb) with (fb + 96) in *.
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ FF LK cr Aw M model fb _ s HH FOK PA OACC) as ((O1 & O8 & ONSH) & Zop & OWR & OCE & OVIS & AOP).
  pose proof (PMASK.iss_vis L ar C HI LY HIok _ FF LK cr Aw M model fb str sm sp 24576 HH) as ISV.
  pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF LK cr Aw M model HH BASE) as (VM0 & VM1 & VM2).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 24576 128 HH ASTK ltac:(lia)) as (SL160 & SH160 & SWR).
  set (op := fb + 464) in *. set (ov := fb + 432) in *. set (oec := fb + 1024) in *. set (ois := fb + 96) in *.
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (_ & VISs & _).
  LeanFeed.pfeed P (PNAENP.aenA_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => op | 34%nat => ov | 35%nat => ty | 36%nat => oec | _ => 0 end)) ltac:(first [assumption | unfold PNAENP.aligned; assumption | clear - SL160 SHI SPT; lia | unfold op, ov, oec; clear - O1 Hty F1 F2 FSAPP FSCEIL SLO SHI SPT; lia]).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T12 & T19 & T20 & T21 & T23 & T25
                 & C104 & C96 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8 & C160).
  unfold PMSP.cfg. change (PNL.pn_read_e_name PMA.AN) with 0xaf548.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xaf548 R1 0x5dc2c M1v (fun a => sp - 128 <= a < sp - 128 + 128) K HH AM MS1 MG1).
  { intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
  { intros a Ha Wa. split; [|intros X; clear - X Wa SL160 FSAPP FSCEIL; lia]. unfold aclientw, aclient_g. right; left. split; [clear - Wa SL160 SHI SPT; lia| intros X; clear - X; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
  set (LB := PNM.bparser_own s ++ LBX) in *.
  assert (INCX : incl LBX LB) by (unfold LB; apply incl_appr; apply incl_refl).
  assert (NCS0 : forall a, sp - 128 <= a < sp -> ~ aclient L ar LB FF sp 24576 a).
  { intros a Xa Hc. destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 24576 a HH SPT Hc) as [Y|Y].
    - clear - Xa Y; lia.
    - clear - Xa Y SL160; lia. }
  assert (EK01f : L5SAR.ek L ar LB FF sp 24576 [] M M1).
  { apply (L5SAR.ek_piece L ar LB FF sp 24576 [] M M1 (fun a => sp - 128 <= a < sp - 128 + 128) FR1). intros a Ha Hc _ X. apply (NCS0 a); [clear - X; lia| exact Hc]. }
  assert (DK01f : L5SAR.dk L ar LB FF sp 24576 M M1) by (apply L5SAR.dk_grows; exact MGM1).
  pose proof (PMKA.ek_sublb L ar LB LBX FF sp 24576 [] M M1 INCX EK01f) as EK01.
  pose proof (PMKA.dk_sublb L ar LB LBX FF sp 24576 M M1 INCX DK01f) as DK01.
  (* [comment removed for export] *)
  assert (SV1 : forall a v, sp - 128 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
  { intros a v Ha1 Ha2 X. apply (proj1 (L5A.u64_at_vis H M1 a v (VISs a 8 ltac:(clear - Ha1 SL160 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SL160 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))).
    rewrite VIS1. exact X. }
  assert (OWN1 : own sp R M1).
  { unfold own. repeat split; (apply SV1; [clear; lia| clear; lia| assumption]). }
  clear C104 C96 C88 C80 C72 C64 C56 C48 C40 C32 C24 C16 C8 SV1.
  (* [comment removed for export] *)
  assert (FRk0 : ff_room 0 FF LK) by (apply (PMAUAR.ff_room_ofB PNRA.FCB 6 FF LK 0 FRM); [clear; lia| left; reflexivity]).
  change 0x5dc2c with (PMA.SM_PC 0).
  apply (PMAUAR.uar_sm L ar C HI LY HIok 0 LBX (PNM.bparser_own s) FF LK cr Aw sp 24576 (sp - 128) (sp - 104) sp (ocell sp) (own sp R)
           fx1 R1 M M1 model model1 K 0xaf5c4 ltac:(left; reflexivity) HH HH1 AM1 K0 ASTK MGM1 EK01 DK01).
  { rewrite L5K.rl2. exact T2. }
  { rewrite L5K.rl4. rewrite (KS1 4%nat) by inl. rewrite <- L5K.rl4. exact Rtp. }
  { rewrite L5K.rl1. exact T1. }
  { reflexivity. }
  { clear; lia. }
  { replace (sp - 128) with (sp + (-8) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { clear; lia. } { clear; lia. } { clear; lia. } { clear; lia. }
  { intros a Ha. exact Ha. }
  { intros Ma Mb OW AG. apply (own_agree sp R Ma Mb ltac:(clear - SL160 SPT; lia) ltac:(clear - SHI SPT; lia) OW AG). }
  { exact FRk0. }
  { intros f Hf. specialize (FRS f Hf). clear - FRS; lia. }
  intros R2 M2 model2 F fl LK2 G G10 RP2 AM2 MRT2 ASTK2 EK02 DK02 EK12f DK12f AGF FW FSHW FSHZ FLC FLW FDEF VF VSH VFL APART.
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *. change (64 - 8) with 56 in *.
  pose proof G as G'. destruct G' as [_ _ _ _ _ _ _ GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 0) with 64 in *.
  pose proof (L5SAR.ek_trans L ar LB FF sp 24576 [] M M1 M2 EK01f EK12f) as EK02f.
  pose proof (L5SAR.dk_trans L ar LB FF sp 24576 M M1 M2 DK01f DK12f) as DK02f.
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
  assert (HH2 : ri_inv HI LB ((F, 0, sp - 128 + 32) :: FF) LK2 cr Aw M2 (vml_of model2)) by exact GHH2.
  set (FF' := (F, 0, sp - 128 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  set (H2 := ahid Aw model2) in *. set (MV2 := mrestrict H2 M2) in *.
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ _ LK2 cr Aw M2 model2 sp 24576 128 HH2 ASTK2 ltac:(lia)) as (_ & _ & SWR2).
  (* [comment removed for export] *)
  assert (R2c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (reg j) = getr R1 (reg j)).
  { intros j Hj. apply (L5SAR.cs_of_preserved R1 R2 j RP2 Hj). }
  assert (B2R : getr R2 (reg 2) = Z_to_bv 64 (sp - 128)) by (rewrite (R2c 2%nat) by inl; exact T2).
  assert (B8R : getr R2 (reg 8) = Z_to_bv 64 sp) by (rewrite (R2c 8%nat) by inl; exact T8).
  assert (B9R : getr R2 (reg 9) = Z_to_bv 64 (sp - 128)) by (rewrite (R2c 9%nat) by inl; exact T9).
  assert (B19R : getr R2 (reg 19) = Z_to_bv 64 op) by (rewrite (R2c 19%nat) by inl; exact T19).
  assert (B20R : getr R2 (reg 20) = Z_to_bv 64 oec) by (rewrite (R2c 20%nat) by inl; exact T20).
  assert (B21R : getr R2 (reg 21) = Z_to_bv 64 ov) by (rewrite (R2c 21%nat) by inl; exact T21).
  assert (B23R : getr R2 (reg 23) = Z_to_bv 64 ty) by (rewrite (R2c 23%nat) by inl; exact T23).
  assert (B25R : getr R2 (reg 25) = Z_to_bv 64 2147450880) by (rewrite (R2c 25%nat) by inl; exact T25).
  assert (B10R : getr R2 (reg 10) = Z_to_bv 64 F) by (rewrite <- L5K.rl10; exact G10).
  assert (FLCv : L5.u64_at RSEGS MV2 (F + 56) fl) by (replace (F + 56) with (F + 64 - 8) by (clear; lia); exact FLC).
  assert (Q0 : 0 <= sp < 2 ^ 64 /\ 0 <= op < 2 ^ 64 /\ 0 <= oec < 2 ^ 64 /\ 0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64 /\ 0 <= ov < 2 ^ 64 /\ 0 <= ty < 2 ^ 64)
    by (clear - SL160 SHI SPT O1 GFR GFLR Hty F1 F2 FSAPP FSCEIL SLO; unfold oec, op, ov in *; lia).
  destruct Q0 as (Q0a & Q0b & Q0d & Q0f & Q0g & Q0h & Q0t).
  assert (Q1 : 140735332487296 <= sp <= 140737488355328) by (clear - SL160 SHI SPT; lia).
  assert (Q3 : 6905856 <= F <= 140737488355264) by (clear - GFR; lia).
  assert (Q4 : (sp - 128) + 128 <= F \/ F + 64 <= (sp - 128)) by (clear - GFCEIL SL160; lia).
  assert (Q5 : (sp - 128) + 128 <= fl \/ fl + 1 <= (sp - 128)) by (clear - GFLR SL160; lia).
  assert (Q7 : 4096 <= fl <= 140737488355327) by (clear - GFLR; lia).
  assert (Qop : 6905856 <= op <= 140737488354912) by (clear - O1; lia).
  LeanFeed.pfeed P (PNAENP.aenB0_conc fx1 R2 MV2 (fun j => match j with 2%nat => sp | 33%nat => op | 34%nat => ov | 35%nat => ty | 36%nat => oec | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNAENP.aligned; assumption]).
  destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y18 & Y22 & Y24 & Y26 & Y27
                 & SH3 & SH2 & SH1 & SH0 & SH7 & SH6 & SH5 & SH4 & HPC & HDESC & HMAG & D24).
  set (W3 := fun a => (F <= a < F + 24) \/ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 8)).
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF' LK2 cr Aw M2 model2 fx1 fx3 R2 0xaf5c4 R3 0xaf658 M3v W3 K HH2 AM2 MS3 MG3).
  { intros a Ha Hn. apply FRZ3; [exact Ha| intros X; apply Hn; left; clear - X; lia| intros X; apply Hn; right; clear - X; lia]. }
  { intros a Ha Wa. split.
    - destruct Wa as [X|X].
      + apply (L5SAR.fframe_client L ar LB FF' 0 0 F 0 (sp - 128 + 32)); [left; reflexivity| change (ff_bytes 0) with 64; clear - X; lia].
      + apply (L5SAR.fframe_shadow_client L ar LB FF' 0 0 F 0 (sp - 128 + 32)); [left; reflexivity|]. change (ff_bytes 0) with 64.
        unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - X; lia.
    - destruct Wa as [X|X]; clear - X GFR SL160 SPT FSAPP FSCEIL; lia. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3. change (mrestrict H2 M3 = M3v) in VIS3.
  assert (EK23f : L5SAR.ek L ar LB FF sp 24576 [] M2 M3).
  { apply (L5SAR.ek_piece L ar LB FF sp 24576 [] M2 M3 W3 FR3). intros a Ha Hc _ X. destruct X as [X|X].
    - destruct (APART a 1 sp 24576 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (Y & _). clear - X Y; lia.
    - destruct (APART a 1 sp 24576 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (_ & Y & _). unfold SB in Y. clear - X Y; lia. }
  pose proof (L5SAR.ek_trans L ar LB FF sp 24576 [] M M2 M3 EK02f EK23f) as EK03f.
  assert (OWN3 : own sp R M3).
  { apply (own_agree sp R M1 M3 ltac:(clear - SL160 SPT; lia) ltac:(clear - SHI SPT; lia) OWN1). intros a Ha. unfold ocell in Ha.
    rewrite FR3; [apply AGF; clear - Ha; lia| clear - Ha SL160 SHI SPT; lia| intros [X|X]; clear - X Ha GFCEIL GFR SL160 SPT; unfold SB in *; lia]. }
  assert (WAPPR : PMKA.wapp (PNRA.W_brun PMA.AD PMA.AN fb)).
  { unfold PNRA.W_brun, PGS.W_srcfG, PNST.berr_W, PNST.cat_W, PNST.dec_W, PNRA.o_src, PNRA.o_is, PNRA.o_bb, PNRA.o_nb, PNRA.o_tb, PNRA.o_stk, PNRA.o_ec, PNRA.o_p, PMSP.o_p, PMSP.o_is, PMSP.o_ec.
    cbn [app pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PMA.AD ADDR_A PMA.AN NADDR_A PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj].
    unfold PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK.
    pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
    repeat apply PMKA.wapp_cons; [..| apply PMKA.wapp_nil]; cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct FA1 as [FA1|FA1]; clear - FA0 FA1 FA2 F1 F2; lia. }
  set (WR := PNRA.W_brun PMA.AD PMA.AN fb) in *.
  assert (BI3 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 24576 (sp - 128) (own sp R) F 0 WR (PNM.bparser_own s) M3 model3 LK2 cr Aw).
  { unfold PMAUK.binv. split; [exact HH3|]. split; [exact AM3|].
    split; [eapply L5LZ.model_rt_trans; [exact MRT1| eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT3]]|].
    split; [apply incl_refl|]. split; [exact GLKI2|]. split; [exact (L5SAR.astk_grows ar M2 M3 sp 24576 ASTK2 MGM3)|].
    split; [apply (L5SAR.ek_W L ar LBX FF sp 24576 WR [] M M3 (PMKA.ek_sublb L ar LB LBX FF sp 24576 [] M M3 INCX EK03f)); intros a _ r0 []|].
    split; [apply (L5SAR.dk_trans L ar LBX FF sp 24576 M M2 M3 DK02); apply L5SAR.dk_grows; exact MGM3|].
    split; [exact OWN3|].
    change (ff_bytes 0 / 8) with 8. apply (L5.defined_grows M2 M3 _ _ MGM3).
    apply (proj1 (L5A.defined_vis H2 M2 (F / 8 + SB) 8 VSH)). intros i Hi. pose proof (FSHZ i Hi) as Z0. unfold MV2 in Z0. rewrite Z0. discriminate. }
  assert (R1c : forall j, In j [3; 4]%nat -> getr R1 (reg j) = getr R (reg j)).
  { intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b [3; 4]%nat). vm_compute. reflexivity. }
  (* [comment removed for export] *)
  assert (AOPp : PMSPA.aobjA FF op PNM.PSIZE) by (apply (PNAPAR.aobj_fbB FF fb op PNM.PSIZE FOK); unfold op, PNM.PSIZE; clear; lia).
  assert (PA3 : PNM.bparser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA (pa_vp_parser PMA.AD) M3 op ois s).
  { apply (PNAPAR.bparser_keepA L ar C HI HIok LB FF LK cr Aw (vml_of model) [] sp 24576 M M3 op ois s HH EK03f PMKA.wapp_nil AOPp);
      [unfold LB; apply incl_appl; apply incl_refl| intros i _ r0 []| intros B m _ i _ r0 []| exact PA]. }
  assert (IA3 : PM.iss_at RSEGS PMA.AD PMSPA.accA M3 ois str sm).
  { apply (PMKA.iss_keepA RSEGS PMA.AD L ar LB FF sp 24576 [] M M3 EK03f PMKA.wapp_nil FRB BRB ois str sm); [| | intros i _ r0 []| intros c n p _ i _ r0 []| exact IA].
    - apply (PNAPAR.aobj_fbB FF fb ois 272 FOK); unfold ois; clear; lia.
    - unfold LB. apply incl_appr. exact INCS. }
  assert (VIS3' : PMSPA.visitor_at RSEGS PMA.AD M3 ov).
  { apply (PMKA.visitor_keepA RSEGS PMA.AD L ar LB FF sp 24576 [] M M3 EK03f PMKA.wapp_nil FRB ov); [| intros i _ r0 []| exact VIS].
    apply (PNAPAR.aobj_fbB FF fb ov 8 FOK); unfold ov; clear; lia. }
  assert (EC3 : PMSPA.ec_at RSEGS M3 oec e cat).
  { apply (PMKA.ec_keepA RSEGS L ar LB FF sp 24576 [] M M3 EK03f PMKA.wapp_nil FRB oec e cat); [| intros i _ r0 []| exact EC].
    apply (PNAPAR.aobj_fbB FF fb oec 16 FOK); unfold oec; clear; lia. }
  assert (BASE3 : PMSTA.base_okA RSEGS PMA.AD M3) by (apply (PMASK.base_keep L ar C LY LB FF sp 24576 [] M M3 EK03f); [intros a _ r0 []| exact BASE]).
  assert (ERR3 : PNSTA.berr_okA RSEGS PMA.AD PMA.AAD PMA.AN M3 ax).
  { apply (PNSTA.berr_okA_frame RSEGS PMA.AD PMA.AAD PMA.AN PMA.addrs_wf_B M M3); [| exact ERR].
    intros a Ha D. apply EK03f. split; [exact Ha|]. split; [| intros r0 []]. unfold aclient, aclient_g. right; right; left.
    pose proof (depA_img a D). rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia| exact (PMA.ly_static L C LY a D)]. }
  assert (AV4 : avis H2 (F / 8 + 2147450880) 1) by (apply (L5A.avis_sub H2 (F / 8 + SB) 8); [exact VSH| unfold SB; clear; lia| unfold SB; clear; lia]).
  assert (R4a : 0 <= F / 8 + 2147450880) by (clear - Q3; lia).
  assert (R4b : F / 8 + 2147450880 + 1 <= 2 ^ 64) by (clear - Q3; pose proof (Z.div_le_upper_bound F 8 17592186044408 ltac:(lia) ltac:(lia)); lia).
  pose proof (L5A.u8_at_vis H2 M3 (F / 8 + 2147450880) 241 AV4 R4a R4b) as UV. rewrite VIS3 in UV.
  assert (U8c : L5.u8_at RSEGS M3 (F / 8 + 2147450880) 241) by (apply (proj1 UV); exact SH0). clear UV.
  (* [comment removed for export] *)
  assert (PRE3 : PNRA.brun_pre RSEGS PMA.AD PMA.AN PMA.AAD M3 fb s str sm ax).
  { refine (PNBKA.pre_after_call L ar LB FF sp 24576 [] M M3 fb s s str sm sm ax ax FRB EK03f PMKA.wapp_nil FOK _ RPRE PA3 IA3 GROW BASE3 ERR3). intros i _ rr []. }
  assert (LM3 : en_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK2 Aw s sm ax cr).
  { unfold en_mem. split; [exact BI3|]. split; [exact PRE3|]. split; [apply PNBKA.src_step_refl|]. split; [apply PNST.bax_le_refl|].
    split; [apply PNBKA.credit_keep_refl|]. split; [exact U8c| reflexivity]. }
  unfold op, ov, oec, ois in *. clear op ov oec ois.
  assert (R3gp : getr R3 (reg 3) = getr R (reg 3)) by (rewrite (KS3 3%nat) by inl; rewrite (R2c 3%nat) by inl; apply R1c; inl).
  assert (R3tp : getr R3 (reg 4) = getr R (reg 4)) by (rewrite (KS3 4%nat) by inl; rewrite (R2c 4%nat) by inl; apply R1c; inl).
  (* [comment removed for export] *)
  pose proof (PNAENK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK2 Aw s sm ax cr CTX G LM3)
    as (PFq & OWNq & SVq & U8vq & WRopq & U8opq & SVrq).
  pose proof BI3 as (HHq & _).
  pose proof PRE3 as (PAq & _ & _ & _ & OACCq & _).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in PAq, OACCq. change (PNRA.o_is PMA.AD fb) with (fb + 96) in PAq. change (PNM.PSIZE + 8) with 424 in OACCq.
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ FF' LK2 cr Aw M3 model3 fb _ s HHq FOK' PAq OACCq) as (_ & _ & _ & _ & OVISq & _).
  pose proof PAq as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NBq & _). change (fb + 464 + PNM.OFF_NB) with (fb + 464 + 344) in NBq.
  set (MVq := mrestrict (ahid Aw model3) M3) in *.
  unfold pfacts in PFq. destruct PFq as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32 & pf33 & pf34).
  assert (E2 : getr R3 (reg 2) = Z_to_bv 64 (sp - 128)) by (rewrite (KS3 2%nat) by inl; exact B2R).
  assert (E8 : getr R3 (reg 8) = Z_to_bv 64 sp) by (rewrite (KS3 8%nat) by inl; exact B8R).
  assert (E9 : getr R3 (reg 9) = Z_to_bv 64 (sp - 128)) by (rewrite (KS3 9%nat) by inl; exact B9R).
  assert (E19 : getr R3 (reg 19) = Z_to_bv 64 (fb + 464)) by (rewrite (KS3 19%nat) by inl; exact B19R).
  assert (E20 : getr R3 (reg 20) = Z_to_bv 64 (fb + 1024)) by (rewrite (KS3 20%nat) by inl; exact B20R).
  assert (E21 : getr R3 (reg 21) = Z_to_bv 64 (fb + 432)) by (rewrite (KS3 21%nat) by inl; exact B21R).
  assert (E23 : getr R3 (reg 23) = Z_to_bv 64 ty) by (rewrite (KS3 23%nat) by inl; exact B23R).
  assert (E25 : getr R3 (reg 25) = Z_to_bv 64 2147450880) by (rewrite (KS3 25%nat) by inl; exact B25R).
  assert (Q34 : 0 <= fb + 432 < 2 ^ 64) by (clear - pf7; lia).
  assert (Q36 : 0 <= fb + 1024 < 2 ^ 64) by (clear - pf7; lia).
  assert (WR2 : L5.writable RSEGS MVq (fb + 464 + 344) 2) by (apply (L5.writable_sub RSEGS MVq (fb + 464) 424); [exact WRopq| clear; lia| clear; lia]).
  assert (WR8 : L5.writable RSEGS MVq (fb + 464 + 352) 8) by (apply (L5.writable_sub RSEGS MVq (fb + 464) 424); [exact WRopq| clear; lia| clear; lia]).
  pose proof (nfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK2 Aw s sm ax cr CTX G LM3) as (NFq & _).
  destruct (PNM.b_nb s) as [n|c n p] eqn:ENB.
  - (* [comment removed for export] *)
    destruct NBq as (Dnb & Anb & (Hn & U8n)).
    assert (U8v : L5.u8_at RSEGS MVq (fb + 464 + 344) (2 * n)).
    { apply (proj2 (L5A.u8_at_vis _ M3 (fb + 464 + 344) (2 * n) (OVISq (fb + 464 + 344) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - pf7; lia) ltac:(clear - pf7; lia))). exact U8n. }
    assert (Q42 : 0 <= 2 * n < 2 ^ 64) by (clear - Hn; lia).
    assert (Q42' : 0 <= 2 * n <= 255) by (clear - Hn; lia).
    assert (TB0 : Z.testbit (2 * n) 0 = false) by (apply Z.testbit_even_0).
    LeanFeed.pfeed P (PNAENP.aenCS_conc fx3 R3 MVq (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 35%nat => ty | 36%nat => fb + 1024 | 42%nat => 2 * n | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNAENP.aligned; assumption]).
    destruct P as (fx4 & R4 & M4v & MG4 & _ & FRZ4 & MS4 & KS4 & Z1 & Z10 & Z11 & Z12 & NB0 & NB1 & SPv).
    apply (PNAENK.en_piece_nb L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK2 Aw s sm ax cr fx3 fx4 R3 R4 0xaf658 0xb2cd0 M4v
             (fun a => sp - 112 <= a < sp - 112 + 8 \/ fb + 464 + 344 <= a < fb + 464 + 344 + 2) (PM.VShort 0) CTX G LM3 MS4 MG4).
    { intros a Ha N. apply FRZ4; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
    { intros a [X|X]; [right; right; clear - X; lia| left; clear - X; lia]. }
    { rewrite ENB. reflexivity. }
    { destruct GROW as (G1 & _). rewrite ENB in G1. exact G1. }
    { rewrite ENB. reflexivity. }
    { intros M5 FR5 MG5 VIS5. unfold PM.vstr_at. split; [exact (L5.defined_grows M3 M5 _ _ MG5 Dnb)|]. split.
      - apply (PMFA.accA_agree M3 M5 (fb + 464 + 344) 24); [| exact Anb].
        intros x Hx. unfold S, SB. apply FR5.
        + pose proof (Z.div_pos x 8 ltac:(clear - Hx pf7; lia) ltac:(clear; lia)). pose proof (Z.div_lt_upper_bound x 8 17592186044416 ltac:(clear; lia) ltac:(clear - Hx pf7; lia)). lia.
        + pose proof (Z.div_pos x 8 ltac:(clear - Hx pf7; lia) ltac:(clear; lia)) as D0. pose proof (Z.div_lt_upper_bound x 8 17592186044416 ltac:(clear; lia) ltac:(clear - Hx pf7; lia)) as D1.
          intros [X|X]; [clear - X D0 D1 pf4; lia| clear - X D0 D1 pf9; lia].
      - split; [clear; lia|]. change (2 * 0) with 0.
        apply (proj1 (L5A.u8_at_vis _ M5 (fb + 464 + 344) 0 (OVISq (fb + 464 + 344) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - pf7; lia) ltac:(clear - pf7; lia))).
        rewrite VIS5. exact NB0. }
    intros M5 model5 LM5 HID5 VIS5 FR5 MG5 ECK5.
    assert (SPL5 : spill M5 sp F).
    { pose proof (PNAENK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK2 Aw _ sm ax cr CTX G LM5) as (_ & _ & _ & _ & _ & _ & SVr5).
      unfold spill. apply (SVr5 (sp - 112) F ltac:(clear; lia) ltac:(clear; lia)). rewrite HID5, VIS5. exact SPv. }
    assert (RK : forall k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R4 (reg k) = getr R3 (reg k)).
    { intros k Hk. apply KS4. revert k Hk. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
    change 0xb2cd0 with (PNL.pn_read_cstring PMA.AN).
    apply (en_body K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK2 Aw _ sm ax cr fx4 R4 ty RCS VAL MKE CTX G LM5).
    + unfold PNRA.binv. rewrite PNBKA.set_cs_done, PNBKA.set_cs_stk. exact INV.
    + exact (ECK5 _ _ EC3).
    + unfold PNRA.btop_pos. rewrite PNBKA.set_cs_stk. exact (PNBKA.btop_pos_refl s INV).
    + pose proof (PNBKA.set_cs_str 0 s (PM.VShort 0) (PNM.b_ng s)) as X. unfold PNRA.bcs_str in X. cbn [Z.eqb] in X. rewrite X. reflexivity.
    + rewrite PNBKA.set_cs_src. reflexivity.
    + exact SPL5.
    + exact Hty.
    + unfold eregs.
      split; [rewrite (RK 2%nat) by inl; exact E2|]. split; [rewrite (RK 3%nat) by inl; exact R3gp|]. split; [rewrite (RK 4%nat) by inl; exact R3tp|].
      split; [rewrite (RK 8%nat) by inl; exact E8|]. split; [rewrite (RK 9%nat) by inl; exact E9|].
      split; [rewrite (RK 18%nat) by inl; exact Y18|]. split; [rewrite (RK 19%nat) by inl; exact E19|]. split; [rewrite (RK 20%nat) by inl; exact E20|].
      split; [rewrite (RK 21%nat) by inl; exact E21|]. split; [rewrite (RK 22%nat) by inl; exact Y22|]. split; [rewrite (RK 23%nat) by inl; exact E23|].
      split; [rewrite (RK 24%nat) by inl; exact Y24|]. split; [rewrite (RK 25%nat) by inl; exact E25|]. split; [rewrite (RK 26%nat) by inl; exact Y26|].
      rewrite (RK 27%nat) by inl; exact Y27.
    + exact Z1.
    + exact Z10.
    + exact Z11.
    + exact Z12.
  - (* [comment removed for export] *)
    destruct NBq as (Dnb & Anb & (U0 & U8n & U16 & Hn & Hc & He & Dp & Ap)).
    cbn [nfacts] in NFq. destruct NFq as (nf1 & nf2 & nf3 & nf4 & nf5 & nf6 & nf7 & nf8 & nf9 & nf10 & nf11 & nf12 & _ & _ & _ & Hpc).
    pose proof (Z.mod_pos_bound (c + 1) 256 ltac:(clear; lia)) as MB.
    assert (Q42 : 0 <= (c + 1) mod 256 < 2 ^ 64) by (clear - MB; lia).
    assert (Q42' : 0 <= (c + 1) mod 256 <= 255) by (clear - MB; lia).
    assert (TB0 : Z.testbit ((c + 1) mod 256) 0 = true) by (apply tb0_long; [clear - Hc; lia| exact He]).
    assert (Q43 : 0 <= p < 2 ^ 64) by (clear - nf3; lia).
    LeanFeed.pfeed P (PNAENP.aenCL_conc fx3 R3 MVq (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 35%nat => ty | 36%nat => fb + 1024 | 42%nat => (c + 1) mod 256 | 43%nat => p | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNAENP.aligned; assumption]).
    destruct P as (fx4 & R4 & M4v & MG4 & _ & FRZ4 & MS4 & KS4 & Z1 & Z10 & Z11 & Z12 & SZ0 & D0 & SPv).
    apply (PNAENK.en_piece_nb L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK2 Aw s sm ax cr fx3 fx4 R3 R4 0xaf658 0xb2cd0 M4v
             (fun a => sp - 112 <= a < sp - 112 + 8 \/ p <= a < p + 1 \/ fb + 464 + 352 <= a < fb + 464 + 352 + 8) (PM.VLong c 0 p) CTX G LM3 MS4 MG4).
    { intros a Ha N. apply FRZ4; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; left; clear - X; lia| intros X; apply N; right; right; exact X]. }
    { intros a [X|[X|X]]; [right; right; clear - X; lia| right; left; exists p, c; split; [rewrite ENB; left; reflexivity| clear - X Hc; lia]| left; clear - X; lia]. }
    { rewrite ENB. reflexivity. }
    { destruct GROW as (G1 & _). rewrite ENB in G1. exact G1. }
    { rewrite ENB. reflexivity. }
    { intros M5 FR5 MG5 VIS5. unfold PM.vstr_at.
      assert (SHK : forall x, 0 <= x < 2 ^ 47 -> M5 (Z_to_bv 64 (x / 8 + 2147450880)) = M3 (Z_to_bv 64 (x / 8 + 2147450880))).
      { intros x Hx. pose proof (Z.div_pos x 8 ltac:(clear - Hx; lia) ltac:(clear; lia)) as D0'. pose proof (Z.div_lt_upper_bound x 8 17592186044416 ltac:(clear; lia) ltac:(clear - Hx; lia)) as D1'.
        apply FR5; [clear - D0' D1'; lia|]. intros [X|[X|X]]; [clear - X D0' D1' pf4; lia| clear - X D0' D1' nf4; lia| clear - X D0' D1' pf9; lia]. }
      split; [exact (L5.defined_grows M3 M5 _ _ MG5 Dnb)|]. split.
      - apply (PMFA.accA_agree M3 M5 (fb + 464 + 344) 24); [| exact Anb]. intros x Hx. unfold S, SB. apply SHK. clear - Hx pf7; lia.
      - split. { apply (L5C.u64_at_agree RSEGS M3 M5 (fb + 464 + 344) (c + 1)); [| clear - pf7; lia| clear - pf7; lia| exact U0].
                 intros j Hj. apply FR5; [clear - Hj pf7; lia|]. intros [X|[X|X]]; [clear - X Hj pf14; lia| clear - X Hj nf10; lia| clear - X Hj; lia]. }
        split. { replace (fb + 464 + 344 + 8) with (fb + 464 + 352) by (clear; lia).
                 apply (proj1 (L5A.u64_at_vis _ M5 (fb + 464 + 352) 0 (OVISq (fb + 464 + 352) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - pf7; lia) ltac:(clear - pf7; lia))).
                 rewrite VIS5. exact SZ0. }
        split. { apply (L5C.u64_at_agree RSEGS M3 M5 (fb + 464 + 344 + 16) p); [| clear - pf7; lia| clear - pf7; lia| exact U16].
                 intros j Hj. apply FR5; [clear - Hj pf7; lia|]. intros [X|[X|X]]; [clear - X Hj pf14; lia| clear - X Hj nf10; lia| clear - X Hj; lia]. }
        split; [clear - Hc; lia|]. split; [exact Hc|]. split; [exact He|].
        split; [exact (L5.defined_grows M3 M5 _ _ MG5 Dp)|].
        apply (PMFA.accA_agree M3 M5 p c); [| exact Ap]. intros x Hx. unfold S, SB. apply SHK. clear - Hx nf3 Hpc; lia. }
    intros M5 model5 LM5 HID5 VIS5 FR5 MG5 ECK5.
    assert (SPL5 : spill M5 sp F).
    { pose proof (PNAENK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK2 Aw _ sm ax cr CTX G LM5) as (_ & _ & _ & _ & _ & _ & SVr5).
      unfold spill. apply (SVr5 (sp - 112) F ltac:(clear; lia) ltac:(clear; lia)). rewrite HID5, VIS5. exact SPv. }
    assert (RK : forall k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R4 (reg k) = getr R3 (reg k)).
    { intros k Hk. apply KS4. revert k Hk. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
    change 0xb2cd0 with (PNL.pn_read_cstring PMA.AN).
    apply (en_body K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK2 Aw _ sm ax cr fx4 R4 ty RCS VAL MKE CTX G LM5).
    + unfold PNRA.binv. rewrite PNBKA.set_cs_done, PNBKA.set_cs_stk. exact INV.
    + exact (ECK5 _ _ EC3).
    + unfold PNRA.btop_pos. rewrite PNBKA.set_cs_stk. exact (PNBKA.btop_pos_refl s INV).
    + pose proof (PNBKA.set_cs_str 0 s (PM.VLong c 0 p) (PNM.b_ng s)) as X. unfold PNRA.bcs_str in X. cbn [Z.eqb] in X. rewrite X. reflexivity.
    + rewrite PNBKA.set_cs_src. reflexivity.
    + exact SPL5.
    + exact Hty.
    + unfold eregs.
      split; [rewrite (RK 2%nat) by inl; exact E2|]. split; [rewrite (RK 3%nat) by inl; exact R3gp|]. split; [rewrite (RK 4%nat) by inl; exact R3tp|].
      split; [rewrite (RK 8%nat) by inl; exact E8|]. split; [rewrite (RK 9%nat) by inl; exact E9|].
      split; [rewrite (RK 18%nat) by inl; exact Y18|]. split; [rewrite (RK 19%nat) by inl; exact E19|]. split; [rewrite (RK 20%nat) by inl; exact E20|].
      split; [rewrite (RK 21%nat) by inl; exact E21|]. split; [rewrite (RK 22%nat) by inl; exact Y22|]. split; [rewrite (RK 23%nat) by inl; exact E23|].
      split; [rewrite (RK 24%nat) by inl; exact Y24|]. split; [rewrite (RK 25%nat) by inl; exact E25|]. split; [rewrite (RK 26%nat) by inl; exact Y26|].
      rewrite (RK 27%nat) by inl; exact Y27.
    + exact Z1.
    + exact Z10.
    + exact Z11.
    + exact Z12.
Qed.
End WithHeap.
End PNACEN.
