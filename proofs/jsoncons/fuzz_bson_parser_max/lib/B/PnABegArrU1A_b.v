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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnABegArrU1E_b PnABegArrU1V_b.

Module PNABAU1A.
Import L5A. Import L5CA. Import L5SAR. Import PNBKA. Import PNABAK. Import PNABA.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

Lemma ba_u1_abaU_ok' K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 :
  ba_u1_abaU_P L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2.
Proof using LY HIok ICok ILY.
  unfold ba_u1_abaU_P.
  intros s6 sm6 ax6 cr6 M1 model1 LK1 Aw1 fx1 R1 fx2 R2 M3 model3 LK3 Aw3 CTX G LM
    Q1 Q2 Q8 Q9 Q10 Q18 Q19 Q3 Q4 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27
    S208 S216 S224 S200 S192 S184 S176 S168 S120 S112 SPL S144 S136 EC1
    BI6 STK6 LEN6 CAP6 UNR6 RP V392 V400 V408 STS DEF3 ACC3 ANN3 ACCO BASE3 AHP MRT3 INC3 INCA3 AM3 HH3 KONT.
  pose proof (PNABAU1E.ba_u1_elem_ok L ar C IL HI LY HIok ICok ILY K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2
                s6 sm6 ax6 cr6 M1 model1 LK1 Aw1 M3 model3 LK3 Aw3 CTX G LM BI6 STK6 LEN6 CAP6 V392 V400 V408 STS DEF3 ACC3 ANN3 ACCO BASE3 AHP
                MRT3 INC3 INCA3 AM3 HH3) as EL.
  assert (VS : PNABAU1V.m3vis (mrestrict (ahid Aw3 model3) M3) sp (fb + 464) (PNM.b_sb (PNBO.set_more s6 1))
                 (40 * Z.of_nat (length (PNM.b_stk (PNBO.set_more s6 1)))) F fl)
    by (eapply PNABAU1V.ba_u1_m3vis_ok; eassumption).
  pose proof CTX as (_ & _ & _ & _ & ENT & _ & _ & FOK & _).
  destruct ENT as (_ & _ & _ & _ & _ & ASTK & _). pose proof ASTK as (_ & SLO & SHI & SPT & _).
  assert (SC : 256 <= PMSPA.pm_scr 7) by (vm_compute; intros X; discriminate X).
  pose proof FOK as ((rs & Hfb) & _).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH3) as (_ & WF & _).
  pose proof (WF _ (or_intror Hfb)) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in F1, F2.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ LK3 cr6 Aw3 M3 model3 HH3) as (_ & _ & _ & VFS & VBLK & _).
  cbv zeta in VFS, VBLK.
  set (FF' := (F, 0, sp - 160 + 32) :: FF) in *.
  set (H3 := ahid Aw3 model3) in *. set (MV := mrestrict H3 M3) in *.
  set (s7 := PNBO.set_more s6 1) in *.
  set (b := PNM.b_sb s7) in *. set (n40 := 40 * Z.of_nat (length (PNM.b_stk s7))) in *. set (c40 := 40 * 2 ^ PNM.b_sk s7) in *.
  set (op := fb + 464) in *.
  unfold PNABAU1V.m3vis in VS.
  destruct VS as (M208 & M216 & M224 & M200 & M192 & M184 & M176 & M168 & M120 & MIMG & MSH & MSH1 & SPB & SPAL & SPW & OPB & OPAL & OPSH
                  & OPZ0 & OPZ10 & OPZ312 & OPZ392 & OPST & FB & FAL & FDEF & FWR & FSH & FSW & FFL & FLB & FLW & FLSH & FFLD & FST & FLST
                  & OPF & OPFL & OPFS & M136 & M144 & SPW4 & MAG & OPW & OPS4 & M112).
  destruct EL as (E392 & E400 & E408 & Bb & ALb & Bn & ALn & Bc & ALc & ZSP & ZE5 & WE & ALE & ZE8 & ZE16 & ZE24 & ZE32 & SDE & STE & FE & FLE
                  & BE & IME & S4E & OPE).
  assert (NC : n40 + 40 <= c40) by (unfold n40, c40; clear - CAP6; lia).
  assert (OPD : op = fb + 464) by reflexivity.
  assert (I2 : 0 <= sp < 2 ^ 64) by (clear - SPB; lia).
  assert (I33 : 0 <= op < 2 ^ 64) by (clear - OPB; lia).
  assert (I34 : 0 <= fb + 432 < 2 ^ 64) by (clear - OPB OPD; lia).
  assert (I41 : 0 <= b < 2 ^ 64) by (clear - Bb; lia).
  assert (I42 : 0 <= n40 < 2 ^ 64) by (clear - Bn; lia).
  assert (I43 : 0 <= c40 < 2 ^ 64) by (clear - Bc; lia).
  assert (I50 : 0 <= F < 2 ^ 64) by (clear - FB; lia).
  assert (I51 : 0 <= fl < 2 ^ 64) by (clear - FLB; lia).
  assert (LT : (b + n40) mod 2 ^ 64 < (b + c40) mod 2 ^ 64).
  { rewrite !Z.mod_small by (clear - Bb Bn Bc; lia). clear - NC; lia. }
  rewrite <- (L5SAR.cs_of_preserved R1 R2 2%nat RP) in Q2 by inl.
  rewrite <- (L5SAR.cs_of_preserved R1 R2 3%nat RP) in Q3 by inl.
  rewrite <- (L5SAR.cs_of_preserved R1 R2 4%nat RP) in Q4 by inl.
  rewrite <- (L5SAR.cs_of_preserved R1 R2 8%nat RP) in Q8 by inl.
  rewrite <- (L5SAR.cs_of_preserved R1 R2 9%nat RP) in Q9 by inl.
  rewrite <- (L5SAR.cs_of_preserved R1 R2 18%nat RP) in Q18 by inl.
  rewrite <- (L5SAR.cs_of_preserved R1 R2 19%nat RP) in Q19 by inl.
  rewrite <- (L5SAR.cs_of_preserved R1 R2 20%nat RP) in Q20 by inl.
  rewrite <- (L5SAR.cs_of_preserved R1 R2 21%nat RP) in Q21 by inl.
  rewrite <- (L5SAR.cs_of_preserved R1 R2 22%nat RP) in Q22 by inl.
  rewrite <- (L5SAR.cs_of_preserved R1 R2 23%nat RP) in Q23 by inl.
  rewrite <- (L5SAR.cs_of_preserved R1 R2 24%nat RP) in Q24 by inl.
  rewrite <- (L5SAR.cs_of_preserved R1 R2 25%nat RP) in Q25 by inl.
  rewrite <- (L5SAR.cs_of_preserved R1 R2 26%nat RP) in Q26 by inl.
  rewrite <- (L5SAR.cs_of_preserved R1 R2 27%nat RP) in Q27 by inl.
  LeanFeed.pfeed P (PNABAP.abaU_conc fx2 R2 MV (fun j => match j with 2%nat => sp | 33%nat => op | 34%nat => fb + 432 | 41%nat => b
                                                 | 42%nat => n40 | 43%nat => c40 | 50%nat => F | 51%nat => fl | _ => 0 end))
    ltac:(first [assumption | unfold PNABAP.aligned; assumption]).
  destruct P as (fx' & R' & M' & MG' & _ & FRZ & MS & KS & T1 & T2 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & T18 & T19
                 & T20 & T21 & T22 & T23 & T24 & T25 & T26 & T27 & W400 & W32 & W24 & W16 & W0).
  assert (BIN : In (b, c40) (PNM.bvec_own b (PNM.b_sk s7) ++ rest_own s7 ++ LBX)) by (apply in_or_app; left; left; reflexivity).
  unfold PMSP.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF' LK3 cr6 Aw3 M3 model3 fx2 fx' R2 _ R' _ M'
           (fun a => b + n40 <= a < b + n40 + 40 \/ op + 400 <= a < op + 400 + 8 \/ sp - 256 <= a < sp - 160) K HH3 AM3 MS MG').
  { intros a Ha N. apply FRZ; [exact Ha| intros X; apply N; right; right; clear - X; lia| intros X; apply N; left; clear - X; lia
                               | intros X; apply N; right; left; clear - X; lia]. }
  { intros a Ha Wa. cbv beta in Wa. split.
    - destruct Wa as [X|[X|X]].
      + unfold aclientw, aclient_g. left. exists (b, c40). split; [exact BIN| cbn [fst snd]; clear - X NC Bn; lia].
      + apply (L5SAR.fframe_client L ar _ FF' 0 0 fb 5 rs); [right; exact Hfb| change (ff_bytes 5) with 2048; clear - X OPD; lia].
      + unfold aclientw, aclient_g. right; left. split; [clear - X SLO SHI SPT SC; lia| intros Y; clear - Y; lia].
    - destruct Wa as [X|[X|X]]; [clear - X IME; lia| clear - X OPB; lia| clear - X SPB; lia]. }
  intros M7 model7 HH7 AM7 MRT7 HID7 VIS7 MG7 FR7 _. change (mrestrict H3 M7 = M') in VIS7.
  rewrite <- VIS7 in W400, W32, W24, W16, W0.
  apply (KONT fx' R' M7 model7 HH7 AM7 MRT7 HID7 MG7).
  - intros a Ha N. exact (FR7 a Ha N).
  - exact (proj1 (L5A.u32_at_vis H3 M7 (b + n40) 3 (VBLK b c40 (b + n40) 4 BIN ltac:(clear - Bn; lia) ltac:(clear - NC; lia)) ltac:(clear - BE; lia) ltac:(clear - BE; lia)) W0).
  - exact (proj1 (L5A.u64_at_vis H3 M7 (b + n40 + 16) 4 (VBLK b c40 (b + n40 + 16) 8 BIN ltac:(clear - Bn; lia) ltac:(clear - NC; lia)) ltac:(clear - BE; lia) ltac:(clear - BE; lia)) W16).
  - exact (proj1 (L5A.u8_at_vis H3 M7 (b + n40 + 24) 0 (VBLK b c40 (b + n40 + 24) 1 BIN ltac:(clear - Bn; lia) ltac:(clear - NC; lia)) ltac:(clear - BE; lia) ltac:(clear - BE; lia)) W24).
  - exact (proj1 (L5A.u64_at_vis H3 M7 (b + n40 + 32) 0 (VBLK b c40 (b + n40 + 32) 8 BIN ltac:(clear - Bn; lia) ltac:(clear - NC; lia)) ltac:(clear - BE; lia) ltac:(clear - BE; lia)) W32).
  - exact (proj1 (L5A.u64_at_vis H3 M7 (op + 400) (b + n40 + 40) (VFS (op + 400) 8 ltac:(clear - F1 OPD; lia) ltac:(clear - F2 OPD; lia)) ltac:(clear - OPB; lia) ltac:(clear - OPB; lia)) W400).
  - unfold tregs.
    split; [exact T2|]. split; [rewrite (KS 3%nat) by inl; exact Q3|]. split; [rewrite (KS 4%nat) by inl; exact Q4|].
    split; [exact T8|]. split; [exact T9|]. split; [exact T20|]. split; [exact T21|]. split; [exact T22|].
    split; [exact T24|]. split; [exact T25|]. split; [exact T26|]. exact T27.
  - exact T18.
  - exact T23.
  - exact T10.
Qed.

End WithHeap.
End PNABAU1A.
