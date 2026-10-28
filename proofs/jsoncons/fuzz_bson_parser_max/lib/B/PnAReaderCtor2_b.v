(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StreamSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout PmLayoutA PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PnModel PmModelFacts PmStatics PmStaticsA PnStatics PnStaticsA
     PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b PnSpecsAX_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgV8A_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b
     PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnStepA_b PnStepA2_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import XIcptAs0_b PnAReaderCtorStmts_b PnAReaderCtorP_b PnAIss1_b PnAReaderCtor1_b PnAReaderCtorKit_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import XIcptA_b XIcptAs0Kit_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia.
Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac dlia := first [ solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_ne ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_ne end ]
                   | solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_st ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_st end ] ].
Local Ltac lia := dlia.
Module PNARC2.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

Theorem memsets : forall (fx : FPState) R0 M0 model0 K LB FF LK0 Aw0 cr sp r fb oo oa str sm R1 M1 model1 LK1 Aw1,
    PNARCS.pre L ar HI R0 M0 model0 K LB FF LK0 Aw0 cr sp r fb oo oa str sm ->
    PNARCS.rmid1 L ar HI R0 M0 model0 LB FF LK0 Aw0 cr sp fb oo R1 M1 model1 LK1 Aw1 ->
    (forall (fx2 : FPState) R2 M2 model2 LK2 Aw2, PNARCS.rmid2 L ar HI R0 M0 model0 LB FF LK0 Aw0 cr sp fb oo R2 M2 model2 LK2 Aw2 ->
        srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx2) R2 0xacc4c M2 model2) K) ->
    srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R1 0xace24 M1 model1) K.
Proof.
  intros fx R0 M0 model0 K LB FF LK0 Aw0 cr sp r fb oo oa str sm R1 M1 model1 LK1 Aw1 PRE MID KONT.
  destruct PRE as (HH0 & AM0 & K0 & ENT & FRM & FRS & FOK & A10 & A11 & A12 & A13 & AOO & OOAP & OO8 & ODEF0 & ACC0 & ACCO0 & OO0' & OO16' & ISS & BASE0 & LOCb & CRED).
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK0 & STKSH0). rewrite L5K.rl4 in Rtp.
  destruct MID as (M2' & M8 & M9 & M18 & M19 & M20 & M21 & M22 & M23 & MCSK & IVP & IRD & SNIS & MC).
  destruct MC as (SRD & SSRC & HC & ODEF & ACC & ACCO & OO0 & OO16 & ACCI & ASTK & STKSH & BASE & LOC & HH & AM & MRT & INCK & INCA & EK & DK).
  unfold PNARCS.op, PNARCS.SCR in *. change (24576 / 8) with 3072 in STKSH.
  destruct SRD as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88). destruct SSRC as (F120 & F128 & F136 & F144 & F152).
  destruct SNIS as (F168 & F176 & F184 & F192 & F200 & F208 & F216 & F224 & F232). replace (fb + 96) with (fb + 464 - 368) in F192 by lia.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof AM as (Mh & MI).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (PNARCK.fb16 FF fb FOK) as F16.
  assert (AOP : PMSPA.aobjA FF (fb + 464) 416) by (apply (PNARCK.frame_aobj FF fb); [exact FOK| lia| lia]).
  assert (O8 : (fb + 464) mod 8 = 0) by lia.
  pose proof (PMKA.aobj_of_aobjA FF _ _ AOP O8) as AOB.
  assert (AOIS : PMSPA.aobjA FF (fb + 96) 272) by (apply (PNARCK.frame_aobj FF fb); [exact FOK| lia| lia]).
  assert (OOAP' : fb + 464 + 416 <= oo \/ oo + 24 <= fb + 464) by (destruct OOAP as [X|X]; [right|left]; Lia.lia).
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47).
  { intros f Hf. destruct (WF f Hf) as (X1 & X2 & _). unfold app_mem, FS_BYTES in *. lia. }
  assert (WAPP : PMKA.wapp [(fb + 464, 416)]).
  { pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK1 cr Aw1 M1 model1 (fb + 464) 416 sp 24576 HH AOB ltac:(lia) ltac:(reflexivity)) as (OR & OBIG & _).
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia| apply PMKA.wapp_nil]. }
  assert (CL : forall a, fb + 464 <= a < fb + 464 + 416 -> aclient L ar LB FF 0 0 a) by (intros a Ha; apply (L5SAR.obj_client L ar LB FF 0 0 _ 416 a AOB); lia).
  assert (SCL : forall a, sp - 24576 <= a < sp -> aclient L ar LB FF 0 0 a) by (intros a Ha; apply L5SAR.stack_client; lia).
  assert (CLF : forall a, fb + 32 <= a < fb + 2040 -> aclient L ar LB FF 0 0 a).
  { intros a Ha. apply (L5SAR.obj_client L ar LB FF 0 0 (fb + 32) 2008 a); [| lia].
    apply (PMKA.aobj_of_aobjA FF _ _ (PNARCK.frame_aobj FF fb (fb + 32) 2008 FOK ltac:(lia) ltac:(lia))). lia. }
  pose proof (PMAIS1.bvu (getr R0 (reg 1))) as UR1. pose proof (PMAIS1.bvu (getr R0 (reg 8))) as UR8. pose proof (PMAIS1.bvu (getr R0 (reg 9))) as UR9.
  pose proof (PMAIS1.bvu (getr R0 (reg 18))) as UR18. pose proof (PMAIS1.bvu (getr R0 (reg 19))) as UR19. pose proof (PMAIS1.bvu (getr R0 (reg 20))) as UR20.
  pose proof (PMAIS1.bvu (getr R0 (reg 21))) as UR21. pose proof (PMAIS1.bvu (getr R0 (reg 22))) as UR22. pose proof (PMAIS1.bvu (getr R0 (reg 23))) as UR23.
  (* [comment removed for export] *)
  destruct (PNARCK.vfacts L ar C IL HI LY HIok ICok ILY LB FF LK1 cr Aw1 M1 model1 sp fb oo HH FOK ASTK AOO OO8 ACC ACCI ACCO ODEF)
    as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13 & V14 & V15 & V16 & V17 & V18 & V19).
  assert (OOSTK' : sp - 4096 + 4096 <= oo \/ oo + 24 <= sp - 4096) by (right; Lia.lia).
  assert (OOIMG : 65536 + 6840320 <= oo \/ oo + 24 <= 65536) by (left; Lia.lia).
  assert (AG11 : forall a, sp - 232 <= a < sp -> M1 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by (intros; reflexivity).
  assert (Q8 : L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) (sp - 8) _) by (apply (PNARCK.svis L ar C HI LY HIok LB FF LK1 cr Aw1 M1 model1 sp (sp - 8) _ HH ASTK); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG11; lia| lia| lia| exact S8]).
  assert (Q16 : L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) (sp - 16) _) by (apply (PNARCK.svis L ar C HI LY HIok LB FF LK1 cr Aw1 M1 model1 sp (sp - 16) _ HH ASTK); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG11; lia| lia| lia| exact S16]).
  assert (Q24 : L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) (sp - 24) _) by (apply (PNARCK.svis L ar C HI LY HIok LB FF LK1 cr Aw1 M1 model1 sp (sp - 24) _ HH ASTK); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG11; lia| lia| lia| exact S24]).
  assert (Q32 : L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) (sp - 32) _) by (apply (PNARCK.svis L ar C HI LY HIok LB FF LK1 cr Aw1 M1 model1 sp (sp - 32) _ HH ASTK); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG11; lia| lia| lia| exact S32]).
  assert (Q40 : L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) (sp - 40) _) by (apply (PNARCK.svis L ar C HI LY HIok LB FF LK1 cr Aw1 M1 model1 sp (sp - 40) _ HH ASTK); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG11; lia| lia| lia| exact S40]).
  assert (Q48 : L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) (sp - 48) _) by (apply (PNARCK.svis L ar C HI LY HIok LB FF LK1 cr Aw1 M1 model1 sp (sp - 48) _ HH ASTK); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG11; lia| lia| lia| exact S48]).
  assert (Q56 : L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) (sp - 56) _) by (apply (PNARCK.svis L ar C HI LY HIok LB FF LK1 cr Aw1 M1 model1 sp (sp - 56) _ HH ASTK); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG11; lia| lia| lia| exact S56]).
  assert (Q64 : L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) (sp - 64) _) by (apply (PNARCK.svis L ar C HI LY HIok LB FF LK1 cr Aw1 M1 model1 sp (sp - 64) _ HH ASTK); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG11; lia| lia| lia| exact S64]).
  assert (Q72 : L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) (sp - 72) _) by (apply (PNARCK.svis L ar C HI LY HIok LB FF LK1 cr Aw1 M1 model1 sp (sp - 72) _ HH ASTK); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG11; lia| lia| lia| exact S72]).
  assert (TQ : forall a v, sp - 232 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1 a v -> L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) a v)
    by (intros a v Ha Hb X; apply (PNARCK.svis L ar C HI LY HIok LB FF LK1 cr Aw1 M1 model1 sp a v HH ASTK); [lia| lia| exact X]).
  pose proof (TQ (sp - 120) _ ltac:(lia) ltac:(lia) F120) as Q120. pose proof (TQ (sp - 128) _ ltac:(lia) ltac:(lia) F128) as Q128.
  pose proof (TQ (sp - 136) _ ltac:(lia) ltac:(lia) F136) as Q136. pose proof (TQ (sp - 144) _ ltac:(lia) ltac:(lia) F144) as Q144.
  pose proof (TQ (sp - 152) _ ltac:(lia) ltac:(lia) F152) as Q152. pose proof (TQ (sp - 168) _ ltac:(lia) ltac:(lia) F168) as Q168.
  pose proof (TQ (sp - 176) _ ltac:(lia) ltac:(lia) F176) as Q176. pose proof (TQ (sp - 184) _ ltac:(lia) ltac:(lia) F184) as Q184.
  pose proof (TQ (sp - 192) _ ltac:(lia) ltac:(lia) F192) as Q192. pose proof (TQ (sp - 200) _ ltac:(lia) ltac:(lia) F200) as Q200.
  pose proof (TQ (sp - 208) _ ltac:(lia) ltac:(lia) F208) as Q208. pose proof (TQ (sp - 216) _ ltac:(lia) ltac:(lia) F216) as Q216.
  pose proof (TQ (sp - 224) _ ltac:(lia) ltac:(lia) F224) as Q224. pose proof (TQ (sp - 232) _ ltac:(lia) ltac:(lia) F232) as Q232.
  LeanFeed.pfeed P (PNARCP.abrcC_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx R1 (mrestrict (ahid Aw1 model1) M1) (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => oo | 43%nat => bv_unsigned (getr R0 (reg 1)) | 44%nat => bv_unsigned (getr R0 (reg 8)) | 45%nat => bv_unsigned (getr R0 (reg 9)) | 46%nat => bv_unsigned (getr R0 (reg 18)) | 47%nat => bv_unsigned (getr R0 (reg 19)) | 48%nat => bv_unsigned (getr R0 (reg 20)) | 49%nat => bv_unsigned (getr R0 (reg 21)) | 50%nat => bv_unsigned (getr R0 (reg 22)) | 51%nat => bv_unsigned (getr R0 (reg 23)) | _ => 0 end)) ltac:(first [assumption | unfold PNARCP.aligned; lia | lia]).
  destruct P as (fx1 & R2 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & aR1 & aR10 & aR11 & aR12).
  assert (E1 : M1v = mrestrict (ahid Aw1 model1) M1) by (apply L5SAR.mem_eq_of_agree; exact FZ1). subst M1v.
  unfold PMSPA.cfg.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok LB FF LK1 cr Aw1 M1 model1 fx fx1 R1 0xace24 R2 0x78130 _ K HH AM MS1 MG1 FZ1).
  intros M1' model1' HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (E1' : M1' = M1) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1'.
  (* [comment removed for export] *)
  assert (RTP : forall Rx, getr Rx (reg 4) = getr R0 (reg 4) -> getr Rx (reg 4) = Z_to_bv 64 (hl_tp L)) by (intros Rx E; rewrite E; exact Rtp).
  apply (PNARCK.amset L ar C HI LY HIok LB FF LK1 cr Aw1 sp 240 (fb + 464) 416 fx1 R2 M1 model1' K 56 48 708148 AOB); [lia| lia| lia| exact HH1| exact AM1| exact ASTK| exact ACC| exact ODEF
     | lia| lia| replace (sp - 240) with (sp + (-15) * 16) by lia; rewrite Z.mod_add by lia; exact A16| exact aR10| exact aR11| exact aR12| | exact aR1| reflexivity| lia| | exact K0|].
  { apply RTP. rewrite (KS1 4%nat) by inl. apply MCSK. right; left; reflexivity. }
  { rewrite (KS1 2%nat) by inl. exact M2'. }
  intros R3 M3 model3 R3a0 RP3 Z64 PRES3 SDEF3 DEF3 MRT3 AM3 HH3.
  assert (CS3 : forall k, In k L5SAR.cs_all -> getr R3 (reg k) = getr R2 (reg k)) by (intros k Hk; apply (L5SAR.cs_of_preserved R2 R3 k RP3 Hk)).
  destruct (PNARCK.mset_post L ar C HI HIok LB FF LK1 cr Aw1 sp 240 (fb + 464) 416 M1 M3 model1' 56 48 HH1 ASTK AOB ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PRES3 SDEF3 DEF3)
    as (EK13 & DK13 & ASTK3).
  assert (ACC3 : PMSPA.accA M3 (fb + 464) 416) by (apply (PMKA.acc_keepA' L ar LB FF sp 24576 _ M1 M3 EK13 WAPP FRB _ 416 AOP ACC)).
  assert (ACCI3 : PMSPA.accA M3 (fb + 96) 272) by (apply (PMKA.acc_keepA' L ar LB FF sp 24576 _ M1 M3 EK13 WAPP FRB _ 272 AOIS ACCI)).
  assert (ACCO3 : PMSPA.accA M3 oo 24) by (apply (PMKA.acc_keepA' L ar LB FF sp 24576 _ M1 M3 EK13 WAPP FRB _ 24 AOO ACCO)).
  assert (ODEF3 : L5.defined M3 (fb + 464) 416).
  { pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK1 cr Aw1 M3 model3 (fb + 464) 416 sp 24576 HH3 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & X & _). exact X. }
  assert (AG13 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF 0 0 a -> ~ (sp - 240 - 2560 <= a < sp - 240) -> ~ (fb + 464 + 56 <= a < fb + 464 + 56 + 48) ->
                 M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha Hc N1 N2. apply PRES3; [exact Ha| apply (L5SAR.aclient_narrow L ar LB FF 0 0); [exact Hc| lia]| exact N2]. }
  assert (AG13s : forall a, sp - 232 <= a < sp -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by (intros a Ha; apply AG13; [lia| apply SCL; lia| lia| lia]).
  (* [comment removed for export] *)
  destruct (PNARCK.vfacts L ar C IL HI LY HIok ICok ILY LB FF LK1 cr Aw1 M3 model3 sp fb oo HH3 FOK ASTK3 AOO OO8 ACC3 ACCI3 ACCO3 ODEF3)
    as (W1' & W2' & W3' & W4' & W5' & W6' & W7' & W8' & W9' & W10' & _).
  assert (T8 : L5.u64_at RSEGS (mrestrict (ahid Aw1 model3) M3) (sp - 8) _) by (apply (PNARCK.svis L ar C HI LY HIok LB FF LK1 cr Aw1 M3 model3 sp (sp - 8) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13s; lia| lia| lia| exact S8]).
  assert (T16 : L5.u64_at RSEGS (mrestrict (ahid Aw1 model3) M3) (sp - 16) _) by (apply (PNARCK.svis L ar C HI LY HIok LB FF LK1 cr Aw1 M3 model3 sp (sp - 16) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13s; lia| lia| lia| exact S16]).
  assert (T24 : L5.u64_at RSEGS (mrestrict (ahid Aw1 model3) M3) (sp - 24) _) by (apply (PNARCK.svis L ar C HI LY HIok LB FF LK1 cr Aw1 M3 model3 sp (sp - 24) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13s; lia| lia| lia| exact S24]).
  assert (T32 : L5.u64_at RSEGS (mrestrict (ahid Aw1 model3) M3) (sp - 32) _) by (apply (PNARCK.svis L ar C HI LY HIok LB FF LK1 cr Aw1 M3 model3 sp (sp - 32) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13s; lia| lia| lia| exact S32]).
  assert (T40 : L5.u64_at RSEGS (mrestrict (ahid Aw1 model3) M3) (sp - 40) _) by (apply (PNARCK.svis L ar C HI LY HIok LB FF LK1 cr Aw1 M3 model3 sp (sp - 40) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13s; lia| lia| lia| exact S40]).
  assert (T48 : L5.u64_at RSEGS (mrestrict (ahid Aw1 model3) M3) (sp - 48) _) by (apply (PNARCK.svis L ar C HI LY HIok LB FF LK1 cr Aw1 M3 model3 sp (sp - 48) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13s; lia| lia| lia| exact S48]).
  assert (T56 : L5.u64_at RSEGS (mrestrict (ahid Aw1 model3) M3) (sp - 56) _) by (apply (PNARCK.svis L ar C HI LY HIok LB FF LK1 cr Aw1 M3 model3 sp (sp - 56) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13s; lia| lia| lia| exact S56]).
  assert (T64 : L5.u64_at RSEGS (mrestrict (ahid Aw1 model3) M3) (sp - 64) _) by (apply (PNARCK.svis L ar C HI LY HIok LB FF LK1 cr Aw1 M3 model3 sp (sp - 64) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13s; lia| lia| lia| exact S64]).
  assert (T72 : L5.u64_at RSEGS (mrestrict (ahid Aw1 model3) M3) (sp - 72) _) by (apply (PNARCK.svis L ar C HI LY HIok LB FF LK1 cr Aw1 M3 model3 sp (sp - 72) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13s; lia| lia| lia| exact S72]).
  assert (TT : forall a v, sp - 232 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1 a v -> L5.u64_at RSEGS (mrestrict (ahid Aw1 model3) M3) a v)
    by (intros a v Ha Hb X; apply (PNARCK.svis L ar C HI LY HIok LB FF LK1 cr Aw1 M3 model3 sp a v HH3 ASTK3); [lia| lia|];
        apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13s; lia| lia| lia| exact X]).
  pose proof (TT (sp - 120) _ ltac:(lia) ltac:(lia) F120) as T120. pose proof (TT (sp - 128) _ ltac:(lia) ltac:(lia) F128) as T128.
  pose proof (TT (sp - 136) _ ltac:(lia) ltac:(lia) F136) as T136. pose proof (TT (sp - 144) _ ltac:(lia) ltac:(lia) F144) as T144.
  pose proof (TT (sp - 152) _ ltac:(lia) ltac:(lia) F152) as T152. pose proof (TT (sp - 168) _ ltac:(lia) ltac:(lia) F168) as T168.
  pose proof (TT (sp - 176) _ ltac:(lia) ltac:(lia) F176) as T176. pose proof (TT (sp - 184) _ ltac:(lia) ltac:(lia) F184) as T184.
  pose proof (TT (sp - 192) _ ltac:(lia) ltac:(lia) F192) as T192. pose proof (TT (sp - 200) _ ltac:(lia) ltac:(lia) F200) as T200.
  pose proof (TT (sp - 208) _ ltac:(lia) ltac:(lia) F208) as T208. pose proof (TT (sp - 216) _ ltac:(lia) ltac:(lia) F216) as T216.
  pose proof (TT (sp - 224) _ ltac:(lia) ltac:(lia) F224) as T224. pose proof (TT (sp - 232) _ ltac:(lia) ltac:(lia) F232) as T232.
  assert (TI0 : L5.u64_at RSEGS (mrestrict (ahid Aw1 model3) M3) (fb + 464 - 368) 1265968).
  { replace (fb + 464 - 368) with (fb + 96) by lia. apply (PNARCK.fvis L ar C HI LY HIok LB FF LK1 cr Aw1 M3 model3 fb _ _ HH3 FOK); [lia| lia|].
    apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; [lia| apply CLF; lia| lia| lia]| lia| lia| exact IVP]. }
  assert (TI1 : L5.u64_at RSEGS (mrestrict (ahid Aw1 model3) M3) (fb + 464 - 208) (fb + 464 - 352)).
  { replace (fb + 464 - 208) with (fb + 256) by lia. replace (fb + 464 - 352) with (fb + 112) by lia.
    apply (PNARCK.fvis L ar C HI LY HIok LB FF LK1 cr Aw1 M3 model3 fb _ _ HH3 FOK); [lia| lia|].
    apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; [lia| apply CLF; lia| lia| lia]| lia| lia| exact IRD]. }
  assert (J2 : getr R3 (reg 2) = Z_to_bv 64 (sp - 240)) by (rewrite CS3, (KS1 2%nat) by inl; exact M2').
  assert (J8 : getr R3 (reg 8) = Z_to_bv 64 (fb + 464 + 24)) by (rewrite CS3, (KS1 8%nat) by inl; exact M8).
  assert (J9 : getr R3 (reg 9) = Z_to_bv 64 (fb + 464 + 104)) by (rewrite CS3, (KS1 9%nat) by inl; exact M9).
  assert (J18 : getr R3 (reg 18) = Z_to_bv 64 (fb + 464 + 40)) by (rewrite CS3, (KS1 18%nat) by inl; exact M18).
  assert (J19 : getr R3 (reg 19) = Z_to_bv 64 ((fb + 464 + 40) / 8 + 2147450880)) by (rewrite CS3, (KS1 19%nat) by inl; exact M19).
  assert (J20 : getr R3 (reg 20) = Z_to_bv 64 0x131ab8) by (rewrite CS3, (KS1 20%nat) by inl; exact M20).
  assert (J21 : getr R3 (reg 21) = Z_to_bv 64 ((fb + 464 + 24) / 8 + 2147450880)) by (rewrite CS3, (KS1 21%nat) by inl; exact M21).
  assert (J22 : getr R3 (reg 22) = Z_to_bv 64 0x131ad0) by (rewrite CS3, (KS1 22%nat) by inl; exact M22).
  assert (J23 : getr R3 (reg 23) = Z_to_bv 64 ((fb + 464 + 104) / 8 + 2147450880)) by (rewrite CS3, (KS1 23%nat) by inl; exact M23).
  LeanFeed.pfeed P (PNARCP.abrcD_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx1 R3 (mrestrict (ahid Aw1 model3) M3) (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => oo | 43%nat => bv_unsigned (getr R0 (reg 1)) | 44%nat => bv_unsigned (getr R0 (reg 8)) | 45%nat => bv_unsigned (getr R0 (reg 9)) | 46%nat => bv_unsigned (getr R0 (reg 18)) | 47%nat => bv_unsigned (getr R0 (reg 19)) | 48%nat => bv_unsigned (getr R0 (reg 20)) | 49%nat => bv_unsigned (getr R0 (reg 21)) | 50%nat => bv_unsigned (getr R0 (reg 22)) | 51%nat => bv_unsigned (getr R0 (reg 23)) | _ => 0 end)) ltac:(first [assumption | unfold PNARCP.aligned; lia | lia]).
  destruct P as (fx4 & R4 & M4v & MG4 & _ & FZ4 & MS4 & KS4 & dR1 & dR2 & dR9 & dR10 & dR11 & dR12 & dR18 & dR19 & dR20 & dR21 & dR22 & dR23 & D272 & D264 & D48).
  set (W4 := fun a => (fb + 464 + 40 <= a < fb + 464 + 40 + 8) \/ (fb + 464 + 256 <= a < fb + 464 + 256 + 16)).
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK1 cr Aw1 M3 model3 fx1 fx4 R3 0xace34 R4 0x78130 M4v W4 K HH3 AM3 MS4 MG4).
  { intros a Ha N. apply FZ4; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
  { intros a Ha Wa. assert (Wa' : fb + 464 <= a < fb + 464 + 416) by (unfold W4 in Wa; lia).
    split; [apply (L5SAR.obj_client L ar LB FF 0 0 _ 416 a AOB); lia| lia]. }
  intros M4 model4 HH4 AM4 MRT4 HID4 VIS4 MGM4 FR4 VV4.
  assert (EK34 : L5SAR.ek L ar LB FF sp 24576 [(fb + 464, 416)] M3 M4).
  { apply (L5SAR.ek_piece L ar LB FF sp 24576 _ M3 M4 W4 FR4). intros a Ha Hc Ho X.
    apply (Ho (fb + 464, 416)); [left; reflexivity| unfold L5.in_rng, W4 in *; cbn [fst snd]; lia]. }
  assert (ASTK4 : L5CA.astk ar M4 sp 24576) by (apply (L5SAR.astk_grows ar M3 M4 sp 24576 ASTK3 MGM4)).
  assert (ACC4 : PMSPA.accA M4 (fb + 464) 416) by (apply (PMKA.acc_keepA' L ar LB FF sp 24576 _ M3 M4 EK34 WAPP FRB _ 416 AOP ACC3)).
  assert (ACCI4 : PMSPA.accA M4 (fb + 96) 272) by (apply (PMKA.acc_keepA' L ar LB FF sp 24576 _ M3 M4 EK34 WAPP FRB _ 272 AOIS ACCI3)).
  assert (ACCO4 : PMSPA.accA M4 oo 24) by (apply (PMKA.acc_keepA' L ar LB FF sp 24576 _ M3 M4 EK34 WAPP FRB _ 24 AOO ACCO3)).
  assert (ODEF4 : L5.defined M4 (fb + 464) 416) by (apply (L5.defined_grows M3 M4 _ _ MGM4); exact ODEF3).
  (* [comment removed for export] *)
  apply (PNARCK.amset L ar C HI LY HIok LB FF LK1 cr Aw1 sp 160 (fb + 464) 416 fx4 R4 M4 model4 K 272 16 707616 AOB); [lia| lia| lia| exact HH4| exact AM4| exact ASTK4| exact ACC4| exact ODEF4
     | lia| lia| replace (sp - 160) with (sp + (-10) * 16) by lia; rewrite Z.mod_add by lia; exact A16| exact dR10| exact dR11| exact dR12| | exact dR1| reflexivity| lia| exact dR2| exact K0|].
  { apply RTP. rewrite (KS4 4%nat) by inl. rewrite CS3 by inl. rewrite (KS1 4%nat) by inl. apply MCSK. right; left; reflexivity. }
  intros R5 M5 model5 R5a0 RP5 Z280 PRES5 SDEF5 DEF5 MRT5 AM5 HH5.
  assert (CS5 : forall k, In k L5SAR.cs_all -> getr R5 (reg k) = getr R4 (reg k)) by (intros k Hk; apply (L5SAR.cs_of_preserved R4 R5 k RP5 Hk)).
  destruct (PNARCK.mset_post L ar C HI HIok LB FF LK1 cr Aw1 sp 160 (fb + 464) 416 M4 M5 model4 272 16 HH4 ASTK4 AOB ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PRES5 SDEF5 DEF5)
    as (EK45 & DK45 & ASTK5).
  assert (ACC5 : PMSPA.accA M5 (fb + 464) 416) by (apply (PMKA.acc_keepA' L ar LB FF sp 24576 _ M4 M5 EK45 WAPP FRB _ 416 AOP ACC4)).
  assert (ACCI5 : PMSPA.accA M5 (fb + 96) 272) by (apply (PMKA.acc_keepA' L ar LB FF sp 24576 _ M4 M5 EK45 WAPP FRB _ 272 AOIS ACCI4)).
  assert (ACCO5 : PMSPA.accA M5 oo 24) by (apply (PMKA.acc_keepA' L ar LB FF sp 24576 _ M4 M5 EK45 WAPP FRB _ 24 AOO ACCO4)).
  assert (ODEF5 : L5.defined M5 (fb + 464) 416).
  { pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK1 cr Aw1 M5 model5 (fb + 464) 416 sp 24576 HH5 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & X & _). exact X. }
  assert (AG15 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF 0 0 a -> ~ (sp - 240 - 2560 <= a < sp - 160) -> ~ (fb + 464 + 40 <= a < fb + 464 + 48)
                 -> ~ (fb + 464 + 56 <= a < fb + 464 + 104) -> ~ (fb + 464 + 256 <= a < fb + 464 + 288) -> M5 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha Hc N1 N2 N3 N4. rewrite PRES5; [| exact Ha| apply (L5SAR.aclient_narrow L ar LB FF 0 0); [exact Hc| lia]| lia].
    rewrite FR4; [| exact Ha| unfold W4; lia]. apply AG13; [exact Ha| exact Hc| lia| lia]. }
  assert (AG15s : forall a, sp - 152 <= a < sp -> M5 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by (intros a Ha; apply AG15; [lia| apply SCL; lia| lia| lia| lia| lia]).
  (* [comment removed for export] *)
  destruct (PNARCK.vfacts L ar C IL HI LY HIok ICok ILY LB FF LK1 cr Aw1 M5 model5 sp fb oo HH5 FOK ASTK5 AOO OO8 ACC5 ACCI5 ACCO5 ODEF5)
    as (X1' & X2' & X3' & X4' & X5' & X6' & X7' & X8' & X9' & X10' & _).
  assert (U8 : L5.u64_at RSEGS (mrestrict (ahid Aw1 model5) M5) (sp - 8) _) by (apply (PNARCK.svis L ar C HI LY HIok LB FF LK1 cr Aw1 M5 model5 sp (sp - 8) _ HH5 ASTK5); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG15s; lia| lia| lia| exact S8]).
  assert (U16 : L5.u64_at RSEGS (mrestrict (ahid Aw1 model5) M5) (sp - 16) _) by (apply (PNARCK.svis L ar C HI LY HIok LB FF LK1 cr Aw1 M5 model5 sp (sp - 16) _ HH5 ASTK5); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG15s; lia| lia| lia| exact S16]).
  assert (U24 : L5.u64_at RSEGS (mrestrict (ahid Aw1 model5) M5) (sp - 24) _) by (apply (PNARCK.svis L ar C HI LY HIok LB FF LK1 cr Aw1 M5 model5 sp (sp - 24) _ HH5 ASTK5); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG15s; lia| lia| lia| exact S24]).
  assert (U32 : L5.u64_at RSEGS (mrestrict (ahid Aw1 model5) M5) (sp - 32) _) by (apply (PNARCK.svis L ar C HI LY HIok LB FF LK1 cr Aw1 M5 model5 sp (sp - 32) _ HH5 ASTK5); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG15s; lia| lia| lia| exact S32]).
  assert (U40 : L5.u64_at RSEGS (mrestrict (ahid Aw1 model5) M5) (sp - 40) _) by (apply (PNARCK.svis L ar C HI LY HIok LB FF LK1 cr Aw1 M5 model5 sp (sp - 40) _ HH5 ASTK5); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG15s; lia| lia| lia| exact S40]).
  assert (U48 : L5.u64_at RSEGS (mrestrict (ahid Aw1 model5) M5) (sp - 48) _) by (apply (PNARCK.svis L ar C HI LY HIok LB FF LK1 cr Aw1 M5 model5 sp (sp - 48) _ HH5 ASTK5); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG15s; lia| lia| lia| exact S48]).
  assert (U56 : L5.u64_at RSEGS (mrestrict (ahid Aw1 model5) M5) (sp - 56) _) by (apply (PNARCK.svis L ar C HI LY HIok LB FF LK1 cr Aw1 M5 model5 sp (sp - 56) _ HH5 ASTK5); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG15s; lia| lia| lia| exact S56]).
  assert (U64 : L5.u64_at RSEGS (mrestrict (ahid Aw1 model5) M5) (sp - 64) _) by (apply (PNARCK.svis L ar C HI LY HIok LB FF LK1 cr Aw1 M5 model5 sp (sp - 64) _ HH5 ASTK5); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG15s; lia| lia| lia| exact S64]).
  assert (U72 : L5.u64_at RSEGS (mrestrict (ahid Aw1 model5) M5) (sp - 72) _) by (apply (PNARCK.svis L ar C HI LY HIok LB FF LK1 cr Aw1 M5 model5 sp (sp - 72) _ HH5 ASTK5); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG15s; lia| lia| lia| exact S72]).
  assert (UT : forall a v, sp - 152 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1 a v -> L5.u64_at RSEGS (mrestrict (ahid Aw1 model5) M5) a v)
    by (intros a v Ha Hb X; apply (PNARCK.svis L ar C HI LY HIok LB FF LK1 cr Aw1 M5 model5 sp a v HH5 ASTK5); [lia| lia|];
        apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG15s; lia| lia| lia| exact X]).
  pose proof (UT (sp - 120) _ ltac:(lia) ltac:(lia) F120) as U120. pose proof (UT (sp - 128) _ ltac:(lia) ltac:(lia) F128) as U128.
  pose proof (UT (sp - 136) _ ltac:(lia) ltac:(lia) F136) as U136. pose proof (UT (sp - 144) _ ltac:(lia) ltac:(lia) F144) as U144.
  pose proof (UT (sp - 152) _ ltac:(lia) ltac:(lia) F152) as U152.
  assert (K2 : getr R5 (reg 2) = Z_to_bv 64 (sp - 160)) by (rewrite CS5 by inl; exact dR2).
  assert (K8 : getr R5 (reg 8) = Z_to_bv 64 (fb + 464 + 24)) by (rewrite CS5, (KS4 8%nat) by inl; exact J8).
  assert (K9 : getr R5 (reg 9) = Z_to_bv 64 (fb + 464 + 16)) by (rewrite CS5 by inl; exact dR9).
  assert (K18 : getr R5 (reg 18) = Z_to_bv 64 (fb + 464 + 288)) by (rewrite CS5 by inl; exact dR18).
  assert (K19 : getr R5 (reg 19) = Z_to_bv 64 2147450880) by (rewrite CS5 by inl; exact dR19).
  assert (K22 : getr R5 (reg 22) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 22)))) by (rewrite CS5 by inl; exact dR22).
  assert (K23 : getr R5 (reg 23) = Z_to_bv 64 2147450880) by (rewrite CS5 by inl; exact dR23).
  LeanFeed.pfeed P (PNARCP.abrcE_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx4 R5 (mrestrict (ahid Aw1 model5) M5) (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => oo | 43%nat => bv_unsigned (getr R0 (reg 1)) | 44%nat => bv_unsigned (getr R0 (reg 8)) | 45%nat => bv_unsigned (getr R0 (reg 9)) | 46%nat => bv_unsigned (getr R0 (reg 18)) | 47%nat => bv_unsigned (getr R0 (reg 19)) | 48%nat => bv_unsigned (getr R0 (reg 20)) | 49%nat => bv_unsigned (getr R0 (reg 21)) | 50%nat => bv_unsigned (getr R0 (reg 22)) | 51%nat => bv_unsigned (getr R0 (reg 23)) | _ => 0 end)) ltac:(first [assumption | unfold PNARCP.aligned; lia | lia]).
  destruct P as (fx6 & R6 & M6v & MG6 & _ & FZ6 & MS6 & KS6 & eR1 & eR10 & eR11 & eR12 & eR18 & E296).
  set (W6 := fun a => fb + 464 + 288 <= a < fb + 464 + 288 + 8).
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK1 cr Aw1 M5 model5 fx4 fx6 R5 0xacc20 R6 0x78130 M6v W6 K HH5 AM5 MS6 MG6).
  { intros a Ha N. apply FZ6; [exact Ha| exact N]. }
  { intros a Ha Wa. unfold W6 in Wa. split; [apply (L5SAR.obj_client L ar LB FF 0 0 _ 416 a AOB); lia| lia]. }
  intros M6 model6 HH6 AM6 MRT6 HID6 VIS6 MGM6 FR6 VV6.
  assert (EK56 : L5SAR.ek L ar LB FF sp 24576 [(fb + 464, 416)] M5 M6).
  { apply (L5SAR.ek_piece L ar LB FF sp 24576 _ M5 M6 W6 FR6). intros a Ha Hc Ho X.
    apply (Ho (fb + 464, 416)); [left; reflexivity| unfold L5.in_rng, W6 in *; cbn [fst snd]; lia]. }
  assert (ASTK6 : L5CA.astk ar M6 sp 24576) by (apply (L5SAR.astk_grows ar M5 M6 sp 24576 ASTK5 MGM6)).
  assert (ACC6 : PMSPA.accA M6 (fb + 464) 416) by (apply (PMKA.acc_keepA' L ar LB FF sp 24576 _ M5 M6 EK56 WAPP FRB _ 416 AOP ACC5)).
  assert (ODEF6 : L5.defined M6 (fb + 464) 416) by (apply (L5.defined_grows M5 M6 _ _ MGM6); exact ODEF5).
  (* [comment removed for export] *)
  apply (PNARCK.amset L ar C HI LY HIok LB FF LK1 cr Aw1 sp 160 (fb + 464) 416 fx6 R6 M6 model6 K 296 16 707660 AOB); [lia| lia| lia| exact HH6| exact AM6| exact ASTK6| exact ACC6| exact ODEF6
     | lia| lia| replace (sp - 160) with (sp + (-10) * 16) by lia; rewrite Z.mod_add by lia; exact A16| exact eR10| exact eR11| exact eR12| | exact eR1| reflexivity| lia| | exact K0|].
  { apply RTP. rewrite (KS6 4%nat) by inl. rewrite CS5 by inl. rewrite (KS4 4%nat) by inl. rewrite CS3 by inl. rewrite (KS1 4%nat) by inl. apply MCSK. right; left; reflexivity. }
  { rewrite (KS6 2%nat) by inl. exact K2. }
  intros R7 M7 model7 R7a0 RP7 Z304 PRES7 SDEF7 DEF7 MRT7 AM7 HH7.
  assert (CS7 : forall k, In k L5SAR.cs_all -> getr R7 (reg k) = getr R6 (reg k)) by (intros k Hk; apply (L5SAR.cs_of_preserved R6 R7 k RP7 Hk)).
  destruct (PNARCK.mset_post L ar C HI HIok LB FF LK1 cr Aw1 sp 160 (fb + 464) 416 M6 M7 model6 296 16 HH6 ASTK6 AOB ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PRES7 SDEF7 DEF7)
    as (EK67 & DK67 & ASTK7).
  assert (EK17 : L5SAR.ek L ar LB FF sp 24576 [(fb + 464, 416)] M1 M7).
  { apply (L5SAR.ek_trans L ar LB FF sp 24576 _ M1 M6 M7); [| exact EK67]. apply (L5SAR.ek_trans L ar LB FF sp 24576 _ M1 M5 M6); [| exact EK56].
    apply (L5SAR.ek_trans L ar LB FF sp 24576 _ M1 M4 M5); [| exact EK45]. apply (L5SAR.ek_trans L ar LB FF sp 24576 _ M1 M3 M4 EK13 EK34). }
  assert (AG17 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF 0 0 a -> ~ (sp - 240 - 2560 <= a < sp - 160) -> ~ (fb + 464 + 40 <= a < fb + 464 + 48)
                 -> ~ (fb + 464 + 56 <= a < fb + 464 + 104) -> ~ (fb + 464 + 256 <= a < fb + 464 + 312) -> M7 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha Hc N1 N2 N3 N4. rewrite PRES7; [| exact Ha| apply (L5SAR.aclient_narrow L ar LB FF 0 0); [exact Hc| lia]| lia].
    rewrite FR6; [| exact Ha| unfold W6; lia]. apply AG15; [exact Ha| exact Hc| lia| lia| lia| lia]. }
  assert (AGX : forall a, (sp - 152 <= a < sp) \/ (fb + 464 <= a < fb + 464 + 416 /\ ~ (fb + 464 + 40 <= a < fb + 464 + 48) /\ ~ (fb + 464 + 56 <= a < fb + 464 + 104)
                          /\ ~ (fb + 464 + 256 <= a < fb + 464 + 312)) -> M7 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha. apply AG17; [lia| destruct Ha as [Ha|Ha]; [apply SCL; lia| apply CL; lia]| lia| lia| lia| lia]. }
  Ltac a64 AG X Ms := apply (L5C.u64_at_agree RSEGS Ms); [intros i Hi; apply AG; (lia || fail 1 "AG")| (lia || fail 1 "B1")| (lia || fail 1 "B2")| exact X].
  Ltac a32 AG X Ms := apply (PMF.u32_at_agree RSEGS Ms); [intros i Hi; apply AG; (lia || fail 1 "AG")| (lia || fail 1 "B1")| (lia || fail 1 "B2")| exact X].
  Ltac a8 AG X Ms := apply (L5C.u8_at_agree RSEGS Ms); [intros i Hi; apply AG; (lia || fail 1 "AG")| (lia || fail 1 "B1")| (lia || fail 1 "B2")| exact X].
  unfold PMSPA.cfg in KONT. apply (KONT fx6 R7 M7 model7 LK1 Aw1).
  unfold PNARCS.rmid2, PNARCS.rmidc, PNARCS.saves_rd, PNARCS.saves_src, PNARCS.hcells, PNARCS.op, PNARCS.SCR.
  split; [rewrite CS7 by inl; rewrite (KS6 2%nat) by inl; exact K2|].
  split; [rewrite CS7 by inl; rewrite (KS6 8%nat) by inl; exact K8|].
  split; [rewrite CS7 by inl; rewrite (KS6 9%nat) by inl; exact K9|].
  split; [rewrite CS7 by inl; replace (fb + 464 + 296) with (fb + 464 + 296) by lia; exact eR18|].
  split; [rewrite CS7 by inl; rewrite (KS6 19%nat) by inl; exact K19|].
  split; [rewrite CS7 by inl; rewrite (KS6 23%nat) by inl; exact K23|].
  split. { assert (R20 : getr R7 (reg 20) = getr R0 (reg 20)) by (rewrite CS7 by inl; rewrite (KS6 20%nat) by inl; rewrite CS5 by inl; rewrite dR20; apply Z_to_bv_bv_unsigned).
           assert (R21 : getr R7 (reg 21) = getr R0 (reg 21)) by (rewrite CS7 by inl; rewrite (KS6 21%nat) by inl; rewrite CS5 by inl; rewrite dR21; apply Z_to_bv_bv_unsigned).
           assert (R22 : getr R7 (reg 22) = getr R0 (reg 22)) by (rewrite CS7 by inl; rewrite (KS6 22%nat) by inl; rewrite K22; apply Z_to_bv_bv_unsigned).
           assert (RK : forall k, In k [3; 4; 24; 25; 26; 27]%nat -> getr R7 (reg k) = getr R0 (reg k)).
           { intros k Hk. assert (Hk' : In k L5SAR.cs_all /\ In k PNARCP.KS_abrcE /\ In k PNARCP.KS_abrcD /\ In k PNARCP.KS_abrcC)
               by (destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; (split; [inl| split; [inl| split; inl]])).
             destruct Hk' as (Q1 & Q2 & Q3 & Q4). rewrite (CS7 k Q1), (KS6 k Q2), (CS5 k Q1), (KS4 k Q3), (CS3 k Q1), (KS1 k Q4). apply MCSK. exact Hk. }
           intros k Hk. destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; [apply RK; inl| apply RK; inl| exact R20| exact R21| exact R22| apply RK; inl| apply RK; inl| apply RK; inl| apply RK; inl]. }
  (* [comment removed for export] *)
  assert (AG47 : forall a, fb + 464 <= a < fb + 464 + 272 -> M7 (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)).
  { intros a Ha. rewrite PRES7; [| lia| apply (L5SAR.aclient_narrow L ar LB FF 0 0); [apply CL; lia| lia]| lia].
    rewrite FR6; [| lia| unfold W6; lia]. apply PRES5; [lia| apply (L5SAR.aclient_narrow L ar LB FF 0 0); [apply CL; lia| lia]| lia]. }
  assert (V4a : forall a n, fb + 464 <= a -> a + n <= fb + 464 + 416 -> L5A.avis (ahid Aw1 model3) a n).
  { intros a n H1 H2. pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK1 cr Aw1 M3 model3 (fb + 464) 416 sp 24576 HH3 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & _ & OV & _).
    eapply L5A.avis_sub; [exact OV| lia| lia]. }
  assert (V6a : forall a n, fb + 464 <= a -> a + n <= fb + 464 + 416 -> L5A.avis (ahid Aw1 model5) a n).
  { intros a n H1 H2. pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK1 cr Aw1 M5 model5 (fb + 464) 416 sp 24576 HH5 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & _ & OV & _).
    eapply L5A.avis_sub; [exact OV| lia| lia]. }
  split. { apply (L5C.u64_at_agree RSEGS M4); [intros i Hi; apply AG47; lia| lia| lia|]. apply (PMAIS1.vis_u64 _ _ _ _ _ VIS4); [apply V4a; lia| lia| lia| exact D48]. }
  split. { replace (fb + 464 + 256) with (fb + 464 + 256) by lia. replace (fb + 96) with (fb + 464 - 368) by lia.
           apply (L5C.u64_at_agree RSEGS M4); [intros i Hi; apply AG47; lia| lia| lia|]. apply (PMAIS1.vis_u64 _ _ _ _ _ VIS4); [apply V4a; lia| lia| lia| exact D264]. }
  split. { replace (fb + 112) with (fb + 464 - 352) by lia.
           apply (L5C.u64_at_agree RSEGS M4); [intros i Hi; apply AG47; lia| lia| lia|]. apply (PMAIS1.vis_u64 _ _ _ _ _ VIS4); [apply V4a; lia| lia| lia| exact D272]. }
  split. { apply (PMF.zeros_at_agree M5); [intros i Hi|exact Z280]. rewrite PRES7; [| lia| apply (L5SAR.aclient_narrow L ar LB FF 0 0); [apply CL; lia| lia]| lia].
           apply FR6; [lia| unfold W6; lia]. }
  split. { apply (L5C.u64_at_agree RSEGS M6); [intros i Hi; apply PRES7; [lia| apply (L5SAR.aclient_narrow L ar LB FF 0 0); [apply CL; lia| lia]| lia]| lia| lia|].
           apply (PMAIS1.vis_u64 _ _ _ _ _ VIS6); [apply V6a; lia| lia| lia| exact E296]. }
  split; [exact Z304|].
  split. { split; [a64 AGX S8 M1|]. split; [a64 AGX S16 M1|]. split; [a64 AGX S24 M1|]. split; [a64 AGX S32 M1|].
           split; [a64 AGX S40 M1|]. split; [a64 AGX S48 M1|]. split; [a64 AGX S56 M1|]. split; [a64 AGX S64 M1|].
           split; [a64 AGX S72 M1|]. split; [a64 AGX S80 M1| a64 AGX S88 M1]. }
  split. { split; [a64 AGX F120 M1|]. split; [a64 AGX F128 M1|]. split; [a64 AGX F136 M1|]. split; [a64 AGX F144 M1| a64 AGX F152 M1]. }
  destruct HC as (H0 & H8 & H9 & H10 & H12 & H32 & H56 & H112 & H144 & H148 & H152 & H160 & Z168).
  split. { split; [a64 AGX H0 M1|]. split; [a8 AGX H8 M1|]. split; [a8 AGX H9 M1|]. split; [a8 AGX H10 M1|]. split; [a32 AGX H12 M1|].
           split; [a64 AGX H32 M1|]. split; [a64 AGX H56 M1|]. split; [a64 AGX H112 M1|]. split; [a32 AGX H144 M1|]. split; [a32 AGX H148 M1|].
           split; [a64 AGX H152 M1|]. split; [a64 AGX H160 M1|]. apply (PMF.zeros_at_agree M1); [intros i Hi; apply AGX; lia| exact Z168]. }
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK1 cr Aw1 M7 model7 (fb + 464) 416 sp 24576 HH7 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & ODEF7 & _).
  assert (OUT0 : forall a n, fb + 32 <= a -> a + n <= fb + 464 \/ fb + 464 + 416 <= a -> forall i, a <= i < a + n -> L5.outside [(fb + 464, 416)] i).
  { intros a n Ha Hn i Hi rg [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
  split; [exact ODEF7|].
  split; [apply (PMKA.acc_keepA' L ar LB FF sp 24576 _ M1 M7 EK17 WAPP FRB _ 416 AOP ACC)|].
  split; [apply (PMKA.acc_keepA' L ar LB FF sp 24576 _ M1 M7 EK17 WAPP FRB _ 24 AOO ACCO)|].
  assert (AOOs : forall a n, oo <= a -> a + n <= oo + 24 -> PMSPA.aobjA FF a n).
  { intros a n Ha Hn. destruct AOO as (f & Hf & X1 & X2). exists f. split; [exact Hf| clear - Ha Hn X1 X2; Lia.lia]. }
  assert (OUTO : forall i, oo <= i < oo + 24 -> L5.outside [(fb + 464, 416)] i).
  { intros i Hi rg [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hi Hr OOAP'. destruct OOAP'; Lia.lia. }
  split. { apply (PMKA.u64_keepA RSEGS L ar LB FF sp 24576 _ M1 M7 EK17 WAPP FRB oo _ (AOOs oo 8 ltac:(Lia.lia) ltac:(Lia.lia)));
             [intros i Hi; apply OUTO; Lia.lia| exact OO0]. }
  split. { apply (PMKA.u32_keepA RSEGS L ar LB FF sp 24576 _ M1 M7 EK17 WAPP FRB (oo + 16) _ (AOOs (oo + 16) 4 ltac:(Lia.lia) ltac:(Lia.lia)));
             [intros i Hi; apply OUTO; Lia.lia| exact OO16]. }
  split; [apply (PMKA.acc_keepA' L ar LB FF sp 24576 _ M1 M7 EK17 WAPP FRB _ 272 AOIS ACCI)|].
  split; [exact ASTK7|].
  split. { change (24576 / 8) with 3072. apply (PMKA.stksh_keepA L ar LB FF sp 24576 _ M1 M7 EK17 WAPP); [lia| lia| lia| | lia| exact STKSH].
           apply PMAIS1.sub8; [exact A16| reflexivity]. }
  split. { apply (PMAIS1.base_ok_agree M1 M7); [|exact BASE]. intros a Ha. unfold PMAIS1.brg in Ha. apply AG17; [lia| | lia| lia| lia| lia].
           unfold aclient, aclient_g. right; right; left. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia|].
           destruct Ha as [Ha|Ha]; [intros X; pose proof (L5A.aly_static_lo L C LYa a X); lia|].
           apply (fun D_ => PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D_)). unfold PMST.dep, pm_initc. cbn [pa_canary pa_need_locks pa_locale_lock PMA.AD ADDR_A].
           destruct Ha as [Ha|[Ha|Ha]];
             [right; left; lia
             | right; right; exists (0x693f93, 0x693f94); split; [left; reflexivity| cbn [fst snd]; lia]
             | right; right; exists (0x694070, 0x694074); split; [right; left; reflexivity| cbn [fst snd]; lia]]. }
  split. { apply (PMAIS1.loc_ok_agree M1 M7 true); [|exact LOC]. intros a Ha. apply AG17; [lia| | lia| lia| lia| lia].
           unfold aclient, aclient_g. right; right; left. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia|].
           apply (fun D_ => PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D_)). unfold PMST.dep, pm_foot. left. cbn [pa_errcat_guard pa_syscat_guard pa_loc_foot pa_atexit PMA.AD ADDR_A app].
           destruct Ha as [X|X]; [exists (0x672532, 0x672c70); split; [right; right; left; reflexivity| cbn [fst snd]; lia]
                                  | exists (0x673398, 0x6733f0); split; [right; right; right; left; reflexivity| cbn [fst snd]; lia]]. }
  split; [exact HH7|]. split; [exact AM7|].
  split. { apply (L5LZ.model_rt_trans model0 model6 model7); [|exact MRT7]. apply (L5LZ.model_rt_trans model0 model5 model6); [|exact MRT6].
           apply (L5LZ.model_rt_trans model0 model4 model5); [|exact MRT5]. apply (L5LZ.model_rt_trans model0 model3 model4); [|exact MRT4].
           apply (L5LZ.model_rt_trans model0 model1' model3); [|exact MRT3]. apply (L5LZ.model_rt_trans model0 model1 model1'); [exact MRT| exact MRT1]. }
  split; [exact INCK|]. split; [exact INCA|].
  split; [apply (L5SAR.ek_trans L ar LB FF sp 24576 _ M0 M1 M7 EK EK17)|].
  apply (L5SAR.dk_trans L ar LB FF sp 24576 M0 M1 M7 DK).
  apply (L5SAR.dk_trans L ar LB FF sp 24576 M1 M3 M7 DK13).
  apply (L5SAR.dk_trans L ar LB FF sp 24576 M3 M4 M7 (L5SAR.dk_grows L ar LB FF sp 24576 M3 M4 MGM4)).
  apply (L5SAR.dk_trans L ar LB FF sp 24576 M4 M5 M7 DK45).
  apply (L5SAR.dk_trans L ar LB FF sp 24576 M5 M6 M7 (L5SAR.dk_grows L ar LB FF sp 24576 M5 M6 MGM6) DK67).
Qed.
End Stage.
End PNARC2.
