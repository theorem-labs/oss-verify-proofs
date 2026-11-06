(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StreamSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx IcptIfaceA
     L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreA L5StepAR PmLayout PmLayoutA PnLayout PnLayoutA PmModel PnModel PmModelFacts PmStatics PmStaticsA PnStatics PnStaticsA
     PmSpecs PmSpecsA PnSpecsAa PnSpecsAX PgSrc PgV8 PgSrcA PgV8A PnRun PnRunA PnRunAa
     PmModelFactsA PmStep PnStepA PnStepA2 PmCertKitG XIcptAs0 PnAReaderCtorStmts PnAReaderCtorP PnAIss1 PnAReaderCtor1 PnAReaderCtorKit Ba0_code_abcbc_abcc0.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.asan Require Import XIcptA XIcptAs0Kit L5CoreB.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia.
Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac dlia := first [ solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_ne ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_ne end ]
                   | solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_st ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_st end ] ].
Local Ltac lia := dlia.
Module PNARC3.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma shz_at (M : word -> option byte) lo g p : shadow_zero M lo g -> lo mod 8 = 0 -> lo <= p -> p < lo + 8 * g -> byte_at M (S p) 0.
Proof.
  intros SZ L8 H1 H2. pose proof (SZ ((p - lo) / 8) ltac:(Lia.lia)) as X. replace (S p) with (S lo + (p - lo) / 8) by (unfold S, SB; Lia.lia). exact X.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

Theorem tail : PMA.opnew_spec L ar HI -> PNSAX.push_root_spec RSEGS PMA.AD L ar HI 0xabff8 ->
  forall (fx : FPState) R0 M0 model0 K LB FF LK0 Aw0 cr sp r fb oo oa str sm R1 M1 model1 LK1 Aw1,
    PNARCS.pre L ar HI R0 M0 model0 K LB FF LK0 Aw0 cr sp r fb oo oa str sm ->
    PNARCS.rmid2 L ar HI R0 M0 model0 LB FF LK0 Aw0 cr sp fb oo R1 M1 model1 LK1 Aw1 ->
    PNARCS.kont L ar HI R0 M0 model0 K LB FF LK0 Aw0 cr sp r fb ->
    srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R1 0xabf60 M1 model1) K.
Proof.
  intros OPN PSH fx R0 M0 model0 K LB FF LK0 Aw0 cr sp r fb oo oa str sm R1 M1 model1 LK1 Aw1 PRE MID KONT.
  destruct PRE as (HH0 & AM0 & K0 & ENT & FRM & FRS & FOK & A10 & A11 & A12 & A13 & AOO & OOAP & OO8 & ODEF0 & ACC0 & ACCO0 & OO0' & OO16' & ISS & BASE0 & LOCb & CRED).
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK0 & STKSH0). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  destruct MID as (M2' & M8 & M9 & M18 & M19 & M23 & MCSK & C48 & C264 & C272 & Z280 & C296 & Z304 & MC).
  destruct MC as (SRD & SSRC & HC & ODEF & ACC & ACCO & OO0 & OO16 & ACCI & ASTK & STKSH & BASE & LOC & HH & AM & MRT & INCK & INCA & EK & DK).
  unfold PNARCS.op, PNARCS.SCR in *. change (24576 / 8) with 3072 in STKSH.
  destruct SRD as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72). destruct SSRC as (S88 & S96 & S104 & S112 & S120).
  destruct HC as (H0 & H8 & H9 & H10 & H12 & H32 & H56 & H112 & H144 & H148 & H152 & H160 & Z168).
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof AM as (Mh & MI).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & STOP & _).
  pose proof (PNARCK.fb16 FF fb FOK) as F16.
  assert (AOP : PMSPA.aobjA FF (fb + 464) 416) by (apply (PNARCK.frame_aobj FF fb); [exact FOK| lia| lia]).
  assert (O8 : (fb + 464) mod 8 = 0) by lia.
  pose proof (PMKA.aobj_of_aobjA FF _ _ AOP O8) as AOB.
  assert (AOIS : PMSPA.aobjA FF (fb + 96) 272) by (apply (PNARCK.frame_aobj FF fb); [exact FOK| lia| lia]).
  assert (OOAP' : fb + 464 + 416 <= oo \/ oo + 24 <= fb + 464) by (destruct OOAP as [X|X]; [right|left]; Lia.lia).
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47).
  { intros f Hf. destruct (WF f Hf) as (X1 & X2 & _). unfold app_mem, FS_BYTES in *. lia. }
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK1 cr Aw1 M1 model1 (fb + 464) 416 sp 24576 HH AOB ltac:(lia) ltac:(reflexivity)) as (OR & OBIG & _).
  assert (WAPP : PMKA.wapp [(fb + 464, 416)]) by (apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia| apply PMKA.wapp_nil]).
  assert (CLF : forall a, fb + 32 <= a < fb + 2040 -> forall LBz sz scz, aclient L ar LBz FF sz scz a).
  { intros a Ha LBz sz scz. apply (L5SAR.obj_client L ar LBz FF sz scz (fb + 32) 2008 a); [| lia].
    apply (PMKA.aobj_of_aobjA FF _ _ (PNARCK.frame_aobj FF fb (fb + 32) 2008 FOK ltac:(lia) ltac:(lia))). lia. }
  assert (SCL : forall a, ahl_ceil ar <= a < 2 ^ 47 -> forall LBz sz scz, ~ (sz - scz <= a < sz) -> aclient L ar LBz FF sz scz a).
  { intros a Ha LBz sz scz N. apply L5SAR.stack_client; [lia| exact N]. }
  pose proof (PMAIS1.bvu (getr R0 (reg 1))) as UR1. pose proof (PMAIS1.bvu (getr R0 (reg 8))) as UR8. pose proof (PMAIS1.bvu (getr R0 (reg 9))) as UR9.
  pose proof (PMAIS1.bvu (getr R0 (reg 18))) as UR18. pose proof (PMAIS1.bvu (getr R0 (reg 19))) as UR19. pose proof (PMAIS1.bvu (getr R0 (reg 20))) as UR20.
  pose proof (PMAIS1.bvu (getr R0 (reg 21))) as UR21. pose proof (PMAIS1.bvu (getr R0 (reg 22))) as UR22. pose proof (PMAIS1.bvu (getr R0 (reg 23))) as UR23.
  assert (RTP : forall Rx, getr Rx (reg 4) = getr R0 (reg 4) -> getr Rx (reg 4) = Z_to_bv 64 (hl_tp L)) by (intros Rx E; rewrite E; exact Rtp).
  destruct (PNARCK.rd_credit L ar C LY cr CRED) as (CR1 & CR2 & CR3).
  LeanFeed.pfeed P (PNARCP.abrcF_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx R1 (mrestrict (ahid Aw1 model1) M1) (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => oo | _ => 0 end)) ltac:(first [assumption | unfold PNARCP.aligned; lia | lia]).
  destruct P as (fx1 & R2 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & fR1 & fR10).
  assert (E1 : M1v = mrestrict (ahid Aw1 model1) M1) by (apply L5SAR.mem_eq_of_agree; exact FZ1). subst M1v.
  unfold PMSPA.cfg.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok LB FF LK1 cr Aw1 M1 model1 fx fx1 R1 0xabf60 R2 0x12dd8c _ K HH AM MS1 MG1 FZ1).
  intros M1' model1' HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (E1' : M1' = M1) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1'.
  (* [comment removed for export] *)
  unfold PMA.opnew_spec, PMSPA.opnew_spec in OPN. cbn [pa_opnew PMA.AD ADDR_A] in OPN.
  apply (OPN fx1 R2 M1 model1' K LB FF LK1 Aw1 cr 16384 (sp - 144) 704360 HH1 AM1 K0).
  { rewrite L5K.rl10. exact fR10. }
  { lia. }
  { exact CR1. }
  { rewrite L5K.rl1. exact fR1. }
  { split; [lia| reflexivity]. }
  { rewrite L5K.rl2, (KS1 2%nat) by inl. exact M2'. }
  { rewrite L5K.rl4, (KS1 4%nat) by inl. apply RTP. apply MCSK. right; left; reflexivity. }
  { unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR. apply (L5SAR.astk_sub ar M1 M1 sp 24576 144 (16 + 4096) ASTK (fun x X => X)); [lia| lia| lia|].
    replace (sp - 144) with (sp + (-9) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  intros fx2 R3 M3 model3 Aw3 q Rq RP3 FRESH HP3 MRT3 IA3 AM3 HH3.
  unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR in HP3. change (16 + 4096) with 4112 in HP3. rewrite L5K.rl10 in Rq.
  destruct FRESH as (QR & QAP & QFA & QDEF & QSH). pose proof QR as (Q0 & Q1 & Q16 & _ & Q4 & Q5). unfold app_mem in Q5.
  assert (CS3 : forall k, In k L5SAR.cs_all -> getr R3 (reg k) = getr R2 (reg k)) by (intros k Hk; apply (L5SAR.cs_of_preserved R2 R3 k RP3 Hk)).
  assert (EK13 : L5SAR.ek L ar LB FF sp 24576 [(fb + 464, 416)] M1 M3).
  { apply (L5SAR.ek_callee L ar LB [] FF [] sp 24576 (sp - 144) 4112 _ [] M1 M3 HP3); [lia| lia| intros a _ _ rg []]. }
  assert (DK13 : L5SAR.dk L ar LB FF sp 24576 M1 M3) by (apply (L5SAR.dk_callee L ar LB [] FF [] sp 24576 (sp - 144) 4112 [] M1 M3 HP3); lia).
  assert (ASTK3 : L5CA.astk ar M3 sp 24576).
  { apply (L5SAR.astk_after L ar C HI HIok LB FF LK1 cr Aw1 M1 M1 M3 _ sp 24576 (sp - 144) 4112 [] HH1 ASTK (fun x X => X) HP3); lia. }
  assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF (sp - 144) 4112 a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha Hc. apply (proj1 HP3). split; [exact Ha|]. split; [exact Hc| intros rg []]. }
  set (LB1 := (q, 16384) :: LB) in *. set (cr1 := adebit L cr 16384) in *.
  (* [comment removed for export] *)
  assert (ACC3 : PMSPA.accA M3 (fb + 464) 416) by (apply (PMKA.acc_keepA' L ar LB FF sp 24576 _ M1 M3 EK13 WAPP FRB _ 416 AOP ACC)).
  assert (ACCI3 : PMSPA.accA M3 (fb + 96) 272) by (apply (PMKA.acc_keepA' L ar LB FF sp 24576 _ M1 M3 EK13 WAPP FRB _ 272 AOIS ACCI)).
  assert (ACCO3 : PMSPA.accA M3 oo 24) by (apply (PMKA.acc_keepA' L ar LB FF sp 24576 _ M1 M3 EK13 WAPP FRB _ 24 AOO ACCO)).
  assert (ODEF3 : L5.defined M3 (fb + 464) 416).
  { pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB1 FF LK1 cr1 Aw3 M3 model3 (fb + 464) 416 sp 24576 HH3 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & X & _). exact X. }
  destruct (PNARCK.vfacts L ar C IL HI LY HIok ICok ILY LB1 FF LK1 cr1 Aw3 M3 model3 sp fb oo HH3 FOK ASTK3 AOO OO8 ACC3 ACCI3 ACCO3 ODEF3)
    as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & X18 & X19).
  assert (OOSTK' : sp - 4096 + 4096 <= oo \/ oo + 24 <= sp - 4096) by (right; Lia.lia).
  assert (OOIMG : 65536 + 6832128 <= oo \/ oo + 24 <= 65536) by (left; Lia.lia).
  assert (CLO : forall a, oo <= a < oo + 24 -> forall LBz sz scz, aclient L ar LBz FF sz scz a).
  { intros a Ha LBz sz scz. apply (L5SAR.obj_client L ar LBz FF sz scz oo 24 a (PMKA.aobj_of_aobjA FF _ _ AOO OO8)). Lia.lia. }
  assert (AG13 : forall a, (sp - 136 <= a < sp) \/ (fb + 32 <= a < fb + 2040) \/ (oo <= a < oo + 24) -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha. apply KEEP3; [lia|]. destruct Ha as [Ha|[Ha|Ha]]; [apply SCL; lia| apply CLF; lia| apply CLO; exact Ha]. }
  assert (U8 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) (sp - 8) _) by (apply (PNARCK.svis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M3 model3 sp (sp - 8) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact S8]).
  assert (U16 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) (sp - 16) _) by (apply (PNARCK.svis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M3 model3 sp (sp - 16) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact S16]).
  assert (U24 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) (sp - 24) _) by (apply (PNARCK.svis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M3 model3 sp (sp - 24) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact S24]).
  assert (U32 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) (sp - 32) _) by (apply (PNARCK.svis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M3 model3 sp (sp - 32) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact S32]).
  assert (U40 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) (sp - 40) _) by (apply (PNARCK.svis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M3 model3 sp (sp - 40) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact S40]).
  assert (U48 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) (sp - 48) _) by (apply (PNARCK.svis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M3 model3 sp (sp - 48) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact S48]).
  assert (U56 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) (sp - 56) _) by (apply (PNARCK.svis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M3 model3 sp (sp - 56) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact S56]).
  assert (U64 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) (sp - 64) _) by (apply (PNARCK.svis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M3 model3 sp (sp - 64) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact S64]).
  assert (U72 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) (sp - 72) _) by (apply (PNARCK.svis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M3 model3 sp (sp - 72) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact S72]).
  assert (U88 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) (sp - 104) _) by (apply (PNARCK.svis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M3 model3 sp (sp - 104) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact S88]).
  assert (U96 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) (sp - 112) _) by (apply (PNARCK.svis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M3 model3 sp (sp - 112) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact S96]).
  assert (U104 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) (sp - 120) _) by (apply (PNARCK.svis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M3 model3 sp (sp - 120) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact S104]).
  assert (U112 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) (sp - 128) _) by (apply (PNARCK.svis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M3 model3 sp (sp - 128) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact S112]).
  assert (U120 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) (sp - 136) _) by (apply (PNARCK.svis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M3 model3 sp (sp - 136) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact S120]).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB1 FF LK1 cr1 Aw3 M3 model3 oo 24 0 0 HH3 (PMKA.aobj_of_aobjA FF _ _ AOO OO8) ltac:(Lia.lia) ltac:(reflexivity))
    as (_ & _ & _ & OOV & _).
  assert (UO0 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) oo 1242168).
  { apply (proj2 (L5A.u64_at_vis (ahid Aw3 model3) M3 oo 1242168 ltac:(eapply L5A.avis_sub; [exact OOV| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact OO0]. }
  assert (UO16 : L5.u32_at RSEGS (mrestrict (ahid Aw3 model3) M3) (oo + 16) 1024).
  { apply (proj2 (L5A.u32_at_vis (ahid Aw3 model3) M3 (oo + 16) 1024 ltac:(eapply L5A.avis_sub; [exact OOV| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (PMF.u32_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact OO16]. }
  assert (J2 : getr R3 (reg 2) = Z_to_bv 64 (sp - 144)) by (rewrite CS3, (KS1 2%nat) by inl; exact M2').
  assert (J8 : getr R3 (reg 8) = Z_to_bv 64 (fb + 464 + 24)) by (rewrite CS3, (KS1 8%nat) by inl; exact M8).
  assert (J9 : getr R3 (reg 9) = Z_to_bv 64 (fb + 464 + 16)) by (rewrite CS3, (KS1 9%nat) by inl; exact M9).
  assert (J18 : getr R3 (reg 18) = Z_to_bv 64 (fb + 464 + 296)) by (rewrite CS3, (KS1 18%nat) by inl; exact M18).
  assert (J19 : getr R3 (reg 19) = Z_to_bv 64 2147450880) by (rewrite CS3, (KS1 19%nat) by inl; exact M19).
  assert (J23 : getr R3 (reg 23) = Z_to_bv 64 2147450880) by (rewrite CS3, (KS1 23%nat) by inl; exact M23).
  LeanFeed.pfeed P (PNARCP.abrcG_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx2 R3 (mrestrict (ahid Aw3 model3) M3)
    (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => oo | 35%nat => q | 43%nat => bv_unsigned (getr R0 (reg 1)) | 44%nat => bv_unsigned (getr R0 (reg 8)) | 45%nat => bv_unsigned (getr R0 (reg 9)) | 46%nat => bv_unsigned (getr R0 (reg 18)) | 47%nat => bv_unsigned (getr R0 (reg 19)) | 48%nat => bv_unsigned (getr R0 (reg 20)) | 49%nat => bv_unsigned (getr R0 (reg 21)) | 50%nat => bv_unsigned (getr R0 (reg 22)) | 51%nat => bv_unsigned (getr R0 (reg 23)) | _ => 0 end)) ltac:(first [assumption | unfold PNARCP.aligned; lia | lia]).
  destruct P as (fx4 & R4 & M4v & MG4 & _ & FZ4 & MS4 & KS4 & gR1 & gR2 & gR8 & gR10 & gR11 & gR12 & gR18 & gR19 & gR21 & gR22 & G312 & G296 & G280).
  set (W4 := fun a => (fb + 464 + 280 <= a < fb + 464 + 280 + 8) \/ (fb + 464 + 296 <= a < fb + 464 + 296 + 8) \/ (fb + 464 + 312 <= a < fb + 464 + 312 + 4)).
  apply (L5SAR.apiece L ar C HI LYa HIok LB1 FF LK1 cr1 Aw3 M3 model3 fx2 fx4 R3 0xabf68 R4 0x77d68 M4v W4 K HH3 AM3 MS4 MG4).
  { intros a Ha N. apply FZ4; [exact Ha| intros X; apply N; unfold W4; left; exact X| intros X; apply N; unfold W4; right; left; exact X
                              | intros X; apply N; unfold W4; right; right; exact X]. }
  { intros a Ha Wa. assert (Wa' : fb + 464 <= a < fb + 464 + 416) by (unfold W4 in Wa; lia).
    split; [apply (L5SAR.obj_client L ar LB1 FF 0 0 _ 416 a AOB); lia| lia]. }
  intros M4 model4 HH4 AM4 MRT4 HID4 VIS4 MGM4 FR4 VV4.
  assert (EK34 : L5SAR.ek L ar LB FF sp 24576 [(fb + 464, 416)] M3 M4).
  { apply (L5SAR.ek_piece L ar LB FF sp 24576 _ M3 M4 W4 FR4). intros a Ha Hc Ho X.
    apply (Ho (fb + 464, 416)); [left; reflexivity| unfold L5.in_rng, W4 in *; cbn [fst snd]; lia]. }
  assert (ASTK4 : L5CA.astk ar M4 sp 24576) by (apply (L5SAR.astk_grows ar M3 M4 sp 24576 ASTK3 MGM4)).
  assert (ACC4 : PMSPA.accA M4 (fb + 464) 416) by (apply (PMKA.acc_keepA' L ar LB FF sp 24576 _ M3 M4 EK34 WAPP FRB _ 416 AOP ACC3)).
  assert (ODEF4 : L5.defined M4 (fb + 464) 416) by (apply (L5.defined_grows M3 M4 _ _ MGM4); exact ODEF3).
  assert (CS4 : forall k, In k [3; 4; 20; 24; 25; 26; 27]%nat -> getr R4 (reg k) = getr R0 (reg k)).
  { intros k Hk. assert (Hk' : In k PNARCP.KS_abrcG /\ In k L5SAR.cs_all /\ In k PNARCP.KS_abrcF /\ In k [3; 4; 20; 21; 22; 24; 25; 26; 27]%nat)
      by (destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; (split; [inl| split; [inl| split; inl]])).
    destruct Hk' as (Y1 & Y2 & Y3 & Y4). rewrite (KS4 k Y1), (CS3 k Y2), (KS1 k Y3). apply MCSK. exact Y4. }
  assert (G9 : getr R4 (reg 9) = Z_to_bv 64 (fb + 464 + 16)) by (rewrite (KS4 9%nat) by inl; exact J9).
  assert (G23 : getr R4 (reg 23) = Z_to_bv 64 2147450880) by (rewrite (KS4 23%nat) by inl; exact J23).

  (* [comment removed for export] *)
  apply (PNARCK.amset L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 sp 96 (fb + 464) 416 fx4 R4 M4 model4 K 320 96 703684 AOB); [lia| lia| lia| exact HH4| exact AM4| exact ASTK4| exact ACC4| exact ODEF4
     | lia| lia| replace (sp - 96) with (sp + (-6) * 16) by lia; rewrite Z.mod_add by lia; exact A16| exact gR10| exact gR11| exact gR12| apply RTP; apply CS4; inl| exact gR1| reflexivity| lia| exact gR2| exact K0|].
  intros R5 M5 model5 R5a0 RP5 Z336 PRES5 SDEF5 DEF5 MRT5 AM5 HH5.
  assert (CS5 : forall k, In k L5SAR.cs_all -> getr R5 (reg k) = getr R4 (reg k)) by (intros k Hk; apply (L5SAR.cs_of_preserved R4 R5 k RP5 Hk)).
  destruct (PNARCK.mset_post L ar C HI HIok LB1 FF LK1 cr1 Aw3 sp 96 (fb + 464) 416 M4 M5 model4 320 96 HH4 ASTK4 AOB ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PRES5 SDEF5 DEF5)
    as (EK45' & DK45' & ASTK5).
  pose proof (L5SAR.ek_tl L ar LB (q, 16384) FF sp 24576 _ M4 M5 EK45') as EK45. pose proof (L5SAR.dk_tl L ar LB (q, 16384) FF sp 24576 M4 M5 DK45') as DK45.
  (* [comment removed for export] *)
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB1 FF LK1 cr1 Aw3 M5 model5 HH5) as (_ & VIS5 & _).
  assert (Y5 : L5.writable RSEGS (mrestrict (ahid Aw3 model5) M5) (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis _ M5 (sp - 4096) 4096 (VIS5 (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M5 sp 24576); [exact ASTK5| lia| lia| lia]. }
  assert (K2 : getr R5 (reg 2) = Z_to_bv 64 (sp - 96)) by (rewrite CS5 by inl; exact gR2).
  assert (K8 : getr R5 (reg 8) = Z_to_bv 64 (fb + 464)) by (rewrite CS5 by inl; exact gR8).
  assert (K9 : getr R5 (reg 9) = Z_to_bv 64 (fb + 464 + 16)) by (rewrite CS5 by inl; exact G9).
  assert (K18 : getr R5 (reg 18) = Z_to_bv 64 (fb + 464 + 320)) by (rewrite CS5 by inl; exact gR18).
  assert (K19 : getr R5 (reg 19) = Z_to_bv 64 (fb + 464 + 344)) by (rewrite CS5 by inl; exact gR19).
  assert (K21 : getr R5 (reg 21) = Z_to_bv 64 (fb + 464 + 368)) by (rewrite CS5 by inl; exact gR21).
  assert (K22 : getr R5 (reg 22) = Z_to_bv 64 (fb + 464 + 392)) by (rewrite CS5 by inl; exact gR22).
  assert (K23 : getr R5 (reg 23) = Z_to_bv 64 2147450880) by (rewrite CS5 by inl; exact G23).
  LeanFeed.pfeed P (PNARCP.abrcH_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx4 R5 (mrestrict (ahid Aw3 model5) M5) (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => oo | _ => 0 end)) ltac:(first [assumption | unfold PNARCP.aligned; lia | lia]).
  destruct P as (fx6 & R6 & M6v & MG6 & _ & FZ6 & MS6 & KS6 & hR1 & hR10 & hR11 & hR12 & hR13 & H88 & H84 & H80).
  set (W6 := fun a => sp - 88 <= a < sp - 88 + 12).
  apply (L5SAR.apiece L ar C HI LYa HIok LB1 FF LK1 cr1 Aw3 M5 model5 fx4 fx6 R5 0xabcc4 R6 0xabff8 M6v W6 K HH5 AM5 MS6 MG6).
  { intros a Ha N. apply FZ6; [exact Ha| exact N]. }
  { intros a Ha Wa. unfold W6 in Wa. split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
  intros M6 model6 HH6 AM6 MRT6 HID6 VIS6 MGM6 FR6 VV6.
  assert (EK56 : L5SAR.ek L ar LB FF sp 24576 [(fb + 464, 416)] M5 M6).
  { apply (L5SAR.ek_piece L ar LB FF sp 24576 _ M5 M6 W6 FR6). intros a Ha Hc Ho X. unfold W6 in X.
    destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK1 cr Aw1 M1 _ sp 24576 a HH SPT Hc) as [Z1|Z1]; lia. }
  assert (ASTK6 : L5CA.astk ar M6 sp 24576) by (apply (L5SAR.astk_grows ar M5 M6 sp 24576 ASTK5 MGM6)).
  assert (EK16 : L5SAR.ek L ar LB FF sp 24576 [(fb + 464, 416)] M1 M6).
  { apply (L5SAR.ek_trans L ar LB FF sp 24576 _ M1 M5 M6); [| exact EK56]. apply (L5SAR.ek_trans L ar LB FF sp 24576 _ M1 M4 M5); [| exact EK45].
    apply (L5SAR.ek_trans L ar LB FF sp 24576 _ M1 M3 M4 EK13 EK34). }
  assert (STKSH6 : shadow_zero M6 (sp - 24576) 3072).
  { apply (PMKA.stksh_keepA L ar LB FF sp 24576 _ M1 M6 EK16 WAPP); [lia| lia| lia| | lia| exact STKSH]. apply PMAIS1.sub8; [exact A16| reflexivity]. }
  assert (ACC6 : PMSPA.accA M6 (fb + 464) 416) by (apply (PMKA.acc_keepA' L ar LB FF sp 24576 _ M1 M6 EK16 WAPP FRB _ 416 AOP ACC)).
  assert (ACS6 : forall a n, sp - 24576 <= a -> a + n <= sp -> PMSPA.accA M6 a n).
  { intros a n Y1 Y2. unfold PMSPA.accA. apply (L5CB.aacc_of_zero M6 (sp - 24576) 3072 a n STKSH6); [apply PMAIS1.sub8; [exact A16| reflexivity]| lia| lia| lia]. }
  assert (ZM6 : PM.zeros_at M6 (fb + 464 + 320) 96).
  { apply (PMF.zeros_at_agree M5); [intros i Hi; apply FR6; [lia| unfold W6; lia]| exact Z336]. }
  assert (H80' : L5.u32_at RSEGS M6 (sp - 80) 0) by (apply (PMAIS1.vis_u32 _ _ _ _ _ VIS6); [apply VIS5; lia| lia| lia| exact H80]).
  assert (H84' : L5.u32_at RSEGS M6 (sp - 84) 0) by (apply (PMAIS1.vis_u32 _ _ _ _ _ VIS6); [apply VIS5; lia| lia| lia| exact H84]).
  assert (H88' : L5.u32_at RSEGS M6 (sp - 88) 0) by (apply (PMAIS1.vis_u32 _ _ _ _ _ VIS6); [apply VIS5; lia| lia| lia| exact H88]).
  (* [comment removed for export] *)
  assert (STD : forall a, PMST.dep PMA.AD a -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a /\ L5.outside [(fb + 464, 416)] a).
  { intros a D. pose proof (PMAIS1.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia|].
    split; [exact (PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D))|]. intros rg [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
  assert (SRO : forall a, 65536 <= a < pa_rw_lo PMA.AD -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a /\ L5.outside [(fb + 464, 416)] a).
  { intros a Ha. cbn [pa_rw_lo PMA.AD ADDR_A] in Ha. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia|].
    split; [intros X; pose proof (L5A.aly_static_lo L C LYa a X); lia|]. intros rg [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
  assert (BASE6 : PMSTA.base_okA RSEGS PMA.AD M6) by (apply (PMKA.base_ok_keepA RSEGS PMA.AD L ar LB FF sp 24576 [(fb + 464, 416)] M1 M6 EK16 PMA.addrs_wf_A STD SRO BASE)).
  unfold PNSAX.push_root_spec, PNSAX.push_spec_at in PSH.
  apply (PSH fx6 R6 M6 model6 K LB1 FF LK1 Aw3 cr1 (fb + 464 + 392) 0 0 [] [] (0, 0, 0) (sp - 96) 703716 HH6 AM6 K0).
  { split; [rewrite L5K.rl1; exact hR1|]. split; [split; [lia| reflexivity]|]. split; [rewrite L5K.rl2, (KS6 2%nat) by inl; exact K2|].
    split; [rewrite L5K.rl3, (KS6 3%nat) by inl; rewrite CS5 by inl; rewrite CS4 by inl; exact Rgp|].
    split; [rewrite L5K.rl4, (KS6 4%nat) by inl; rewrite CS5 by inl; apply RTP; apply CS4; inl|].
    change (PMSPA.pm_scr 0) with 12288. split.
    { apply (L5SAR.astk_sub ar M6 M6 sp 24576 96 12288 ASTK6 (fun _ X => X)); [lia|lia|lia|]. replace (sp - 96) with (sp + (-6) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
    change (12288 / 8) with 1536. apply (PMKA.shadow_zero_sub M6 (sp - 24576) 3072 (sp - 96 - 12288) 1536);
      [apply PMAIS1.sub8; [exact A16| reflexivity]| replace (sp - 96 - 12288) with (sp - 12384) by lia; apply PMAIS1.sub8; [exact A16| reflexivity]| lia| lia| lia| exact STKSH6]. }
  { intros f Hf. specialize (FRS f Hf). lia. }
  { rewrite L5K.rl10. exact hR10. }
  { apply (PNARCK.frame_aobj FF fb); [exact FOK| lia| lia]. }
  { lia. }
  { unfold PMSPA.accA in *. apply (L5CB.aacc_sub M6 (fb + 464) 416); [exact ACC6| lia| lia]. }
  { left. split; [apply (PMCG.u64_of_zeros RSEGS M6); [apply (PMCG.zeros_sub M6 (fb + 464 + 320) 96); [exact ZM6| lia| lia]| lia| lia]|].
    split; [apply (PMCG.u64_of_zeros RSEGS M6); [apply (PMCG.zeros_sub M6 (fb + 464 + 320) 96); [exact ZM6| lia| lia]| lia| lia]|].
    split; [apply (PMCG.u64_of_zeros RSEGS M6); [apply (PMCG.zeros_sub M6 (fb + 464 + 320) 96); [exact ZM6| lia| lia]| lia| lia]|].
    split; [reflexivity|]. split; [reflexivity|]. split; reflexivity. }
  { left; reflexivity. }
  { intros _; lia. }
  { exact BASE6. }
  { unfold PNSAX.cells_root. exists (sp - 80), (sp - 84), (sp - 88). cbn [fst snd].
    split; [rewrite L5K.rl11; exact hR11|]. split; [rewrite L5K.rl12; exact hR12|]. split; [rewrite L5K.rl13; exact hR13|].
    assert (AC : forall p, sp - 96 <= p -> p + 4 <= sp -> p mod 4 = 0 -> PNSAX.arg_cell ar M6 FF (sp - 96) (fb + 464 + 392) p 4).
    { intros p P1 P2 P4. unfold PNSAX.arg_cell, PNSAX.arg_ok. split; [exact P4|]. split; [apply ACS6; lia|].
      split; [split; [right; lia| right; lia]|].
      apply (shz_at M6 (sp - 24576) 3072); [exact STKSH6| apply PMAIS1.sub8; [exact A16| reflexivity]| lia| lia]. }
    assert (S4 : forall d, d mod 4 = 0 -> (sp - d) mod 4 = 0).
    { intros d D4. pose proof A16 as A16'. clear - D4 A16'. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    split; [apply AC; [lia| lia| apply S4; reflexivity]|]. split; [apply AC; [lia| lia| apply S4; reflexivity]|]. split; [apply AC; [lia| lia| apply S4; reflexivity]|].
    split; [exact H80'|]. split; [exact H84'|]. split; [exact H88'|]. split; [lia|]. split; lia. }
  { intros _. exact CR2. }
  intros fx7 R7 M7 model7 LK7 Aw7 b7 k7 lenv7 cr7 RP7 LEN7 VEC7 ACCV7 BASE7 PO7 HP7 MRT7 INC7 IA7 AM7 HH7.
  destruct PO7 as [(X & _)|(_ & Ek7 & Ecr7)]; [exfalso; apply X; reflexivity|].
  cbn in Ek7. subst k7. change (PMSPA.pm_scr 0) with 12288 in HP7. cbn [app] in VEC7. change (PNM.BSZ * 2 ^ 0) with 40 in Ecr7. subst cr7.
  assert (ASTK7 : L5CA.astk ar M7 sp 24576).
  { apply (PMKA.astk_after_ahpres L ar LB1 FF M6 M7 sp 24576 (sp - 96) 12288 [(fb + 464 + 392, 24)] ASTK6 HP7); lia. }
  assert (EK67 : L5SAR.ek L ar LB FF sp 24576 [(fb + 464, 416)] M6 M7).
  { apply (L5SAR.ek_tl L ar LB (q, 16384) FF sp 24576 _ M6 M7).
    apply (L5SAR.ek_callee L ar LB1 [] FF [] sp 24576 (sp - 96) 12288 [(fb + 464, 416)] [(fb + 464 + 392, 24)] M6 M7 HP7); [lia| lia|].
    intros a Hc Ho rg [<-|[]] Hr. apply (Ho (fb + 464, 416)); [left; reflexivity| unfold L5.in_rng in *; cbn [fst snd] in *; lia]. }
  assert (DK67 : L5SAR.dk L ar LB FF sp 24576 M6 M7).
  { apply (L5SAR.dk_tl L ar LB (q, 16384) FF sp 24576 M6 M7). apply (L5SAR.dk_callee L ar LB1 [] FF [] sp 24576 (sp - 96) 12288 [(fb + 464 + 392, 24)] M6 M7 HP7); lia. }
  (* [comment removed for export] *)
  assert (T76 : forall a, 0 <= a < 2 ^ 64 -> ((sp - 96 <= a < sp) \/ (fb + 32 <= a < fb + 2040)) -> ~ (fb + 464 + 392 <= a < fb + 464 + 416) -> M7 (Z_to_bv 64 a) = M6 (Z_to_bv 64 a)).
  { intros a Ha Hr N. apply (proj1 HP7). split; [exact Ha|]. split; [destruct Hr as [Hr|Hr]; [apply SCL; lia| apply CLF; lia]|].
    intros rg [<-|[]] Hq. unfold L5.in_rng in Hq. cbn [fst snd] in Hq. lia. }
  assert (T65 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 88 <= a < sp - 76) -> M6 (Z_to_bv 64 a) = M5 (Z_to_bv 64 a)) by (intros a Ha N; apply FR6; [exact Ha| unfold W6; lia]).
  assert (T54 : forall a, 0 <= a < 2 ^ 64 -> ((sp - 96 <= a < sp) \/ (fb + 32 <= a < fb + 2040)) -> ~ (fb + 464 + 320 <= a < fb + 464 + 416) -> M5 (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)).
  { intros a Ha Hr N. apply PRES5; [exact Ha| destruct Hr as [Hr|Hr]; [apply SCL; lia| apply CLF; lia]| lia]. }
  assert (T43 : forall a, 0 <= a < 2 ^ 64 -> ~ W4 a -> M4 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)) by (intros a Ha N; apply FR4; [exact Ha| exact N]).
  assert (AG71 : forall a, (sp - 72 <= a < sp) \/ (fb + 32 <= a < fb + 2040 /\ ~ (fb + 464 + 280 <= a < fb + 464 + 288) /\ ~ (fb + 464 + 296 <= a < fb + 464 + 304)
                           /\ ~ (fb + 464 + 312 <= a < fb + 464 + 416)) -> M7 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Hr. destruct Hr as [Hr|Hr].
    - rewrite (T76 a ltac:(lia) ltac:(lia) ltac:(lia)), (T65 a ltac:(lia) ltac:(lia)), (T54 a ltac:(lia) ltac:(lia) ltac:(lia)), (T43 a ltac:(lia) ltac:(unfold W4; lia)).
      apply (AG13 a). lia.
    - rewrite (T76 a ltac:(lia) ltac:(lia) ltac:(lia)), (T65 a ltac:(lia) ltac:(lia)), (T54 a ltac:(lia) ltac:(lia) ltac:(lia)), (T43 a ltac:(lia) ltac:(unfold W4; lia)).
      apply (AG13 a). lia. }
  assert (AG74 : forall a, fb + 464 + 280 <= a < fb + 464 + 320 -> M7 (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)).
  { intros a Hr. rewrite (T76 a ltac:(lia) ltac:(lia) ltac:(lia)), (T65 a ltac:(lia) ltac:(lia)). exact (T54 a ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (AG75 : forall a, fb + 464 + 320 <= a < fb + 464 + 392 -> M7 (Z_to_bv 64 a) = M5 (Z_to_bv 64 a)).
  { intros a Hr. rewrite (T76 a ltac:(lia) ltac:(lia) ltac:(lia)). exact (T65 a ltac:(lia) ltac:(lia)). }
  assert (QS73 : forall y, q <= y < q + 16384 -> M7 (Z_to_bv 64 (S y)) = M3 (Z_to_bv 64 (S y))).
  { intros y Hy.
    assert (HSy : in_shadow_of q 16384 (S y) /\ 2147450880 <= S y < 2147450880 + 2 ^ 44).
    { unfold in_shadow_of, S, SB. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    destruct HSy as (HSy & SR).
    assert (Hb : forall sz scz, aclient L ar LB1 FF sz scz (S y)) by (intros sz scz; do 6 right; exists (q, 16384); split; [left; reflexivity| exact HSy]).
    rewrite (proj1 HP7 (S y)).
    2:{ split; [lia|]. split; [apply Hb|]. intros rg [<-|[]] Hq. unfold L5.in_rng in Hq. cbn [fst snd] in Hq. lia. }
    rewrite (T65 (S y) ltac:(lia) ltac:(lia)), (PRES5 (S y) ltac:(lia) (Hb _ _) ltac:(lia)). exact (T43 (S y) ltac:(lia) ltac:(unfold W4; lia)). }
  assert (QA7 : PMSPA.accA M7 q PM.CHUNK).
  { unfold PM.CHUNK. apply (PMFA.accA_agree M3 M7 q 16384); [intros y Hy; apply QS73; lia|].
    unfold PMSPA.accA. apply (L5CB.aacc_of_blk M3 q 16384 q 16384 QSH); lia. }
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH7) as (WB7 & _).
  destruct (WB7 (q, 16384) ltac:(unfold LB1, PM.vec_own; cbn [app]; right; left; reflexivity)) as (_ & QD7 & _). cbn [fst snd] in QD7.
  assert (ACC7 : PMSPA.accA M7 (fb + 464) 416) by (apply (PMKA.acc_keepA' L ar LB FF sp 24576 _ M6 M7 EK67 WAPP FRB _ 416 AOP ACC6)).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK7 _ Aw7 M7 model7 (fb + 464) 416 sp 24576 HH7 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & ODEF7 & _).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB1 FF LK1 cr1 Aw3 M3 model3 (fb + 464) 416 sp 24576 HH3 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & _ & OVIS3 & _).
  (* [comment removed for export] *)
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK7 _ Aw7 M7 model7 HH7) as (_ & VIS7 & _).
  assert (Zc8 : L5.u64_at RSEGS (mrestrict (ahid Aw7 model7) M7) (sp - 8) _) by (apply (PNARCK.svis L ar C HI LY HIok _ FF LK7 _ Aw7 M7 model7 sp (sp - 8) _ HH7 ASTK7); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG71; lia| lia| lia| exact S8]).
  assert (Zc16 : L5.u64_at RSEGS (mrestrict (ahid Aw7 model7) M7) (sp - 16) _) by (apply (PNARCK.svis L ar C HI LY HIok _ FF LK7 _ Aw7 M7 model7 sp (sp - 16) _ HH7 ASTK7); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG71; lia| lia| lia| exact S16]).
  assert (Zc24 : L5.u64_at RSEGS (mrestrict (ahid Aw7 model7) M7) (sp - 24) _) by (apply (PNARCK.svis L ar C HI LY HIok _ FF LK7 _ Aw7 M7 model7 sp (sp - 24) _ HH7 ASTK7); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG71; lia| lia| lia| exact S24]).
  assert (Zc32 : L5.u64_at RSEGS (mrestrict (ahid Aw7 model7) M7) (sp - 32) _) by (apply (PNARCK.svis L ar C HI LY HIok _ FF LK7 _ Aw7 M7 model7 sp (sp - 32) _ HH7 ASTK7); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG71; lia| lia| lia| exact S32]).
  assert (Zc40 : L5.u64_at RSEGS (mrestrict (ahid Aw7 model7) M7) (sp - 40) _) by (apply (PNARCK.svis L ar C HI LY HIok _ FF LK7 _ Aw7 M7 model7 sp (sp - 40) _ HH7 ASTK7); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG71; lia| lia| lia| exact S40]).
  assert (Zc48 : L5.u64_at RSEGS (mrestrict (ahid Aw7 model7) M7) (sp - 48) _) by (apply (PNARCK.svis L ar C HI LY HIok _ FF LK7 _ Aw7 M7 model7 sp (sp - 48) _ HH7 ASTK7); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG71; lia| lia| lia| exact S48]).
  assert (Zc56 : L5.u64_at RSEGS (mrestrict (ahid Aw7 model7) M7) (sp - 56) _) by (apply (PNARCK.svis L ar C HI LY HIok _ FF LK7 _ Aw7 M7 model7 sp (sp - 56) _ HH7 ASTK7); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG71; lia| lia| lia| exact S56]).
  assert (Zc64 : L5.u64_at RSEGS (mrestrict (ahid Aw7 model7) M7) (sp - 64) _) by (apply (PNARCK.svis L ar C HI LY HIok _ FF LK7 _ Aw7 M7 model7 sp (sp - 64) _ HH7 ASTK7); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG71; lia| lia| lia| exact S64]).
  assert (Zc72 : L5.u64_at RSEGS (mrestrict (ahid Aw7 model7) M7) (sp - 72) _) by (apply (PNARCK.svis L ar C HI LY HIok _ FF LK7 _ Aw7 M7 model7 sp (sp - 72) _ HH7 ASTK7); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG71; lia| lia| lia| exact S72]).
  assert (Y7 : L5.writable RSEGS (mrestrict (ahid Aw7 model7) M7) (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis _ M7 (sp - 4096) 4096 (VIS7 (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M7 sp 24576); [exact ASTK7| lia| lia| lia]. }
  assert (Z2 : getr R7 (reg 2) = Z_to_bv 64 (sp - 96)) by (rewrite (L5SAR.cs_of_preserved R6 R7 2 RP7) by inl; rewrite (KS6 2%nat) by inl; exact K2).
  LeanFeed.pfeed P (PNARCP.abrcZ_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx7 R7 (mrestrict (ahid Aw7 model7) M7) (fun j => match j with 2%nat => sp | 43%nat => bv_unsigned (getr R0 (reg 1)) | 44%nat => bv_unsigned (getr R0 (reg 8)) | 45%nat => bv_unsigned (getr R0 (reg 9)) | 46%nat => bv_unsigned (getr R0 (reg 18)) | 47%nat => bv_unsigned (getr R0 (reg 19)) | 48%nat => bv_unsigned (getr R0 (reg 20)) | 49%nat => bv_unsigned (getr R0 (reg 21)) | 50%nat => bv_unsigned (getr R0 (reg 22)) | 51%nat => bv_unsigned (getr R0 (reg 23)) | _ => 0 end)) ltac:(first [assumption | unfold PNARCP.aligned; lia | lia]).
  destruct P as (fx8 & R8 & M8v & MG8 & _ & FZ8 & MS8 & KS8 & zR1 & zR2 & zR8 & zR9 & zR18 & zR19 & zR20 & zR21 & zR22 & zR23).
  assert (E8 : M8v = mrestrict (ahid Aw7 model7) M7) by (apply L5SAR.mem_eq_of_agree; exact FZ8). subst M8v.
  assert (R8ra : getr R8 (reg 1) = Z_to_bv 64 r) by (rewrite zR1, Z_to_bv_bv_unsigned; exact Rra).
  pose proof (PMK.ret_to RSEGS fx8 R8 (mrestrict (ahid Aw7 model7) M7) 0xabd0c W_abcbc r F_abcbc eq_refl D_abcbc R8ra ltac:(lia) Hr2) as MS9.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK7 _ Aw7 M7 model7 fx7 fx8 R7 0xabce4 R8 r _ K HH7 AM7 ltac:(eapply msteps_trans; [exact MS8| exact MS9]) MG8 FZ8).
  intros M7' model7' HH7' AM7' MRT7' HID7' VIS7' MGM7' FR7'.
  assert (E7' : M7' = M7) by (apply L5SAR.mem_eq_of_agree; exact FR7'). subst M7'.
  (* [comment removed for export] *)
  Ltac a64 AG X Ms := apply (L5C.u64_at_agree RSEGS Ms); [intros i Hi; apply AG; (lia || fail 1 "AG")| (lia || fail 1 "B1")| (lia || fail 1 "B2")| exact X].
  Ltac a32 AG X Ms := apply (PMF.u32_at_agree RSEGS Ms); [intros i Hi; apply AG; (lia || fail 1 "AG")| (lia || fail 1 "B1")| (lia || fail 1 "B2")| exact X].
  Ltac a8 AG X Ms := apply (L5C.u8_at_agree RSEGS Ms); [intros i Hi; apply AG; (lia || fail 1 "AG")| (lia || fail 1 "B1")| (lia || fail 1 "B2")| exact X].
  unfold PNARCS.kont in KONT. apply (KONT fx8 R8 M7 model7' LK7 Aw7 q b7 (adebit L cr1 40)).
  - apply L5SAR.preserved_by_index. intros k Hk.
    assert (CH : forall k', In k' [3; 4; 24; 25; 26; 27]%nat -> getr R8 (reg k') = getr R0 (reg k')).
    { intros k' Hk'. assert (Y : In k' PNARCP.KS_abrcZ /\ In k' L5SAR.cs_all /\ In k' PNARCP.KS_abrcH /\ In k' [3; 4; 20; 24; 25; 26; 27]%nat)
        by (destruct Hk' as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; (split; [inl| split; [inl| split; inl]])).
      destruct Y as (Y1 & Y2 & Y3 & Y4). rewrite (KS8 k' Y1), (L5SAR.cs_of_preserved R6 R7 k' RP7 Y2), (KS6 k' Y3), (CS5 k' Y2). apply CS4. exact Y4. }
    unfold L5SAR.cs_all in Hk. destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|Hk]]]]]]]]]]].
    + rewrite zR2. exact (eq_sym Rsp).
    + apply CH; left; reflexivity.
    + apply CH; right; left; reflexivity.
    + rewrite zR8, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite zR9, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite zR18, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite zR19, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite zR20, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite zR21, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite zR22, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite zR23, Z_to_bv_bv_unsigned; reflexivity.
    + apply CH; right; right; exact Hk.
  - apply (PNARCK.bparser_init_at M7 (fb + 464) (fb + 96) q b7).
    + a64 AG71 H0 M1.
    + exact ODEF7.
    + exact ACC7.
    + a8 AG71 H8 M1.
    + a8 AG71 H9 M1.
    + a8 AG71 H10 M1.
    + a32 AG71 H12 M1.
    + a64 AG71 H32 M1.
    + a64 AG71 C48 M1.
    + a64 AG71 H56 M1.
    + a64 AG71 H112 M1.
    + a32 AG71 H144 M1.
    + a32 AG71 H148 M1.
    + a64 AG71 H152 M1.
    + a64 AG71 H160 M1.
    + apply (PMF.zeros_at_agree M1); [intros i Hi; apply AG71; lia| exact Z168].
    + a64 AG71 C264 M1.
    + replace (fb + 96 + 16) with (fb + 112) by lia. a64 AG71 C272 M1.
    + apply (L5C.u64_at_agree RSEGS M4); [intros i Hi; apply AG74; lia| lia| lia|].
      apply (PMAIS1.vis_u64 _ _ _ _ _ VIS4); [eapply L5A.avis_sub; [exact OVIS3| lia| lia]| lia| lia| exact G280].
    + a64 AG71 C296 M1.
    + apply (L5C.u64_at_agree RSEGS M4); [intros i Hi; apply AG74; lia| lia| lia|].
      apply (PMAIS1.vis_u64 _ _ _ _ _ VIS4); [eapply L5A.avis_sub; [exact OVIS3| lia| lia]| lia| lia| exact G296].
    + apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG71; lia| lia| lia|].
      apply (PMCG.u64_of_zeros RSEGS M1); [apply (PMCG.zeros_sub M1 (fb + 464 + 296) 16); [exact Z304| lia| lia]| lia| lia].
    + exact Q16.
    + exact QD7.
    + exact QA7.
    + apply (PMF.u32_at_agree RSEGS M4); [intros i Hi; apply AG74; lia| lia| lia|].
      apply (PMAIS1.vis_u32 _ _ _ _ _ VIS4); [eapply L5A.avis_sub; [exact OVIS3| lia| lia]| lia| lia| exact G312].
    + apply (L5C.u64_at_agree RSEGS M5); [intros i Hi; apply AG75; lia| lia| lia|].
      apply (PMCG.u64_of_zeros RSEGS M5); [apply (PMCG.zeros_sub M5 (fb + 464 + 320) 96); [exact Z336| lia| lia]| lia| lia].
    + apply (L5C.u64_at_agree RSEGS M5); [intros i Hi; apply AG75; lia| lia| lia|].
      apply (PMCG.u64_of_zeros RSEGS M5); [apply (PMCG.zeros_sub M5 (fb + 464 + 320) 96); [exact Z336| lia| lia]| lia| lia].
    + apply (L5C.u64_at_agree RSEGS M5); [intros i Hi; apply AG75; lia| lia| lia|].
      apply (PMCG.u64_of_zeros RSEGS M5); [apply (PMCG.zeros_sub M5 (fb + 464 + 320) 96); [exact Z336| lia| lia]| lia| lia].
    + apply (L5C.u8_at_agree RSEGS M5); [intros i Hi; apply AG75; lia| lia| lia|].
      apply (PMCG.u8_of_zeros RSEGS M5); [apply (PMCG.zeros_sub M5 (fb + 464 + 320) 96); [exact Z336| lia| lia]| lia| lia].
    + apply (L5C.u8_at_agree RSEGS M5); [intros i Hi; apply AG75; lia| lia| lia|].
      apply (PMCG.u8_of_zeros RSEGS M5); [apply (PMCG.zeros_sub M5 (fb + 464 + 320) 96); [exact Z336| lia| lia]| lia| lia].
    + exact VEC7.
    + lia.
    + lia.
  - change (PMSPA.pm_scr 6) with 24576. apply (L5SAR.ahpres_of L ar LB FF sp 24576 _ M0 M7).
    + apply (L5SAR.ek_trans L ar LB FF sp 24576 _ M0 M1 M7 EK). apply (L5SAR.ek_trans L ar LB FF sp 24576 _ M1 M6 M7 EK16 EK67).
    + pose proof ASTK7 as (_ & _ & _ & _ & SD7 & _). exact SD7.
    + apply (L5SAR.dk_trans L ar LB FF sp 24576 M0 M1 M7 DK).
      apply (L5SAR.dk_trans L ar LB FF sp 24576 M1 M3 M7 DK13).
      apply (L5SAR.dk_trans L ar LB FF sp 24576 M3 M4 M7 (L5SAR.dk_grows L ar LB FF sp 24576 M3 M4 MGM4)).
      apply (L5SAR.dk_trans L ar LB FF sp 24576 M4 M5 M7 DK45).
      apply (L5SAR.dk_trans L ar LB FF sp 24576 M5 M6 M7 (L5SAR.dk_grows L ar LB FF sp 24576 M5 M6 MGM6) DK67).
  - exact CR3.
  - apply (L5LZ.model_rt_trans model0 model7 model7'); [|exact MRT7']. apply (L5LZ.model_rt_trans model0 model6 model7); [|exact MRT7].
    apply (L5LZ.model_rt_trans model0 model5 model6); [|exact MRT6]. apply (L5LZ.model_rt_trans model0 model4 model5); [|exact MRT5].
    apply (L5LZ.model_rt_trans model0 model3 model4); [|exact MRT4]. apply (L5LZ.model_rt_trans model0 model1' model3); [|exact MRT3].
    apply (L5LZ.model_rt_trans model0 model1 model1'); [exact MRT| exact MRT1].
  - intros x Hx. apply INCK. apply INC7. exact Hx.
  - intros x Hx. apply IA7. apply IA3. apply INCA. exact Hx.
  - exact AM7'.
  - apply (PNARCK.ri_swap12 L ar C HI HIok (b7, PNM.BSZ * 2 ^ 0) (q, 16384) LB). exact HH7'.
Qed.
End Stage.
End PNARC3.
