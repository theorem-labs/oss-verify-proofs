(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StreamSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0 L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0S9 L5StepARB0S9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAEx PmSpecsA PmSpecsAX PeSpecsAb PnStatics.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCModelA PeCSpecsA PeCSpecsAb PeSpecsBXJ PmModelFactsA PmStep PeStepAB0 PeStepB2 PmCertKitG XIcptAs0B0 PeBCRdCtorStmts PeBCRdCtorP PeBIss1 PeBCRdCtor1 PeBRdKit PeBEmbKitJ.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_b4b64_b4b68.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.asan Require Import XIcptAB0S9 XIcptAs0KitB0S9 L5CoreBB0S9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia.
Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac dlia := first [ solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_ne ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_ne end ]
                   | solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_st ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_st end ] ].
Local Ltac lia := dlia.
Module PMBRD3.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma shz_at (M : word -> option byte) lo g p : shadow_zero M lo g -> lo mod 8 = 0 -> lo <= p -> p < lo + 8 * g -> byte_at M (S p) 0.
Proof.
  intros SZ L8 H1 H2. pose proof (SZ ((p - lo) / 8) ltac:(Lia.lia)) as X. replace (S p) with (S lo + (p - lo) / 8) by (unfold S, SB; Lia.lia). exact X.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma vec_set8 M M' v b k stk : 0 <= v -> v + 24 <= 2 ^ 64 -> 0 <= b -> b + 32 * 2 ^ k <= 2 ^ 64 ->
  L5C.agree_on M M' v 8 -> L5C.agree_on M M' (v + 16) 8 -> PMFA.agA M M' b (32 * 2 ^ k) ->
  L5.u64_at RSEGS M' (v + 8) (b + 32 * Z.of_nat (length stk)) ->
  PM.vec_at RSEGS PMSPA.accA PMSPA.annA M v b k stk -> PM.vec_at RSEGS PMSPA.accA PMSPA.annA M' v b k stk.
Proof.
  intros Hv Hv' Hb Hb' AG0 AG16 [AGB SHB] N8 (V0 & V8 & V16 & Hk & Hlen & Hal & DB & CB & AN & EL).
  pose proof (PM.pow2_pos k ltac:(Lia.lia)) as P2.
  split; [apply (L5C.u64_at_agree RSEGS M M'); [exact AG0| Lia.lia| Lia.lia| exact V0]|]. split; [exact N8|].
  split; [apply (L5C.u64_at_agree RSEGS M M'); [exact AG16| Lia.lia| Lia.lia| exact V16]|].
  split; [exact Hk|]. split; [exact Hlen|]. split; [exact Hal|].
  split; [apply (L5C.defined_agree M M' b _ AGB DB)|].
  split; [apply (PMFA.accA_agree M M'); [eapply PMFA.agsh_sub; [exact SHB| Lia.lia| Lia.lia]| exact CB]|].
  split; [apply (PMFA.annA_agree M M'); [exact (PMFA.mod16_8 b Hal)| Lia.lia| apply PMFA.blk8| exact SHB| exact AN]|].
  intros n Hn. apply (PMF.pstate_at_agree RSEGS M M'); [Lia.lia| Lia.lia| |apply EL; exact Hn].
  assert (Z.of_nat n < Z.of_nat (length stk)) by (apply Nat2Z.inj_lt; exact Hn).
  eapply (L5C.agree_on_sub M M' b (32 * 2 ^ k)); [exact AGB| Lia.lia| Lia.lia].
Qed.

Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMB.ly_as0 L C LY.

Theorem tail : PMB.opnew_spec L ar HI -> PMBX.slow_mi_spec L ar HI ->
  forall (fx : FPState) R0 M0 model0 K LB FF LK0 Aw0 cr sp r fb oa str sm R1 M1 model1 LK1 Aw1,
    PMBRS.pre L ar HI R0 M0 model0 K LB FF LK0 Aw0 cr sp r fb oa str sm ->
    PMBRS.rmid2 L ar HI R0 M0 model0 LB FF LK0 Aw0 cr sp fb R1 M1 model1 LK1 Aw1 ->
    PMBRS.kont L ar HI R0 M0 model0 K LB FF LK0 Aw0 cr sp r fb ->
    srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R1 0xb4dd4 M1 model1) K.
Proof.
  intros OPN PSH fx R0 M0 model0 K LB FF LK0 Aw0 cr sp r fb oa str sm R1 M1 model1 LK1 Aw1 PRE MID KONT.
  destruct PRE as (HH0 & AM0 & K0 & ENT & FRM & FRS & FOK & A10 & A11 & A12 & A13 & ODEF0 & ACC0 & ACCO0 & OO0' & OO8' & OO24' & ISS & BASE0 & LOCb & CRED).
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK0 & STKSH0). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  destruct MID as (M2' & M8 & M9 & M18 & M19 & M21 & MCSK & C48 & C264 & C272 & Z280 & C296 & Z304 & MC).
  destruct MC as (SRD & SSRC & HC & ODEF & ACC & ACCO & OO0 & OO8 & OO24 & ACCI & ASTK & STKSH & BASE & LOC & HH & AM & MRT & INCK & INCA & EK & DK).
  unfold PMBRS.op, PMBRS.SCR in *. change (24576 / 8) with 3072 in STKSH.
  destruct SRD as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72). destruct SSRC as (S104 & S112 & S120 & S128 & S136).
  destruct HC as (H0 & H8 & H9 & H12 & H16 & H20 & H32 & H56 & H112 & H144 & H148 & H152 & H160 & Z168).
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof AM as (Mh & MI).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & STOP & _).
  pose proof (PMBRDK.fb16 FF fb FOK) as F16.
  assert (AOP : PMSPA.aobjA FF (fb + 592) 384) by (apply (PMBRDK.frame_aobj FF fb); [exact FOK| lia| lia]).
  assert (O8 : (fb + 592) mod 8 = 0) by lia.
  pose proof (PMKB.aobj_of_aobjA FF _ _ AOP O8) as AOB.
  assert (AOIS : PMSPA.aobjA FF (fb + 96) 272) by (apply (PMBRDK.frame_aobj FF fb); [exact FOK| lia| lia]).
  assert (AOO : PMSPA.aobjA FF (fb + 592 + 464) 32) by (apply (PMBRDK.frame_aobj FF fb); [exact FOK| lia| lia]).
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47).
  { intros f Hf. destruct (WF f Hf) as (X1 & X2 & _). unfold app_mem, FS_BYTES in *. lia. }
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK1 cr Aw1 M1 model1 (fb + 592) 384 sp 24576 HH AOB ltac:(lia) ltac:(reflexivity)) as (OR & OBIG & _).
  assert (WAPP : PMKB.wapp [(fb + 592, 384)]) by (apply PMKB.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia| apply PMKB.wapp_nil]).
  assert (CLF : forall a, fb + 32 <= a < fb + 2040 -> forall LBz sz scz, aclient L ar LBz FF sz scz a).
  { intros a Ha LBz sz scz. apply (L5SAR.obj_client L ar LBz FF sz scz (fb + 32) 2008 a); [| lia].
    apply (PMKB.aobj_of_aobjA FF _ _ (PMBRDK.frame_aobj FF fb (fb + 32) 2008 FOK ltac:(lia) ltac:(lia))). lia. }
  assert (SCL : forall a, ahl_ceil ar <= a < 2 ^ 47 -> forall LBz sz scz, ~ (sz - scz <= a < sz) -> aclient L ar LBz FF sz scz a).
  { intros a Ha LBz sz scz N. apply L5SAR.stack_client; [lia| exact N]. }
  pose proof (PMBIS1.bvu (getr R0 (reg 1))) as UR1. pose proof (PMBIS1.bvu (getr R0 (reg 8))) as UR8. pose proof (PMBIS1.bvu (getr R0 (reg 9))) as UR9.
  pose proof (PMBIS1.bvu (getr R0 (reg 18))) as UR18. pose proof (PMBIS1.bvu (getr R0 (reg 19))) as UR19. pose proof (PMBIS1.bvu (getr R0 (reg 20))) as UR20.
  pose proof (PMBIS1.bvu (getr R0 (reg 21))) as UR21. pose proof (PMBIS1.bvu (getr R0 (reg 22))) as UR22. pose proof (PMBIS1.bvu (getr R0 (reg 23))) as UR23.
  assert (RTP : forall Rx, getr Rx (reg 4) = getr R0 (reg 4) -> getr Rx (reg 4) = Z_to_bv 64 (hl_tp L)) by (intros Rx E; rewrite E; exact Rtp).
  destruct (PMBRDK.rd_credit L ar C LY cr CRED) as (CR1 & CR2 & CR3).

  pose proof (PMBRDP.ardF_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx R1 (mrestrict (ahid Aw1 model1) M1) (fun j => match j with 2%nat => sp | 33%nat => fb + 592 | _ => 0 end)) as P.
  cbn beta iota in P.
  L5SAR.feed P ltac:(first [assumption | unfold PMBRDP.aligned; lia | lia]).
  destruct P as (fx1 & R2 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & fR1 & fR10).
  assert (E1 : M1v = mrestrict (ahid Aw1 model1) M1) by (apply L5SAR.mem_eq_of_agree; exact FZ1). subst M1v.
  unfold PMSPA.cfg.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok LB FF LK1 cr Aw1 M1 model1 fx fx1 R1 0xb4dd4 R2 0x136668 _ K HH AM MS1 MG1 FZ1).
  intros M1' model1' HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (E1' : M1' = M1) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1'.

  unfold PMB.opnew_spec, PMSPA.opnew_spec in OPN. cbn [pa_opnew PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B] in OPN.
  apply (OPN fx1 R2 M1 model1' K LB FF LK1 Aw1 cr 16384 (sp - 144) 740828 HH1 AM1 K0).
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
  assert (EK13 : L5SAR.ek L ar LB FF sp 24576 [(fb + 592, 384)] M1 M3).
  { apply (L5SAR.ek_callee L ar LB [] FF [] sp 24576 (sp - 144) 4112 _ [] M1 M3 HP3); [lia| lia| intros a _ _ rg []]. }
  assert (DK13 : L5SAR.dk L ar LB FF sp 24576 M1 M3) by (apply (L5SAR.dk_callee L ar LB [] FF [] sp 24576 (sp - 144) 4112 [] M1 M3 HP3); lia).
  assert (ASTK3 : L5CA.astk ar M3 sp 24576).
  { apply (L5SAR.astk_after L ar C HI HIok LB FF LK1 cr Aw1 M1 M1 M3 _ sp 24576 (sp - 144) 4112 [] HH1 ASTK (fun x X => X) HP3); lia. }
  assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF (sp - 144) 4112 a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha Hc. apply (proj1 HP3). split; [exact Ha|]. split; [exact Hc| intros rg []]. }
  set (LB1 := (q, 16384) :: LB) in *. set (cr1 := adebit L cr 16384) in *.

  assert (ACC3 : PMSPA.accA M3 (fb + 592) 384) by (apply (PMKB.acc_keepA' L ar LB FF sp 24576 _ M1 M3 EK13 WAPP FRB _ 384 AOP ACC)).
  assert (ACCI3 : PMSPA.accA M3 (fb + 96) 272) by (apply (PMKB.acc_keepA' L ar LB FF sp 24576 _ M1 M3 EK13 WAPP FRB _ 272 AOIS ACCI)).
  assert (ACCO3 : PMSPA.accA M3 (fb + 1056) 32) by (replace (fb + 1056) with (fb + 592 + 464) by lia; apply (PMKB.acc_keepA' L ar LB FF sp 24576 _ M1 M3 EK13 WAPP FRB _ 32 AOO ACCO)).
  assert (ODEF3 : L5.defined M3 (fb + 592) 384).
  { pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB1 FF LK1 cr1 Aw3 M3 model3 (fb + 592) 384 sp 24576 HH3 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & X & _). exact X. }
  destruct (PMBRDK.vfacts L ar C IL HI LY HIok ICok ILY LB1 FF LK1 cr1 Aw3 M3 model3 sp fb HH3 FOK ASTK3 ACC3 ACCI3 ACCO3 ODEF3)
    as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15).
  assert (AG13 : forall a, (sp - 136 <= a < sp) \/ (fb + 32 <= a < fb + 2040) -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha. apply KEEP3; [lia|]. destruct Ha as [Ha|Ha]; [apply SCL; lia| apply CLF; lia]. }
  assert (U8 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) (sp - 8) _) by (apply (PMBRDK.svis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M3 model3 sp (sp - 8) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact S8]).
  assert (U16 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) (sp - 16) _) by (apply (PMBRDK.svis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M3 model3 sp (sp - 16) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact S16]).
  assert (U24 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) (sp - 24) _) by (apply (PMBRDK.svis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M3 model3 sp (sp - 24) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact S24]).
  assert (U32 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) (sp - 32) _) by (apply (PMBRDK.svis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M3 model3 sp (sp - 32) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact S32]).
  assert (U40 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) (sp - 40) _) by (apply (PMBRDK.svis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M3 model3 sp (sp - 40) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact S40]).
  assert (U48 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) (sp - 48) _) by (apply (PMBRDK.svis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M3 model3 sp (sp - 48) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact S48]).
  assert (U56 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) (sp - 56) _) by (apply (PMBRDK.svis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M3 model3 sp (sp - 56) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact S56]).
  assert (U64 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) (sp - 64) _) by (apply (PMBRDK.svis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M3 model3 sp (sp - 64) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact S64]).
  assert (U72 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) (sp - 72) _) by (apply (PMBRDK.svis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M3 model3 sp (sp - 72) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact S72]).
  assert (U104 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) (sp - 104) _) by (apply (PMBRDK.svis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M3 model3 sp (sp - 104) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact S104]).
  assert (U112 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) (sp - 112) _) by (apply (PMBRDK.svis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M3 model3 sp (sp - 112) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact S112]).
  assert (U120 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) (sp - 120) _) by (apply (PMBRDK.svis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M3 model3 sp (sp - 120) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact S120]).
  assert (U128 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) (sp - 128) _) by (apply (PMBRDK.svis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M3 model3 sp (sp - 128) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact S128]).
  assert (U136 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) (sp - 136) _) by (apply (PMBRDK.svis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M3 model3 sp (sp - 136) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact S136]).
  assert (UO0 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) (fb + 592 + 464) 1276856).
  { apply (PMBRDK.fvis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M3 model3 fb _ _ HH3 FOK); [lia| lia|].
    apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact OO0]. }
  assert (UO8 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) (fb + 592 + 472) 16777216).
  { apply (PMBRDK.fvis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M3 model3 fb _ _ HH3 FOK); [lia| lia|].
    apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact OO8]. }
  assert (UO24 : L5.u32_at RSEGS (mrestrict (ahid Aw3 model3) M3) (fb + 592 + 488) 1024).
  { pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB1 FF LK1 cr1 Aw3 M3 model3 (fb + 32) 2008 0 0 HH3
                  (PMKB.aobj_of_aobjA FF _ _ (PMBRDK.frame_aobj FF fb (fb + 32) 2008 FOK ltac:(lia) ltac:(lia)) ltac:(lia)) ltac:(lia) ltac:(reflexivity)) as (_ & _ & _ & FV & _).
    apply (proj2 (L5A.u32_at_vis (ahid Aw3 model3) M3 (fb + 592 + 488) 1024 ltac:(eapply L5A.avis_sub; [exact FV| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (PMF.u32_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact OO24]. }
  assert (J2 : getr R3 (reg 2) = Z_to_bv 64 (sp - 144)) by (rewrite CS3, (KS1 2%nat) by inl; exact M2').
  assert (J8 : getr R3 (reg 8) = Z_to_bv 64 (fb + 592 + 32)) by (rewrite CS3, (KS1 8%nat) by inl; exact M8).
  assert (J9 : getr R3 (reg 9) = Z_to_bv 64 (fb + 592 + 24)) by (rewrite CS3, (KS1 9%nat) by inl; exact M9).
  assert (J18 : getr R3 (reg 18) = Z_to_bv 64 (fb + 592 + 304)) by (rewrite CS3, (KS1 18%nat) by inl; exact M18).
  assert (J19 : getr R3 (reg 19) = Z_to_bv 64 2147450880) by (rewrite CS3, (KS1 19%nat) by inl; exact M19).
  assert (J21 : getr R3 (reg 21) = Z_to_bv 64 2147450880) by (rewrite CS3, (KS1 21%nat) by inl; exact M21).
  pose proof (PMBRDP.ardG_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx2 R3 (mrestrict (ahid Aw3 model3) M3)
    (fun j => match j with 2%nat => sp | 33%nat => fb + 592 | 35%nat => q | 43%nat => bv_unsigned (getr R0 (reg 1)) | 44%nat => bv_unsigned (getr R0 (reg 8)) | 45%nat => bv_unsigned (getr R0 (reg 9)) | 46%nat => bv_unsigned (getr R0 (reg 18)) | 47%nat => bv_unsigned (getr R0 (reg 19)) | 48%nat => bv_unsigned (getr R0 (reg 20)) | 49%nat => bv_unsigned (getr R0 (reg 21)) | 50%nat => bv_unsigned (getr R0 (reg 22)) | 51%nat => bv_unsigned (getr R0 (reg 23)) | _ => 0 end)) as P.
  cbn beta iota in P.
  L5SAR.feed P ltac:(first [assumption | unfold PMBRDP.aligned; lia | lia]).
  destruct P as (fx4 & R4 & M4v & MG4 & _ & FZ4 & MS4 & KS4 & gR1 & gR2 & gR8 & gR10 & gR11 & gR12 & gR18 & gR19 & G328 & G320 & G304 & G288).
  set (W4 := fun a => (fb + 592 + 288 <= a < fb + 592 + 288 + 8) \/ (fb + 592 + 304 <= a < fb + 592 + 304 + 8) \/ (fb + 592 + 320 <= a < fb + 592 + 320 + 4)
                      \/ (fb + 592 + 328 <= a < fb + 592 + 328 + 8)).
  apply (L5SAR.apiece L ar C HI LYa HIok LB1 FF LK1 cr1 Aw3 M3 model3 fx2 fx4 R3 0xb4ddc R4 0x792dc M4v W4 K HH3 AM3 MS4 MG4).
  { intros a Ha N. apply FZ4; [exact Ha| intros X; apply N; unfold W4; left; exact X| intros X; apply N; unfold W4; right; left; exact X
                              | intros X; apply N; unfold W4; right; right; left; exact X| intros X; apply N; unfold W4; right; right; right; exact X]. }
  { intros a Ha Wa. assert (Wa' : fb + 592 <= a < fb + 592 + 384) by (unfold W4 in Wa; lia).
    split; [apply (L5SAR.obj_client L ar LB1 FF 0 0 _ 384 a AOB); lia| lia]. }
  intros M4 model4 HH4 AM4 MRT4 HID4 VIS4 MGM4 FR4 VV4.
  assert (EK34 : L5SAR.ek L ar LB FF sp 24576 [(fb + 592, 384)] M3 M4).
  { apply (L5SAR.ek_piece L ar LB FF sp 24576 _ M3 M4 W4 FR4). intros a Ha Hc Ho X.
    apply (Ho (fb + 592, 384)); [left; reflexivity| unfold L5.in_rng, W4 in *; cbn [fst snd]; lia]. }
  assert (ASTK4 : L5CA.astk ar M4 sp 24576) by (apply (L5SAR.astk_grows ar M3 M4 sp 24576 ASTK3 MGM4)).
  assert (ACC4 : PMSPA.accA M4 (fb + 592) 384) by (apply (PMKB.acc_keepA' L ar LB FF sp 24576 _ M3 M4 EK34 WAPP FRB _ 384 AOP ACC3)).
  assert (ODEF4 : L5.defined M4 (fb + 592) 384) by (apply (L5.defined_grows M3 M4 _ _ MGM4); exact ODEF3).
  assert (CS4 : forall k, In k [3; 4; 20; 22; 23; 24; 25; 26; 27]%nat -> getr R4 (reg k) = getr R0 (reg k)).
  { intros k Hk. assert (Hk' : In k PMBRDP.KS_ardG /\ In k L5SAR.cs_all /\ In k PMBRDP.KS_ardF)
      by (destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; (split; [inl| split; inl])).
    destruct Hk' as (Y1 & Y2 & Y3). rewrite (KS4 k Y1), (CS3 k Y2), (KS1 k Y3). apply MCSK. exact Hk. }

  apply (PMBRDK.amset L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 sp 96 (fb + 592) 384 fx4 R4 M4 model4 K 336 24 740068 AOB); [lia| lia| lia| exact HH4| exact AM4| exact ASTK4| exact ACC4| exact ODEF4
     | lia| lia| replace (sp - 96) with (sp + (-6) * 16) by lia; rewrite Z.mod_add by lia; exact A16| exact gR10| exact gR11| exact gR12| apply RTP; apply CS4; inl| exact gR1| reflexivity| lia| exact gR2| exact K0|].
  intros R5a M5a model5a R5aa0 RP5a Z336a PRES5a SDEF5a DEF5a MRT5a AM5a HH5a.
  assert (CS5a : forall k, In k L5SAR.cs_all -> getr R5a (reg k) = getr R4 (reg k)) by (intros k Hk; apply (L5SAR.cs_of_preserved R4 R5a k RP5a Hk)).
  destruct (PMBRDK.mset_post L ar C HI HIok LB1 FF LK1 cr1 Aw3 sp 96 (fb + 592) 384 M4 M5a model4 336 24 HH4 ASTK4 AOB ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PRES5a SDEF5a DEF5a)
    as (EK45a & DK45a & ASTK5a).

  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB1 FF LK1 cr1 Aw3 M5a model5a HH5a) as (_ & VIS5a & _).
  assert (Y5a : L5.writable RSEGS (mrestrict (ahid Aw3 model5a) M5a) (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis _ M5a (sp - 4096) 4096 (VIS5a (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M5a sp 24576); [exact ASTK5a| lia| lia| lia]. }
  assert (Ka2 : getr R5a (reg 2) = Z_to_bv 64 (sp - 96)) by (rewrite CS5a by inl; exact gR2).
  assert (Ka8 : getr R5a (reg 8) = Z_to_bv 64 (fb + 592)) by (rewrite CS5a by inl; exact gR8).
  assert (Ka9 : getr R5a (reg 9) = Z_to_bv 64 (fb + 592 + 24)) by (rewrite CS5a by inl; rewrite (KS4 9%nat) by inl; exact J9).
  assert (Ka18 : getr R5a (reg 18) = Z_to_bv 64 (fb + 592 + 336)) by (rewrite CS5a by inl; exact gR18).
  assert (Ka19 : getr R5a (reg 19) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 19)))) by (rewrite CS5a by inl; exact gR19).
  assert (Ka21 : getr R5a (reg 21) = Z_to_bv 64 2147450880) by (rewrite CS5a by inl; rewrite (KS4 21%nat) by inl; exact J21).
  pose proof (PMBRDP.ardG2_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx4 R5a (mrestrict (ahid Aw3 model5a) M5a) (fun j => match j with 2%nat => sp | 33%nat => fb + 592 | 43%nat => bv_unsigned (getr R0 (reg 1)) | 44%nat => bv_unsigned (getr R0 (reg 8)) | 45%nat => bv_unsigned (getr R0 (reg 9)) | 46%nat => bv_unsigned (getr R0 (reg 18)) | 47%nat => bv_unsigned (getr R0 (reg 19)) | 48%nat => bv_unsigned (getr R0 (reg 20)) | 49%nat => bv_unsigned (getr R0 (reg 21)) | 50%nat => bv_unsigned (getr R0 (reg 22)) | 51%nat => bv_unsigned (getr R0 (reg 23)) | _ => 0 end)) as P.
  cbn beta iota in P.
  L5SAR.feed P ltac:(first [assumption | unfold PMBRDP.aligned; lia | lia]).
  destruct P as (fx5 & R5b & M5v & MG5b & _ & FZ5b & MS5b & KS5b & g2R1 & g2R10 & g2R11 & g2R12 & g2R20).
  assert (E5b : M5v = mrestrict (ahid Aw3 model5a) M5a) by (apply L5SAR.mem_eq_of_agree; exact FZ5b). subst M5v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok LB1 FF LK1 cr1 Aw3 M5a model5a fx4 fx5 R5a 0xb4ae4 R5b 0x792dc _ K HH5a AM5a MS5b MG5b FZ5b).
  intros M5a' model5b HH5b AM5b MRT5b HID5b VIS5b MGM5b FR5b.
  assert (E5a' : M5a' = M5a) by (apply L5SAR.mem_eq_of_agree; exact FR5b). subst M5a'.
  assert (ACC5a : PMSPA.accA M5a (fb + 592) 384) by (apply (PMKB.acc_keepA' L ar LB FF sp 24576 _ M4 M5a (L5SAR.ek_tl L ar LB (q, 16384) FF sp 24576 _ M4 M5a EK45a) WAPP FRB _ 384 AOP ACC4)).
  assert (ODEF5a : L5.defined M5a (fb + 592) 384).
  { pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB1 FF LK1 cr1 Aw3 M5a model5a (fb + 592) 384 sp 24576 HH5a AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & X & _). exact X. }

  apply (PMBRDK.amset L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 sp 96 (fb + 592) 384 fx5 R5b M5a model5b K 360 24 740088 AOB); [lia| lia| lia| exact HH5b| exact AM5b| exact ASTK5a| exact ACC5a| exact ODEF5a
     | lia| lia| replace (sp - 96) with (sp + (-6) * 16) by lia; rewrite Z.mod_add by lia; exact A16| exact g2R10| exact g2R11| exact g2R12| | exact g2R1| reflexivity| lia| | exact K0|].
  { apply RTP. rewrite (KS5b 4%nat) by inl. rewrite CS5a by inl. apply CS4; inl. }
  { rewrite (KS5b 2%nat) by inl. exact Ka2. }
  intros R5 M5 model5 R5a0 RP5 Z360 PRES5b SDEF5 DEF5 MRT5 AM5 HH5.
  assert (CS5b : forall k, In k L5SAR.cs_all -> getr R5 (reg k) = getr R5b (reg k)) by (intros k Hk; apply (L5SAR.cs_of_preserved R5b R5 k RP5 Hk)).
  destruct (PMBRDK.mset_post L ar C HI HIok LB1 FF LK1 cr1 Aw3 sp 96 (fb + 592) 384 M5a M5 model5b 360 24 HH5b ASTK5a AOB ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PRES5b SDEF5 DEF5)
    as (EK45b & DK45b & ASTK5).
  assert (CS5 : forall k, In k L5SAR.cs_all -> In k PMBRDP.KS_ardG2 -> getr R5 (reg k) = getr R4 (reg k))
    by (intros k H1 H2; rewrite (CS5b k H1), (KS5b k H2), (CS5a k H1); reflexivity).
  pose proof (L5SAR.ek_tl L ar LB (q, 16384) FF sp 24576 _ M4 M5 (L5SAR.ek_trans L ar LB1 FF sp 24576 _ M4 M5a M5 EK45a EK45b)) as EK45.
  pose proof (L5SAR.dk_tl L ar LB (q, 16384) FF sp 24576 M4 M5 (L5SAR.dk_trans L ar LB1 FF sp 24576 M4 M5a M5 DK45a DK45b)) as DK45.

  assert (PRES5 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB1 FF (sp - 96) 2560 a -> ~ (fb + 592 + 336 <= a < fb + 592 + 336 + 48) -> M5 (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)).
  { intros a Ha Hc N. rewrite PRES5b; [| exact Ha| exact Hc| lia]. apply PRES5a; [exact Ha| exact Hc| lia]. }
  assert (Z336 : PM.zeros_at M5 (fb + 592 + 336) 48).
  { intros i Hi. destruct (Z_lt_le_dec i 24) as [Li|Li].
    - unfold byte_at. rewrite PRES5b; [apply Z336a; lia| lia| apply (L5SAR.obj_client L ar LB1 FF _ _ _ 384 _ AOB); lia| lia].
    - replace (fb + 592 + 336 + i) with (fb + 592 + 360 + (i - 24)) by lia. apply Z360. lia. }

  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB1 FF LK1 cr1 Aw3 M5 model5 HH5) as (_ & VIS5 & _).
  assert (Y5 : L5.writable RSEGS (mrestrict (ahid Aw3 model5) M5) (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis _ M5 (sp - 4096) 4096 (VIS5 (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M5 sp 24576); [exact ASTK5| lia| lia| lia]. }
  assert (K2 : getr R5 (reg 2) = Z_to_bv 64 (sp - 96)) by (rewrite CS5b by inl; rewrite (KS5b 2%nat) by inl; exact Ka2).
  assert (K8 : getr R5 (reg 8) = Z_to_bv 64 (fb + 592)) by (rewrite CS5b by inl; rewrite (KS5b 8%nat) by inl; exact Ka8).
  assert (K9 : getr R5 (reg 9) = Z_to_bv 64 (fb + 592 + 24)) by (rewrite CS5b by inl; rewrite (KS5b 9%nat) by inl; exact Ka9).
  assert (K18 : getr R5 (reg 18) = Z_to_bv 64 (fb + 592 + 336)) by (rewrite CS5b by inl; rewrite (KS5b 18%nat) by inl; exact Ka18).
  assert (K19 : getr R5 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 19)))) by (rewrite CS5b by inl; rewrite (KS5b 19%nat) by inl; exact Ka19).
  assert (K20 : getr R5 (reg 20) = Z_to_bv 64 (fb + 592 + 360)) by (rewrite CS5b by inl; exact g2R20).
  assert (K21 : getr R5 (reg 21) = Z_to_bv 64 2147450880) by (rewrite CS5b by inl; rewrite (KS5b 21%nat) by inl; exact Ka21).
  assert (ZV0 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model5) M5) (fb + 592 + 360) 0).
  { apply (PMBRDK.fvis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M5 model5 fb _ _ HH5 FOK); [lia| lia|].
    apply (PMCG.u64_of_zeros RSEGS M5); [apply (PMCG.zeros_sub M5 (fb + 592 + 360) 24); [exact Z360| lia| lia]| lia| lia]. }
  assert (ZV8 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model5) M5) (fb + 592 + 368) 0).
  { apply (PMBRDK.fvis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M5 model5 fb _ _ HH5 FOK); [lia| lia|].
    apply (PMCG.u64_of_zeros RSEGS M5); [apply (PMCG.zeros_sub M5 (fb + 592 + 360) 24); [exact Z360| lia| lia]| lia| lia]. }
  assert (ZV16 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model5) M5) (fb + 592 + 376) 0).
  { apply (PMBRDK.fvis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M5 model5 fb _ _ HH5 FOK); [lia| lia|].
    apply (PMCG.u64_of_zeros RSEGS M5); [apply (PMCG.zeros_sub M5 (fb + 592 + 360) 24); [exact Z360| lia| lia]| lia| lia]. }
  assert (ACC5 : PMSPA.accA M5 (fb + 592) 384) by (apply (PMKB.acc_keepA' L ar LB FF sp 24576 _ M4 M5 EK45 WAPP FRB _ 384 AOP ACC4)).
  assert (ACCI5 : PMSPA.accA M5 (fb + 96) 272) by (apply (PMKB.acc_keepA' L ar LB FF sp 24576 _ M1 M5 (L5SAR.ek_trans L ar LB FF sp 24576 _ M1 M4 M5 (L5SAR.ek_trans L ar LB FF sp 24576 _ M1 M3 M4 EK13 EK34) EK45) WAPP FRB _ 272 AOIS ACCI)).
  assert (ACCO5 : PMSPA.accA M5 (fb + 1056) 32) by (replace (fb + 1056) with (fb + 592 + 464) by lia; apply (PMKB.acc_keepA' L ar LB FF sp 24576 _ M1 M5 (L5SAR.ek_trans L ar LB FF sp 24576 _ M1 M4 M5 (L5SAR.ek_trans L ar LB FF sp 24576 _ M1 M3 M4 EK13 EK34) EK45) WAPP FRB _ 32 AOO ACCO)).
  assert (ODEF5 : L5.defined M5 (fb + 592) 384).
  { pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB1 FF LK1 cr1 Aw3 M5 model5 (fb + 592) 384 sp 24576 HH5 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & X & _). exact X. }
  destruct (PMBRDK.vfacts L ar C IL HI LY HIok ICok ILY LB1 FF LK1 cr1 Aw3 M5 model5 sp fb HH5 FOK ASTK5 ACC5 ACCI5 ACCO5 ODEF5)
    as (XH1 & XH2 & XH3 & XH4 & XH5 & XH6 & XH7 & XH8 & XH9 & XH10 & XH11 & XH12 & XH13 & XH14 & XH15).
  pose proof (PMBRDP.ardH_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx5 R5 (mrestrict (ahid Aw3 model5) M5) (fun j => match j with 2%nat => sp | 33%nat => fb + 592 | 43%nat => bv_unsigned (getr R0 (reg 1)) | 44%nat => bv_unsigned (getr R0 (reg 8)) | 45%nat => bv_unsigned (getr R0 (reg 9)) | 46%nat => bv_unsigned (getr R0 (reg 18)) | 47%nat => bv_unsigned (getr R0 (reg 19)) | 48%nat => bv_unsigned (getr R0 (reg 20)) | 49%nat => bv_unsigned (getr R0 (reg 21)) | 50%nat => bv_unsigned (getr R0 (reg 22)) | 51%nat => bv_unsigned (getr R0 (reg 23)) | _ => 0 end)) as P.
  cbn beta iota in P.
  L5SAR.feed P ltac:(first [assumption | unfold PMBRDP.aligned; lia | lia]).
  destruct P as (fx6 & R6 & M6v & MG6 & _ & FZ6 & MS6 & KS6 & hR1 & hR10 & hR11 & hR12 & hR19 & hR22 & hR23 & H84 & H80).
  set (W6 := fun a => sp - 84 <= a < sp - 84 + 8).
  apply (L5SAR.apiece L ar C HI LYa HIok LB1 FF LK1 cr1 Aw3 M5 model5 fx5 fx6 R5 0xb4af8 R6 0xb5250 M6v W6 K HH5 AM5 MS6 MG6).
  { intros a Ha N. apply FZ6; [exact Ha| exact N]. }
  { intros a Ha Wa. unfold W6 in Wa. split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
  intros M6 model6 HH6 AM6 MRT6 HID6 VIS6 MGM6 FR6 VV6.
  assert (EK56 : L5SAR.ek L ar LB FF sp 24576 [(fb + 592, 384)] M5 M6).
  { apply (L5SAR.ek_piece L ar LB FF sp 24576 _ M5 M6 W6 FR6). intros a Ha Hc Ho X. unfold W6 in X.
    destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK1 cr Aw1 M1 _ sp 24576 a HH SPT Hc) as [Z1|Z1]; lia. }
  assert (ASTK6 : L5CA.astk ar M6 sp 24576) by (apply (L5SAR.astk_grows ar M5 M6 sp 24576 ASTK5 MGM6)).
  assert (EK16 : L5SAR.ek L ar LB FF sp 24576 [(fb + 592, 384)] M1 M6).
  { apply (L5SAR.ek_trans L ar LB FF sp 24576 _ M1 M5 M6); [| exact EK56]. apply (L5SAR.ek_trans L ar LB FF sp 24576 _ M1 M4 M5); [| exact EK45].
    apply (L5SAR.ek_trans L ar LB FF sp 24576 _ M1 M3 M4 EK13 EK34). }
  assert (STKSH6 : shadow_zero M6 (sp - 24576) 3072).
  { apply (PMKB.stksh_keepA L ar LB FF sp 24576 _ M1 M6 EK16 WAPP); [lia| lia| lia| | lia| exact STKSH]. apply PMBIS1.sub8; [exact A16| reflexivity]. }
  assert (ACC6 : PMSPA.accA M6 (fb + 592) 384) by (apply (PMKB.acc_keepA' L ar LB FF sp 24576 _ M1 M6 EK16 WAPP FRB _ 384 AOP ACC)).
  assert (ACS6 : forall a n, sp - 24576 <= a -> a + n <= sp -> PMSPA.accA M6 a n).
  { intros a n Y1 Y2. unfold PMSPA.accA. apply (L5CB.aacc_of_zero M6 (sp - 24576) 3072 a n STKSH6); [apply PMBIS1.sub8; [exact A16| reflexivity]| lia| lia| lia]. }
  assert (ZM6 : PM.zeros_at M6 (fb + 592 + 336) 48).
  { apply (PMF.zeros_at_agree M5); [intros i Hi; apply FR6; [lia| unfold W6; lia]| exact Z336]. }
  assert (H80' : L5.u32_at RSEGS M6 (sp - 80) 0) by (apply (PMBIS1.vis_u32 _ _ _ _ _ VIS6); [apply VIS5; lia| lia| lia| exact H80]).
  assert (H84' : L5.u32_at RSEGS M6 (sp - 84) 0) by (apply (PMBIS1.vis_u32 _ _ _ _ _ VIS6); [apply VIS5; lia| lia| lia| exact H84]).

  unfold PMBX.slow_mi_spec, PMSBX.slow_spec_at in PSH. cbn [paa_esp_mi PMB.AAD PeLayoutA.AADDR_B PeCLayoutB.CAADDR_B] in PSH.
  apply (PSH fx6 R6 M6 model6 K LB1 FF LK1 Aw3 cr1 (fb + 592 + 360) 0 0 [] [] (PM.PS 0 0 0 0) (sp - 96) 740200 HH6 AM6 K0).
  { split; [rewrite L5K.rl1; exact hR1|]. split; [split; [lia| reflexivity]|]. split; [rewrite L5K.rl2, (KS6 2%nat) by inl; exact K2|].
    split; [rewrite L5K.rl3, (KS6 3%nat) by inl; rewrite CS5 by inl; rewrite CS4 by inl; exact Rgp|].
    split; [rewrite L5K.rl4, (KS6 4%nat) by inl; rewrite CS5 by inl; apply RTP; apply CS4; inl|].
    change (PMSPA.pm_scr 0) with 12288. split.
    { apply (L5SAR.astk_sub ar M6 M6 sp 24576 96 12288 ASTK6 (fun _ X => X)); [lia|lia|lia|]. replace (sp - 96) with (sp + (-6) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
    change (12288 / 8) with 1536. apply (PMKB.shadow_zero_sub M6 (sp - 24576) 3072 (sp - 96 - 12288) 1536);
      [apply PMBIS1.sub8; [exact A16| reflexivity]| replace (sp - 96 - 12288) with (sp - 12384) by lia; apply PMBIS1.sub8; [exact A16| reflexivity]| lia| lia| lia| exact STKSH6]. }
  { intros f Hf. specialize (FRS f Hf). lia. }
  { rewrite L5K.rl10. exact hR10. }
  { apply (PMBRDK.frame_aobj FF fb); [exact FOK| lia| lia]. }
  { lia. }
  { unfold PMSPA.accA in *. apply (L5CB.aacc_sub M6 (fb + 592) 384); [exact ACC6| lia| lia]. }
  { left. split; [apply (PMCG.u64_of_zeros RSEGS M6); [apply (PMCG.zeros_sub M6 (fb + 592 + 336) 48); [exact ZM6| lia| lia]| lia| lia]|].
    split; [apply (PMCG.u64_of_zeros RSEGS M6); [apply (PMCG.zeros_sub M6 (fb + 592 + 336) 48); [exact ZM6| lia| lia]| lia| lia]|].
    split; [apply (PMCG.u64_of_zeros RSEGS M6); [apply (PMCG.zeros_sub M6 (fb + 592 + 336) 48); [exact ZM6| lia| lia]| lia| lia]|].
    split; [reflexivity|]. split; [reflexivity|]. split; reflexivity. }
  { left; reflexivity. }
  { lia. }
  { unfold PMSAX.cells_mi. exists (sp - 80), (sp - 84), 0, 0.
    split; [rewrite L5K.rl11; exact hR11|]. split; [rewrite L5K.rl12; exact hR12|]. split; [lia|]. split; [lia|].
    split; [apply ACS6; lia|]. split; [apply ACS6; lia|].
    split; [unfold PMSAX.arg_ok; split; [right; lia| right; lia]|]. split; [unfold PMSAX.arg_ok; split; [right; lia| right; lia]|].
    split; [apply (shz_at M6 (sp - 24576) 3072); [exact STKSH6| apply PMBIS1.sub8; [exact A16| reflexivity]| lia| lia]|].
    split; [apply (shz_at M6 (sp - 24576) 3072); [exact STKSH6| apply PMBIS1.sub8; [exact A16| reflexivity]| lia| lia]|].
    split; [exact H80'|]. split; [exact H84'|]. split; [lia|]. split; [lia| reflexivity]. }
  { exact CR2. }
  intros fx7 R7 M7 model7 LK7 Aw7 b7 k7 cr7 RP7 VEC7 ACCV7 Ek7 Ecr7 A07 HP7 MRT7 INC7 IA7 AM7 HH7.
  assert (A07' : getr R7 (reg 10) = Z_to_bv 64 (b7 + 32)) by (pose proof A07 as X; rewrite L5K.rl10 in X; exact X).
  cbn in Ek7. subst k7. change (PMSPA.pm_scr 0) with 12288 in HP7. cbn [app] in VEC7. change (32 * 2 ^ 0) with 32 in Ecr7. subst cr7.
  assert (ASTK7 : L5CA.astk ar M7 sp 24576).
  { apply (PMKB.astk_after_ahpres L ar LB1 FF M6 M7 sp 24576 (sp - 96) 12288 [(fb + 592 + 360, 24)] ASTK6 HP7); lia. }
  assert (EK67 : L5SAR.ek L ar LB FF sp 24576 [(fb + 592, 384)] M6 M7).
  { apply (L5SAR.ek_tl L ar LB (q, 16384) FF sp 24576 _ M6 M7).
    apply (L5SAR.ek_callee L ar LB1 [] FF [] sp 24576 (sp - 96) 12288 [(fb + 592, 384)] [(fb + 592 + 360, 24)] M6 M7 HP7); [lia| lia|].
    intros a Hc Ho rg [<-|[]] Hr. apply (Ho (fb + 592, 384)); [left; reflexivity| unfold L5.in_rng in *; cbn [fst snd] in *; lia]. }
  assert (DK67 : L5SAR.dk L ar LB FF sp 24576 M6 M7).
  { apply (L5SAR.dk_tl L ar LB (q, 16384) FF sp 24576 M6 M7). apply (L5SAR.dk_callee L ar LB1 [] FF [] sp 24576 (sp - 96) 12288 [(fb + 592 + 360, 24)] M6 M7 HP7); lia. }

  assert (T76 : forall a, 0 <= a < 2 ^ 64 -> ((sp - 96 <= a < sp) \/ (fb + 32 <= a < fb + 2040)) -> ~ (fb + 592 + 360 <= a < fb + 592 + 384) -> M7 (Z_to_bv 64 a) = M6 (Z_to_bv 64 a)).
  { intros a Ha Hr N. apply (proj1 HP7). split; [exact Ha|]. split; [destruct Hr as [Hr|Hr]; [apply SCL; lia| apply CLF; lia]|].
    intros rg [<-|[]] Hq. unfold L5.in_rng in Hq. cbn [fst snd] in Hq. lia. }
  assert (T65 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 84 <= a < sp - 76) -> M6 (Z_to_bv 64 a) = M5 (Z_to_bv 64 a)) by (intros a Ha N; apply FR6; [exact Ha| unfold W6; lia]).
  assert (T54 : forall a, 0 <= a < 2 ^ 64 -> ((sp - 96 <= a < sp) \/ (fb + 32 <= a < fb + 2040)) -> ~ (fb + 592 + 336 <= a < fb + 592 + 384) -> M5 (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)).
  { intros a Ha Hr N. apply PRES5; [exact Ha| destruct Hr as [Hr|Hr]; [apply SCL; lia| apply CLF; lia]| lia]. }
  assert (T43 : forall a, 0 <= a < 2 ^ 64 -> ~ W4 a -> M4 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)) by (intros a Ha N; apply FR4; [exact Ha| exact N]).
  assert (AG71 : forall a, (sp - 72 <= a < sp) \/ (fb + 32 <= a < fb + 2040 /\ ~ (fb + 592 + 288 <= a < fb + 592 + 296) /\ ~ (fb + 592 + 304 <= a < fb + 592 + 312)
                           /\ ~ (fb + 592 + 320 <= a < fb + 592 + 384)) -> M7 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Hr. destruct Hr as [Hr|Hr].
    - rewrite (T76 a ltac:(lia) ltac:(lia) ltac:(lia)), (T65 a ltac:(lia) ltac:(lia)), (T54 a ltac:(lia) ltac:(lia) ltac:(lia)), (T43 a ltac:(lia) ltac:(unfold W4; lia)).
      apply (AG13 a). lia.
    - rewrite (T76 a ltac:(lia) ltac:(lia) ltac:(lia)), (T65 a ltac:(lia) ltac:(lia)), (T54 a ltac:(lia) ltac:(lia) ltac:(lia)), (T43 a ltac:(lia) ltac:(unfold W4; lia)).
      apply (AG13 a). lia. }
  assert (AG74 : forall a, fb + 592 + 288 <= a < fb + 592 + 336 -> M7 (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)).
  { intros a Hr. rewrite (T76 a ltac:(lia) ltac:(lia) ltac:(lia)), (T65 a ltac:(lia) ltac:(lia)). exact (T54 a ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (AG75 : forall a, fb + 592 + 336 <= a < fb + 592 + 360 -> M7 (Z_to_bv 64 a) = M5 (Z_to_bv 64 a)).
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
  assert (ACC7 : PMSPA.accA M7 (fb + 592) 384) by (apply (PMKB.acc_keepA' L ar LB FF sp 24576 _ M6 M7 EK67 WAPP FRB _ 384 AOP ACC6)).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK7 _ Aw7 M7 model7 (fb + 592) 384 sp 24576 HH7 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & ODEF7 & _).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB1 FF LK1 cr1 Aw3 M3 model3 (fb + 592) 384 sp 24576 HH3 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & _ & OVIS3 & _).

  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK7 _ Aw7 M7 model7 HH7) as (_ & VIS7 & _).
  assert (Y7 : L5.writable RSEGS (mrestrict (ahid Aw7 model7) M7) (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis _ M7 (sp - 4096) 4096 (VIS7 (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M7 sp 24576); [exact ASTK7| lia| lia| lia]. }
  assert (Zc8 : L5.u64_at RSEGS (mrestrict (ahid Aw7 model7) M7) (sp - 8) _) by (apply (PMBRDK.svis L ar C HI LY HIok _ FF LK7 _ Aw7 M7 model7 sp (sp - 8) _ HH7 ASTK7); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG71; lia| lia| lia| exact S8]).
  assert (Zc16 : L5.u64_at RSEGS (mrestrict (ahid Aw7 model7) M7) (sp - 16) _) by (apply (PMBRDK.svis L ar C HI LY HIok _ FF LK7 _ Aw7 M7 model7 sp (sp - 16) _ HH7 ASTK7); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG71; lia| lia| lia| exact S16]).
  assert (Zc24 : L5.u64_at RSEGS (mrestrict (ahid Aw7 model7) M7) (sp - 24) _) by (apply (PMBRDK.svis L ar C HI LY HIok _ FF LK7 _ Aw7 M7 model7 sp (sp - 24) _ HH7 ASTK7); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG71; lia| lia| lia| exact S24]).
  assert (Zc32 : L5.u64_at RSEGS (mrestrict (ahid Aw7 model7) M7) (sp - 32) _) by (apply (PMBRDK.svis L ar C HI LY HIok _ FF LK7 _ Aw7 M7 model7 sp (sp - 32) _ HH7 ASTK7); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG71; lia| lia| lia| exact S32]).
  assert (Zc40 : L5.u64_at RSEGS (mrestrict (ahid Aw7 model7) M7) (sp - 40) _) by (apply (PMBRDK.svis L ar C HI LY HIok _ FF LK7 _ Aw7 M7 model7 sp (sp - 40) _ HH7 ASTK7); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG71; lia| lia| lia| exact S40]).
  assert (Zc48 : L5.u64_at RSEGS (mrestrict (ahid Aw7 model7) M7) (sp - 48) _) by (apply (PMBRDK.svis L ar C HI LY HIok _ FF LK7 _ Aw7 M7 model7 sp (sp - 48) _ HH7 ASTK7); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG71; lia| lia| lia| exact S48]).
  assert (Zc56 : L5.u64_at RSEGS (mrestrict (ahid Aw7 model7) M7) (sp - 56) _) by (apply (PMBRDK.svis L ar C HI LY HIok _ FF LK7 _ Aw7 M7 model7 sp (sp - 56) _ HH7 ASTK7); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG71; lia| lia| lia| exact S56]).
  assert (Zc64 : L5.u64_at RSEGS (mrestrict (ahid Aw7 model7) M7) (sp - 64) _) by (apply (PMBRDK.svis L ar C HI LY HIok _ FF LK7 _ Aw7 M7 model7 sp (sp - 64) _ HH7 ASTK7); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG71; lia| lia| lia| exact S64]).
  assert (Zc72 : L5.u64_at RSEGS (mrestrict (ahid Aw7 model7) M7) (sp - 72) _) by (apply (PMBRDK.svis L ar C HI LY HIok _ FF LK7 _ Aw7 M7 model7 sp (sp - 72) _ HH7 ASTK7); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG71; lia| lia| lia| exact S72]).
  assert (Z2 : getr R7 (reg 2) = Z_to_bv 64 (sp - 96)) by (rewrite (L5SAR.cs_of_preserved R6 R7 2 RP7) by inl; rewrite (KS6 2%nat) by inl; exact K2).
  assert (Z19 : getr R7 (reg 19) = Z_to_bv 64 (fb + 592 + 368)) by (rewrite (L5SAR.cs_of_preserved R6 R7 19 RP7) by inl; exact hR19).
  assert (Z21 : getr R7 (reg 21) = Z_to_bv 64 2147450880) by (rewrite (L5SAR.cs_of_preserved R6 R7 21 RP7) by inl; rewrite (KS6 21%nat) by inl; exact K21).
  assert (Z22 : getr R7 (reg 22) = Z_to_bv 64 ((fb + 592 + 368) / 8 + 2147450880)) by (rewrite (L5SAR.cs_of_preserved R6 R7 22 RP7) by inl; exact hR22).
  assert (EK17 : L5SAR.ek L ar LB FF sp 24576 [(fb + 592, 384)] M1 M7) by (apply (L5SAR.ek_trans L ar LB FF sp 24576 _ M1 M6 M7 EK16 EK67)).
  assert (ACCI7 : PMSPA.accA M7 (fb + 96) 272) by (apply (PMKB.acc_keepA' L ar LB FF sp 24576 _ M1 M7 EK17 WAPP FRB _ 272 AOIS ACCI)).
  assert (ACCO7 : PMSPA.accA M7 (fb + 1056) 32) by (replace (fb + 1056) with (fb + 592 + 464) by lia; apply (PMKB.acc_keepA' L ar LB FF sp 24576 _ M1 M7 EK17 WAPP FRB _ 32 AOO ACCO)).
  destruct (PMBRDK.vfacts L ar C IL HI LY HIok ICok ILY _ FF LK7 _ Aw7 M7 model7 sp fb HH7 FOK ASTK7 ACC7 ACCI7 ACCO7 ODEF7)
    as (XZ1 & XZ2 & XZ3 & XZ4 & XZ5 & XZ6 & XZ7 & XZ8 & XZ9 & XZ10 & XZ11 & XZ12 & XZ13 & XZ14 & XZ15).
  destruct (PMBEK.blk_facts L ar C HI LY HIok _ FF LK7 _ Aw7 M7 _ b7 (32 * 2 ^ 0) HH7 ltac:(left; reflexivity)) as (Bb0 & Bb1 & Bb2 & Bb3 & Bb16 & Bb5 & Bb6 & Bb7 & Bb8).
  change (32 * 2 ^ 0) with 32 in Bb1, Bb2, Bb3, Bb5, Bb6, Bb7, Bb8.
  pose proof (PMBRDP.ardZ_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx7 R7 (mrestrict (ahid Aw7 model7) M7) (fun j => match j with 2%nat => sp | 33%nat => fb + 592 | 41%nat => b7 + 32 | 43%nat => bv_unsigned (getr R0 (reg 1)) | 44%nat => bv_unsigned (getr R0 (reg 8)) | 45%nat => bv_unsigned (getr R0 (reg 9)) | 46%nat => bv_unsigned (getr R0 (reg 18)) | 47%nat => bv_unsigned (getr R0 (reg 19)) | 48%nat => bv_unsigned (getr R0 (reg 20)) | 49%nat => bv_unsigned (getr R0 (reg 21)) | 50%nat => bv_unsigned (getr R0 (reg 22)) | 51%nat => bv_unsigned (getr R0 (reg 23)) | _ => 0 end)) as P.
  cbn beta iota in P.
  L5SAR.feed P ltac:(first [assumption | unfold PMBRDP.aligned; lia | lia]).
  destruct P as (fx8 & R8 & M8v & MG8 & _ & FZ8 & MS8 & KS8 & zR1 & zR2 & zR8 & zR9 & zR10 & zR11 & zR18 & zR19 & zR20 & zR21 & zR22 & zR23 & Z368).
  assert (R8ra : getr R8 (reg 1) = Z_to_bv 64 r) by (rewrite zR1, Z_to_bv_bv_unsigned; exact Rra).
  pose proof (PMK.ret_to RSEGS fx8 R8 M8v 0xb4bb4 W_b4b64 r F_b4b64 eq_refl D_b4b64 R8ra ltac:(lia) Hr2) as MS9.
  set (W8 := fun a => fb + 592 + 368 <= a < fb + 592 + 368 + 8).
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK7 _ Aw7 M7 model7 fx7 fx8 R7 0xb4b68 R8 r M8v W8 K HH7 AM7 ltac:(eapply msteps_trans; [exact MS8| exact MS9]) MG8).
  { intros a Ha N. apply FZ8; [exact Ha| exact N]. }
  { intros a Ha Wa. unfold W8 in Wa. split; [apply (L5SAR.obj_client L ar _ FF 0 0 (fb + 592) 384 a AOB); lia| lia]. }
  intros Mz model7' HH7' AM7' MRT7' HID7' VIS7' MGM8 FR8 VV8.

  assert (T87 : forall a, 0 <= a < 2 ^ 64 -> ~ (fb + 592 + 368 <= a < fb + 592 + 376) -> Mz (Z_to_bv 64 a) = M7 (Z_to_bv 64 a)).
  { intros a Ha N. apply FR8; [exact Ha| unfold W8; lia]. }
  assert (AG81 : forall a, (sp - 72 <= a < sp) \/ (fb + 32 <= a < fb + 2040 /\ ~ (fb + 592 + 288 <= a < fb + 592 + 296) /\ ~ (fb + 592 + 304 <= a < fb + 592 + 312)
                           /\ ~ (fb + 592 + 320 <= a < fb + 592 + 384)) -> Mz (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Hr. rewrite T87; [apply AG71; exact Hr| lia| lia]. }
  assert (AG84 : forall a, fb + 592 + 288 <= a < fb + 592 + 336 -> Mz (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)).
  { intros a Hr. rewrite T87; [apply AG74; exact Hr| lia| lia]. }
  assert (AG85 : forall a, fb + 592 + 336 <= a < fb + 592 + 360 -> Mz (Z_to_bv 64 a) = M5 (Z_to_bv 64 a)).
  { intros a Hr. rewrite T87; [apply AG75; exact Hr| lia| lia]. }
  clear AG71 AG74 AG75. rename AG81 into AG71. rename AG84 into AG74. rename AG85 into AG75.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (SHW : forall x, 0 <= x < 2 ^ 47 -> Mz (Z_to_bv 64 (S x)) = M7 (Z_to_bv 64 (S x))).
  { intros x Hx. apply T87; [unfold S, SB; Lia.lia|]. unfold S, SB. destruct OBIG as [YW|YW]; Lia.lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (ODEF8 : L5.defined Mz (fb + 592) 384) by (apply (L5.defined_grows M7 Mz _ _ MGM8); exact ODEF7).
  assert (ACC8 : PMSPA.accA Mz (fb + 592) 384) by (apply (PMFA.accA_agree M7 Mz); [intros x Hx; apply SHW; lia| exact ACC7]).
  assert (QD8 : L5.defined Mz q 16384) by (apply (L5.defined_grows M7 Mz _ _ MGM8); exact QD7).
  assert (QA8 : PMSPA.accA Mz q PM.CHUNK) by (apply (PMFA.accA_agree M7 Mz); [intros x Hx; apply SHW; unfold PM.CHUNK in Hx; lia| exact QA7]).
  clear ODEF7 ACC7 QD7 QA7. rename ODEF8 into ODEF7. rename ACC8 into ACC7. rename QD8 into QD7. rename QA8 into QA7.
  assert (VEC8 : PM.vec_at RSEGS PMSPA.accA PMSPA.annA Mz (fb + 592 + 360) b7 0 [PM.PS 0 0 0 0]).
  { apply (vec_set8 M7 Mz); [lia| lia| lia| change (32 * 2 ^ 0) with 32; lia| | | | | exact VEC7].
    - intros i Hi. apply T87; lia.
    - intros i Hi. apply T87; lia.
    - change (32 * 2 ^ 0) with 32. split.
      + intros i Hi. apply T87; [lia|]. destruct AOP as (f & Hf & Xf1 & Xf2). destruct (Bb8 f Hf) as [Y|Y]; lia.
      + intros x Hx. apply SHW. lia.
    - cbn [length Z.of_nat]. replace (b7 + 32 * Z.of_nat 1) with (b7 + 32) by lia. replace (fb + 592 + 360 + 8) with (fb + 592 + 368) by lia.
      apply (PMBIS1.vis_u64 _ _ _ _ _ VIS7'); [eapply L5A.avis_sub; [exact (proj1 (proj2 (proj2 (proj2 (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK7 _ Aw7 M7 model7 (fb + 592) 384 sp 24576 HH7 AOB ltac:(lia) ltac:(reflexivity))))))| lia| lia]| lia| lia| exact Z368]. }

  Ltac a64 AG X Ms := apply (L5C.u64_at_agree RSEGS Ms); [intros i Hi; apply AG; (lia || fail 1 "AG")| (lia || fail 1 "B1")| (lia || fail 1 "B2")| exact X].
  Ltac a32 AG X Ms := apply (PMF.u32_at_agree RSEGS Ms); [intros i Hi; apply AG; (lia || fail 1 "AG")| (lia || fail 1 "B1")| (lia || fail 1 "B2")| exact X].
  Ltac a8 AG X Ms := apply (L5C.u8_at_agree RSEGS Ms); [intros i Hi; apply AG; (lia || fail 1 "AG")| (lia || fail 1 "B1")| (lia || fail 1 "B2")| exact X].
  unfold PMBRS.kont in KONT. apply (KONT fx8 R8 Mz model7' LK7 Aw7 q b7 (adebit L cr1 32)).
  - apply L5SAR.preserved_by_index. intros k Hk.
    assert (CH : forall k', In k' [3; 4; 24; 25; 26; 27]%nat -> getr R8 (reg k') = getr R0 (reg k')).
    { intros k' Hk'. assert (Y : In k' PMBRDP.KS_ardZ /\ In k' L5SAR.cs_all /\ In k' PMBRDP.KS_ardH /\ In k' PMBRDP.KS_ardG2)
        by (destruct Hk' as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; (split; [inl| split; [inl| split; inl]])).
      destruct Y as (Y1 & Y2 & Y3 & Y4). rewrite (KS8 k' Y1), (L5SAR.cs_of_preserved R6 R7 k' RP7 Y2), (KS6 k' Y3), (CS5 k' Y2 Y4). apply CS4.
      destruct Hk' as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; inl. }
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
  - apply (PMBRDK.parser_init_at Mz (fb + 592) (fb + 96) q b7).
    + a64 AG71 H0 M1.
    + exact ODEF7.
    + exact ACC7.
    + a8 AG71 H8 M1.
    + a8 AG71 H9 M1.
    + a32 AG71 H12 M1.
    + a8 AG71 H16 M1.
    + a32 AG71 H20 M1.
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
      apply (PMBIS1.vis_u64 _ _ _ _ _ VIS4); [eapply L5A.avis_sub; [exact OVIS3| lia| lia]| lia| lia| exact G288].
    + a64 AG71 C296 M1.
    + apply (L5C.u64_at_agree RSEGS M4); [intros i Hi; apply AG74; lia| lia| lia|].
      apply (PMBIS1.vis_u64 _ _ _ _ _ VIS4); [eapply L5A.avis_sub; [exact OVIS3| lia| lia]| lia| lia| exact G304].
    + apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG71; lia| lia| lia|].
      apply (PMCG.u64_of_zeros RSEGS M1); [apply (PMCG.zeros_sub M1 (fb + 592 + 304) 16); [exact Z304| lia| lia]| lia| lia].
    + exact Q16.
    + exact QD7.
    + exact QA7.
    + apply (PMF.u32_at_agree RSEGS M4); [intros i Hi; apply AG74; lia| lia| lia|].
      apply (PMBIS1.vis_u32 _ _ _ _ _ VIS4); [eapply L5A.avis_sub; [exact OVIS3| lia| lia]| lia| lia| exact G320].
    + apply (L5C.u64_at_agree RSEGS M4); [intros i Hi; apply AG74; lia| lia| lia|].
      apply (PMBIS1.vis_u64 _ _ _ _ _ VIS4); [eapply L5A.avis_sub; [exact OVIS3| lia| lia]| lia| lia| exact G328].
    + apply (L5C.u8_at_agree RSEGS M5); [intros i Hi; apply AG75; lia| lia| lia|].
      apply (PMCG.u8_of_zeros RSEGS M5); [apply (PMCG.zeros_sub M5 (fb + 592 + 336) 48); [exact Z336| lia| lia]| lia| lia].
    + exact VEC8.
    + lia.
    + lia.
  - change (PMSPA.pm_scr 6) with 24576. apply (L5SAR.ahpres_of L ar LB FF sp 24576 _ M0 Mz).
    + apply (L5SAR.ek_trans L ar LB FF sp 24576 _ M0 M1 Mz EK). apply (L5SAR.ek_trans L ar LB FF sp 24576 _ M1 M7 Mz EK17).
      apply (L5SAR.ek_piece L ar LB FF sp 24576 _ M7 Mz W8 FR8). intros a Ha Hc Ho X.
      apply (Ho (fb + 592, 384)); [left; reflexivity| unfold L5.in_rng, W8 in *; cbn [fst snd]; lia].
    + pose proof ASTK7 as (_ & _ & _ & _ & SD7 & _). apply (L5.defined_grows M7 Mz _ _ MGM8). exact SD7.
    + apply (L5SAR.dk_trans L ar LB FF sp 24576 M0 M7 Mz); [| exact (L5SAR.dk_grows L ar LB FF sp 24576 M7 Mz MGM8)].
      apply (L5SAR.dk_trans L ar LB FF sp 24576 M0 M1 M7 DK).
      apply (L5SAR.dk_trans L ar LB FF sp 24576 M1 M3 M7 DK13).
      apply (L5SAR.dk_trans L ar LB FF sp 24576 M3 M4 M7 (L5SAR.dk_grows L ar LB FF sp 24576 M3 M4 MGM4)).
      apply (L5SAR.dk_trans L ar LB FF sp 24576 M4 M5 M7 DK45).
      apply (L5SAR.dk_trans L ar LB FF sp 24576 M5 M6 M7 (L5SAR.dk_grows L ar LB FF sp 24576 M5 M6 MGM6) DK67).
  - exact CR3.
  - apply (L5LZ.model_rt_trans model0 model7 model7'); [|exact MRT7']. apply (L5LZ.model_rt_trans model0 model6 model7); [|exact MRT7].
    apply (L5LZ.model_rt_trans model0 model5 model6); [|exact MRT6]. apply (L5LZ.model_rt_trans model0 model5b model5); [|exact MRT5]. apply (L5LZ.model_rt_trans model0 model5a model5b); [|exact MRT5b].
    apply (L5LZ.model_rt_trans model0 model4 model5a); [|exact MRT5a].
    apply (L5LZ.model_rt_trans model0 model3 model4); [|exact MRT4]. apply (L5LZ.model_rt_trans model0 model1' model3); [|exact MRT3].
    apply (L5LZ.model_rt_trans model0 model1 model1'); [exact MRT| exact MRT1].
  - intros x Hx. apply INCK. apply INC7. exact Hx.
  - intros x Hx. apply IA7. apply IA3. apply INCA. exact Hx.
  - exact AM7'.
  - unfold PM.parser_own, PMSPA.parser_init, PM.src_own, PM.vec_own. cbn [PM.p_src PM.p_b PM.p_k PM.p_tb PM.sr_qc PM.vs_own app].
    apply (PMBRDK.ri_swap12 L ar C HI HIok). unfold LB1, PM.vec_own in HH7'. cbn [app] in HH7'. unfold PM.CHUNK. exact HH7'.
Qed.
End Stage.
End PMBRD3.
