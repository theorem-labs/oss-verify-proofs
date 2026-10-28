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
     PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b PnSpecsAX_b PnSpecsAXR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8 PnModelFacts. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgV8A_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b
     PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnStepA_b PnStepA2_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import XIcptAs0_b PnAReaderCtorStmts_b PnAReaderCtorP_b PnAIss1_b PnAReaderCtor1_b PnAReaderCtorKit_b Ba0_code_abcbc_abcc0_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import XIcptA_b XIcptAs0Kit_b L5CoreB_b.
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
Module PNARC3.
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

Lemma bvec_of_hole (M M' : word -> option byte) v b k stk : 0 <= v -> v + 24 <= 2 ^ 64 -> 0 <= b -> b + PNM.BSZ * 2 ^ k <= 2 ^ 64 ->
  L5C.agree_on M M' v 8 -> L5C.agree_on M M' (v + 16) 8 -> PMFA.agA M M' b (PNM.BSZ * 2 ^ k) ->
  L5.u64_at RSEGS M' (v + 8) (b + PNM.BSZ * Z.of_nat (length stk)) ->
  PNSAXR.bvec_hole RSEGS M v b k stk -> PNM.bvec_at RSEGS PMSPA.accA PNRA.annA M' v b k stk.
Proof.
  intros H1 H2 H3 H4 AG0 AG16 (AGB & SHB) V8 (V0 & V16 & Hk & Hlen & Hal & DB & CB & AB & EL).
  assert (Hnk : PNM.BSZ * Z.of_nat (length stk) <= PNM.BSZ * 2 ^ k) by (unfold PNM.BSZ; Lia.nia).
  unfold PNM.bvec_at.
  split; [apply (L5C.u64_at_agree RSEGS M M'); [exact AG0| Lia.lia| Lia.lia| exact V0]|]. split; [exact V8|].
  split; [apply (L5C.u64_at_agree RSEGS M M'); [exact AG16| Lia.lia| Lia.lia| exact V16]|].
  split; [exact Hk|]. split; [exact Hlen|]. split; [exact Hal|].
  split; [exact (L5C.defined_agree M M' b _ AGB DB)|].
  split; [apply (PMFA.accA_agree M M' b _); [apply (PMFA.agsh_sub M M' b (PNM.BSZ * 2 ^ k)); [exact SHB| Lia.lia| Lia.nia]| exact CB]|].
  assert (C8 : (PNM.BSZ * 2 ^ k) mod 8 = 0) by (replace (PNM.BSZ * 2 ^ k) with ((5 * 2 ^ k) * 8) by (unfold PNM.BSZ; Lia.lia); apply Z.mod_mul; Lia.lia).
  split; [apply (PMFA.annA_agree M M' b _ _); [apply PMFA.mod16_8; exact Hal| unfold PNM.BSZ in *; Lia.nia| exact C8| exact SHB| exact AB]|].
  intros i Hi. apply (PNMF.bstate_at_agree RSEGS M M'); [unfold PNM.BSZ in *; Lia.nia| unfold PNM.BSZ in *; Lia.nia| | exact (EL i Hi)].
  eapply (L5C.agree_on_sub M M'); [exact AGB| unfold PNM.BSZ; Lia.nia| unfold PNM.BSZ in *; Lia.nia].
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma stack_zeros6 M sp : shadow_zero M (sp - 24576) 3072 -> sp mod 16 = 0 -> L5KA.zeros_at M (sp / 8 + 2147450368) 512.
Proof.
  intros SZ S16 i Hi. pose proof (SZ (2560 + i) ltac:(Lia.lia)) as X. unfold byte_at, S, SB in X.
  replace (sp / 8 + 2147450368 + i) with ((sp - 24576) / 8 + 2147450880 + (2560 + i)) by Lia.lia. exact X.
Qed.
Lemma stack_sh_in (ar : asan_run) M sp : L5CA.astk ar M sp 24576 -> forall i, 0 <= i < 512 -> in_shadow_of (ahl_ceil ar) (ar_sptop ar - ahl_ceil ar) (sp / 8 + 2147450368 + i).
Proof.
  intros (A16 & SLO & SHI & _) i Hi. unfold in_shadow_of, S, SB. Lia.lia.
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

Theorem tail : PMA.opnew_spec L ar HI -> PNSAXR.push_root_slow_spec RSEGS PMA.AD L ar HI 0xad11c ->
  forall (fx : FPState) R0 M0 model0 K LB FF LK0 Aw0 cr sp r fb oo oa str sm R1 M1 model1 LK1 Aw1,
    PNARCS.pre L ar HI R0 M0 model0 K LB FF LK0 Aw0 cr sp r fb oo oa str sm ->
    PNARCS.rmid2 L ar HI R0 M0 model0 LB FF LK0 Aw0 cr sp fb oo R1 M1 model1 LK1 Aw1 ->
    PNARCS.kont L ar HI R0 M0 model0 K LB FF LK0 Aw0 cr sp r fb ->
    srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R1 0xacc4c M1 model1) K.
Proof.
  intros OPN PSH fx R0 M0 model0 K LB FF LK0 Aw0 cr sp r fb oo oa str sm R1 M1 model1 LK1 Aw1 PRE MID KONT.
  destruct PRE as (HH0 & AM0 & K0 & ENT & FRM & FRS & FOK & A10 & A11 & A12 & A13 & AOO & OOAP & OO8 & ODEF0 & ACC0 & ACCO0 & OO0' & OO16' & ISS & BASE0 & LOCb & CRED).
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK0 & STKSH0). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  destruct MID as (M2' & MR8 & M9 & M18 & M19 & M23 & MCSK & C40 & C256 & C264 & Z272 & C288 & Z296 & MC).
  destruct MC as (SRD & SSRC & HC & ODEF & ACC & ACCO & OO0 & OO16 & ACCI & ASTK & STKSH & BASE & LOC & HH & AM & MRT & INCK & INCA & EK & DK).
  unfold PNARCS.op, PNARCS.SCR in *. change (24576 / 8) with 3072 in STKSH.
  destruct SRD as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88). destruct SSRC as (S120 & S128 & S136 & S144 & S152).
  destruct HC as (H0 & H8 & H9 & H10 & H12 & H24 & H48 & H104 & H136 & H140 & H144 & H152 & Z160).
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
  assert (J22F : getr R1 (reg 22) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 22)))) by (rewrite (MCSK 22%nat) by inl; symmetry; apply Z_to_bv_bv_unsigned).
  LeanFeed.pfeed P (PNARCP.abrcF_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx R1 (mrestrict (ahid Aw1 model1) M1) (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => oo | 50%nat => bv_unsigned (getr R0 (reg 22)) | _ => 0 end)) ltac:(first [assumption | unfold PNARCP.aligned; lia | lia]).
  destruct P as (fx1 & R2 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & fR1 & fR10).
  assert (E1 : M1v = mrestrict (ahid Aw1 model1) M1) by (apply L5SAR.mem_eq_of_agree; exact FZ1). subst M1v.
  unfold PMSPA.cfg.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok LB FF LK1 cr Aw1 M1 model1 fx fx1 R1 0xacc4c R2 0x130338 _ K HH AM MS1 MG1 FZ1).
  intros M1' model1' HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (E1' : M1' = M1) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1'.
  (* [comment removed for export] *)
  unfold PMA.opnew_spec, PMSPA.opnew_spec in OPN. cbn [pa_opnew PMA.AD ADDR_A] in OPN.
  apply (OPN fx1 R2 M1 model1' K LB FF LK1 Aw1 cr 16384 (sp - 160) 707668 HH1 AM1 K0).
  { rewrite L5K.rl10. exact fR10. }
  { lia. }
  { exact CR1. }
  { rewrite L5K.rl1. exact fR1. }
  { split; [lia| reflexivity]. }
  { rewrite L5K.rl2, (KS1 2%nat) by inl. exact M2'. }
  { rewrite L5K.rl4, (KS1 4%nat) by inl. apply RTP. apply MCSK. right; left; reflexivity. }
  { unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR. apply (L5SAR.astk_sub ar M1 M1 sp 24576 160 (16 + 4096) ASTK (fun x X => X)); [lia| lia| lia|].
    replace (sp - 160) with (sp + (-10) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  intros fx2 R3 M3 model3 Aw3 q Rq RP3 FRESH HP3 MRT3 IA3 AM3 HH3.
  unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR in HP3. change (16 + 4096) with 4112 in HP3. rewrite L5K.rl10 in Rq.
  destruct FRESH as (QR & QAP & QFA & QDEF & QSH). pose proof QR as (Q0 & Q1 & Q16 & _ & Q4 & Q5). unfold app_mem in Q5.
  assert (CS3 : forall k, In k L5SAR.cs_all -> getr R3 (reg k) = getr R2 (reg k)) by (intros k Hk; apply (L5SAR.cs_of_preserved R2 R3 k RP3 Hk)).
  assert (EK13 : L5SAR.ek L ar LB FF sp 24576 [(fb + 464, 416)] M1 M3).
  { apply (L5SAR.ek_callee L ar LB [] FF [] sp 24576 (sp - 160) 4112 _ [] M1 M3 HP3); [lia| lia| intros a _ _ rg []]. }
  assert (DK13 : L5SAR.dk L ar LB FF sp 24576 M1 M3) by (apply (L5SAR.dk_callee L ar LB [] FF [] sp 24576 (sp - 160) 4112 [] M1 M3 HP3); lia).
  assert (ASTK3 : L5CA.astk ar M3 sp 24576).
  { apply (L5SAR.astk_after L ar C HI HIok LB FF LK1 cr Aw1 M1 M1 M3 _ sp 24576 (sp - 160) 4112 [] HH1 ASTK (fun x X => X) HP3); lia. }
  assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF (sp - 160) 4112 a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
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
  assert (OOIMG : 65536 + 6840320 <= oo \/ oo + 24 <= 65536) by (left; Lia.lia).
  assert (CLO : forall a, oo <= a < oo + 24 -> forall LBz sz scz, aclient L ar LBz FF sz scz a).
  { intros a Ha LBz sz scz. apply (L5SAR.obj_client L ar LBz FF sz scz oo 24 a (PMKA.aobj_of_aobjA FF _ _ AOO OO8)). Lia.lia. }
  assert (AG13 : forall a, (sp - 152 <= a < sp) \/ (fb + 32 <= a < fb + 2040) \/ (oo <= a < oo + 24) -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
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
  assert (U120 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) (sp - 120) _) by (apply (PNARCK.svis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M3 model3 sp (sp - 120) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact S120]).
  assert (U128 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) (sp - 128) _) by (apply (PNARCK.svis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M3 model3 sp (sp - 128) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact S128]).
  assert (U136 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) (sp - 136) _) by (apply (PNARCK.svis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M3 model3 sp (sp - 136) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact S136]).
  assert (U144 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) (sp - 144) _) by (apply (PNARCK.svis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M3 model3 sp (sp - 144) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact S144]).
  assert (U152 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) (sp - 152) _) by (apply (PNARCK.svis L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 M3 model3 sp (sp - 152) _ HH3 ASTK3); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact S152]).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB1 FF LK1 cr1 Aw3 M3 model3 oo 24 0 0 HH3 (PMKA.aobj_of_aobjA FF _ _ AOO OO8) ltac:(Lia.lia) ltac:(reflexivity))
    as (_ & _ & _ & OOV & _).
  assert (UO0 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model3) M3) oo 1251800).
  { apply (proj2 (L5A.u64_at_vis (ahid Aw3 model3) M3 oo 1251800 ltac:(eapply L5A.avis_sub; [exact OOV| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact OO0]. }
  assert (UO16 : L5.u32_at RSEGS (mrestrict (ahid Aw3 model3) M3) (oo + 16) 1024).
  { apply (proj2 (L5A.u32_at_vis (ahid Aw3 model3) M3 (oo + 16) 1024 ltac:(eapply L5A.avis_sub; [exact OOV| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (PMF.u32_at_agree RSEGS M1); [intros i Hi; apply AG13; lia| lia| lia| exact OO16]. }
  assert (J2 : getr R3 (reg 2) = Z_to_bv 64 (sp - 160)) by (rewrite CS3, (KS1 2%nat) by inl; exact M2').
  assert (J8 : getr R3 (reg 8) = Z_to_bv 64 (fb + 464 + 24)) by (rewrite CS3, (KS1 8%nat) by inl; exact MR8).
  assert (J9 : getr R3 (reg 9) = Z_to_bv 64 (fb + 464 + 16)) by (rewrite CS3, (KS1 9%nat) by inl; exact M9).
  assert (J18 : getr R3 (reg 18) = Z_to_bv 64 (fb + 464 + 296)) by (rewrite CS3, (KS1 18%nat) by inl; exact M18).
  assert (J19 : getr R3 (reg 19) = Z_to_bv 64 2147450880) by (rewrite CS3, (KS1 19%nat) by inl; exact M19).
  assert (J23 : getr R3 (reg 23) = Z_to_bv 64 2147450880) by (rewrite CS3, (KS1 23%nat) by inl; exact M23).
  assert (J22 : getr R3 (reg 22) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 22)))) by (rewrite CS3 by inl; rewrite (KS1 22%nat) by inl; exact J22F).
  LeanFeed.pfeed P (PNARCP.abrcG_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx2 R3 (mrestrict (ahid Aw3 model3) M3)
    (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => oo | 35%nat => q | 43%nat => bv_unsigned (getr R0 (reg 1)) | 44%nat => bv_unsigned (getr R0 (reg 8)) | 45%nat => bv_unsigned (getr R0 (reg 9)) | 46%nat => bv_unsigned (getr R0 (reg 18)) | 47%nat => bv_unsigned (getr R0 (reg 19)) | 48%nat => bv_unsigned (getr R0 (reg 20)) | 49%nat => bv_unsigned (getr R0 (reg 21)) | 50%nat => bv_unsigned (getr R0 (reg 22)) | 51%nat => bv_unsigned (getr R0 (reg 23)) | _ => 0 end)) ltac:(first [assumption | unfold PNARCP.aligned; lia | lia]).
  destruct P as (fx4 & R4 & M4v & MG4 & _ & FZ4 & MS4 & KS4 & gR1 & gR2 & gR8 & gR10 & gR11 & gR12 & gR18 & gR19 & gR21 & gR22 & G312 & G296 & G280).
  set (W4 := fun a => (fb + 464 + 280 <= a < fb + 464 + 280 + 8) \/ (fb + 464 + 296 <= a < fb + 464 + 296 + 8) \/ (fb + 464 + 312 <= a < fb + 464 + 312 + 4)).
  apply (L5SAR.apiece L ar C HI LYa HIok LB1 FF LK1 cr1 Aw3 M3 model3 fx2 fx4 R3 0xacc54 R4 0x78130 M4v W4 K HH3 AM3 MS4 MG4).
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
  apply (PNARCK.amset L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 sp 112 (fb + 464) 416 fx4 R4 M4 model4 K 320 48 706780 AOB); [lia| lia| lia| exact HH4| exact AM4| exact ASTK4| exact ACC4| exact ODEF4
     | lia| lia| replace (sp - 112) with (sp + (-7) * 16) by lia; rewrite Z.mod_add by lia; exact A16| exact gR10| exact gR11| exact gR12| apply RTP; apply CS4; inl| exact gR1| reflexivity| lia| exact gR2| exact K0|].
  intros R5 M5 model5 R5a0 RP5 Z368 PRES5 SDEF5 DEF5 MRT5 AM5 HH5.
  assert (CS5 : forall k, In k L5SAR.cs_all -> getr R5 (reg k) = getr R4 (reg k)) by (intros k Hk; apply (L5SAR.cs_of_preserved R4 R5 k RP5 Hk)).
  destruct (PNARCK.mset_post L ar C HI HIok LB1 FF LK1 cr1 Aw3 sp 112 (fb + 464) 416 M4 M5 model4 320 48 HH4 ASTK4 AOB ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PRES5 SDEF5 DEF5)
    as (EK45' & DK45' & ASTK5).
  pose proof (L5SAR.ek_tl L ar LB (q, 16384) FF sp 24576 _ M4 M5 EK45') as EK45. pose proof (L5SAR.dk_tl L ar LB (q, 16384) FF sp 24576 M4 M5 DK45') as DK45.
  (* [comment removed for export] *)
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB1 FF LK1 cr1 Aw3 M5 model5 HH5) as (_ & VIS5 & _).
  assert (Y5 : L5.writable RSEGS (mrestrict (ahid Aw3 model5) M5) (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis _ M5 (sp - 4096) 4096 (VIS5 (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M5 sp 24576); [exact ASTK5| lia| lia| lia]. }
  assert (K2 : getr R5 (reg 2) = Z_to_bv 64 (sp - 112)) by (rewrite CS5 by inl; exact gR2).
  assert (K8 : getr R5 (reg 8) = Z_to_bv 64 (fb + 464)) by (rewrite CS5 by inl; exact gR8).
  assert (K9 : getr R5 (reg 9) = Z_to_bv 64 (fb + 464 + 16)) by (rewrite CS5 by inl; exact G9).
  assert (K18 : getr R5 (reg 18) = Z_to_bv 64 (fb + 464 + 320)) by (rewrite CS5 by inl; exact gR18).
  assert (K19 : getr R5 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 19)))) by (rewrite CS5 by inl; exact gR19).
  assert (K22 : getr R5 (reg 22) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 22)))) by (rewrite CS5 by inl; exact gR22).
  assert (K23 : getr R5 (reg 23) = Z_to_bv 64 2147450880) by (rewrite CS5 by inl; exact G23).
  LeanFeed.pfeed P (PNARCP.abrcG2_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx4 R5 (mrestrict (ahid Aw3 model5) M5) (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 47%nat => bv_unsigned (getr R0 (reg 19)) | 50%nat => bv_unsigned (getr R0 (reg 22)) | _ => 0 end)) ltac:(first [assumption | unfold PNARCP.aligned; lia | lia]).
  destruct P as (fx5 & R5a & M5v & MG5a & _ & FZ5a & MS5a & KS5a & aR1 & aR2 & aR8 & aR10 & aR11 & aR12 & aR18 & aR19 & aR21 & aR22).
  assert (E5 : M5v = mrestrict (ahid Aw3 model5) M5) by (apply L5SAR.mem_eq_of_agree; exact FZ5a). subst M5v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok LB1 FF LK1 cr1 Aw3 M5 model5 fx4 fx5 R5 706780 R5a 0x78130 _ K HH5 AM5 MS5a MG5a FZ5a).
  intros M5' model5a HH5a AM5a MRT5a HID5a VIS5a MGM5a FR5a.
  assert (E5' : M5' = M5) by (apply L5SAR.mem_eq_of_agree; exact FR5a). subst M5'.
  assert (ACC5 : PMSPA.accA M5 (fb + 464) 416) by (apply (PMKA.acc_keepA' L ar LB FF sp 24576 _ M4 M5 EK45 WAPP FRB _ 416 AOP ACC4)).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB1 FF LK1 cr1 Aw3 M5 model5a (fb + 464) 416 sp 24576 HH5a AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & ODEF5 & _).
  apply (PNARCK.amset L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 sp 112 (fb + 464) 416 fx5 R5a M5 model5a K 368 24 706800 AOB); [lia| lia| lia| exact HH5a| exact AM5a| exact ASTK5| exact ACC5| exact ODEF5
     | lia| lia| replace (sp - 112) with (sp + (-7) * 16) by lia; rewrite Z.mod_add by lia; exact A16| exact aR10| exact aR11| exact aR12| apply RTP; rewrite (KS5a 4%nat), CS5 by inl; apply CS4; inl| exact aR1| reflexivity| lia| exact aR2| exact K0|].
  intros R5b M5b model5b R5b0 RP5b Z392 PRES5b SDEF5b DEF5b MRT5b AM5b HH5b.
  assert (CS5b : forall k, In k L5SAR.cs_all -> getr R5b (reg k) = getr R5a (reg k)) by (intros k Hk; apply (L5SAR.cs_of_preserved R5a R5b k RP5b Hk)).
  destruct (PNARCK.mset_post L ar C HI HIok LB1 FF LK1 cr1 Aw3 sp 112 (fb + 464) 416 M5 M5b model5a 368 24 HH5a ASTK5 AOB ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PRES5b SDEF5b DEF5b)
    as (EK55b' & DK55b' & ASTK5b).
  pose proof (L5SAR.ek_tl L ar LB (q, 16384) FF sp 24576 _ M5 M5b EK55b') as EK55b. pose proof (L5SAR.dk_tl L ar LB (q, 16384) FF sp 24576 M5 M5b DK55b') as DK55b.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB1 FF LK1 cr1 Aw3 M5b model5b HH5b) as (_ & VIS5b & _).
  assert (Y5b : L5.writable RSEGS (mrestrict (ahid Aw3 model5b) M5b) (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis _ M5b (sp - 4096) 4096 (VIS5b (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M5b sp 24576); [exact ASTK5b| lia| lia| lia]. }
  assert (KB2 : getr R5b (reg 2) = Z_to_bv 64 (sp - 112)) by (rewrite CS5b by inl; exact aR2).
  assert (KB8 : getr R5b (reg 8) = Z_to_bv 64 (fb + 464)) by (rewrite CS5b by inl; exact aR8).
  assert (KB9 : getr R5b (reg 9) = Z_to_bv 64 (fb + 464 + 16)) by (rewrite CS5b, (KS5a 9%nat) by inl; exact K9).
  assert (KB18 : getr R5b (reg 18) = Z_to_bv 64 (fb + 464 + 320)) by (rewrite CS5b by inl; exact aR18).
  assert (KB19 : getr R5b (reg 19) = Z_to_bv 64 (fb + 464 + 368)) by (rewrite CS5b by inl; exact aR19).
  assert (KB22 : getr R5b (reg 22) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 22)))) by (rewrite CS5b by inl; exact aR22).
  assert (KB23 : getr R5b (reg 23) = Z_to_bv 64 2147450880) by (rewrite CS5b, (KS5a 23%nat) by inl; exact K23).
  LeanFeed.pfeed P (PNARCP.abrcG3_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx5 R5b (mrestrict (ahid Aw3 model5b) M5b) (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 50%nat => bv_unsigned (getr R0 (reg 22)) | _ => 0 end)) ltac:(first [assumption | unfold PNARCP.aligned; lia | lia]).
  destruct P as (fx5c & R5c & M5v & MG5c & _ & FZ5c & MS5c & KS5c & cR1 & cR2 & cR8 & cR10 & cR11 & cR12 & cR18 & cR19 & cR21 & cR22).
  assert (E5 : M5v = mrestrict (ahid Aw3 model5b) M5b) by (apply L5SAR.mem_eq_of_agree; exact FZ5c). subst M5v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok LB1 FF LK1 cr1 Aw3 M5b model5b fx5 fx5c R5b 706800 R5c 0x78130 _ K HH5b AM5b MS5c MG5c FZ5c).
  intros M5' model5c HH5c AM5c MRT5c HID5c VIS5c MGM5c FR5c.
  assert (E5' : M5' = M5b) by (apply L5SAR.mem_eq_of_agree; exact FR5c). subst M5'.
  assert (ACC5b : PMSPA.accA M5b (fb + 464) 416) by (apply (PMKA.acc_keepA' L ar LB FF sp 24576 _ M5 M5b EK55b WAPP FRB _ 416 AOP ACC5)).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB1 FF LK1 cr1 Aw3 M5b model5c (fb + 464) 416 sp 24576 HH5c AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & ODEF5b & _).
  apply (PNARCK.amset L ar C HI LY HIok LB1 FF LK1 cr1 Aw3 sp 112 (fb + 464) 416 fx5c R5c M5b model5c K 392 24 706820 AOB); [lia| lia| lia| exact HH5c| exact AM5c| exact ASTK5b| exact ACC5b| exact ODEF5b
     | lia| lia| replace (sp - 112) with (sp + (-7) * 16) by lia; rewrite Z.mod_add by lia; exact A16| exact cR10| exact cR11| exact cR12| apply RTP; rewrite (KS5c 4%nat), CS5b, (KS5a 4%nat), CS5 by inl; apply CS4; inl| exact cR1| reflexivity| lia| exact cR2| exact K0|].
  intros R5d M5d model5d R5d0 RP5d Z416 PRES5d SDEF5d DEF5d MRT5d AM5d HH5d.
  assert (CS5d : forall k, In k L5SAR.cs_all -> getr R5d (reg k) = getr R5c (reg k)) by (intros k Hk; apply (L5SAR.cs_of_preserved R5c R5d k RP5d Hk)).
  destruct (PNARCK.mset_post L ar C HI HIok LB1 FF LK1 cr1 Aw3 sp 112 (fb + 464) 416 M5b M5d model5c 392 24 HH5c ASTK5b AOB ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PRES5d SDEF5d DEF5d)
    as (EK5bd' & DK5bd' & ASTK5d).
  pose proof (L5SAR.ek_tl L ar LB (q, 16384) FF sp 24576 _ M5b M5d EK5bd') as EK5bd. pose proof (L5SAR.dk_tl L ar LB (q, 16384) FF sp 24576 M5b M5d DK5bd') as DK5bd.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB1 FF LK1 cr1 Aw3 M5d model5d HH5d) as (_ & VIS5d & _ & _ & _ & _ & _ & VSTSH5d).
  assert (Y5d : L5.writable RSEGS (mrestrict (ahid Aw3 model5d) M5d) (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis _ M5d (sp - 4096) 4096 (VIS5d (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M5d sp 24576); [exact ASTK5d| lia| lia| lia]. }
  assert (KH2 : getr R5d (reg 2) = Z_to_bv 64 (sp - 112)) by (rewrite CS5d by inl; exact cR2).
  assert (KH8 : getr R5d (reg 8) = Z_to_bv 64 (fb + 464)) by (rewrite CS5d by inl; exact cR8).
  assert (KH9 : getr R5d (reg 9) = Z_to_bv 64 (fb + 464 + 16)) by (rewrite CS5d, (KS5c 9%nat) by inl; exact KB9).
  assert (KH18 : getr R5d (reg 18) = Z_to_bv 64 (fb + 464 + 320)) by (rewrite CS5d by inl; exact cR18).
  assert (KH19 : getr R5d (reg 19) = Z_to_bv 64 (fb + 464 + 368)) by (rewrite CS5d by inl; exact cR19).
  assert (KH22 : getr R5d (reg 22) = Z_to_bv 64 (fb + 464 + 392)) by (rewrite CS5d by inl; exact cR22).
  assert (KH23 : getr R5d (reg 23) = Z_to_bv 64 2147450880) by (rewrite CS5d, (KS5c 23%nat) by inl; exact KB23).
  assert (CSH : forall k, In k [3; 4; 20; 24; 25; 26; 27]%nat -> getr R5d (reg k) = getr R0 (reg k)).
  { intros k Hk. assert (Hk' : In k L5SAR.cs_all /\ In k PNARCP.KS_abrcG3 /\ In k PNARCP.KS_abrcG2)
      by (destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; (split; [inl| split; inl])).
    destruct Hk' as (Y1 & Y2 & Y3). rewrite (CS5d k Y1), (KS5c k Y2), (CS5b k Y1), (KS5a k Y3), (CS5 k Y1). apply CS4. exact Hk. }
  assert (EK15d : L5SAR.ek L ar LB FF sp 24576 [(fb + 464, 416)] M1 M5d).
  { apply (L5SAR.ek_trans L ar LB FF sp 24576 _ M1 M5b M5d); [| exact EK5bd]. apply (L5SAR.ek_trans L ar LB FF sp 24576 _ M1 M5 M5b); [| exact EK55b].
    apply (L5SAR.ek_trans L ar LB FF sp 24576 _ M1 M4 M5); [| exact EK45]. apply (L5SAR.ek_trans L ar LB FF sp 24576 _ M1 M3 M4 EK13 EK34). }
  assert (ACC5d : PMSPA.accA M5d (fb + 464) 416) by (apply (PMKA.acc_keepA' L ar LB FF sp 24576 _ M1 M5d EK15d WAPP FRB _ 416 AOP ACC)).
  assert (ACCI5d : PMSPA.accA M5d (fb + 96) 272) by (apply (PMKA.acc_keepA' L ar LB FF sp 24576 _ M1 M5d EK15d WAPP FRB _ 272 AOIS ACCI)).
  assert (ACCO5d : PMSPA.accA M5d oo 24) by (apply (PMKA.acc_keepA' L ar LB FF sp 24576 _ M1 M5d EK15d WAPP FRB _ 24 AOO ACCO)).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB1 FF LK1 cr1 Aw3 M5d model5d (fb + 464) 416 sp 24576 HH5d AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & ODEF5d & OVIS5d & _).
  destruct (PNARCK.vfacts L ar C IL HI LY HIok ICok ILY LB1 FF LK1 cr1 Aw3 M5d model5d sp fb oo HH5d FOK ASTK5d AOO OO8 ACC5d ACCI5d ACCO5d ODEF5d)
    as (XH1 & XH2 & XH3 & XH4 & XH5 & XH6 & XH7 & XH8 & XH9 & XH10 & XH11 & XH12 & XH13 & XH14 & XH15 & XH16 & XH17 & XH18 & XH19).
  assert (STKSH5d : shadow_zero M5d (sp - 24576) 3072).
  { apply (PMKA.stksh_keepA L ar LB FF sp 24576 _ M1 M5d EK15d WAPP); [lia| lia| lia| | lia| exact STKSH]. apply PMAIS1.sub8; [exact A16| reflexivity]. }
  assert (ZSH5d : L5KA.zeros_at (mrestrict (ahid Aw3 model5d) M5d) (sp / 8 + 2147450368) 512).
  { apply (proj2 (L5A.zeros_at_vis _ M5d _ 512 (VSTSH5d _ 512 (stack_sh_in ar M5d sp ASTK5d)))). exact (stack_zeros6 M5d sp STKSH5d A16). }
  assert (UZ392 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model5d) M5d) (fb + 464 + 392) 0).
  { apply (proj2 (L5A.u64_at_vis (ahid Aw3 model5d) M5d (fb + 464 + 392) 0 ltac:(eapply L5A.avis_sub; [exact OVIS5d| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (PMCG.u64_of_zeros RSEGS M5d); [apply (PMCG.zeros_sub M5d (fb + 464 + 392) 24); [exact Z416| lia| lia]| lia| lia]. }
  assert (UZ400 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model5d) M5d) (fb + 464 + 400) 0).
  { apply (proj2 (L5A.u64_at_vis (ahid Aw3 model5d) M5d (fb + 464 + 400) 0 ltac:(eapply L5A.avis_sub; [exact OVIS5d| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (PMCG.u64_of_zeros RSEGS M5d); [apply (PMCG.zeros_sub M5d (fb + 464 + 392) 24); [exact Z416| lia| lia]| lia| lia]. }
  assert (UZ408 : L5.u64_at RSEGS (mrestrict (ahid Aw3 model5d) M5d) (fb + 464 + 408) 0).
  { apply (proj2 (L5A.u64_at_vis (ahid Aw3 model5d) M5d (fb + 464 + 408) 0 ltac:(eapply L5A.avis_sub; [exact OVIS5d| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (PMCG.u64_of_zeros RSEGS M5d); [apply (PMCG.zeros_sub M5d (fb + 464 + 392) 24); [exact Z416| lia| lia]| lia| lia]. }
  LeanFeed.pfeed P (PNARCP.abrcH_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx5c R5d (mrestrict (ahid Aw3 model5d) M5d) (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | _ => 0 end)) ltac:(first [assumption | unfold PNARCP.aligned; lia | lia]).
  destruct P as (fx6 & R6 & M6v & MG6 & _ & FZ6 & MS6 & KS6 & hR1 & hR10 & hR11 & hR12 & hR13 & hR20 & hR21 & hR24 & hR25 & HW104 & HW100 & HW96).
  set (W6 := fun a => sp - 104 <= a < sp - 104 + 12).
  apply (L5SAR.apiece L ar C HI LYa HIok LB1 FF LK1 cr1 Aw3 M5d model5d fx5c fx6 R5d 0xac904 R6 0xad11c M6v W6 K HH5d AM5d MS6 MG6).
  { intros a Ha N. apply FZ6; [exact Ha| exact N]. }
  { intros a Ha Wa. unfold W6 in Wa. split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
  intros M6 model6 HH6 AM6 MRT6 HID6 VIS6 MGM6 FR6 VV6.
  assert (EK56 : L5SAR.ek L ar LB FF sp 24576 [(fb + 464, 416)] M5d M6).
  { apply (L5SAR.ek_piece L ar LB FF sp 24576 _ M5d M6 W6 FR6). intros a Ha Hc Ho X. unfold W6 in X.
    destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK1 cr Aw1 M1 _ sp 24576 a HH SPT Hc) as [Z1|Z1]; lia. }
  assert (ASTK6 : L5CA.astk ar M6 sp 24576) by (apply (L5SAR.astk_grows ar M5d M6 sp 24576 ASTK5d MGM6)).
  assert (EK16 : L5SAR.ek L ar LB FF sp 24576 [(fb + 464, 416)] M1 M6) by (apply (L5SAR.ek_trans L ar LB FF sp 24576 _ M1 M5d M6 EK15d EK56)).
  assert (STKSH6 : shadow_zero M6 (sp - 24576) 3072).
  { apply (PMKA.stksh_keepA L ar LB FF sp 24576 _ M1 M6 EK16 WAPP); [lia| lia| lia| | lia| exact STKSH]. apply PMAIS1.sub8; [exact A16| reflexivity]. }
  assert (ACC6 : PMSPA.accA M6 (fb + 464) 416) by (apply (PMKA.acc_keepA' L ar LB FF sp 24576 _ M1 M6 EK16 WAPP FRB _ 416 AOP ACC)).
  assert (ACS6 : forall a n, sp - 24576 <= a -> a + n <= sp -> PMSPA.accA M6 a n).
  { intros a n Y1 Y2. unfold PMSPA.accA. apply (L5CB.aacc_of_zero M6 (sp - 24576) 3072 a n STKSH6); [apply PMAIS1.sub8; [exact A16| reflexivity]| lia| lia| lia]. }
  assert (ZM6 : PM.zeros_at M6 (fb + 464 + 392) 24).
  { apply (PMF.zeros_at_agree M5d); [intros i Hi; apply FR6; [lia| unfold W6; lia]| exact Z416]. }
  assert (H96' : L5.u32_at RSEGS M6 (sp - 96) 0) by (apply (PMAIS1.vis_u32 _ _ _ _ _ VIS6); [apply VIS5d; lia| lia| lia| exact HW96]).
  assert (H100' : L5.u32_at RSEGS M6 (sp - 100) 0) by (apply (PMAIS1.vis_u32 _ _ _ _ _ VIS6); [apply VIS5d; lia| lia| lia| exact HW100]).
  assert (H104' : L5.u32_at RSEGS M6 (sp - 104) 0) by (apply (PMAIS1.vis_u32 _ _ _ _ _ VIS6); [apply VIS5d; lia| lia| lia| exact HW104]).
  (* [comment removed for export] *)
  assert (STD : forall a, PMST.dep PMA.AD a -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a /\ L5.outside [(fb + 464, 416)] a).
  { intros a D. pose proof (PMAIS1.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia|].
    split; [exact (PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D))|]. intros rg [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
  assert (SRO : forall a, 65536 <= a < pa_rw_lo PMA.AD -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a /\ L5.outside [(fb + 464, 416)] a).
  { intros a Ha. cbn [pa_rw_lo PMA.AD ADDR_A] in Ha. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia|].
    split; [intros X; pose proof (L5A.aly_static_lo L C LYa a X); lia|]. intros rg [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
  assert (BASE6 : PMSTA.base_okA RSEGS PMA.AD M6) by (apply (PMKA.base_ok_keepA RSEGS PMA.AD L ar LB FF sp 24576 [(fb + 464, 416)] M1 M6 EK16 PMA.addrs_wf_A STD SRO BASE)).
  unfold PNSAXR.push_root_slow_spec in PSH.
  apply (PSH fx6 R6 M6 model6 K LB1 FF LK1 Aw3 cr1 (fb + 464 + 392) (0, 0, 0) (sp - 112) 706948 HH6 AM6 K0).
  { split; [rewrite L5K.rl1; exact hR1|]. split; [split; [lia| reflexivity]|]. split; [rewrite L5K.rl2, (KS6 2%nat) by inl; exact KH2|].
    split; [rewrite L5K.rl3, (KS6 3%nat) by inl; rewrite CSH by inl; exact Rgp|].
    split; [rewrite L5K.rl4, (KS6 4%nat) by inl; apply RTP; apply CSH; inl|].
    change (PMSPA.pm_scr 0) with 12288. split.
    { apply (L5SAR.astk_sub ar M6 M6 sp 24576 112 12288 ASTK6 (fun _ X => X)); [lia|lia|lia|]. replace (sp - 112) with (sp + (-7) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
    change (12288 / 8) with 1536. apply (PMKA.shadow_zero_sub M6 (sp - 24576) 3072 (sp - 112 - 12288) 1536);
      [apply PMAIS1.sub8; [exact A16| reflexivity]| replace (sp - 112 - 12288) with (sp - 12400) by lia; apply PMAIS1.sub8; [exact A16| reflexivity]| lia| lia| lia| exact STKSH6]. }
  { intros f Hf. specialize (FRS f Hf). lia. }
  { rewrite L5K.rl10. exact hR10. }
  { apply (PNARCK.frame_aobj FF fb); [exact FOK| lia| lia]. }
  { lia. }
  { unfold PMSPA.accA in *. apply (L5CB.aacc_sub M6 (fb + 464) 416); [exact ACC6| lia| lia]. }
  { apply (PMCG.u64_of_zeros RSEGS M6); [apply (PMCG.zeros_sub M6 (fb + 464 + 392) 24); [exact ZM6| lia| lia]| lia| lia]. }
  { apply (PMCG.u64_of_zeros RSEGS M6); [apply (PMCG.zeros_sub M6 (fb + 464 + 392) 24); [exact ZM6| lia| lia]| lia| lia]. }
  { apply (PMCG.u64_of_zeros RSEGS M6); [apply (PMCG.zeros_sub M6 (fb + 464 + 392) 24); [exact ZM6| lia| lia]| lia| lia]. }
  { exact BASE6. }
  { unfold PNSAX.cells_root. exists (sp - 96), (sp - 100), (sp - 104). cbn [fst snd].
    split; [rewrite L5K.rl11; exact hR11|]. split; [rewrite L5K.rl12; exact hR12|]. split; [rewrite L5K.rl13; exact hR13|].
    assert (AC : forall p, sp - 112 <= p -> p + 4 <= sp -> p mod 4 = 0 -> PNSAX.arg_cell ar M6 FF (sp - 112) (fb + 464 + 392) p 4).
    { intros p P1 P2 P4. unfold PNSAX.arg_cell, PNSAX.arg_ok. split; [exact P4|]. split; [apply ACS6; lia|].
      split; [split; [right; lia| right; lia]|].
      apply (shz_at M6 (sp - 24576) 3072); [exact STKSH6| apply PMAIS1.sub8; [exact A16| reflexivity]| lia| lia]. }
    assert (S4 : forall d, d mod 4 = 0 -> (sp - d) mod 4 = 0).
    { intros d D4. pose proof A16 as A16'. clear - D4 A16'. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    split; [apply AC; [lia| lia| apply S4; reflexivity]|]. split; [apply AC; [lia| lia| apply S4; reflexivity]|]. split; [apply AC; [lia| lia| apply S4; reflexivity]|].
    split; [exact H96'|]. split; [exact H100'|]. split; [exact H104'|]. split; [lia|]. split; lia. }
  { exact CR2. }
  intros fx7 R7 M7 model7 LK7 Aw7 b7 RP7 R10b B4096 BHI HOLE7 DISJ7 ACCV7 BASE7 HP7 MRT7 INC7 IA7 AM7 HH7.
  change (PMSPA.pm_scr 0) with 12288 in HP7.
  assert (ASTK7 : L5CA.astk ar M7 sp 24576).
  { apply (PMKA.astk_after_ahpres L ar LB1 FF M6 M7 sp 24576 (sp - 112) 12288 [(fb + 464 + 392, 24)] ASTK6 HP7); lia. }
  assert (EK67 : L5SAR.ek L ar LB FF sp 24576 [(fb + 464, 416)] M6 M7).
  { apply (L5SAR.ek_tl L ar LB (q, 16384) FF sp 24576 _ M6 M7).
    apply (L5SAR.ek_callee L ar LB1 [] FF [] sp 24576 (sp - 112) 12288 [(fb + 464, 416)] [(fb + 464 + 392, 24)] M6 M7 HP7); [lia| lia|].
    intros a Hc Ho rg [<-|[]] Hr. apply (Ho (fb + 464, 416)); [left; reflexivity| unfold L5.in_rng in *; cbn [fst snd] in *; lia]. }
  assert (DK67 : L5SAR.dk L ar LB FF sp 24576 M6 M7).
  { apply (L5SAR.dk_tl L ar LB (q, 16384) FF sp 24576 M6 M7). apply (L5SAR.dk_callee L ar LB1 [] FF [] sp 24576 (sp - 112) 12288 [(fb + 464 + 392, 24)] M6 M7 HP7); lia. }
  (* [comment removed for export] *)
  assert (T76 : forall a, 0 <= a < 2 ^ 64 -> ((sp - 112 <= a < sp) \/ (fb + 32 <= a < fb + 2040)) -> ~ (fb + 464 + 392 <= a < fb + 464 + 416) -> M7 (Z_to_bv 64 a) = M6 (Z_to_bv 64 a)).
  { intros a Ha Hr N. apply (proj1 HP7). split; [exact Ha|]. split; [destruct Hr as [Hr|Hr]; [apply SCL; lia| apply CLF; lia]|].
    intros rg [<-|[]] Hq. unfold L5.in_rng in Hq. cbn [fst snd] in Hq. lia. }
  assert (T65 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 104 <= a < sp - 92) -> M6 (Z_to_bv 64 a) = M5d (Z_to_bv 64 a)) by (intros a Ha N; apply FR6; [exact Ha| unfold W6; lia]).
  assert (T5d : forall a, 0 <= a < 2 ^ 64 -> ((sp - 112 <= a < sp) \/ (fb + 32 <= a < fb + 2040)) -> ~ (fb + 464 + 392 <= a < fb + 464 + 416) -> M5d (Z_to_bv 64 a) = M5b (Z_to_bv 64 a)).
  { intros a Ha Hr N. apply PRES5d; [exact Ha| destruct Hr as [Hr|Hr]; [apply SCL; lia| apply CLF; lia]| lia]. }
  assert (T5b : forall a, 0 <= a < 2 ^ 64 -> ((sp - 112 <= a < sp) \/ (fb + 32 <= a < fb + 2040)) -> ~ (fb + 464 + 368 <= a < fb + 464 + 392) -> M5b (Z_to_bv 64 a) = M5 (Z_to_bv 64 a)).
  { intros a Ha Hr N. apply PRES5b; [exact Ha| destruct Hr as [Hr|Hr]; [apply SCL; lia| apply CLF; lia]| lia]. }
  assert (T54 : forall a, 0 <= a < 2 ^ 64 -> ((sp - 112 <= a < sp) \/ (fb + 32 <= a < fb + 2040)) -> ~ (fb + 464 + 320 <= a < fb + 464 + 368) -> M5 (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)).
  { intros a Ha Hr N. apply PRES5; [exact Ha| destruct Hr as [Hr|Hr]; [apply SCL; lia| apply CLF; lia]| lia]. }
  assert (T43 : forall a, 0 <= a < 2 ^ 64 -> ~ W4 a -> M4 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)) by (intros a Ha N; apply FR4; [exact Ha| exact N]).
  assert (AG71 : forall a, (sp - 88 <= a < sp) \/ (fb + 32 <= a < fb + 2040 /\ ~ (fb + 464 + 280 <= a < fb + 464 + 288) /\ ~ (fb + 464 + 296 <= a < fb + 464 + 304)
                           /\ ~ (fb + 464 + 312 <= a < fb + 464 + 416)) -> M7 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Hr. destruct Hr as [Hr|Hr].
    - rewrite (T76 a ltac:(lia) ltac:(lia) ltac:(lia)), (T65 a ltac:(lia) ltac:(lia)), (T5d a ltac:(lia) ltac:(lia) ltac:(lia)), (T5b a ltac:(lia) ltac:(lia) ltac:(lia)),
        (T54 a ltac:(lia) ltac:(lia) ltac:(lia)), (T43 a ltac:(lia) ltac:(unfold W4; lia)).
      apply (AG13 a). lia.
    - rewrite (T76 a ltac:(lia) ltac:(lia) ltac:(lia)), (T65 a ltac:(lia) ltac:(lia)), (T5d a ltac:(lia) ltac:(lia) ltac:(lia)), (T5b a ltac:(lia) ltac:(lia) ltac:(lia)),
        (T54 a ltac:(lia) ltac:(lia) ltac:(lia)), (T43 a ltac:(lia) ltac:(unfold W4; lia)).
      apply (AG13 a). lia. }
  assert (ACC7 : PMSPA.accA M7 (fb + 464) 416) by (apply (PMKA.acc_keepA' L ar LB FF sp 24576 _ M6 M7 EK67 WAPP FRB _ 416 AOP ACC6)).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK7 _ Aw7 M7 model7 (fb + 464) 416 sp 24576 HH7 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & ODEF7 & OVIS7 & _).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB1 FF LK1 cr1 Aw3 M3 model3 (fb + 464) 416 sp 24576 HH3 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & _ & OVIS3 & _).
  (* [comment removed for export] *)
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK7 _ Aw7 M7 model7 HH7) as (_ & VIS7 & _ & _ & _ & _ & _ & VSTSH7).
  assert (Zc8 : L5.u64_at RSEGS (mrestrict (ahid Aw7 model7) M7) (sp - 8) _) by (apply (PNARCK.svis L ar C HI LY HIok _ FF LK7 _ Aw7 M7 model7 sp (sp - 8) _ HH7 ASTK7); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG71; lia| lia| lia| exact S8]).
  assert (Zc16 : L5.u64_at RSEGS (mrestrict (ahid Aw7 model7) M7) (sp - 16) _) by (apply (PNARCK.svis L ar C HI LY HIok _ FF LK7 _ Aw7 M7 model7 sp (sp - 16) _ HH7 ASTK7); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG71; lia| lia| lia| exact S16]).
  assert (Zc24 : L5.u64_at RSEGS (mrestrict (ahid Aw7 model7) M7) (sp - 24) _) by (apply (PNARCK.svis L ar C HI LY HIok _ FF LK7 _ Aw7 M7 model7 sp (sp - 24) _ HH7 ASTK7); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG71; lia| lia| lia| exact S24]).
  assert (Zc32 : L5.u64_at RSEGS (mrestrict (ahid Aw7 model7) M7) (sp - 32) _) by (apply (PNARCK.svis L ar C HI LY HIok _ FF LK7 _ Aw7 M7 model7 sp (sp - 32) _ HH7 ASTK7); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG71; lia| lia| lia| exact S32]).
  assert (Zc40 : L5.u64_at RSEGS (mrestrict (ahid Aw7 model7) M7) (sp - 40) _) by (apply (PNARCK.svis L ar C HI LY HIok _ FF LK7 _ Aw7 M7 model7 sp (sp - 40) _ HH7 ASTK7); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG71; lia| lia| lia| exact S40]).
  assert (Zc48 : L5.u64_at RSEGS (mrestrict (ahid Aw7 model7) M7) (sp - 48) _) by (apply (PNARCK.svis L ar C HI LY HIok _ FF LK7 _ Aw7 M7 model7 sp (sp - 48) _ HH7 ASTK7); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG71; lia| lia| lia| exact S48]).
  assert (Zc56 : L5.u64_at RSEGS (mrestrict (ahid Aw7 model7) M7) (sp - 56) _) by (apply (PNARCK.svis L ar C HI LY HIok _ FF LK7 _ Aw7 M7 model7 sp (sp - 56) _ HH7 ASTK7); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG71; lia| lia| lia| exact S56]).
  assert (Zc64 : L5.u64_at RSEGS (mrestrict (ahid Aw7 model7) M7) (sp - 64) _) by (apply (PNARCK.svis L ar C HI LY HIok _ FF LK7 _ Aw7 M7 model7 sp (sp - 64) _ HH7 ASTK7); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG71; lia| lia| lia| exact S64]).
  assert (Zc72 : L5.u64_at RSEGS (mrestrict (ahid Aw7 model7) M7) (sp - 72) _) by (apply (PNARCK.svis L ar C HI LY HIok _ FF LK7 _ Aw7 M7 model7 sp (sp - 72) _ HH7 ASTK7); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG71; lia| lia| lia| exact S72]).
  assert (Zc80 : L5.u64_at RSEGS (mrestrict (ahid Aw7 model7) M7) (sp - 80) _) by (apply (PNARCK.svis L ar C HI LY HIok _ FF LK7 _ Aw7 M7 model7 sp (sp - 80) _ HH7 ASTK7); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG71; lia| lia| lia| exact S80]).
  assert (Zc88 : L5.u64_at RSEGS (mrestrict (ahid Aw7 model7) M7) (sp - 88) _) by (apply (PNARCK.svis L ar C HI LY HIok _ FF LK7 _ Aw7 M7 model7 sp (sp - 88) _ HH7 ASTK7); [lia| lia|]; apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG71; lia| lia| lia| exact S88]).
  assert (EK17 : L5SAR.ek L ar LB FF sp 24576 [(fb + 464, 416)] M1 M7) by (apply (L5SAR.ek_trans L ar LB FF sp 24576 _ M1 M6 M7 EK16 EK67)).
  assert (ACCI7 : PMSPA.accA M7 (fb + 96) 272) by (apply (PMKA.acc_keepA' L ar LB FF sp 24576 _ M1 M7 EK17 WAPP FRB _ 272 AOIS ACCI)).
  assert (ACCO7 : PMSPA.accA M7 oo 24) by (apply (PMKA.acc_keepA' L ar LB FF sp 24576 _ M1 M7 EK17 WAPP FRB _ 24 AOO ACCO)).
  destruct (PNARCK.vfacts L ar C IL HI LY HIok ICok ILY _ FF LK7 _ Aw7 M7 model7 sp fb oo HH7 FOK ASTK7 AOO OO8 ACC7 ACCI7 ACCO7 ODEF7)
    as (XZ1 & XZ2 & XZ3 & XZ4 & XZ5 & XZ6 & XZ7 & XZ8 & XZ9 & XZ10 & XZ11 & XZ12 & XZ13 & XZ14 & XZ15 & XZ16 & XZ17 & XZ18 & XZ19).
  assert (STKSH7 : shadow_zero M7 (sp - 24576) 3072).
  { apply (PMKA.stksh_keepA L ar LB FF sp 24576 _ M1 M7 EK17 WAPP); [lia| lia| lia| | lia| exact STKSH]. apply PMAIS1.sub8; [exact A16| reflexivity]. }
  assert (ZSH7 : L5KA.zeros_at (mrestrict (ahid Aw7 model7) M7) (sp / 8 + 2147450368) 512).
  { apply (proj2 (L5A.zeros_at_vis _ M7 _ 512 (VSTSH7 _ 512 (stack_sh_in ar M7 sp ASTK7)))). exact (stack_zeros6 M7 sp STKSH7 A16). }
  assert (ZW96 : L5.u32_at RSEGS (mrestrict (ahid Aw7 model7) M7) (sp - 96) 0).
  { apply (proj2 (L5A.u32_at_vis (ahid Aw7 model7) M7 (sp - 96) 0 (VIS7 (sp - 96) 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (PMF.u32_at_agree RSEGS M6); [intros i Hi; apply T76; lia| lia| lia| exact H96']. }
  assert (ZW100 : L5.u32_at RSEGS (mrestrict (ahid Aw7 model7) M7) (sp - 100) 0).
  { apply (proj2 (L5A.u32_at_vis (ahid Aw7 model7) M7 (sp - 100) 0 (VIS7 (sp - 100) 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (PMF.u32_at_agree RSEGS M6); [intros i Hi; apply T76; lia| lia| lia| exact H100']. }
  assert (ZW104 : L5.u32_at RSEGS (mrestrict (ahid Aw7 model7) M7) (sp - 104) 0).
  { apply (proj2 (L5A.u32_at_vis (ahid Aw7 model7) M7 (sp - 104) 0 (VIS7 (sp - 104) 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (PMF.u32_at_agree RSEGS M6); [intros i Hi; apply T76; lia| lia| lia| exact H104']. }
  assert (Y7 : L5.writable RSEGS (mrestrict (ahid Aw7 model7) M7) (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis _ M7 (sp - 4096) 4096 (VIS7 (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M7 sp 24576); [exact ASTK7| lia| lia| lia]. }
  assert (Z2 : getr R7 (reg 2) = Z_to_bv 64 (sp - 112)) by (rewrite (L5SAR.cs_of_preserved R6 R7 2 RP7) by inl; rewrite (KS6 2%nat) by inl; exact KH2).
  assert (Z8 : getr R7 (reg 8) = Z_to_bv 64 (fb + 464)) by (rewrite (L5SAR.cs_of_preserved R6 R7 8 RP7) by inl; rewrite (KS6 8%nat) by inl; exact KH8).
  assert (Z9 : getr R7 (reg 9) = Z_to_bv 64 (fb + 464 + 16)) by (rewrite (L5SAR.cs_of_preserved R6 R7 9 RP7) by inl; rewrite (KS6 9%nat) by inl; exact KH9).
  assert (Z18 : getr R7 (reg 18) = Z_to_bv 64 (fb + 464 + 320)) by (rewrite (L5SAR.cs_of_preserved R6 R7 18 RP7) by inl; rewrite (KS6 18%nat) by inl; exact KH18).
  assert (Z19 : getr R7 (reg 19) = Z_to_bv 64 (fb + 464 + 368)) by (rewrite (L5SAR.cs_of_preserved R6 R7 19 RP7) by inl; rewrite (KS6 19%nat) by inl; exact KH19).
  assert (Z22 : getr R7 (reg 22) = Z_to_bv 64 (fb + 464 + 392)) by (rewrite (L5SAR.cs_of_preserved R6 R7 22 RP7) by inl; rewrite (KS6 22%nat) by inl; exact KH22).
  assert (Z23 : getr R7 (reg 23) = Z_to_bv 64 2147450880) by (rewrite (L5SAR.cs_of_preserved R6 R7 23 RP7) by inl; rewrite (KS6 23%nat) by inl; exact KH23).
  pose proof hR20 as Z20. pose proof hR21 as Z21. pose proof hR24 as Z24. pose proof hR25 as Z25.
  rewrite <- (L5SAR.cs_of_preserved R6 R7 20 RP7) in Z20 by inl. rewrite <- (L5SAR.cs_of_preserved R6 R7 21 RP7) in Z21 by inl.
  rewrite <- (L5SAR.cs_of_preserved R6 R7 24 RP7) in Z24 by inl. rewrite <- (L5SAR.cs_of_preserved R6 R7 25 RP7) in Z25 by inl.
  rewrite L5K.rl10 in R10b. change PNM.BSZ with 40 in R10b, BHI, DISJ7.
  pose proof HOLE7 as (_ & _ & _ & _ & HB16 & _).
  pose proof (PMAIS1.bvu (getr R0 (reg 24))) as UR24. pose proof (PMAIS1.bvu (getr R0 (reg 25))) as UR25.
  LeanFeed.pfeed P (PNARCP.abrcZ_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx7 R7 (mrestrict (ahid Aw7 model7) M7) (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 43%nat => bv_unsigned (getr R0 (reg 1)) | 44%nat => bv_unsigned (getr R0 (reg 8)) | 45%nat => bv_unsigned (getr R0 (reg 9)) | 46%nat => bv_unsigned (getr R0 (reg 18)) | 47%nat => bv_unsigned (getr R0 (reg 19)) | 48%nat => bv_unsigned (getr R0 (reg 20)) | 49%nat => bv_unsigned (getr R0 (reg 21)) | 50%nat => bv_unsigned (getr R0 (reg 22)) | 51%nat => bv_unsigned (getr R0 (reg 23)) | 52%nat => bv_unsigned (getr R0 (reg 24)) | 53%nat => bv_unsigned (getr R0 (reg 25)) | 59%nat => b7 | _ => 0 end)) ltac:(first [assumption | unfold PNARCP.aligned; lia | lia]).
  destruct P as (fx8 & R8 & M8v & MG8 & _ & FZ8 & MS8 & KS8 & zR1 & zR2 & zR8 & zR9 & zR10 & zR11 & zR18 & zR19 & zR20 & zR21 & zR22 & zR23 & zR24 & zR25 & Z400).
  assert (R8ra : getr R8 (reg 1) = Z_to_bv 64 r) by (rewrite zR1, Z_to_bv_bv_unsigned; exact Rra).
  pose proof (PMK.ret_to RSEGS fx8 R8 M8v 0xac9d8 W_abcbc r F_abcbc eq_refl D_abcbc R8ra ltac:(lia) Hr2) as MS9.
  set (W8 := fun a => fb + 464 + 400 <= a < fb + 464 + 400 + 8).
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK7 _ Aw7 M7 model7 fx7 fx8 R7 706948 R8 r M8v W8 K HH7 AM7 ltac:(eapply msteps_trans; [exact MS8| exact MS9]) MG8).
  { intros a Ha N. apply FZ8; [exact Ha| exact N]. }
  { intros a Ha Wa. assert (Wa' : fb + 464 <= a < fb + 464 + 416) by (unfold W8 in Wa; lia).
    split; [apply (L5SAR.obj_client L ar _ FF 0 0 _ 416 a AOB); lia| lia]. }
  intros M8 model8 HH8 AM8 MRT8 HID8 VIS8 MGM8 FR8 VV8.
  assert (EK78 : L5SAR.ek L ar LB FF sp 24576 [(fb + 464, 416)] M7 M8).
  { apply (L5SAR.ek_piece L ar LB FF sp 24576 _ M7 M8 W8 FR8). intros a Ha Hc Ho X.
    apply (Ho (fb + 464, 416)); [left; reflexivity| unfold L5.in_rng, W8 in *; cbn [fst snd]; lia]. }
  assert (ASTK8 : L5CA.astk ar M8 sp 24576) by (apply (L5SAR.astk_grows ar M7 M8 sp 24576 ASTK7 MGM8)).
  assert (ACC8 : PMSPA.accA M8 (fb + 464) 416) by (apply (PMKA.acc_keepA' L ar LB FF sp 24576 _ M7 M8 EK78 WAPP FRB _ 416 AOP ACC7)).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK7 _ Aw7 M8 model8 (fb + 464) 416 sp 24576 HH8 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & ODEF8 & _).
  assert (AG81 : forall a, (sp - 88 <= a < sp) \/ (fb + 32 <= a < fb + 2040 /\ ~ (fb + 464 + 280 <= a < fb + 464 + 288) /\ ~ (fb + 464 + 296 <= a < fb + 464 + 304)
                           /\ ~ (fb + 464 + 312 <= a < fb + 464 + 416)) -> M8 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Hr. rewrite (FR8 a ltac:(lia) ltac:(unfold W8; lia)). apply AG71. exact Hr. }
  assert (AG84 : forall a, fb + 464 + 280 <= a < fb + 464 + 320 -> M8 (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)).
  { intros a Hr. rewrite (FR8 a ltac:(lia) ltac:(unfold W8; lia)), (T76 a ltac:(lia) ltac:(lia) ltac:(lia)), (T65 a ltac:(lia) ltac:(lia)), (T5d a ltac:(lia) ltac:(lia) ltac:(lia)),
      (T5b a ltac:(lia) ltac:(lia) ltac:(lia)). exact (T54 a ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (AG85 : forall a, fb + 464 + 320 <= a < fb + 464 + 368 -> M8 (Z_to_bv 64 a) = M5 (Z_to_bv 64 a)).
  { intros a Hr. rewrite (FR8 a ltac:(lia) ltac:(unfold W8; lia)), (T76 a ltac:(lia) ltac:(lia) ltac:(lia)), (T65 a ltac:(lia) ltac:(lia)), (T5d a ltac:(lia) ltac:(lia) ltac:(lia)).
    exact (T5b a ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (AG86 : forall a, fb + 464 + 368 <= a < fb + 464 + 392 -> M8 (Z_to_bv 64 a) = M5b (Z_to_bv 64 a)).
  { intros a Hr. rewrite (FR8 a ltac:(lia) ltac:(unfold W8; lia)), (T76 a ltac:(lia) ltac:(lia) ltac:(lia)), (T65 a ltac:(lia) ltac:(lia)).
    exact (T5d a ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (QS83 : forall y, q <= y < q + 16384 -> M8 (Z_to_bv 64 (S y)) = M3 (Z_to_bv 64 (S y))).
  { intros y Hy.
    assert (HSy : in_shadow_of q 16384 (S y) /\ 2147450880 <= S y < 2147450880 + 2 ^ 44).
    { unfold in_shadow_of, S, SB. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    destruct HSy as (HSy & SR).
    assert (Hb : forall sz scz, aclient L ar LB1 FF sz scz (S y)) by (intros sz scz; do 6 right; exists (q, 16384); split; [left; reflexivity| exact HSy]).
    rewrite (FR8 (S y) ltac:(lia) ltac:(unfold W8; lia)).
    rewrite (proj1 HP7 (S y)).
    2:{ split; [lia|]. split; [apply Hb|]. intros rg [<-|[]] Hq. unfold L5.in_rng in Hq. cbn [fst snd] in Hq. lia. }
    rewrite (T65 (S y) ltac:(lia) ltac:(lia)), (PRES5d (S y) ltac:(lia) (Hb _ _) ltac:(lia)), (PRES5b (S y) ltac:(lia) (Hb _ _) ltac:(lia)), (PRES5 (S y) ltac:(lia) (Hb _ _) ltac:(lia)).
    exact (T43 (S y) ltac:(lia) ltac:(unfold W4; lia)). }
  assert (QA8 : PMSPA.accA M8 q PM.CHUNK).
  { unfold PM.CHUNK. apply (PMFA.accA_agree M3 M8 q 16384); [intros y Hy; apply QS83; lia|].
    unfold PMSPA.accA. apply (L5CB.aacc_of_blk M3 q 16384 q 16384 QSH); lia. }
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH8) as (WB8 & _).
  destruct (WB8 (q, 16384) ltac:(unfold LB1, PNM.bvec_own; cbn [app]; right; left; reflexivity)) as (_ & QD8 & _). cbn [fst snd] in QD8.
  (* [comment removed for export] *)
  Ltac a64 AG X Ms := apply (L5C.u64_at_agree RSEGS Ms); [intros i Hi; apply AG; (lia || fail 1 "AG")| (lia || fail 1 "B1")| (lia || fail 1 "B2")| exact X].
  Ltac a32 AG X Ms := apply (PMF.u32_at_agree RSEGS Ms); [intros i Hi; apply AG; (lia || fail 1 "AG")| (lia || fail 1 "B1")| (lia || fail 1 "B2")| exact X].
  Ltac a8 AG X Ms := apply (L5C.u8_at_agree RSEGS Ms); [intros i Hi; apply AG; (lia || fail 1 "AG")| (lia || fail 1 "B1")| (lia || fail 1 "B2")| exact X].
  unfold PNARCS.kont in KONT. apply (KONT fx8 R8 M8 model8 LK7 Aw7 q b7 (adebit L cr1 40)).
  - apply L5SAR.preserved_by_index. intros k Hk.
    assert (CH : forall k', In k' [3; 4; 26; 27]%nat -> getr R8 (reg k') = getr R0 (reg k')).
    { intros k' Hk'. assert (Y : In k' PNARCP.KS_abrcZ /\ In k' L5SAR.cs_all /\ In k' PNARCP.KS_abrcH)
        by (destruct Hk' as [<-|[<-|[<-|[<-|[]]]]]; (split; [inl| split; inl])).
      destruct Y as (Y1 & Y2 & Y3). rewrite (KS8 k' Y1), (L5SAR.cs_of_preserved R6 R7 k' RP7 Y2), (KS6 k' Y3). apply CSH.
      destruct Hk' as [<-|[<-|[<-|[<-|[]]]]]; inl. }
    unfold L5SAR.cs_all in Hk. destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|Hk]]]]]]]]]]]]].
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
    + rewrite zR24, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite zR25, Z_to_bv_bv_unsigned; reflexivity.
    + apply CH; right; right; exact Hk.
  - apply (PNARCK.bparser_init_at M8 (fb + 464) (fb + 96) q b7).
    + a64 AG81 H0 M1.
    + exact ODEF8.
    + exact ACC8.
    + a8 AG81 H8 M1.
    + a8 AG81 H9 M1.
    + a8 AG81 H10 M1.
    + a32 AG81 H12 M1.
    + a64 AG81 H24 M1.
    + a64 AG81 C40 M1.
    + a64 AG81 H48 M1.
    + a64 AG81 H104 M1.
    + a32 AG81 H136 M1.
    + a32 AG81 H140 M1.
    + a64 AG81 H144 M1.
    + a64 AG81 H152 M1.
    + apply (PMF.zeros_at_agree M1); [intros i Hi; apply AG81; lia| exact Z160].
    + a64 AG81 C256 M1.
    + replace (fb + 96 + 16) with (fb + 112) by lia. a64 AG81 C264 M1.
    + apply (L5C.u64_at_agree RSEGS M4); [intros i Hi; apply AG84; lia| lia| lia|].
      apply (PMAIS1.vis_u64 _ _ _ _ _ VIS4); [eapply L5A.avis_sub; [exact OVIS3| lia| lia]| lia| lia| exact G280].
    + a64 AG81 C288 M1.
    + apply (L5C.u64_at_agree RSEGS M4); [intros i Hi; apply AG84; lia| lia| lia|].
      apply (PMAIS1.vis_u64 _ _ _ _ _ VIS4); [eapply L5A.avis_sub; [exact OVIS3| lia| lia]| lia| lia| exact G296].
    + apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG81; lia| lia| lia|].
      apply (PMCG.u64_of_zeros RSEGS M1); [apply (PMCG.zeros_sub M1 (fb + 464 + 296) 16); [exact Z296| lia| lia]| lia| lia].
    + exact Q16.
    + exact QD8.
    + exact QA8.
    + apply (PMF.u32_at_agree RSEGS M4); [intros i Hi; apply AG84; lia| lia| lia|].
      apply (PMAIS1.vis_u32 _ _ _ _ _ VIS4); [eapply L5A.avis_sub; [exact OVIS3| lia| lia]| lia| lia| exact G312].
    + apply (L5C.u64_at_agree RSEGS M5); [intros i Hi; apply AG85; lia| lia| lia|].
      apply (PMCG.u64_of_zeros RSEGS M5); [apply (PMCG.zeros_sub M5 (fb + 464 + 320) 48); [exact Z368| lia| lia]| lia| lia].
    + apply (L5C.u64_at_agree RSEGS M5); [intros i Hi; apply AG85; lia| lia| lia|].
      apply (PMCG.u64_of_zeros RSEGS M5); [apply (PMCG.zeros_sub M5 (fb + 464 + 320) 48); [exact Z368| lia| lia]| lia| lia].
    + apply (L5C.u64_at_agree RSEGS M5); [intros i Hi; apply AG85; lia| lia| lia|].
      apply (PMCG.u64_of_zeros RSEGS M5); [apply (PMCG.zeros_sub M5 (fb + 464 + 320) 48); [exact Z368| lia| lia]| lia| lia].
    + apply (L5C.u8_at_agree RSEGS M5); [intros i Hi; apply AG85; lia| lia| lia|].
      apply (PMCG.u8_of_zeros RSEGS M5); [apply (PMCG.zeros_sub M5 (fb + 464 + 320) 48); [exact Z368| lia| lia]| lia| lia].
    + apply (L5C.u8_at_agree RSEGS M5b); [intros i Hi; apply AG86; lia| lia| lia|].
      apply (PMCG.u8_of_zeros RSEGS M5b); [apply (PMCG.zeros_sub M5b (fb + 464 + 368) 24); [exact Z392| lia| lia]| lia| lia].
    + apply (bvec_of_hole M7 M8 (fb + 464 + 392) b7 0 [PNSAX.mk_root (0, 0, 0) 0]); [lia| lia| lia| unfold PNM.BSZ; lia| | | | | exact HOLE7].
      * intros i Hi. apply FR8; [lia| unfold W8; lia].
      * intros i Hi. apply FR8; [lia| unfold W8; lia].
      * unfold PNM.BSZ. split; intros x Hx.
        -- apply FR8; [lia| unfold W8; lia].
        -- assert (SR : 2147450880 <= S x < 2147450880 + 2 ^ 44).
           { unfold S, SB. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia. }
           Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
           apply FR8; [lia| unfold W8; lia].
      * replace (fb + 464 + 392 + 8) with (fb + 464 + 400) by lia.
        replace (b7 + PNM.BSZ * Z.of_nat (length [PNSAX.mk_root (0, 0, 0) 0])) with (b7 + 40) by (unfold PNM.BSZ; simpl; lia).
        apply (PMAIS1.vis_u64 _ _ _ _ _ VIS8); [eapply L5A.avis_sub; [exact OVIS7| lia| lia]| lia| lia| exact Z400].
    + lia.
    + lia.
  - change (PMSPA.pm_scr 6) with 24576. apply (L5SAR.ahpres_of L ar LB FF sp 24576 _ M0 M8).
    + apply (L5SAR.ek_trans L ar LB FF sp 24576 _ M0 M1 M8 EK). apply (L5SAR.ek_trans L ar LB FF sp 24576 _ M1 M7 M8 EK17 EK78).
    + pose proof ASTK8 as (_ & _ & _ & _ & SD8 & _). exact SD8.
    + apply (L5SAR.dk_trans L ar LB FF sp 24576 M0 M1 M8 DK).
      apply (L5SAR.dk_trans L ar LB FF sp 24576 M1 M3 M8 DK13).
      apply (L5SAR.dk_trans L ar LB FF sp 24576 M3 M4 M8 (L5SAR.dk_grows L ar LB FF sp 24576 M3 M4 MGM4)).
      apply (L5SAR.dk_trans L ar LB FF sp 24576 M4 M5 M8 DK45).
      apply (L5SAR.dk_trans L ar LB FF sp 24576 M5 M5b M8 DK55b).
      apply (L5SAR.dk_trans L ar LB FF sp 24576 M5b M5d M8 DK5bd).
      apply (L5SAR.dk_trans L ar LB FF sp 24576 M5d M6 M8 (L5SAR.dk_grows L ar LB FF sp 24576 M5d M6 MGM6)).
      apply (L5SAR.dk_trans L ar LB FF sp 24576 M6 M7 M8 DK67 (L5SAR.dk_grows L ar LB FF sp 24576 M7 M8 MGM8)).
  - exact CR3.
  - apply (L5LZ.model_rt_trans model0 model7 model8); [|exact MRT8]. apply (L5LZ.model_rt_trans model0 model6 model7); [|exact MRT7].
    apply (L5LZ.model_rt_trans model0 model5d model6); [|exact MRT6]. apply (L5LZ.model_rt_trans model0 model5c model5d); [|exact MRT5d].
    apply (L5LZ.model_rt_trans model0 model5b model5c); [|exact MRT5c]. apply (L5LZ.model_rt_trans model0 model5a model5b); [|exact MRT5b].
    apply (L5LZ.model_rt_trans model0 model5 model5a); [|exact MRT5a]. apply (L5LZ.model_rt_trans model0 model4 model5); [|exact MRT5].
    apply (L5LZ.model_rt_trans model0 model3 model4); [|exact MRT4]. apply (L5LZ.model_rt_trans model0 model1' model3); [|exact MRT3].
    apply (L5LZ.model_rt_trans model0 model1 model1'); [exact MRT| exact MRT1].
  - intros x Hx. apply INCK. apply INC7. exact Hx.
  - intros x Hx. apply IA7. apply IA3. apply INCA. exact Hx.
  - exact AM8.
  - apply (PNARCK.ri_swap12 L ar C HI HIok (b7, PNM.BSZ * 2 ^ 0) (q, 16384) LB). exact HH8.
Qed.
End Stage.
End PNARC3.
