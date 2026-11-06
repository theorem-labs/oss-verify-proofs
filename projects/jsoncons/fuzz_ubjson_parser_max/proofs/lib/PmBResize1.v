(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0 L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0 L5StepARB0 PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAb PmModelFactsA PmStep PmStepAB0 PmBRzKit PmBResizeP PmBReset1.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBResize1 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5DefsAB0.L5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBResize1.PMBRZ1.WithHeap.Call."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreAB0.L5CA."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Arith.PeanoNat.Nat."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0Aw"; "1app"; "1bool"; "1cons"; "1false"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"; "2ex"]; ["2not"; "2or"; "3Z"; "0FF"; "0HI"; "0K"; "0KS"; "0L"; "0LB"; "0LB'"; "0LBo"; "0LK"; "4Model"; "5bvmap"; "0M"; "0M'"]; ["0P"; "0R"; "0R0"; "0R1"; "6credit"; "6regs_preserved"; "7aacc"; "7ahid"; "7ar_sptop"; "7fframe"; "7ri_inv"; "7vml"; "7vml_of"; "9defined"; "9u64_at"; "9u8_at"]; ["8SCFG"; ":avis"; ";kept0"; ";mem_ok"; ";saves"; ";stok"; "<VLong"; "<VShort"; "<pot_text"; "<tb_ok"; "<vs_cap"; "<vs_own"; "<vstr"; "=HV"; "=accA"; "=cfg"]; ["=credit_keep"; "=scA"; ">FPState"; ">getr"; "?srealizes"; "@mem_grows"; "Aastk"; "Bloaded_segments"; "0S"; "0SCFG_P"; "Ceqb"; "DIn"; "Dexistsb"; "Dforallb"; "Eadd"; "Ele"]; ["Elt"; "Emodulo"; "Emul"; "Eof_nat"; "Epow"; "Esub"; "Etestbit"; "0V"; "0a"; "0a'"; "0ar"; "0b0"; "0c"; "0cr"; "0cr'"; "0cr0"]; ["0fx"; "0k"; "0k'"; "0l"; "0m"; "0model"; "0n"; "0n0"; "0o"; "0p"; "0pd"; "0q"; "0s"; "FZ_to_bv"; "Fbv"; "Fbv_unsigned"]; ["0tg"; "0tg'"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac dlia := first [ solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_ne ]
| solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_ne end ]
| solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_st ]
| solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_st end ] ].
Local Ltac lia := dlia.
Module PMBRZ1.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation vstr_at := (PM.vstr_at RSEGS PMSPA.accA).
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMB.ly_as0 L C LY.
Abbreviation HV := (PMSPA.HV L ar).
Abbreviation scA := (PMSPA.scA L).
Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LB : list (Z * Z)) (FF LK0 : list fframe) (Aw0 : list (Z * Z)) (cr0 : credit).
Variables (o n S r tg : Z) (s : PM.vstr).
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis K0 : K [].
Hypothesis STK0 : L5CA.astk ar M0 S 14336.
Hypothesis AO : PMSPA.aobjA FF o 24.
Hypothesis Ho3 : o mod 8 = 0.
Hypothesis Hn1 : 0 <= n <= PM.vs_size s + PM.CHUNK.
Hypothesis Hn2 : n < 2 ^ 26 + PM.CHUNK.
Hypothesis OPN : PMB.opnew_spec L ar HI.
Hypothesis OPD : PMB.opdel_spec L ar HI.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
(s' : PM.vstr) (tg' : Z) (cr' : credit),
regs_preserved R0 R' -> vstr_at M' o s' -> PM.vs_size s' = n -> PM.tb_ok s' tg' ->
(n <= PM.vs_cap s -> PM.vs_own s' = PM.vs_own s /\ tg' = tg) ->
L5CA.ahpres L ar LB FF S (PMSPA.pm_scr 1) [(o, 24)] M0 M' ->
PMSPA.credit_keep cr0 cr' (scA (PM.pot_text HV s tg)) (scA (PM.pot_text HV s' tg')) ->
model_rt model0 model' -> incl LK' LK0 -> incl Aw0 Aw' -> L5CA.amodel_ok Aw' model' ->
ri_inv HI (PM.vs_own s' ++ LB) FF LK' cr' Aw' M' (vml_of model') ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K.
Definition saves (M : word -> option byte) : Prop :=
L5.u64_at RSEGS M (S - 8) (bv_unsigned (getr R0 (reg 1))) /\ L5.u64_at RSEGS M (S - 16) (bv_unsigned (getr R0 (reg 8)))
/\ L5.u64_at RSEGS M (S - 24) (bv_unsigned (getr R0 (reg 9))) /\ L5.u64_at RSEGS M (S - 32) (bv_unsigned (getr R0 (reg 18)))
/\ L5.u64_at RSEGS M (S - 40) (bv_unsigned (getr R0 (reg 19))) /\ L5.u64_at RSEGS M (S - 48) (bv_unsigned (getr R0 (reg 20)))
/\ L5.u64_at RSEGS M (S - 56) (bv_unsigned (getr R0 (reg 21))) /\ L5.u64_at RSEGS M (S - 64) (bv_unsigned (getr R0 (reg 22)))
/\ L5.u64_at RSEGS M (S - 72) (bv_unsigned (getr R0 (reg 23))) /\ L5.u64_at RSEGS M (S - 80) (bv_unsigned (getr R0 (reg 24))).
Definition kept0 (R : bvmap 5 word) : Prop := forall x, In x [3; 4; 25; 26; 27]%nat -> getr R (reg x) = getr R0 (reg x).
Definition stok (model : Model) (LK : list fframe) (Aw : list (Z * Z)) : Prop :=
L5CA.amodel_ok Aw model /\ model_rt model0 model /\ incl LK LK0 /\ incl Aw0 Aw.
Definition mem_ok (M : word -> option byte) : Prop :=
L5SAR.ek L ar LB FF S 14336 [(o, 24)] M0 M /\ L5SAR.dk L ar LB FF S 14336 M0 M /\ L5CA.astk ar M S 14336 /\ PMSPA.accA M o 24.
Lemma sub_in : ltac2:(TCodec.tc2 tcn__PmBResize1 "J'6'7%211'>'3&R=&R<&R:r1%211r3%53:21qV4;1%83<15(<%<3;21&R;%13@97r2r5%43C21p041pV4E1p081pV8F1pQ>G1").
Proof. intros KS l.
intros H k Hk. rewrite forallb_forall in H. specialize (H k Hk). apply existsb_exists in H. destruct H as (x & Hx & E). apply Nat.eqb_eq in E. subst x. exact Hx.
Qed.
Lemma regs_back : ltac2:(TCodec.tc2 tcn__PmBResize1 "SG&My5'S>yR0%211%5241'>&R3r1&S=&RCu2%211%42<1%7261vR8%72=1%;3=31r2u8%:11%<2D1%?241&S?vQ2%B214%32G1%B2H1%F3H61r3u9%E11%G2O1%J241%K2:2%<2Q01%K2Q11%O3Q141r4uB%N11%Q02Q81%Q3241%Q42C2%E2Q91%Q42Q:1%Q83Q:41r5uC%Q711%Q92QA1%Q<241%Q=2L2%N2QB1%Q=2QC1%QA3QC41r6uD%Q@11%QB2QJ1%QE241%QF2Q52%Q72QK1%QF2QL1%QJ3QL41r7uE%QI11%QK2R31%QN241%QO2Q>2%Q@2R41%QO2R51%R33R541r8uF%R211%R42R<1%R7241%R82QG2%QI2R=1%R82R>1%R<3R>41r9uG%R;11%R=2RE1%R@241%RA2R02%R22RF1%RA2RG1%RE3RG41r:uH%RD11%RF2RN1%RI241%RJ2R92%R;2RO1%RJ2S01%RN3S041&QBr;%211&Q5r<%22RB1p041p081p0B1p0L1p0Q61p0Q@1p0QJ1p0R41p0R>1p0RH1p0S41pR8SA1").
Proof using All. intros R1.
intros E2 E8 E9 E18 E19 E20 E21 E22 E23 E24 KP. apply L5SAR.preserved_by_index. intros x Hx. unfold L5SAR.cs_all in Hx.
destruct Hx as [<-|Hx]; [rewrite E2, Rsp0; reflexivity|].
destruct Hx as [<-|Hx]; [apply KP; cbn; auto|]. destruct Hx as [<-|Hx]; [apply KP; cbn; auto|].
destruct Hx as [<-|Hx]; [rewrite E8; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E9; apply Z_to_bv_bv_unsigned|].
destruct Hx as [<-|Hx]; [rewrite E18; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E19; apply Z_to_bv_bv_unsigned|].
destruct Hx as [<-|Hx]; [rewrite E20; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E21; apply Z_to_bv_bv_unsigned|].
destruct Hx as [<-|Hx]; [rewrite E22; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E23; apply Z_to_bv_bv_unsigned|].
destruct Hx as [<-|Hx]; [rewrite E24; apply Z_to_bv_bv_unsigned|].
apply KP. destruct Hx as [<-|[<-|[<-|[]]]]; cbn; auto 10.
Qed.
Lemma vfacts : ltac2:(TCodec.tc2 tcn__PmBResize1 "S>'6';'B%2211%411&Q9%611&Q4'S>yR0%211'9y8%511%311p051'L&Q:vDr6vCr5r4r3r2&Q<r1%211%;8:9876541&R6vRJvR8+^P0%443:21'=&R?&RE%1265%321>&R>%12A@&RD+2+Q?%3221%:251&QA&Q7r9r7%3221%531MLp071p0?1pV:QD1pUBQE1+Vb\P0vS8%G221+H%E231&Q8%11Q0+XPPP0%L221%N251'A+QoonlP0+`PPPPPTP0%N221%Q321=%Q42;4%6221%Q7281%Q82@1&Q=%13QFCA%N2QHQF%Q031EC&R;(:%14R?R?QKQJr<%43R@21%QA2QOQM%Q>2QOQN%Q?2R3R1%QD221r:%Q:271%Q<31R5R4p041p081p0:1pV4RL1pUBRM1pV:RN1pVHRO1%R02D1%R12G1%R22J1%R32Q>1p0R51p0R;1pV<RH1pQNRJ1p4S61pULS41pQHS61pQDS91").
Proof using All. intros LB' LK cr Aw M model.
intros HH STK. pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB' FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB' FF LK cr Aw M model o 24 S 14336 HH (PMKB.aobj_of_aobjA FF o 24 AO Ho3) ltac:(lia) ltac:(reflexivity))
as ((O1 & O2 & O3 & O4 & O5) & OBIG & ODEF & OVIS & _).
split; [intros a m X1 X2; apply VIS; lia|]. split; [lia|]. split; [exact ODEF|]. split; [exact OVIS|].
intros q m a k Hin X1 X2. exact (VBLK q m a k Hin X1 X2).
Qed.
Lemma bfacts : ltac2:(TCodec.tc2 tcn__PmBResize1 "S0'6';'B%2211%411&Q9%611&Q4'S>yR0%211'9y8%511%311p051&Q;&Q:vDr8vCr7r6r5r4r3%9887654321&R;(:r2%24LL51r9%53M21'=&R?+TP0%221<'A&R>%12?>+RPP0%7221+Vb\P0%921C%7231'>&RA+@%22H1z%53Q@21&R@%123K&RE&Q8vRJ%211+XPPP0%5221%I2D1+QoonlP0%K2F1+`PQoooPP0%M21Q7%K231&RD+2+Q?%3221%Q32N1&Q=%13QAQ?Q>vS8%Q72Q21+H%Q5231%Q:21QD%Q8241%Q=271%Q>2:1%Q?2@1%Q@2F1%QA2N1%QB2Q11%QC2Q81%QD2QA1p0QF1p0QM1pV:RF1pVHRG1pU@R:1pQNR<1p4RH1pULRF1pQHRH1pQDRK1").
Proof using All. intros LB' LK cr Aw M V q m.
intros HH Hin. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
destruct (WB (q, m) Hin) as ((Q0 & Q1 & Q2 & Q3 & Q4 & Q5) & DQ & _ & _ & _ & FA & _). cbn [fst snd] in *.
rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in Q1. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5.
destruct AO as (f & Hf & X1 & X2). specialize (FA f (in_or_app _ _ _ (or_introl Hf))).
repeat split; try lia. exact DQ.
Qed.
Lemma finish_long : ltac2:(TCodec.tc2 tcn__PmBResize1 "V1'R2&My5'S>yR0%211%5241'9y8%611%311p061'L'6&Q9%211';'B%2211%611&Q4&QEr7r6r5%43321'>&R3r:&S=&RCu2%211%42O1%7261&REvR8+R@%3221%:2Q31%>3Q361r;u8%=11%?2Q:1%B241vS8%B2Q;1%F3Q;31r<uD%E11%G2QB1%J241%I2QBQ0%M3QB21r=uF%L11%N2QI1%Q1241vS6%Q12QJ1%Q53QJ31&QBr>%211&QD%113&QCr?%211&Q>&R7r@&R>+1%22Q41%6454Q01rA+@%62Q31%:4931J'=&R?%129H&R@%12JO%5231+J%621I&RD+2+K%3221%;2N1%=261&RA%12L6z%R:3RC21&QNrE%231HM&Q:vD(4(:rB%24RLRL1NvH%53RM21vCrDrCrF&Q<%11?%>8=765Q@431&QI(QF%13=QL7%321Q;&QJvS<%211%Q:2R11%D4S>S>I>(8%11S?%H3S@31&QK%118%S;3SB31vS@%S=3SFE1%QE231p0;1&R0vRO&R1vG&QH&QMvRJ%2241%431F<%7261%L3Q3RGQ>%7341Q3%:291%=4<Q;41'R4&Q@vR9%211&QOrLrK+j[[@rJrI%66RI54321vE%<4RK921p0>1p0M1p0Q=1p0QB1p0R21p0R61p0R;1p0RD1p0RK1p0S01p0S81p0S<1p0S?1p0SC1p0SL1p0T41p0T=1p0TM1pUNU31pW4U71p2U81pVHU91p4U81pQHU=1pV<UA1pQNUC1pR4UI1pV2V01").
Proof using All. intros fx R M model LK Aw q A tg' cr'.
intros STO A2 A8 A20 A22 KP SV (EK & DK & STK & ACO) W0 W16 Hn HA HAe ACQ HH TBOK OWN CK.
destruct STO as (AM & MRT & ILK & IAW).
pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
destruct (bfacts _ _ _ _ _ _ q A HH (or_introl eq_refl)) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & DQ & QO).
destruct (vfacts _ _ _ _ _ _ HH STK) as (VSTK & (O1 & O2 & O5) & ODEF & OVIS & VBLK).
set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
pose proof (PMKB.aobj_of_aobjA FF o 24 AO Ho3) as AOB.
assert (Hn2' : n < 67125248) by (unfold PM.CHUNK in Hn2; lia).
destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80).
assert (VU64 : forall a v, S - 80 <= a -> a + 8 <= S -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS MV a v).
{ intros a v X1 X2 X. apply (proj2 (L5A.u64_at_vis H M a v (VSTK a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
pose proof (VU64 (S - 8) _ ltac:(lia) ltac:(lia) S8) as V8. pose proof (VU64 (S - 16) _ ltac:(lia) ltac:(lia) S16) as V16.
pose proof (VU64 (S - 24) _ ltac:(lia) ltac:(lia) S24) as V24. pose proof (VU64 (S - 32) _ ltac:(lia) ltac:(lia) S32) as V32.
pose proof (VU64 (S - 40) _ ltac:(lia) ltac:(lia) S40) as V40. pose proof (VU64 (S - 48) _ ltac:(lia) ltac:(lia) S48) as V48.
pose proof (VU64 (S - 56) _ ltac:(lia) ltac:(lia) S56) as V56. pose proof (VU64 (S - 64) _ ltac:(lia) ltac:(lia) S64) as V64.
pose proof (VU64 (S - 72) _ ltac:(lia) ltac:(lia) S72) as V72. pose proof (VU64 (S - 80) _ ltac:(lia) ltac:(lia) S80) as V80.
assert (WST : L5.writable RSEGS MV (S - 80) 80).
{ apply (proj2 (L5A.writable_vis H M (S - 80) 80 (VSTK (S - 80) 80 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). apply (L5SAR.astk_writable ar M S 14336); [exact STK| lia| lia| lia]. }
assert (WOV : L5.writable RSEGS MV o 24).
{ apply (proj2 (L5A.writable_vis H M o 24 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
assert (WQV : L5.writable RSEGS MV (q + n) 1).
{ apply (proj2 (L5A.writable_vis H M (q + n) 1 (VBLK q A (q + n) 1 (or_introl eq_refl) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M q A (q + n) 1 DQ); lia| lia| lia]. }
pose proof (PMF.u8_of_u64 RSEGS M o (A + 1) ltac:(lia) W0) as B0. pose proof (PMF.odd_byte A HAe ltac:(lia)) as ODB.
assert (B0v : L5.u8_at RSEGS MV o ((A + 1) mod 256)).
{ apply (proj2 (L5A.u8_at_vis H M o _ (L5A.avis_sub H o 24 o 1 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact B0. }
assert (H33 : 0 <= (A + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (A + 1) 256 ltac:(lia)); lia).
assert (Dqo : q + n + 1 <= o \/ o + 24 <= q + n) by lia.
assert (Dqf : q + n + 1 <= S - 80 \/ S - 80 + 80 <= q + n) by lia.
assert (Dof : S - 80 + 80 <= o \/ o + 24 <= S - 80) by lia.
assert (A10 : getr R (reg 10) = Z_to_bv 64 (bv_unsigned (getr R (reg 10)))) by (symmetry; apply Z_to_bv_bv_unsigned).
pose proof (bv_unsigned_in_range 64 (getr R (reg 10))) as H10. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 1))) as G1.
pose proof (bv_unsigned_in_range 64 (getr R0 (reg 8))) as G8. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 9))) as G9.
pose proof (bv_unsigned_in_range 64 (getr R0 (reg 18))) as G18. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 19))) as G19.
pose proof (bv_unsigned_in_range 64 (getr R0 (reg 20))) as G20. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 21))) as G21.
pose proof (bv_unsigned_in_range 64 (getr R0 (reg 22))) as G22. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 23))) as G23.
pose proof (bv_unsigned_in_range 64 (getr R0 (reg 24))) as G24. change (bv_modulus 64) with (2 ^ 64) in *.
cfeed P (PMBRZP.aapML_conc fx R MV (fun j => match j with 2%nat => S | 10%nat => o | 33%nat => (A + 1) mod 256 | 35%nat => q | 38%nat => n
| 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
| 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19)) | 49%nat => bv_unsigned (getr R0 (reg 20))
| 50%nat => bv_unsigned (getr R0 (reg 21)) | 51%nat => bv_unsigned (getr R0 (reg 22)) | 52%nat => bv_unsigned (getr R0 (reg 23))
| 53%nat => bv_unsigned (getr R0 (reg 24)) | 54%nat => bv_unsigned (getr R (reg 10)) | _ => 0 end)) ltac:(first [assumption | unfold PMBRZP.aligned; lia | lia]).
destruct P as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & E1 & E2 & E8 & E9 & _ & E18 & E19 & E20 & E21 & E22 & E23 & E24 & C0 & C8).
assert (R1ra : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite E1, Z_to_bv_bv_unsigned; exact Rra0).
pose proof (PMK.ret_to RSEGS fx1 R1 M1v 0xd2dc4 (ltac:(oW' 0xd2dc4%Z)) r (ltac:(oF' 0xd2dc4%Z)) eq_refl (ltac:(oD' 0xd2dc4%Z)) R1ra ltac:(lia) Hr2) as MS2.
set (W1 := fun a => (o + 8 <= a < o + 8 + 8) \/ (q + n + 0 <= a < q + n + 0 + 1)).
unfold PMSPA.cfg.
apply (L5SAR.apiece L ar C HI LYa HIok ((q, A) :: LB) FF LK cr' Aw M model fx fx1 R 0xd2d70 R1 r M1v W1 K HH AM).
{ eapply msteps_trans; [exact MS1| exact MS2]. }
{ exact MG1. }
{ intros a Ha N. apply FZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
{ intros a Ha [Wa|Wa]; split.
- apply (L5SAR.obj_client L ar _ FF 0 0 o 24 a AOB); lia.
- lia.
- apply (L5SAR.block_client L ar ((q, A) :: LB) FF 0 0 q A a (or_introl eq_refl)); lia.
- lia. }
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
assert (NSH : forall x, W1 x -> x < BIGSHADOW_LO \/ BIGSHADOW_HI <= x) by (intros x [X|X]; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia).
assert (AG : forall a m, 0 <= a -> a + m <= 2 ^ 64 -> (forall i, a <= i < a + m -> ~ W1 i) -> L5C.agree_on M M1 a m).
{ intros a0 m0 Ha0 Hm0 X i Hi. apply FR1; [lia| apply X; exact Hi]. }
assert (OVIS1 : L5A.avis (ahid Aw model1) o 24) by (rewrite HID1; exact OVIS).
apply (KONT fx1 R1 M1 model1 LK Aw (PM.VLong A n q) tg' cr').
- apply regs_back; try assumption.
intros x Hx. rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
- split; [intros i Hi; apply MGM1; apply ODEF; exact Hi|].
split; [apply (PMFA.accA_agree M M1 o 24 (PMBRZK.agsh_frame M M1 W1 o 24 FR1 NSH ltac:(lia) ltac:(lia)) ACO)|].
split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AG; [lia|lia| intros i Hi X; destruct X as [X|X]; lia]|lia|lia|exact W0]|].
split; [rewrite <- VIS1 in C8; exact (proj1 (L5A.u64_at_vis _ M1 (o + 8) n (L5A.avis_sub _ o 24 (o + 8) 8 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) C8)|].
split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AG; [lia|lia| intros i Hi X; destruct X as [X|X]; lia]|lia|lia|exact W16]|].
split; [lia|]. split; [lia|]. split; [exact HAe|]. split; [intros i Hi; apply MGM1; apply DQ; exact Hi|].
apply (PMFA.accA_agree M M1 q A (PMBRZK.agsh_frame M M1 W1 q A FR1 NSH ltac:(lia) ltac:(lia)) ACQ).
- reflexivity.
- exact TBOK.
- intros X. destruct (OWN X) as (Ow1 & Ow2). split; [exact Ow1| exact Ow2].
- change (PMSPA.pm_scr 1) with 14336. apply (L5SAR.ahpres_of L ar LB FF S 14336 _ M0 M1).
+ apply (L5SAR.ek_trans L ar LB FF S 14336 _ M0 M M1 EK).
apply (L5SAR.ek_piece L ar LB FF S 14336 _ M M1 W1 FR1). intros a Ha CA OW Wa. destruct Wa as [X|X].
* apply (OW (o, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
* exact (PMBRS1.own_not_aclient L ar C HI HIok [(q, A)] LB FF LK cr' Aw M _ q A a S 14336 HH (or_introl eq_refl) ltac:(lia) CA).
+ pose proof (L5SAR.astk_grows ar M M1 S 14336 STK MGM1) as (_ & _ & _ & _ & D1 & _). exact D1.
+ apply (L5SAR.dk_trans L ar LB FF S 14336 M0 M M1 DK). apply (L5SAR.dk_grows L ar LB FF S 14336 M M1 MGM1).
- exact CK.
- exact (L5LZ.model_rt_trans model0 model model1 MRT MRT1).
- exact ILK.
- exact IAW.
- exact AM1.
- exact HH1.
Qed.
Lemma aacc_sub : ltac2:(TCodec.tc2 tcn__PmBResize1 "O'S>yR0%211'9y8%511%311p051'B&Q6r5r4r3%43321&R?%1253&R>%1265r6%3219%6231r8%=31<;p031p091p0<1pV6B1pUDC1pV4D1pUBE1pQNG1").
Proof. intros M a k a' k'. intros AC H1 H2 x Hx. apply AC. clear - H1 H2 Hx. lia. Qed.
Lemma finish_short : ltac2:(TCodec.tc2 tcn__PmBResize1 "U;'R2&My5'S>yR0%211%5241'9y8%611%311p061'L'6&Q9%211';'B%2211%611&Q4&QEr5r4r3%43321'>&R3r8&S=&RCu2%211%42O1%7261&REvR8+R@%3221%:2Q31%>3Q361r9u8%=11%?2Q:1%B241vS8%B2Q;1%F3Q;31r:uD%E11%G2QB1%J241&R>+1%22:1%L2QE1%Q03QE51r;uF%O11%Q12QL1%Q4241vS6%Q42QM1%Q83QM31&QBr<%211&QD%113&QCr=%211&Q?&R7r>%3421Q0M'=&R?z%221G+WO%42I1%6231'3&RF%12D7(5%R03421%;2Q4K+F%=2M1%?231&Q:vDvHvCr@r?rB&Q<rA%211%:89876Q0541&QI(QG%11Q<vS@%4221&QJvS<%211%Q22QB1(8%11S2&QK%116%RM3S431p061&R0vRO&R1vG&QH&QMvRJ%2241%431AD%7261%633GF%9281%<4;Q231'R4&Q@vR9%211&QOrHrG+j[[@rFrE%66R454321vE%<4R6921p0>1p0L1p0Q71p0Q=1p0QI1p0QN1p0R41p0R<1p0RA1p0RE1p0RH1p0RL1p0S51p0S@1p0SI1p0T91pUNT?1pUHTC1p4TB1pQHTG1pV<TK1pQNTM1pR4U31pV2U:1").
Proof using All. intros fx R M model LK Aw b0 cr'.
intros STO A2 A8 A20 A22 KP SV (EK & DK & STK & ACO) B0 HB0 EVB Hn HH TBOK OWN CK.
destruct STO as (AM & MRT & ILK & IAW).
pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
destruct (vfacts _ _ _ _ _ _ HH STK) as (VSTK & (O1 & O2 & O5) & ODEF & OVIS & VBLK).
set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
pose proof (PMKB.aobj_of_aobjA FF o 24 AO Ho3) as AOB.
destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80).
assert (VU64 : forall a v, S - 80 <= a -> a + 8 <= S -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS MV a v).
{ intros a v X1 X2 X. apply (proj2 (L5A.u64_at_vis H M a v (VSTK a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
pose proof (VU64 (S - 8) _ ltac:(lia) ltac:(lia) S8) as V8. pose proof (VU64 (S - 16) _ ltac:(lia) ltac:(lia) S16) as V16.
pose proof (VU64 (S - 24) _ ltac:(lia) ltac:(lia) S24) as V24. pose proof (VU64 (S - 32) _ ltac:(lia) ltac:(lia) S32) as V32.
pose proof (VU64 (S - 40) _ ltac:(lia) ltac:(lia) S40) as V40. pose proof (VU64 (S - 48) _ ltac:(lia) ltac:(lia) S48) as V48.
pose proof (VU64 (S - 56) _ ltac:(lia) ltac:(lia) S56) as V56. pose proof (VU64 (S - 64) _ ltac:(lia) ltac:(lia) S64) as V64.
pose proof (VU64 (S - 72) _ ltac:(lia) ltac:(lia) S72) as V72. pose proof (VU64 (S - 80) _ ltac:(lia) ltac:(lia) S80) as V80.
assert (WST : L5.writable RSEGS MV (S - 80) 80).
{ apply (proj2 (L5A.writable_vis H M (S - 80) 80 (VSTK (S - 80) 80 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). apply (L5SAR.astk_writable ar M S 14336); [exact STK| lia| lia| lia]. }
assert (WOV : L5.writable RSEGS MV o 24).
{ apply (proj2 (L5A.writable_vis H M o 24 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
assert (B0v : L5.u8_at RSEGS MV o b0).
{ apply (proj2 (L5A.u8_at_vis H M o _ (L5A.avis_sub H o 24 o 1 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact B0. }
assert (Dof : S - 80 + 80 <= o \/ o + 24 <= S - 80) by lia.
assert (A10 : getr R (reg 10) = Z_to_bv 64 (bv_unsigned (getr R (reg 10)))) by (symmetry; apply Z_to_bv_bv_unsigned).
pose proof (bv_unsigned_in_range 64 (getr R (reg 10))) as H10. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 1))) as G1.
pose proof (bv_unsigned_in_range 64 (getr R0 (reg 8))) as G8. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 9))) as G9.
pose proof (bv_unsigned_in_range 64 (getr R0 (reg 18))) as G18. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 19))) as G19.
pose proof (bv_unsigned_in_range 64 (getr R0 (reg 20))) as G20. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 21))) as G21.
pose proof (bv_unsigned_in_range 64 (getr R0 (reg 22))) as G22. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 23))) as G23.
pose proof (bv_unsigned_in_range 64 (getr R0 (reg 24))) as G24. change (bv_modulus 64) with (2 ^ 64) in *.
cfeed P (PMBRZP.aapMS_conc fx R MV (fun j => match j with 2%nat => S | 10%nat => o | 33%nat => b0 | 38%nat => n
| 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
| 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19)) | 49%nat => bv_unsigned (getr R0 (reg 20))
| 50%nat => bv_unsigned (getr R0 (reg 21)) | 51%nat => bv_unsigned (getr R0 (reg 22)) | 52%nat => bv_unsigned (getr R0 (reg 23))
| 53%nat => bv_unsigned (getr R0 (reg 24)) | 54%nat => bv_unsigned (getr R (reg 10)) | _ => 0 end)) ltac:(first [assumption | unfold PMBRZP.aligned; lia | lia]).
destruct P as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & E1 & E2 & E8 & E9 & _ & E18 & E19 & E20 & E21 & E22 & E23 & E24 & CN & CB).
assert (R1ra : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite E1, Z_to_bv_bv_unsigned; exact Rra0).
pose proof (PMK.ret_to RSEGS fx1 R1 M1v 0xd2dc4 (ltac:(oW' 0xd2dc4%Z)) r (ltac:(oF' 0xd2dc4%Z)) eq_refl (ltac:(oD' 0xd2dc4%Z)) R1ra ltac:(lia) Hr2) as MS2.
set (W1 := fun a => o + 0 <= a < o + 0 + 24).
unfold PMSPA.cfg.
apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr' Aw M model fx fx1 R 0xd2d70 R1 r M1v W1 K HH AM).
{ eapply msteps_trans; [exact MS1| exact MS2]. }
{ exact MG1. }
{ intros a Ha N. apply FZ1; [exact Ha| exact N]. }
{ intros a Ha Wa. split; [apply (L5SAR.obj_client L ar _ FF 0 0 o 24 a AOB); unfold W1 in Wa; lia| unfold W1 in Wa; lia]. }
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
assert (NSH : forall x, W1 x -> x < BIGSHADOW_LO \/ BIGSHADOW_HI <= x) by (intros x X; unfold W1 in X; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia).
apply (KONT fx1 R1 M1 model1 LK Aw (PM.VShort n) tg cr').
- apply regs_back; try assumption.
intros x Hx. rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
- split; [intros i Hi; apply MGM1; apply ODEF; exact Hi|].
split; [apply (PMFA.accA_agree M M1 o 24 (PMBRZK.agsh_frame M M1 W1 o 24 FR1 NSH ltac:(lia) ltac:(lia)) ACO)|].
split; [lia|]. rewrite <- VIS1 in CB. exact (proj1 (L5A.u8_at_vis _ M1 o (2 * n) (L5A.avis_sub _ o 24 o 1 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) CB).
- reflexivity.
- exact TBOK.
- intros X. split; [exact (OWN X)| reflexivity].
- change (PMSPA.pm_scr 1) with 14336. apply (L5SAR.ahpres_of L ar LB FF S 14336 _ M0 M1).
+ apply (L5SAR.ek_trans L ar LB FF S 14336 _ M0 M M1 EK).
apply (L5SAR.ek_piece L ar LB FF S 14336 _ M M1 W1 FR1). intros a Ha CA OW Wa. unfold W1 in Wa.
apply (OW (o, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
+ pose proof (L5SAR.astk_grows ar M M1 S 14336 STK MGM1) as (_ & _ & _ & _ & D1 & _). exact D1.
+ apply (L5SAR.dk_trans L ar LB FF S 14336 M0 M M1 DK). apply (L5SAR.dk_grows L ar LB FF S 14336 M M1 MGM1).
- exact CK.
- exact (L5LZ.model_rt_trans model0 model model1 MRT MRT1).
- exact ILK.
- exact IAW.
- exact AM1.
- exact HH1.
Qed.
Lemma saves_keep : ltac2:(TCodec.tc2 tcn__PmBResize1 "R2'S>yR0%211'9y8%511%311p051'B!p021'=&R?zr1%3221&R@&RD+2+R0%3221%5271%;271&@r3r2%211%411'>r5&S=%12N7%311r6%113%73M31p091p0?1pUBN1&REvR8+R@%3221%O21M%L2N4%Q2221r4%11F%I11p041pUBQ:1+SoomohPPR@%Q821<+Q?%Q52Q41%Q;2?1%Q=241&QD%11Ip011p041p0;1p0H1pR2QE1pR0QI1pQNQJ1").
Proof using All. intros M M' P.
intros FRZ X HS (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80).
assert (AG : forall a, S - 80 <= a -> a + 8 <= S -> L5C.agree_on M M' a 8).
{ intros a H1 H2 i Hi. apply FRZ; [lia| apply X; lia]. }
unfold saves. repeat split; (eapply (L5C.u64_at_agree RSEGS M M'); [apply AG; lia|lia|lia|eassumption]).
Qed.
Lemma mem_ok_fill : ltac2:(TCodec.tc2 tcn__PmBResize1 "SN'S>yR0%211'9y8%511%311p051'B'6';%1233%311&Q9%511&Q4'L&Q:vD&2r5vH%33;21vCr4r3r2r9&Q<r1%211%>8=9876541&QCr:%211&R5r;%2214'=&R?z%221<&R@&RD+2+R0%3221%52B1%:271&@r<%<21I&R>%123A%<2L1%A241%711&REvR8+R@%3221+R`0%5221%H21Q6%F2Q74%K221%A11'>r?&S=%12R5Q>%311r@%113%73R431p091p0D1p0M1pUBR61%Q82Q7Q;+Q?%Q62Q51%Q;2M1'AvS8r=%Q?221%Q322Q5+H%Q5251%QC231%QE251'?&R;(:%14RGRGR5R2%33RE1;%QJ2R7Mr>%Q?2O1%Q@2R:R7%QN221%R0251%R1271q2S01%=2S11qVHS21%?2S31%I2A1%R=1Q9p021p0M1p0Q11p0Q31p0R=1p0RA1p0RE1pV<S51p4S:1pULS81pQHS:1pQFS=1pV:SB1pVFSC1pR0SE1pQNSF1").
Proof using All. intros M M' pd m LBo LK cr Aw model.
intros HH (EK & DK & STK & ACO) MG FR H0 H1 WH. pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
destruct (vfacts _ _ _ _ _ _ HH STK) as (_ & (O1 & O2 & O5) & _).
set (P := fun a => (pd <= a < pd + m) \/ (S - 80 - 2560 <= a < S - 80)).
assert (FRP : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha N. apply FR; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
assert (NSH : forall x, P x -> x < BIGSHADOW_LO \/ BIGSHADOW_HI <= x).
{ intros x [X|X]; unfold BIGSHADOW_LO, BIGSHADOW_HI; [| lia].
destruct WH as [W|(q & A & Hin & W1 & W2)]; [lia|].
destruct (bfacts _ _ _ _ _ _ q A HH (in_or_app _ _ _ (or_introl Hin))) as (_ & _ & _ & _ & _ & Q5 & _). lia. }
split; [|split; [|split]].
- apply (L5SAR.ek_trans L ar LB FF S 14336 _ M0 M M' EK).
apply (L5SAR.ek_piece L ar LB FF S 14336 _ M M' P FRP). intros a Ha CA OW [Pa|Pa].
+ destruct WH as [W|(q & A & Hin & W1 & W2)].
* apply (OW (o, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
* exact (PMBRS1.own_not_aclient L ar C HI HIok LBo LB FF LK cr Aw M _ q A a S 14336 HH Hin ltac:(lia) CA).
+ destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ S 14336 a HH SPT (L5SAR.aclient_appb L ar LB LBo FF S 14336 a CA)) as [Z1|Z1]; lia.
- apply (L5SAR.dk_trans L ar LB FF S 14336 M0 M M' DK). apply (L5SAR.dk_grows L ar LB FF S 14336 M M' MG).
- exact (L5SAR.astk_grows ar M M' S 14336 STK MG).
- exact (PMFA.accA_agree M M' o 24 (PMBRZK.agsh_frame M M' P o 24 FRP NSH ltac:(lia) ltac:(lia)) ACO).
Qed.
Lemma fit_short : ltac2:(TCodec.tc2 tcn__PmBResize1 "TO'R2&My5'S>yR0%211%5241'9y8%611%311p061'L'6&Q9%211';'B%2211%611&QEr5r4r3%43321'>'QLvS<(QG%116%53431vS6&R>%12;:%93A31&R?+1%221?+F%4281zr7%7221vS@%C3K14&R3r>&S=&RCu2%211%42QA1%7261&REvR8+R@%3221%:2QE1%Q13QE61r?u8%=11%?2QL1%B241vS8%B2QM1%Q93QM31r@u9%E11%G2R41%J241r:%J2R51%QA3R531rAu:%M11%O2R<1%Q2241%Q12R<Q8%QH3R<21rBuB%Q411%Q62RC1%Q9241r=%Q92RD1%R03RD31rCuG%Q<11%Q>2RK1%QA241%Q@2RKQI%R73RK21&QBrD%211&QD%113&QCrE%211&Q?&R7rF&RB+2%221L%6454Q?1&Q:vDvHvCvROrG&Q<%11<%88765A4F31'R4&Q@vR9%211&QOrJrI+j[RHrH%56H4321=vE%;4J821p0=1p0G1p0O1p0Q31p0Q61p0Q:1p0QB1p0QK1p0R31p0R<1p0RE1p0S41p0S71p0S;1p0S>1p0SB1p0SG1p0SN1pV:T61pV@T71p4T61pQHT;1pV<T?1pQNTA1pR4TG1pV2TN1").
Proof using All. intros fx R M model LK Aw n0 m.
intros STO Es En Hm Hn Hn0 Etg A2 A8 A9 A10 A18 A23 KP SV MO B0 HH.
pose proof MO as (EK & DK & STK & ACO). pose proof STO as (AM & MRT & ILK & IAW).
pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
destruct (vfacts _ _ _ _ _ _ HH STK) as (VSTK & (O1 & O2 & O5) & ODEF & OVIS & VBLK).
set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
pose proof (PMKB.aobj_of_aobjA FF o 24 AO Ho3) as AOB.
assert (WST : L5.writable RSEGS MV (S - 80) 80).
{ apply (proj2 (L5A.writable_vis H M (S - 80) 80 (VSTK (S - 80) 80 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). apply (L5SAR.astk_writable ar M S 14336); [exact STK| lia| lia| lia]. }
assert (WOV : L5.writable RSEGS MV o 24).
{ apply (proj2 (L5A.writable_vis H M o 24 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
assert (Dof : S - 80 + 80 <= o \/ o + 24 <= S - 80) by lia.
cfeed P (PMBRZP.afitS_conc fx R MV (fun j => match j with 2%nat => S | 10%nat => o | 34%nat => n0 | 43%nat => m | _ => 0 end)) ltac:(first [assumption | unfold PMBRZP.aligned; lia | lia]).
destruct P as (fx1 & R1 & M1v & MG1 & FRw & _ & MS1 & KS1 & F1 & F10 & _ & F12 & F20 & F22).
assert (EM : M1v = MV) by (apply functional_extensionality; exact FRw). subst M1v.
assert (F2 : getr R1 (reg 2) = Z_to_bv 64 (S - 80)) by (rewrite (KS1 2%nat) by inl; exact A2).
unfold PMSPA.cfg.
apply (PMBRZK.fill_stage_pre L ar C HI LY HIok LB FF LK cr0 Aw M model fx fx1 R 0xd2c58 R1 (o + n0 + 1) m (S - 80) 0xd2d70 K HH (proj1 STO) MS1
(aic_shadow_defined _ _ _ _ _ ICok _ _ _ _ _ _ _ HH) F1 ltac:(split; [lia| reflexivity]) F2 F10 F12 ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(apply (L5.defined_sub M (S - 14336) 14336); [exact SDEF| lia| lia])).
{ right. exists o, 24. split; [exact AOB|]. lia. }
{ apply (L5.defined_sub M o 24); [exact ODEF| lia| lia]. }
{ apply (aacc_sub M o 24); [exact ACO| lia| lia]. }
intros R3 M3 model3 HH3 AM3 MRT3 HID3 MG3 FR3 D3 KS3 A3.
assert (KSR : forall x, In x L5K.CS -> getr R3 (reg x) = getr R1 (reg x)) by exact KS3.
apply (finish_short fx1 R3 M3 model3 LK Aw (2 * n0) cr0).
- split; [exact AM3|]. split; [exact (L5LZ.model_rt_trans model0 model model3 MRT MRT3)|]. split; [exact ILK| exact IAW].
- rewrite (KSR 2%nat) by inl. exact F2.
- rewrite (KSR 8%nat) by inl. rewrite (KS1 8%nat) by inl. exact A8.
- rewrite (KSR 20%nat) by inl. exact F20.
- rewrite (KSR 22%nat) by inl. rewrite F22. f_equal. lia.
- intros x Hx. rewrite (KSR x) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
- apply (saves_keep M M3 (fun a => (o + n0 + 1 <= a < o + n0 + 1 + m) \/ (S - 80 - 2560 <= a < S - 80))).
+ intros a Ha N. apply FR3; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X].
+ intros a Ha [X|X]; lia.
+ lia.
+ exact SV.
- apply (mem_ok_fill M M3 (o + n0 + 1) m [] LK cr0 Aw model HH MO MG3 FR3 ltac:(lia) ltac:(lia)). left; lia.
- apply (L5C.u8_at_agree RSEGS M M3); [intros i Hi; apply FR3; lia| lia| lia| exact B0].
- lia.
- apply PMF.even_byte.
- lia.
- exact HH3.
- subst tg. unfold PM.tb_ok. cbn. lia.
- intros _. rewrite Es. reflexivity.
- rewrite Es. unfold PMSPA.credit_keep, PMSPA.scA, PM.pot_text. cbn [PM.vs_cap fst snd]. lia.
Qed.
Lemma fit_long : ltac2:(TCodec.tc2 tcn__PmBResize1 "UG'R2&My5'S>yR0%211%5241'9y8%611%311p061'L'6&Q9%211';'B%2211%611&QEr7r6r5%43321'>'QLvS<(QFr4r3%33821%73651vS6&R>%12<5%;3C31&R?+1%221:&REr8%2214%62:1&R3r>&S=&RCu2%211%42Q@1%7261vR8+R@%>221%92QC1%O3QC51r?u8%<11%>2QJ1%A241vS8%A2QK1%Q73QK31r@u9%D11%F2R21%I241%H2R2M%Q>3R221rAu:%K11%M2R91%Q0241%O2R9Q7%QE3R921rBuB%Q211%Q42R@1%Q7241r<%Q72RA1%QM3RA31&QBrC%211&QD%113&QCrD%211&Q>&R7rE%R02JQL%4432Q51rF+@%R42Q81%84731Q6z%R421J'=+J%R721?&RD+2+K%3221%R<2D1%8261&RA%12C6%RL3S41=&QNrJ%231KD&QIvS@%22S01&Q:vD(4(:rH%24S@S@M1vH%53SA21vCvROrIrL&Q<rK%211%?8>87D6541'R4&Q@vR9%211&QOrOrN+j[RHrM%56QE4321>vE%;4QG821p0=1p0N1p0Q21p0Q61p0Q:1p0QD1p0QG1p0QL1p0R21p0R61p0R91p0R=1p0RF1p0RN1p0S61p0S?1p0SM1p0T21p0T61p0T;1p0TD1pV:TL1pVDTM1pV@TN1pUJTO1p4TN1pQHU31pV<U71pQNU91pR4U?1pV2UF1").
Proof using All. intros fx R M model LK Aw c n0 p m.
intros STO Es En Hm Hn A2 A8 A9 A10 A18 KP SV MO W0 W16 Hn0 Hc Hce ACP TBOK HH.
pose proof MO as (EK & DK & STK & ACO). pose proof STO as (AM & MRT & ILK & IAW).
pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
destruct (bfacts _ _ _ _ _ _ p c HH (or_introl eq_refl)) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & DP & QO).
destruct (vfacts _ _ _ _ _ _ HH STK) as (VSTK & (O1 & O2 & O5) & ODEF & OVIS & VBLK).
set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
assert (Hn2' : n < 67125248) by (unfold PM.CHUNK in Hn2; lia).
assert (WST : L5.writable RSEGS MV (S - 80) 80).
{ apply (proj2 (L5A.writable_vis H M (S - 80) 80 (VSTK (S - 80) 80 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). apply (L5SAR.astk_writable ar M S 14336); [exact STK| lia| lia| lia]. }
assert (WOV : L5.writable RSEGS MV o 24).
{ apply (proj2 (L5A.writable_vis H M o 24 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
assert (W16v : L5.u64_at RSEGS MV (o + 16) p).
{ apply (proj2 (L5A.u64_at_vis H M (o + 16) p (L5A.avis_sub H o 24 (o + 16) 8 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact W16. }
assert (Dof : S - 80 + 80 <= o \/ o + 24 <= S - 80) by lia.
cfeed P (PMBRZP.afitL_conc fx R MV (fun j => match j with 2%nat => S | 10%nat => o | 34%nat => n0 | 35%nat => p | 43%nat => m | _ => 0 end)) ltac:(first [assumption | unfold PMBRZP.aligned; lia | lia]).
destruct P as (fx1 & R1 & M1v & MG1 & FRw & _ & MS1 & KS1 & F1 & F10 & _ & F12 & F20 & F22).
assert (EM : M1v = MV) by (apply functional_extensionality; exact FRw). subst M1v.
assert (F2 : getr R1 (reg 2) = Z_to_bv 64 (S - 80)) by (rewrite (KS1 2%nat) by inl; exact A2).
unfold PMSPA.cfg.
apply (PMBRZK.fill_stage_pre L ar C HI LY HIok ((p, c) :: LB) FF LK cr0 Aw M model fx fx1 R 0xd2c58 R1 (n0 + p) m (S - 80) 0xd2d70 K HH (proj1 STO) MS1
(aic_shadow_defined _ _ _ _ _ ICok _ _ _ _ _ _ _ HH) F1 ltac:(split; [lia| reflexivity]) F2 F10 F12 ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(apply (L5.defined_sub M (S - 14336) 14336); [exact SDEF| lia| lia])).
{ left. exists p, c. split; [left; reflexivity| lia]. }
{ apply (L5.defined_sub M p c); [exact DP| lia| lia]. }
{ apply (aacc_sub M p c); [exact ACP| lia| lia]. }
intros R3 M3 model3 HH3 AM3 MRT3 HID3 MG3 FR3 D3 KS3 A3.
assert (KSR : forall x, In x L5K.CS -> getr R3 (reg x) = getr R1 (reg x)) by exact KS3.
set (P := fun a => (n0 + p <= a < n0 + p + m) \/ (S - 80 - 2560 <= a < S - 80)).
assert (FRP : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha N. apply FR3; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
assert (NSH : forall x, P x -> x < BIGSHADOW_LO \/ BIGSHADOW_HI <= x) by (intros x [X|X]; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia).
apply (finish_long fx1 R3 M3 model3 LK Aw p c tg cr0).
- split; [exact AM3|]. split; [exact (L5LZ.model_rt_trans model0 model model3 MRT MRT3)|]. split; [exact ILK| exact IAW].
- rewrite (KSR 2%nat) by inl. exact F2.
- rewrite (KSR 8%nat) by inl. rewrite (KS1 8%nat) by inl. exact A8.
- rewrite (KSR 20%nat) by inl. exact F20.
- rewrite (KSR 22%nat) by inl. rewrite F22. f_equal. lia.
- intros x Hx. rewrite (KSR x) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
- apply (saves_keep M M3 P FRP); [intros a Ha [X|X]; lia| lia| exact SV].
- apply (mem_ok_fill M M3 (n0 + p) m [(p, c)] LK cr0 Aw model HH MO MG3 FR3 ltac:(lia) ltac:(lia)). right. exists p, c. split; [left; reflexivity| lia].
- apply (L5C.u64_at_agree RSEGS M M3); [intros i Hi; apply FRP; [lia| intros [X|X]; lia]| lia| lia| exact W0].
- apply (L5C.u64_at_agree RSEGS M M3); [intros i Hi; apply FRP; [lia| intros [X|X]; lia]| lia| lia| exact W16].
- lia.
- lia.
- exact Hce.
- exact (PMFA.accA_agree M M3 p c (PMBRZK.agsh_frame M M3 P p c FRP NSH ltac:(lia) ltac:(lia)) ACP).
- exact HH3.
- rewrite Es in TBOK. unfold PM.tb_ok in *. cbn [PM.vs_cap] in *. exact TBOK.
- intros _. rewrite Es. split; reflexivity.
- rewrite Es. unfold PMSPA.credit_keep, PMSPA.scA, PM.pot_text. cbn [PM.vs_cap fst snd]. lia.
Qed.
End Call.
End WithHeap.
End PMBRZ1.
