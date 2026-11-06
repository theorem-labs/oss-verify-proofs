(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0
L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0 L5StepARB0 PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx
PmSpecsA PmSpecsAX PmSpecsAb PmModelFactsA PmStep PmStepAB0 PmBRzKit PmBResizeP PmBReset1 PmBResize1.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBResize2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBResize2.PMBRZ2.WithHeap.Call."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreAB0.L5CA."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0Aw"; "0B"; "0BX"; "1None"; "1app"; "1cons"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2ex"; "2not"]; ["2or"; "3Z"; "0FF"; "0HI"; "0K"; "0L"; "0LB"; "0LB'"; "0LBo"; "0LK"; "4Model"; "5bvmap"; "0M"; "0M1"; "0M3"; "0R"]; ["6credit"; "7aacc"; "7aclient"; "7acredit_ok"; "7adebit"; "7ar_sptop"; "7fframe"; "7ri_inv"; "7shadow_blk"; "7vml_of"; "9defined"; "9range"; "9u64_at"; "8SCFG"; ":kept0"; ":mem_ok"]; [":saves"; ":stok"; ";VLong"; ";VShort"; ";pot_text"; ";tb_ok"; ";vs_cap"; ";vstr"; "<HV"; "<OPNEW_SCR"; "<accA"; "<cfg"; "<credit_keep"; "<credit_le"; "<scA"; "=FPState"]; ["=getr"; ">srealizes"; "?mem_grows"; "@ahpres"; "Aloaded_segments"; "0S"; "0SCFG_P"; "BIn"; "Cadd"; "Cle"; "Clt"; "Cmodulo"; "Cmul"; "Cof_nat"; "Cpow"; "Csub"]; ["0a"; "0a'"; "0ar"; "0c"; "0cr"; "0cr0"; "0dst"; "0fx"; "0k"; "0k'"; "0len"; "0m"; "0model"; "0n"; "0n0"; "0o"]; ["0p"; "0pc"; "0q"; "0s"; "0s'"; "DZ_to_bv"; "Dbv"; "0tg"; "0u"]]).
Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac dlia := first [ solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_ne ]
| solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_ne end ]
| solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_st ]
| solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_st end ] ].
Local Ltac lia := dlia.
Module PMBRZ2.
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
Let sub_in := PMBRZ1.sub_in.
Let vfacts := PMBRZ1.vfacts L ar C IL HI LY HIok ICok ILY R0 M0 model0 K LB FF LK0 Aw0 cr0 o n S r tg s Rra0 RAok Rsp0 Rtp0 K0 STK0 AO Ho3 Hn1 Hn2 OPN OPD KONT.
Let bfacts := PMBRZ1.bfacts L ar C IL HI LY HIok ICok ILY R0 M0 model0 K LB FF LK0 Aw0 cr0 o n S r tg s Rra0 RAok Rsp0 Rtp0 K0 STK0 AO Ho3 Hn1 Hn2 OPN OPD KONT.
Let finish_long := PMBRZ1.finish_long L ar C IL HI LY HIok ICok ILY R0 M0 model0 K LB FF LK0 Aw0 cr0 o n S r tg s Rra0 RAok Rsp0 Rtp0 K0 STK0 AO Ho3 Hn1 Hn2 OPN OPD KONT.
Let saves_keep := PMBRZ1.saves_keep L ar C IL HI LY HIok ICok ILY R0 M0 model0 K LB FF LK0 Aw0 cr0 o n S r tg s Rra0 RAok Rsp0 Rtp0 K0 STK0 AO Ho3 Hn1 Hn2 OPN OPD KONT.
Let mem_ok_fill := PMBRZ1.mem_ok_fill L ar C IL HI LY HIok ICok ILY R0 M0 model0 K LB FF LK0 Aw0 cr0 o n S r tg s Rra0 RAok Rsp0 Rtp0 K0 STK0 AO Ho3 Hn1 Hn2 OPN OPD KONT.
Lemma aacc_sub : ltac2:(TCodec.tc2 tcn__PmBResize2 "O'S6yR0%211'9y8%511%311p051'A&Q1r5r4r3%43321&R9%1253&R8%1265r6%3219%6231r8%=31<;p031p091p0<1pUDB1pU4C1pUBD1pU2E1pQJG1").
Proof. intros M a k a' k'. intros AC H1 H2 x Hx. apply AC. clear - H1 H2 Hx. lia. Qed.
Lemma mem_ok_obj : ltac2:(TCodec.tc2 tcn__PmBResize2 "R4'S6yR0%211'9y8%511%311p051&Q?r2%211&R2r3%2214'A'<&R9zr1%3221&R:&R>+2+R0%3221%5271%;271&?vRO%=21D&R8+H%2241%=2H1%C251%811'=r6&S5%12Q6K%311r7%113%73Q531p091p0C1pU2Q01+Vb\P0%Q021D+Q?%M2L1%Q32C1'@+QoonlP0+`PPPPPTP0%I221%Q821L%Q92I4%6221%QC1Bp021p0:1p0>1p0A1p0QC1p0QG1pQLQK1pQJQL1").
Proof using All. intros M M1.
intros (EK & DK & STK & ACO) MG FR H0 H1 H5. split; [|split; [|split]].
- apply (L5SAR.ek_trans L ar LB FF S 14336 _ M0 M M1 EK).
apply (L5SAR.ek_piece L ar LB FF S 14336 _ M M1 (fun a => o <= a < o + 24) FR). intros a Ha CA OW Wa.
apply (OW (o, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
- apply (L5SAR.dk_trans L ar LB FF S 14336 M0 M M1 DK). apply (L5SAR.dk_grows L ar LB FF S 14336 M M1 MG).
- exact (L5SAR.astk_grows ar M M1 S 14336 STK MG).
- apply (PMFA.accA_agree M M1 o 24); [| exact ACO].
apply (PMBRZK.agsh_frame M M1 (fun a => o <= a < o + 24) o 24 FR); [intros x X; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia| lia| lia].
Qed.
Lemma mem_ok_mem : ltac2:(TCodec.tc2 tcn__PmBResize2 "SN'S6yR0%211'9y8%511%311p051'7';'A%2211%411&Q6%611&Q0'J&Q7vC&5r7vF%33;21vBr6r5r4r9&Q9r3%211%>8=9876541&Q?r:%211'<&R9zr1%3221&R:&R>+2+R0%3221%5271%;271&Q2vEvRBr;%Q03Q81N&R?vR5+R@%3221+R`0r2%;7:97Q3321&?%H2Q8O&R8%12Q:Q6%G2Q21%M241%611'=r>&S5%12R4Q;%311r?%113%73R331p091p0A1p0N1pU2R31%J2GF%Q;21Q9%Q82Q:I%Q>221r=%?2RBJ%211(4%11RA%E3RA31%M11p081pU2R@1&Q:r<%231R5R4'>&R7(:%14RGRGQ8QK%33RG1O%QO2Q:R8r8%Q82R:1%Q92Q=R0%R3221%R5251%R6271q2S01%=2S11qV6S21%?2S31%R>1Q;p021p0C1p0G1p0Q51p0RA1p0RE1pUFS;1pU>S<1pUJS71p4S<1pU:S:1pQDS<1pQBS?1pQLSE1pQJSF1").
Proof using All. intros M M1 LBo LK cr Aw model dst len.
intros HH (EK & DK & STK & ACO) PRES SD DD (q & A & Hin & X1 & X2). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
destruct (vfacts _ _ _ _ _ _ HH STK) as (_ & (O1 & O2 & O5) & ODEF & _).
destruct (bfacts _ _ _ _ _ _ q A HH (in_or_app _ _ _ (or_introl Hin))) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & _).
assert (PRESl : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF (S - 80) 2560 a -> ~ (dst <= a < dst + len) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha Hc Hd. apply PRES; [exact Ha| apply (L5SAR.aclient_appb L ar LB LBo FF (S - 80) 2560 a Hc)| exact Hd]. }
assert (NC : forall a, aclient L ar LB FF S 14336 a -> ~ (dst <= a < dst + len)).
{ intros a CA Da. exact (PMBRS1.own_not_aclient L ar C HI HIok LBo LB FF LK cr Aw M _ q A a S 14336 HH Hin ltac:(lia) CA). }
split; [|split; [|split]].
- apply (L5SAR.ek_trans L ar LB FF S 14336 _ M0 M M1 EK).
apply (L5SAR.ek_mem L ar LB FF S 14336 (S - 80) 2560 (fun a => dst <= a < dst + len) _ M M1 PRESl); [lia| lia|].
intros a CA _. exact (NC a CA).
- apply (L5SAR.dk_trans L ar LB FF S 14336 M0 M M1 DK).
apply (L5SAR.dk_mem L ar LB FF S 14336 (S - 80) 2560 (fun a => dst <= a < dst + len) M M1 PRESl SD); [| intros a; clear; lia| lia| lia].
intros a Da. replace a with (dst + (a - dst)) by lia. apply DD. lia.
- apply (L5SAR.astk_after_eq L ar C HI HIok _ FF LK cr Aw M M M1 _ S 14336 (S - 80) 2560 HH STK (fun x X => X)); [| exact SD| lia| lia| lia].
intros a Ha Hs Hns. apply PRES; [exact Ha| apply L5SAR.stack_client; lia| lia].
- apply (PMFA.accA_agree M M1 o 24); [| exact ACO]. intros x Hx. pose proof (PMKB.S_in_shadow x ltac:(lia)) as SX. unfold BIGSHADOW_LO, BIGSHADOW_HI in SX.
apply PRES; [unfold HeapIfaceA.S, HeapIfaceA.SB in *; lia| | unfold HeapIfaceA.S, HeapIfaceA.SB in *; lia].
destruct AO as (f & Hf & F1 & F2). unfold aclient, aclient_g. do 5 right. left. exists f. split; [exact Hf|].
unfold in_shadow_of. split; apply PMKB.S_mono; lia.
Qed.
Lemma accA_mem : ltac2:(TCodec.tc2 tcn__PmBResize2 "RN'S6yR0%211'9y8%511%311p051'7';'A%2211%411'<&R9zr1%3221&R:&R>+2+R0%3221%5271%;271&Q2vEvRBr7vB&R?vR5+R@%3221+R`0r2%;7:987321&?r3%I2;1&R8r6%22>1%I251%O251%811'=r:&S5r4%22QA1%411r;%113%83Q@31p0:1p0D1p0Q11pU2Q@1&R7(:%14QCQCGJ%33QC1E%QA2Q@>r5%I21@+Q?%Q@2Q?1%QF231'@r8%O21Q;+QoonlP0%QK221+`PQoooPP0%QM215%7231&QJr<%231QCQ6%332:QDp021p061p0?1p0E1p0G1p0L1p2R=1pV6R>1pUFR?1pU>R@1pQ@R?1pQLRE1pQJRF1").
Proof using All. intros M M1 LB' dst len q A.
intros PRES Hin H0 H1 HD AC. apply (PMFA.accA_agree M M1 q A); [| exact AC]. intros x Hx. pose proof (PMKB.S_in_shadow x ltac:(lia)) as SX.
unfold BIGSHADOW_LO, BIGSHADOW_HI in SX.
apply PRES; [unfold HeapIfaceA.S, HeapIfaceA.SB in *; lia| | unfold HeapIfaceA.S, HeapIfaceA.SB in *; lia].
unfold aclient, aclient_g. do 6 right. exists (q, A). split; [exact Hin|]. cbn [fst snd]. unfold in_shadow_of. split; apply PMKB.S_mono; lia.
Qed.
Lemma saves_mem : ltac2:(TCodec.tc2 tcn__PmBResize2 "RK'S6yR0%211'9y8%511%311p051'7';'A%2211%411'<&R9zr1%3221&R:&R>+2+R0%3221%5271%;271&Q2vEvRBr5vB&R?vR5+R@%3221+R`0r2%;7:987321&?r3%I2;1&R8r4%22>1%I251%O251%811'=r8&S5%12Q@8%311r9%113%73Q?31p091p0C1p0Q01pU2Q?1%B2DG&Q5%11Q1+XPPP0%Q0221%QA251+TP0%I231+^P0%K221%QF21Q5+Q?%QC2QB1%QI2Q81+SoonPPPPP0%QK21=r6%QM2QL1&Q@r;%211p011p051p081p0;1p0?1p0E1p0L1pUFR<1pU>R=1pQ@R<1pQLRB1pQJRC1").
Proof using All. intros M M1 LB' dst len.
intros PRES H1 H2 H3 H5 H4 SV. apply (saves_keep M M1 (fun a => (a < ahl_ceil ar \/ 2 ^ 47 <= a \/ (S - 80 - 2560 <= a < S - 80)) \/ (dst <= a < dst + len))); [| | lia| exact SV].
- intros a Ha N. apply PRES; [exact Ha| apply L5SAR.stack_client; lia| intros X; apply N; right; exact X].
- intros a Ha [X|X]; lia.
Qed.
Lemma grow_store : ltac2:(TCodec.tc2 tcn__PmBResize2 "W9'QO&Ky5'S6yR0%211%5241'9y8%611%311p061'J'7&Q6%211';'A%2211%611&QAr8r7r6%43321'=vRM&R8r5%2261%53=41&R9+1%221:z%421>&R:%12;>'<+Q@%921B&R>+2+K%3221%>2G1%8261&R;+8%22L1%I3Q11@'@+j[Z<%L3Q4Q01+j[YH%N3Q6Q21&R0rA&S5&R=uG%211%42QL1%7261+F%72QM1%Q93QM31r<%Q5214u:%;11%=2R51%@2?1r:%@2R61%QB3R631%Q6281%Q72;1%Q82G1%L2J1rBu2%G11%I2RA1%L241&R?vR5+R@%3221%O2RE1%R13RE61rCu8%Q211%Q42RL1%Q7241vRO%Q72RM1%R93RM31rDu9%Q:11%Q<2S41%Q?241r>%Q?2S51%RA3S531rEuB%QB11%QD2S<1%QG241r@%QG2S=1%RI3S=31rFuD%QJ11%QL2SD1%QO241r?%QO2SE1%S13SE31rGuE%R211%R42SL1%R7241%S73SK17rHuF%R811%R:2T21%R=241%R<2T2S<%S>3T221&Q>rI%211&Q@%113&Q?rJ%211&QJrK%231Q7Q?&Q7vC(6(:%14T6T6Q4Q<vF%43T721vB&Q4vEvRE%3321QCrL&Q9%11@%?8>98D4I31&QE(QB%13QBT;Q:vS7%T<21T7%5231&QFvS3%211%T821TB&QL%C3BAQ=&QN&QD&QHvRB%22G1%431:>%62I1%B3QETLQ=%7341@%92L1%<4L;41'R1&R4&Q=vR6%211&QKrQ2rQ1rQ0rO%56943R321vD%<4;821p0>1p0L1p0Q11p0Q81p0QI1p0QM1p0R11p0R41p0R81p0R@1p0RG1p0S01p0S91p0SB1p0SK1p0T71p0U51p0U:1p0UD1p0UG1p0UJ1p0UN1p0V51pV4V=1p2V>1p6V?1pUHV@1pUNVA1p4V@1pQDVE1pUJVI1pQJVK1pR0W11pU@W81").
Proof using All. intros fx R M model LK Aw n0 m B A pc.
intros STO En Hm Hn0 HnA HA HA8 PC A2 A8 A9 A18 A20 A21 A22 KP SV MO ACB HH TBOK GROW CK.
pose proof MO as (EK & DK & STK & ACO). pose proof STO as (AM & MRT & ILK & IAW).
pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
destruct (bfacts _ _ _ _ _ _ B A HH (or_introl eq_refl)) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & DB & QO).
destruct (vfacts _ _ _ _ _ _ HH STK) as (VSTK & (O1 & O2 & O5) & ODEF & OVIS & VBLK).
set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
pose proof (PMKB.aobj_of_aobjA FF o 24 AO Ho3) as AOB.
assert (Hn2' : n < 67125248) by (unfold PM.CHUNK in Hn2; lia).
assert (WST : L5.writable RSEGS MV (S - 80) 80).
{ apply (proj2 (L5A.writable_vis H M (S - 80) 80 (VSTK (S - 80) 80 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). apply (L5SAR.astk_writable ar M S 14336); [exact STK| lia| lia| lia]. }
assert (WOV : L5.writable RSEGS MV o 24).
{ apply (proj2 (L5A.writable_vis H M o 24 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
assert (Dof : S - 80 + 80 <= o \/ o + 24 <= S - 80) by lia.
pose proof (bv_unsigned_in_range 64 (getr R (reg 10))) as G10. pose proof (bv_unsigned_in_range 64 (getr R (reg 24))) as G24.
change (bv_modulus 64) with (2 ^ 64) in G10, G24.
assert (A24 : getr R (reg 24) = Z_to_bv 64 (bv_unsigned (getr R (reg 24)))) by (symmetry; apply Z_to_bv_bv_unsigned).
assert (A10' : getr R (reg 10) = Z_to_bv 64 (bv_unsigned (getr R (reg 10)))) by (symmetry; apply Z_to_bv_bv_unsigned).
assert (STORED : exists fx1 R1 M1v, msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) MV (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 0x77600) M1v (seg_rom RSEGS))
/\ mem_grows MV M1v /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (o + 0 <= a < o + 0 + 24) -> M1v (Z_to_bv 64 a) = MV (Z_to_bv 64 a))
/\ (forall x, In x [2; 3; 4; 8; 9; 18; 20; 21; 22; 25; 26; 27]%nat -> getr R1 (reg x) = getr R (reg x))
/\ getr R1 (reg 1) = Z_to_bv 64 863600 /\ getr R1 (reg 10) = Z_to_bv 64 (n0 + B) /\ getr R1 (reg 12) = Z_to_bv 64 m
/\ L5.u64_at RSEGS M1v (o + 16) B /\ L5.u64_at RSEGS M1v o (2 * (A / 2) + 1)).
{ destruct PC as [->|(-> & A23 & Hn022 & A10)].
- cfeed P (PMBRZP.apF_conc fx R MV (fun j => match j with 2%nat => S | 10%nat => o | 34%nat => n0 | 38%nat => n | 40%nat => A | 41%nat => B
| 43%nat => m | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 24)) | _ => 0 end)) ltac:(first [assumption | unfold PMBRZP.aligned; lia | lia]).
destruct P as (fx1 & R1 & M1v & MG1 & _ & FR1 & MS1 & KS1 & F1 & F10 & _ & F12 & C16 & _ & C0).
exists fx1, R1, M1v. split; [exact MS1|]. split; [exact MG1|]. split; [exact FR1|].
split; [intros x Hx; apply KS1; revert x Hx; apply sub_in; vm_compute; reflexivity|].
split; [exact F1|]. split; [exact F10|]. split; [exact F12|]. split; [exact C16| exact C0].
- cfeed P (PMBRZP.apDS_conc fx R MV (fun j => match j with 2%nat => S | 10%nat => o | 34%nat => n0 | 38%nat => n | 40%nat => A | 41%nat => B
| 43%nat => m | 56%nat => bv_unsigned (getr R (reg 24)) | _ => 0 end)) ltac:(first [assumption | unfold PMBRZP.aligned; lia | lia]).
destruct P as (fx1 & R1 & M1v & MG1 & _ & FR1 & MS1 & KS1 & F1 & F10 & _ & F12 & C16 & _ & C0).
exists fx1, R1, M1v. split; [exact MS1|]. split; [exact MG1|]. split; [exact FR1|].
split; [intros x Hx; apply KS1; revert x Hx; apply sub_in; vm_compute; reflexivity|].
split; [exact F1|]. split; [exact F10|]. split; [exact F12|]. split; [exact C16| exact C0]. }
destruct STORED as (fx1 & R1 & M1v & MS1 & MG1 & FR1 & KS1 & F1 & F10 & F12 & C16 & C0).
set (W1 := fun a => o + 0 <= a < o + 0 + 24).
unfold PMSPA.cfg.
apply (L5SAR.apiece L ar C HI LYa HIok ((B, A) :: LB) FF LK (adebit L cr0 A) Aw M model fx fx1 R pc R1 0x77600 M1v W1 K HH AM MS1 MG1 FR1).
{ intros a Ha Wa. unfold W1 in Wa. split; [apply (L5SAR.obj_client L ar _ FF 0 0 o 24 a AOB); lia| lia]. }
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1' VV1.
assert (OVIS1 : L5A.avis (ahid Aw model1) o 24) by (rewrite HID1; exact OVIS).
assert (NSH1 : forall x, W1 x -> x < BIGSHADOW_LO \/ BIGSHADOW_HI <= x) by (intros x X; unfold W1 in X; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia).
assert (MO1 : mem_ok M1) by (apply (mem_ok_obj M M1 MO MGM1); [intros a Ha N; apply FR1'; [exact Ha| unfold W1; lia]| lia| lia| exact O5]).
assert (ACB1 : PMSPA.accA M1 B A) by (apply (PMFA.accA_agree M M1 B A (PMBRZK.agsh_frame M M1 W1 B A FR1' NSH1 ltac:(lia) ltac:(lia)) ACB)).
assert (C16' : L5.u64_at RSEGS M1 (o + 16) B).
{ rewrite <- VIS1 in C16. exact (proj1 (L5A.u64_at_vis _ M1 (o + 16) B (L5A.avis_sub _ o 24 (o + 16) 8 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) C16). }
assert (C0' : L5.u64_at RSEGS M1 o (2 * (A / 2) + 1)).
{ rewrite <- VIS1 in C0. exact (proj1 (L5A.u64_at_vis _ M1 o _ (L5A.avis_sub _ o 24 o 8 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) C0). }
assert (F2 : getr R1 (reg 2) = Z_to_bv 64 (S - 80)) by (rewrite (KS1 2%nat) by inl; exact A2).
assert (AM1' : L5CA.amodel_ok Aw model1) by exact AM1.
apply (PMBRZK.fill_stage L ar C HI LY HIok ((B, A) :: LB) FF LK (adebit L cr0 A) Aw M1 model1 fx1 R1 (n0 + B) m (S - 80) 0xd2d70 K HH1 AM1'
(aic_shadow_defined _ _ _ _ _ ICok _ _ _ _ _ _ _ HH1) F1 ltac:(split; [lia| reflexivity]) F2 F10 F12 ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(pose proof (L5SAR.astk_grows ar M M1 S 14336 STK MGM1) as (_ & _ & _ & _ & D1 & _); apply (L5.defined_sub M1 (S - 14336) 14336); [exact D1| lia| lia])).
{ left. exists B, A. split; [left; reflexivity| lia]. }
{ apply (L5.defined_sub M1 B A); [intros i Hi; apply MGM1; apply DB; exact Hi| lia| lia]. }
{ apply (aacc_sub M1 B A); [exact ACB1| lia| lia]. }
intros R3 M3 model3 HH3 AM3 MRT3 HID3 MG3 FR3 D3 KS3 A3.
assert (KSR : forall x, In x L5K.CS -> getr R3 (reg x) = getr R1 (reg x)) by exact KS3.
set (P3 := fun a => (n0 + B <= a < n0 + B + m) \/ (S - 80 - 2560 <= a < S - 80)).
assert (FRP : forall a, 0 <= a < 2 ^ 64 -> ~ P3 a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
{ intros a Ha N. apply FR3; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
assert (NSH3 : forall x, P3 x -> x < BIGSHADOW_LO \/ BIGSHADOW_HI <= x) by (intros x [X|X]; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia).
apply (finish_long fx1 R3 M3 model3 LK Aw B A (tg + 1) (adebit L cr0 A)).
- split; [exact AM3|]. split; [exact (L5LZ.model_rt_trans model0 model1 model3 (L5LZ.model_rt_trans model0 model model1 MRT MRT1) MRT3)|]. split; [exact ILK| exact IAW].
- rewrite (KSR 2%nat) by inl. exact F2.
- rewrite (KSR 8%nat) by inl. rewrite (KS1 8%nat) by inl. exact A8.
- rewrite (KSR 20%nat) by inl. rewrite (KS1 20%nat) by inl. exact A20.
- rewrite (KSR 22%nat) by inl. rewrite (KS1 22%nat) by inl. exact A22.
- intros x Hx. rewrite (KSR x) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
- apply (saves_keep M1 M3 P3 FRP); [intros a Ha [X|X]; lia| lia|].
apply (saves_keep M M1 W1); [intros a Ha N; apply FR1'; [exact Ha| exact N]| intros a Ha X; unfold W1 in X; lia| lia| exact SV].
- apply (mem_ok_fill M1 M3 (n0 + B) m [(B, A)] LK (adebit L cr0 A) Aw model1 HH1 MO1 MG3 FR3 ltac:(lia) ltac:(lia)). right. exists B, A. split; [left; reflexivity| lia].
- apply (L5C.u64_at_agree RSEGS M1 M3); [intros i Hi; apply FRP; [lia| intros [X|X]; lia]| lia| lia|].
replace (A + 1) with (2 * (A / 2) + 1) by lia. exact C0'.
- apply (L5C.u64_at_agree RSEGS M1 M3); [intros i Hi; apply FRP; [lia| intros [X|X]; lia]| lia| lia| exact C16'].
- lia.
- lia.
- lia.
- exact (PMFA.accA_agree M1 M3 B A (PMBRZK.agsh_frame M1 M3 P3 B A FRP NSH3 ltac:(lia) ltac:(lia)) ACB1).
- exact HH3.
- exact TBOK.
- intros X. exfalso. lia.
- exact CK.
Qed.
Lemma aacc_of_block : ltac2:(TCodec.tc2 tcn__PmBResize2 "Q;'S6yR0%211'9y8%511%311p051'A&Q8r5r4r3%43321'=&R;+8%2271z%53;21&R9r6%2241r7%421>&R8%125@r8%3215%9231&Q1r:%2319;p041p0:1p0=1p0A1p0H1pUBN1pV2O1pUHQ01pVBQ11pQJQ31").
Proof. intros M u m p k.
intros [SZ SP] U8 U0 H1 H2 a Ha. clear - SZ SP U8 U0 H1 H2 Ha. unfold shadow_zero, byte_at in SZ, SP |- *.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
assert (E : HeapIfaceA.S a = HeapIfaceA.S u + (a / 8 - u / 8)) by (unfold HeapIfaceA.S; Lia.lia).
destruct (Z_lt_le_dec (a / 8 - u / 8) (m / 8)) as [LT|GE].
- left. rewrite E. apply SZ. Lia.lia.
- right. exists (m mod 8). assert (NZ : m mod 8 <> 0) by Lia.lia. assert (G : a / 8 - u / 8 = m / 8) by Lia.lia.
split. rewrite E, G. apply SP. exact NZ. Lia.lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
Lemma gan_short : ltac2:(TCodec.tc2 tcn__PmBResize2 "W7'QO&Ky5'S6yR0%211%5241'9y8%611%311p061'J'7&Q6%211';'A%2211%611&QAr7r6r5%43321'='QGvS3(QC%116%53431vRM&R8%12;:%93A31&R9+1%221?'<zr8%6221+F%8231%6231&R:%12?H+Q@%=21K&R>+2+K%3221%B2Q01%@261&R;+8%22A1%Q13Q91C&R0rA&S5&R=u2%211%42QO1%7261&R?vR5+R@%3221%:2R31%Q?3R361rBu8%=11%?2R:1%B241vRO%B2R;1%QG3R;31rCu9%E11%G2RB1%J241r=%J2RC1%QO3RC31rDu:%M11%O2RJ1%Q2241%R53RI17rEuB%Q311%Q52S01%Q8241r@%Q82S11%R=3S131rFuC%Q;11%Q=2S81%Q@241%R<2NR8%Q@2S91%RE3S931rGuE%QC11%QE2S@1%QH241r?%QH2SA1%RM3SA31rHuF%QK11%QM2SH1%R0241%QO2SHRM%S43SH21rIuG%R211%R42SO1%R7241%R62SORI%S;3SO21&Q>rJ%211&Q@%113&Q?rK%211&QJrL%231Q8Q@&Q7vC(6(:%14T3T3Q5Q=vF%43T421vB&Q4vEvRE%3321QDrM&Q9%11@%?8>98D4I31&QE(QB%13QCT3Q;vS7%T421T0%5231&QF%11T<%SK21T9&QL%B3A@Q<&QN&QD&QHvRB%22F1%431TE=%62H1%A3QDTCQ<%7341?%92K1%<4K;41'R1&R4&Q=vR6%211&QKrQ3rQ2+j[Y0rQ1rQ0%66:54321vD%=4<921p0?1p0M1p0Q11p0Q81p0QI1p0QM1p0R11p0R41p0R81p0R@1p0RH1p0S11p0S:1p0SC1p0SJ1p0T31p0T<1p0TK1p0U01p0U91p0U<1p0UD1p0UH1p0UM1p0V41p2V<1p6V=1pUHV>1pUNV?1p4V>1pQDVC1pUJVG1pQJVI1pR0VO1pU@W61").
Proof using All. intros fx R M model LK Aw n0 m B A.
intros STO Es En Hm Hn0 HnA HA HA8 A2 A8 A9 A10 A18 A19 A21 A22 A23 KP SV MO ACB HH TBOK GROW CK.
pose proof MO as (EK & DK & STK & ACO). pose proof STO as (AM & MRT & ILK & IAW).
pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
destruct (bfacts _ _ _ _ _ _ B A HH (or_introl eq_refl)) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & DB & QO).
destruct (vfacts _ _ _ _ _ _ HH STK) as (VSTK & (O1 & O2 & O5) & ODEF & OVIS & VBLK).
set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
pose proof (PMKB.aobj_of_aobjA FF o 24 AO Ho3) as AOB.
assert (WST : L5.writable RSEGS MV (S - 80) 80).
{ apply (proj2 (L5A.writable_vis H M (S - 80) 80 (VSTK (S - 80) 80 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). apply (L5SAR.astk_writable ar M S 14336); [exact STK| lia| lia| lia]. }
cfeed P (PMBRZP.apN_conc fx R MV (fun j => match j with 2%nat => S | 34%nat => n0 | 41%nat => B | 42%nat => o + 1 | _ => 0 end)) ltac:(first [assumption | unfold PMBRZP.aligned; lia | lia]).
destruct P as (fx1 & R1 & M1v & MG1 & FRw & _ & EX).
assert (EM : M1v = MV) by (apply functional_extensionality; exact FRw). subst M1v.
assert (MODE : (n0 - 0) mod 2 ^ 64 = n0) by (rewrite Z.sub_0_r; apply Z.mod_small; lia).
unfold PMSPA.cfg.
destruct EX as [(MS1 & KS1 & F1 & F11 & F12 & F20 & F)|(MS1 & KS1 & F20 & F)]; rewrite MODE in F.
-
assert (F10 : getr R1 (reg 10) = Z_to_bv 64 B) by (rewrite (KS1 10%nat) by inl; exact A10).
assert (F2 : getr R1 (reg 2) = Z_to_bv 64 (S - 80)) by (rewrite (KS1 2%nat) by inl; exact A2).
assert (F4 : getr R1 (reg 4) = Z_to_bv 64 (hl_tp L)) by (rewrite (KS1 4%nat) by inl; rewrite (KP 4%nat) by (cbn; auto); exact Rtp0).
apply (PMBRZK.move_stage_pre L ar C HI LY HIok IL ICok ILY ((B, A) :: LB) FF LK (adebit L cr0 A) Aw M model fx fx1 R 0xd2d20 R1 B (o + 1) n0 (S - 80) 0xd2d38 K
HH AM K0 MS1 F1 ltac:(split; [lia| reflexivity]) F2 F4 F10 F11 F12 ltac:(lia)).
{ apply (L5SAR.astk_sub ar M M S 14336 80 2560 STK (fun x X => X)); [lia| lia| lia|]. replace (S - 80) with (S + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
{ exists B, A. split; [left; reflexivity| lia]. }
{ apply (L5.defined_sub M B A); [exact DB| lia| lia]. }
{ apply (aacc_sub M B A); [exact ACB| lia| lia]. }
{ right. exists o, 24. split; [exact AOB| lia]. }
{ apply (L5.defined_sub M o 24); [exact ODEF| lia| lia]. }
{ apply (aacc_sub M o 24); [exact ACO| lia| lia]. }
{ lia. }
intros R3 M3 model3 RP3 R3_10 PRES3 SDEF3 D3 MRT3 AM3 HH3.
assert (C3 : forall x, In x L5SAR.cs_all -> getr R3 (reg x) = getr R1 (reg x)) by (intros x Hx; exact (L5SAR.cs_of_preserved R1 R3 x RP3 Hx)).
apply (grow_store fx1 R3 M3 model3 LK Aw n0 m B A 0xd2d38).
+ split; [exact AM3|]. split; [exact (L5LZ.model_rt_trans model0 model model3 MRT MRT3)|]. split; [exact ILK| exact IAW].
+ exact En.
+ exact Hm.
+ lia.
+ exact HnA.
+ exact HA.
+ exact HA8.
+ right. split; [reflexivity|]. split; [rewrite (C3 23%nat) by inl; rewrite (KS1 23%nat) by inl; exact A23|]. split; [lia| exact R3_10].
+ rewrite (C3 2%nat) by inl. exact F2.
+ rewrite (C3 8%nat) by inl. rewrite (KS1 8%nat) by inl. exact A8.
+ rewrite (C3 9%nat) by inl. rewrite (KS1 9%nat) by inl. exact A9.
+ rewrite (C3 18%nat) by inl. rewrite (KS1 18%nat) by inl. exact A18.
+ rewrite (C3 20%nat) by inl. exact F20.
+ rewrite (C3 21%nat) by inl. rewrite (KS1 21%nat) by inl. exact A21.
+ rewrite (C3 22%nat) by inl. rewrite (KS1 22%nat) by inl. exact A22.
+ intros x Hx. rewrite (C3 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
+ exact (saves_mem M M3 _ B n0 PRES3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SV).
+ apply (mem_ok_mem M M3 [(B, A)] LK (adebit L cr0 A) Aw model B n0 HH MO PRES3 SDEF3 D3). exists B, A. split; [left; reflexivity| lia].
+ exact (accA_mem M M3 _ B n0 B A PRES3 (or_introl eq_refl) ltac:(lia) ltac:(lia) ltac:(lia) ACB).
+ exact HH3.
+ exact TBOK.
+ exact GROW.
+ exact CK.
-
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK (adebit L cr0 A) Aw M model fx fx1 R 0xd2d20 R1 0xd2d38 _ K HH AM MS1 (fun x X => X) (fun a _ => eq_refl)).
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
assert (EM1 : M1 = M).
{ apply functional_extensionality. intros x. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply FR1. pose proof (bv_unsigned_in_range 64 x) as X.
change (bv_modulus 64) with (2 ^ 64) in X. exact X. }
subst M1.
assert (En0 : n0 = 0) by lia.
apply (grow_store fx1 R1 M model1 LK Aw n0 m B A 0xd2d38).
+ split; [exact AM1|]. split; [exact (L5LZ.model_rt_trans model0 model model1 MRT MRT1)|]. split; [exact ILK| exact IAW].
+ exact En.
+ exact Hm.
+ lia.
+ exact HnA.
+ exact HA.
+ exact HA8.
+ right. split; [reflexivity|]. split; [rewrite (KS1 23%nat) by inl; exact A23|]. split; [lia| rewrite (KS1 10%nat) by inl; rewrite A10; f_equal; lia].
+ rewrite (KS1 2%nat) by inl. exact A2.
+ rewrite (KS1 8%nat) by inl. exact A8.
+ rewrite (KS1 9%nat) by inl. exact A9.
+ rewrite (KS1 18%nat) by inl. exact A18.
+ exact F20.
+ rewrite (KS1 21%nat) by inl. exact A21.
+ rewrite (KS1 22%nat) by inl. exact A22.
+ intros x Hx. rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
+ exact SV.
+ exact MO.
+ exact ACB.
+ exact HH1.
+ exact TBOK.
+ exact GROW.
+ exact CK.
Qed.
Lemma gan_long_del : ltac2:(TCodec.tc2 tcn__PmBResize2 "W>'QO&Ky5'S6yR0%211%5241'9y8%611%311p061'J'7&Q6%211';'A%2211%611&QAr9r8r7%43321'=vRM&R8r6r4%3221%63>51&R9+1r5%3221z%521?&R:%12=5'<+Q@%:21>&R>+2+K%3221%?2C1%8261&R;+8%22L1%K3Q31@+Jr=%G221%H22:%A221&R0rC&S5&R=u2%211%42QN1%7261&R?vR5+R@%3221%:2R21%Q>3R261rDu8%=11%?2R91%B241vRO%B2R:1%QF3R:31rEu9%E11%G2RA1%J241%I2RAO%QM3RA21rFuB%L11%N2RH1%Q1241r@%Q12RI1%R53RI31rGuC%Q411%Q62S01%Q9241%R;3RO17rHuD%Q:11%Q<2S61%Q?241r?%Q?2S71%RC3S731rIuE%QB11%QD2S>1%QG241%RI3S=17rJuF%QH11%QJ2SD1%QM241%QL2SDRN%S03SD21rKuG%QO11%R12SK1%R4241%QM2Q8RN%R42SL1%S83SL31&Q>rL%211&Q@%113&Q?rM%211&QJrN%231QEQL&?%SE3SMQ?Q1%211&Q7vC(6(:%14T3T3Q?QE%24T4T4Q2BvF%53T521%63T641vB&Q4vEvRE%3321QNrQ0&Q9rO%211%B8A:9G5J41&QE(QB%13R0T;QHvS7%T<21T6%5231&QFvS3%211%T621TB&QL%D3CBQK&QN&QD&QHvRB%22H1%431:>%62J1%B3R3TLQL%7341@%92M1%<4M;41'R1&R4&Q=vR6%211&QKrQ6rQ5+j[YHrQ4rQ3%66:54321vD%=4<921p0?1p0M1p0Q21p0Q91p0QM1p0R11p0R51p0R91p0R<1p0R@1p0RI1p0S11p0S81p0SA1p0SH1p0T11p0T91p0TB1p0U11p0U71p0U<1p0UF1p0UI1p0UL1p0V11p0V91p2VA1p6VB1pUHVC1pV2VD1pUNVE1pU8VF1p4VE1pQDVJ1pUJVN1pQJW01pR0W61pU@W=1").
Proof using All. intros fx R M model LK Aw c n0 p m B A.
intros STO En Hm Hn0 HnA HA HA8 Hc A2 A8 A9 A18 A19 A20 A21 A22 A23 KP SV MO ACB NBp HH TBOK GROW CK.
pose proof MO as (EK & DK & STK & ACO). pose proof STO as (AM & MRT & ILK & IAW).
pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
destruct (bfacts _ _ _ _ _ _ B A HH (or_introl eq_refl)) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & DB & QO).
destruct (bfacts _ _ _ _ _ _ p c HH (or_intror (or_introl eq_refl))) as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & DP & PO).
destruct (vfacts _ _ _ _ _ _ HH STK) as (VSTK & (O1 & O2 & O5) & ODEF & OVIS & VBLK).
set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
assert (WST : L5.writable RSEGS MV (S - 80) 80).
{ apply (proj2 (L5A.writable_vis H M (S - 80) 80 (VSTK (S - 80) 80 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). apply (L5SAR.astk_writable ar M S 14336); [exact STK| lia| lia| lia]. }
cfeed P (PMBRZP.apDL_conc fx R MV (fun j => match j with 2%nat => S | 37%nat => c - 1 | 42%nat => p | _ => 0 end)) ltac:(first [assumption | unfold PMBRZP.aligned; lia | lia]).
destruct P as (fx1 & R1 & M1v & MG1 & FRw & _ & MS1 & KS1 & F1 & F10 & _).
assert (EM : M1v = MV) by (apply functional_extensionality; exact FRw). subst M1v.
unfold PMSPA.cfg.
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK (adebit L cr0 A) Aw M model fx fx1 R 0xd2d38 R1 0xd0890 _ K HH AM MS1 (fun x X => X) (fun a _ => eq_refl)).
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
assert (EM1 : M1 = M).
{ apply functional_extensionality. intros x. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply FR1. pose proof (bv_unsigned_in_range 64 x) as X.
change (bv_modulus 64) with (2 ^ 64) in X. exact X. }
subst M1.
set (LBc := (B, A) :: (p, c) :: LB) in *.
assert (Ip : In (p, c) LBc) by (right; left; reflexivity).
assert (ELB : lb_remove p LBc = (B, A) :: LB).
{ unfold LBc. cbn [lb_remove fst]. destruct (Z.eqb_spec B p) as [X|_]; [exfalso; exact (NBp X)|]. rewrite Z.eqb_refl. reflexivity. }
assert (STKd : L5CA.astk ar M (S - 80) PMSPA.OPDEL_SCR).
{ apply (L5SAR.astk_sub ar M M S 14336 80 PMSPA.OPDEL_SCR STK (fun x X => X)); unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR; [lia| lia| lia|].
replace (S - 80) with (S + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
unfold PMB.opdel_spec, PMSPA.opdel_spec, PMSPA.opdel_spec_at in OPD. cbn [pa_opdel PMB.AD ADDR_B] in OPD.
apply (OPD fx1 R1 M model1 K LBc FF LK Aw (adebit L cr0 A) p c (S - 80) 0xd2d4c HH1 AM1 K0 Ip).
{ rewrite L5K.rl10. exact F10. }
{ rewrite L5K.rl1. exact F1. }
{ split; [lia| reflexivity]. }
{ rewrite L5K.rl2. rewrite (KS1 2%nat) by inl. exact A2. }
{ rewrite L5K.rl4. rewrite (KS1 4%nat) by inl. rewrite (KP 4%nat) by (cbn; auto). exact Rtp0. }
{ exact STKd. }
intros fx4 R4 M4 model4 Aw4 RP4 HP4 MRT4 IAW4 AM4 HH4. rewrite ELB in HP4, HH4.
assert (C4 : forall x, In x [2; 8; 9; 18; 20; 21; 22]%nat -> getr R4 (reg x) = getr R (reg x)).
{ intros x Hx. rewrite (L5SAR.cs_of_preserved R1 R4 x RP4) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
apply KS1. revert x Hx. apply sub_in. vm_compute. reflexivity. }
assert (EK14 : L5SAR.ek L ar LB FF S 14336 [(o, 24)] M M4).
{ apply (L5SAR.ek_callee L ar LB [(B, A)] FF [] S 14336 (S - 80) PMSPA.OPDEL_SCR [(o, 24)] [] M M4 HP4); [unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR; lia| lia|].
intros a _ _ rr []. }
assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47).
{ pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & WF & FSAPP & FSCEIL & _).
intros f Hf. destruct (WF f Hf) as (X1 & X2 & _). unfold app_mem, FS_BYTES in *. lia. }
assert (WAPP : PMKB.wapp [(o, 24)]).
{ apply PMKB.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia| apply PMKB.wapp_nil]. }
apply (grow_store fx4 R4 M4 model4 LK Aw4 n0 m B A 0xd2d4c).
- split; [exact AM4|]. split; [exact (L5LZ.model_rt_trans model0 model1 model4 (L5LZ.model_rt_trans model0 model model1 MRT MRT1) MRT4)|].
split; [exact ILK| intros x Hx; exact (IAW4 x (IAW x Hx))].
- exact En.
- exact Hm.
- exact Hn0.
- exact HnA.
- exact HA.
- exact HA8.
- left; reflexivity.
- rewrite (C4 2%nat) by inl. exact A2.
- rewrite (C4 8%nat) by inl. exact A8.
- rewrite (C4 9%nat) by inl. exact A9.
- rewrite (C4 18%nat) by inl. exact A18.
- rewrite (C4 20%nat) by inl. exact A20.
- rewrite (C4 21%nat) by inl. exact A21.
- rewrite (C4 22%nat) by inl. exact A22.
- intros x Hx. rewrite (L5SAR.cs_of_preserved R1 R4 x RP4) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
- destruct HP4 as (PR4 & _ & _).
apply (saves_keep M M4 (fun a => a < ahl_ceil ar \/ 2 ^ 47 <= a \/ (S - 80 - PMSPA.OPDEL_SCR <= a < S - 80))); [| | lia| exact SV].
+ intros a Ha N. apply PR4. split; [exact Ha|]. split; [apply L5SAR.stack_client; lia| intros rr []].
+ intros a Ha X. unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR in X. lia.
- split; [|split; [|split]].
+ exact (L5SAR.ek_trans L ar LB FF S 14336 _ M0 M M4 EK EK14).
+ apply (L5SAR.dk_trans L ar LB FF S 14336 M0 M M4 DK).
apply (L5SAR.dk_callee L ar LB [(B, A)] FF [] S 14336 (S - 80) PMSPA.OPDEL_SCR [] M M4 HP4); unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR; lia.
+ apply (L5SAR.astk_after_eq L ar C HI HIok LBc FF LK (adebit L cr0 A) Aw M M M4 _ S 14336 (S - 80) PMSPA.OPDEL_SCR HH1 STK (fun x X => X));
[| | unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR; lia| lia| lia].
* intros a Ha Hs Hns. destruct HP4 as (PR4 & _ & _). apply PR4. split; [exact Ha|]. split; [apply L5SAR.stack_client; lia| intros rr []].
* destruct HP4 as (_ & SD4 & _). intros a Ha. replace a with ((S - 80 - PMSPA.OPDEL_SCR) + (a - (S - 80 - PMSPA.OPDEL_SCR))) by lia. apply SD4. lia.
+ exact (PMKB.acc_keepA' L ar LB FF S 14336 [(o, 24)] M M4 EK14 WAPP FRB o 24 AO ACO).
- exact (PMFA.accA_agree M M4 B A (PMBRZK.agsh_ahpres L ar _ FF (S - 80) PMSPA.OPDEL_SCR [] M M4 B A HP4 (or_introl eq_refl) PMKB.wapp_nil ltac:(lia) ltac:(lia)) ACB).
- exact HH4.
- exact TBOK.
- exact GROW.
- exact CK.
Qed.
Lemma gan_long : ltac2:(TCodec.tc2 tcn__PmBResize2 "WF'QO&Ky5'S6yR0%211%5241'9y8%611%311p061'J'7&Q6%211';'A%2211%611&QAr9r8r7%43321'=vRM&R8r6r4%3221%63>51&R9+1r5%3221'<z%621@&R:%12BC%5231%32@8+Q@%<21@&R>+2+K%3221%A2E1%>261&R;+8%22N1%M3Q51A+Jr=%I221%J22:%G221&R0rC&S5&R=u2%211%42R01%7261&R?vR5+R@%3221%:2R41%Q@3R461rDu8%=11%?2R;1%B241vRO%B2R<1%QH3R<31rEu9%E11%G2RC1%J241%I2RCO%QO3RC21rFu:%L11%N2RJ1%Q1241%R53RI17rGuB%Q211%Q42S01%Q7241rA%Q72S11%R=3S131rHuC%Q:11%Q<2S81%Q?241%RC3S717rIuE%Q@11%QB2S>1%QE241r?%QE2S?1%RK3S?31rJuF%QH11%QJ2SF1%QM241%QL2SFS0%S23SF21rKuG%QO11%R12SM1%R4241%QM2Q8S0%R42SN1%S:3SN31&Q>rL%211&Q@%113&Q?rM%211&QJrN%231QEQLrO%431Q3D'@%SG2Q;QC%SC21N%SI2O?%SE21Q>%5231&Q7vC(6(:%14T:T:Q>QD%24T;T;Q0BvF%53T<21%63T=41vB&Q4vEvRE%3321QMrQ1&Q9rQ0%211%B8A:9J5L41&QE(QB%13QOTBQGvS7%TC21T=%5231&QFvS3%211%T<21TI&QL%D3CBQI&QN&QD&QHvRB%22H1%431:>%62J1%B3R1U3QH%7341@%92M1%<4M;41'R1&R4&Q=vR6%211&QKrQ7rQ6+j[Y0rQ5rQ4%66:54321vD%=4<921p0?1p0M1p0Q21p0Q91p0QM1p0R41p0R71p0R;1p0R?1p0RB1p0RF1p0RO1p0S71p0S@1p0SG1p0T01p0T71p0T?1p0TH1p0U71p0U=1p0UB1p0UK1p0UM1p0V41p0V91p0VA1p2VI1p6VJ1pUHVK1pV2VL1pUNVM1pU8VN1p4VM1pQDW21pUJW61pQJW81pR0W>1pU@WE1").
Proof using All. intros fx R M model LK Aw c n0 p m B A.
intros STO En Hm Hn0 HnA HA HA8 Hc A2 A8 A9 A10 A18 A19 A21 A22 A23 KP SV MO ACB ACP ABp HH TBOK GROW CK.
pose proof MO as (EK & DK & STK & ACO). pose proof STO as (AM & MRT & ILK & IAW).
pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
assert (NBp : B <> p) by lia.
destruct (bfacts _ _ _ _ _ _ B A HH (or_introl eq_refl)) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & DB & QO).
destruct (bfacts _ _ _ _ _ _ p c HH (or_intror (or_introl eq_refl))) as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & DP & PO).
destruct (vfacts _ _ _ _ _ _ HH STK) as (VSTK & (O1 & O2 & O5) & ODEF & OVIS & VBLK).
set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
assert (WST : L5.writable RSEGS MV (S - 80) 80).
{ apply (proj2 (L5A.writable_vis H M (S - 80) 80 (VSTK (S - 80) 80 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). apply (L5SAR.astk_writable ar M S 14336); [exact STK| lia| lia| lia]. }
cfeed P (PMBRZP.apN_conc fx R MV (fun j => match j with 2%nat => S | 34%nat => n0 | 41%nat => B | 42%nat => p | _ => 0 end)) ltac:(first [assumption | unfold PMBRZP.aligned; lia | lia]).
destruct P as (fx1 & R1 & M1v & MG1 & FRw & _ & EX).
assert (EM : M1v = MV) by (apply functional_extensionality; exact FRw). subst M1v.
assert (MODE : (n0 - 0) mod 2 ^ 64 = n0) by (rewrite Z.sub_0_r; apply Z.mod_small; lia).
unfold PMSPA.cfg.
destruct EX as [(MS1 & KS1 & F1 & F11 & F12 & F20 & F)|(MS1 & KS1 & F20 & F)]; rewrite MODE in F.
- assert (F10 : getr R1 (reg 10) = Z_to_bv 64 B) by (rewrite (KS1 10%nat) by inl; exact A10).
assert (F2 : getr R1 (reg 2) = Z_to_bv 64 (S - 80)) by (rewrite (KS1 2%nat) by inl; exact A2).
assert (F4 : getr R1 (reg 4) = Z_to_bv 64 (hl_tp L)) by (rewrite (KS1 4%nat) by inl; rewrite (KP 4%nat) by (cbn; auto); exact Rtp0).
apply (PMBRZK.move_stage_pre L ar C HI LY HIok IL ICok ILY ((B, A) :: (p, c) :: LB) FF LK (adebit L cr0 A) Aw M model fx fx1 R 0xd2d20 R1 B p n0 (S - 80) 0xd2d38 K
HH AM K0 MS1 F1 ltac:(split; [lia| reflexivity]) F2 F4 F10 F11 F12 ltac:(lia)).
{ apply (L5SAR.astk_sub ar M M S 14336 80 2560 STK (fun x X => X)); [lia| lia| lia|]. replace (S - 80) with (S + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
{ exists B, A. split; [left; reflexivity| lia]. }
{ apply (L5.defined_sub M B A); [exact DB| lia| lia]. }
{ apply (aacc_sub M B A); [exact ACB| lia| lia]. }
{ left. exists p, c. split; [right; left; reflexivity| lia]. }
{ apply (L5.defined_sub M p c); [exact DP| lia| lia]. }
{ apply (aacc_sub M p c); [exact ACP| lia| lia]. }
{ lia. }
intros R3 M3 model3 RP3 R3_10 PRES3 SDEF3 D3 MRT3 AM3 HH3.
assert (C3 : forall x, In x L5SAR.cs_all -> getr R3 (reg x) = getr R1 (reg x)) by (intros x Hx; exact (L5SAR.cs_of_preserved R1 R3 x RP3 Hx)).
apply (gan_long_del fx1 R3 M3 model3 LK Aw c n0 p m B A).
+ split; [exact AM3|]. split; [exact (L5LZ.model_rt_trans model0 model model3 MRT MRT3)|]. split; [exact ILK| exact IAW].
+ exact En.
+ exact Hm.
+ lia.
+ exact HnA.
+ exact HA.
+ exact HA8.
+ exact Hc.
+ rewrite (C3 2%nat) by inl. exact F2.
+ rewrite (C3 8%nat) by inl. rewrite (KS1 8%nat) by inl. exact A8.
+ rewrite (C3 9%nat) by inl. rewrite (KS1 9%nat) by inl. exact A9.
+ rewrite (C3 18%nat) by inl. rewrite (KS1 18%nat) by inl. exact A18.
+ rewrite (C3 19%nat) by inl. rewrite (KS1 19%nat) by inl. exact A19.
+ rewrite (C3 20%nat) by inl. exact F20.
+ rewrite (C3 21%nat) by inl. rewrite (KS1 21%nat) by inl. exact A21.
+ rewrite (C3 22%nat) by inl. rewrite (KS1 22%nat) by inl. exact A22.
+ rewrite (C3 23%nat) by inl. rewrite (KS1 23%nat) by inl. exact A23.
+ intros x Hx. rewrite (C3 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
+ exact (saves_mem M M3 _ B n0 PRES3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SV).
+ apply (mem_ok_mem M M3 [(B, A); (p, c)] LK (adebit L cr0 A) Aw model B n0 HH MO PRES3 SDEF3 D3). exists B, A. split; [left; reflexivity| lia].
+ exact (accA_mem M M3 _ B n0 B A PRES3 (or_introl eq_refl) ltac:(lia) ltac:(lia) ltac:(lia) ACB).
+ exact NBp.
+ exact HH3.
+ exact TBOK.
+ exact GROW.
+ exact CK.
- apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK (adebit L cr0 A) Aw M model fx fx1 R 0xd2d20 R1 0xd2d38 _ K HH AM MS1 (fun x X => X) (fun a _ => eq_refl)).
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
assert (EM1 : M1 = M).
{ apply functional_extensionality. intros x. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply FR1. pose proof (bv_unsigned_in_range 64 x) as X.
change (bv_modulus 64) with (2 ^ 64) in X. exact X. }
subst M1.
apply (gan_long_del fx1 R1 M model1 LK Aw c n0 p m B A).
+ split; [exact AM1|]. split; [exact (L5LZ.model_rt_trans model0 model model1 MRT MRT1)|]. split; [exact ILK| exact IAW].
+ exact En.
+ exact Hm.
+ lia.
+ exact HnA.
+ exact HA.
+ exact HA8.
+ exact Hc.
+ rewrite (KS1 2%nat) by inl. exact A2.
+ rewrite (KS1 8%nat) by inl. exact A8.
+ rewrite (KS1 9%nat) by inl. exact A9.
+ rewrite (KS1 18%nat) by inl. exact A18.
+ rewrite (KS1 19%nat) by inl. exact A19.
+ exact F20.
+ rewrite (KS1 21%nat) by inl. exact A21.
+ rewrite (KS1 22%nat) by inl. exact A22.
+ rewrite (KS1 23%nat) by inl. exact A23.
+ intros x Hx. rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
+ exact SV.
+ exact MO.
+ exact ACB.
+ exact NBp.
+ exact HH1.
+ exact TBOK.
+ exact GROW.
+ exact CK.
Qed.
Lemma grow_credit : ltac2:(TCodec.tc2 tcn__PmBResize2 "QO'QG'A&QEvS3vS7%3221&R9&QF%115&R>+2+K%3221%7251&R<%1257r4%:11%<231'=r5%>11&R?+1%2281%63H41%D26>&QM&QNvE&QD&QHvRB%2241%431ON%7261vRE%:221'<&Q3r7%23<51&QL&Q4%13?84r8&R8%12Q;H%B3?31%E2D1%84>6?1+F%Q>2Q@1%?231%@2=1p0B1p0N1p0Q01p0Q81p0Q>1p0QG1p2QL1pV:QN1").
Proof using All. intros s' A.
intros (T0 & T1 & _) Hc Hc' Ec HA (CR1 & CR2).
pose proof (PMB.ly_cost L C LY) as (HK & HL & HB).
assert (Htg : tg <= 22).
{ destruct (Z.eq_dec tg 23) as [E|Nq]; [|lia]. rewrite E in T1. change (2 ^ 23) with 8388608 in T1. lia. }
pose proof (PMF.pot_text_step HV s s' tg Hc') as (P1 & P2).
unfold PMSPA.scA, PM.credit_add, PM.cost1, PM.pot_text, PMSPA.HV, LibIfaceAJ.heap_view in P1, P2, CR1, CR2 |- *.
cbn [fst snd HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead] in P1, P2, CR1, CR2 |- *. rewrite HK, HL, HB in *. rewrite ?Ec in P1, P2 |- *.
split; [unfold acredit_ok; rewrite HK, HL, HB; split; nia|]. split; [|exact Htg].
unfold PMSPA.credit_keep, adebit. rewrite HK, HL, HB. cbn [fst snd]. split; nia.
Qed.
Lemma mem_ok_new : ltac2:(TCodec.tc2 tcn__PmBResize2 "QL'S6yR0%211'9y8%511%311p051'7';'A%2211%411&Q6%611&Q0'J&Q7vC&5r5vF%33;21vBr4r3r2r7&Q9r1%211%>8=9876541&Q?r8%211&R3vEvRB%C3K;A&R?vR5+R@%3221&QI(8&Q;%211r9%=9<;:I6521?%A12p021p0A1p0E1pUJQ51p4Q:1pU:Q81pQDQ:1p8Q=1pQNQC1pQJQD1").
Proof using All. intros M M3 BX LK cr Aw model.
intros HH (EK & DK & STK & ACO) HP. pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
destruct (vfacts _ _ _ _ _ _ HH STK) as (_ & (O1 & O2 & O5) & _).
assert (EK13 : L5SAR.ek L ar LB FF S 14336 [(o, 24)] M M3).
{ apply (L5SAR.ek_callee L ar LB BX FF [] S 14336 (S - 80) PMSPA.OPNEW_SCR [(o, 24)] [] M M3 HP); [unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR; lia| lia|].
intros a _ _ rr []. }
assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47).
{ pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & WF & FSAPP & FSCEIL & _).
intros f Hf. destruct (WF f Hf) as (X1 & X2 & _). unfold app_mem, FS_BYTES in *. lia. }
assert (WAPP : PMKB.wapp [(o, 24)]).
{ apply PMKB.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia| apply PMKB.wapp_nil]. }
split; [|split; [|split]].
- exact (L5SAR.ek_trans L ar LB FF S 14336 _ M0 M M3 EK EK13).
- apply (L5SAR.dk_trans L ar LB FF S 14336 M0 M M3 DK).
apply (L5SAR.dk_callee L ar LB BX FF [] S 14336 (S - 80) PMSPA.OPNEW_SCR [] M M3 HP); unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR; lia.
- apply (L5SAR.astk_after_eq L ar C HI HIok _ FF LK cr Aw M M M3 _ S 14336 (S - 80) PMSPA.OPNEW_SCR HH STK (fun x X => X));
[| | unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR; lia| lia| lia].
+ intros a Ha Hs Hns. destruct HP as (PR & _ & _). apply PR. split; [exact Ha|]. split; [apply L5SAR.stack_client; lia| intros rr []].
+ destruct HP as (_ & SD & _). intros a Ha. replace a with ((S - 80 - PMSPA.OPNEW_SCR) + (a - (S - 80 - PMSPA.OPNEW_SCR))) by lia. apply SD. lia.
- exact (PMKB.acc_keepA' L ar LB FF S 14336 [(o, 24)] M M3 EK13 WAPP FRB o 24 AO ACO).
Qed.
Lemma saves_new : ltac2:(TCodec.tc2 tcn__PmBResize2 "QJ'S6yR0%211'9y8%511%311p051'7';'A%2211%411&R3vEvRBr1vB&R?vR5+R@%3221&QI(8&Q;%211r3r2%?9>=<;76321&R9&R8&Q5%11A+XPPP0%@221+TP0%6221+^P0%8221%:21D&R>+2+Q?%3221%?2I1+SoonPPPPP0%A21>&Q@r7%211p011p051p081p0>1p0J1pQ@Q;1pQNQA1pQJQB1").
Proof using All. intros M M3 LB'.
intros (PR & _ & _) H1 H2 H3 SV.
apply (saves_keep M M3 (fun a => a < ahl_ceil ar \/ 2 ^ 47 <= a \/ (S - 80 - PMSPA.OPNEW_SCR <= a < S - 80))); [| | lia| exact SV].
- intros a Ha Nq. apply PR. split; [exact Ha|]. split; [apply L5SAR.stack_client; lia| intros rr []].
- intros a Ha X. unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR in X. lia.
Qed.
Lemma grow_short : ltac2:(TCodec.tc2 tcn__PmBResize2 "U8'QO&Ky5'S6yR0%211%5241'9y8%611%311p061'J'7&Q6%211';'A%2211%611&QAr5r4r3%43321'='QGvS3(QC%116%53431vRM&R8%12;:%93A31&R9+1%221?&R:+F%2219'<zr7%9221%:226%5221&QEvS7%22F1&QM&QNvE&QD&QHvRB%2241%431N9%7261vRE%:221&R0r?&S5&R=u2%211%42R11%7261&R?vR5+R@%3221%:2R51%QA3R561r@u8%=11%?2R<1%B241vRO%B2R=1%QI3R=31rAu9%E11%G2RD1%J241r;%J2RE1%R13RE31rBu:%M11%O2RL1%Q2241%Q12RLQF%R83RL21rCuB%Q411%Q62S31%Q9241r>%Q92S41%R@3S431rDuG%Q<11%Q>2S;1%QA241%Q@2S;R8%RG3S;21&Q>rE%211&Q@%113&Q?rF%211&Q7vCvFvBrG&Q9%118%78654>R5F31'R1&R4&Q=vR6%211&QKrJrI+j[T0rH%5694321>vD%<4;821p0>1p0G1p0K1p0N1p0Q21p0Q:1p0QC1p0QK1p0R41p0R=1p0RL1p0S81p0S<1p0SC1p0SG1p0SK1p0T01p0T71pUHT?1pUNT@1p4T?1pQDTD1pUJTH1pQJTJ1pR0U01pU@U71").
Proof using All. intros fx R M model LK Aw n0 m.
intros STO Es En Hm Hn Hn0 TBOK CR A2 A8 A9 A10 A18 A23 KP SV MO HH.
pose proof MO as (EK & DK & STK & ACO). pose proof STO as (AM & MRT & ILK & IAW).
pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
destruct (vfacts _ _ _ _ _ _ HH STK) as (VSTK & (O1 & O2 & O5) & ODEF & OVIS & VBLK).
set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
assert (WST : L5.writable RSEGS MV (S - 80) 80).
{ apply (proj2 (L5A.writable_vis H M (S - 80) 80 (VSTK (S - 80) 80 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). apply (L5SAR.astk_writable ar M S 14336); [exact STK| lia| lia| lia]. }
assert (WOV : L5.writable RSEGS MV o 24).
{ apply (proj2 (L5A.writable_vis H M o 24 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
assert (Dof : S - 80 + 80 <= o \/ o + 24 <= S - 80) by lia.
assert (Hn2' : n < 67125248) by (unfold PM.CHUNK in Hn2; lia).
assert (Hn1' : n <= 22 + 16384) by (pose proof Hn1 as Hn1c; rewrite Es in Hn1c; cbn [PM.vs_size] in Hn1c; unfold PM.CHUNK in Hn1c; lia).
set (A := Z.lor (Z.max 44 n) 7 + 1).
destruct (PMF.tb_law_first n A ltac:(lia) Hn1' eq_refl) as (LAW & LA1 & LA2 & LA3 & LA4).
assert (EA : A = 8 * (Z.max 44 n / 8) + 8) by (unfold A; apply PMF.lor7; lia).
assert (REQ : exists fx2 R2, msteps RSEGS (@mkst fx R (Z_to_bv 64 0xd2c80) MV (seg_rom RSEGS)) (@mkst fx2 R2 (Z_to_bv 64 0x12d21c) MV (seg_rom RSEGS))
/\ getr R2 (reg 1) = Z_to_bv 64 863520 /\ getr R2 (reg 10) = Z_to_bv 64 A /\ getr R2 (reg 19) = Z_to_bv 64 (o + 1) /\ getr R2 (reg 21) = Z_to_bv 64 A
/\ getr R2 (reg 22) = Z_to_bv 64 n /\ (forall x, In x [2; 3; 4; 8; 9; 18; 23; 25; 26; 27]%nat -> getr R2 (reg x) = getr R (reg x))).
{ cfeed P (PMBRZP.agrowS_conc fx R MV (fun j => match j with 2%nat => S | 10%nat => o | 34%nat => n0 | 43%nat => m | _ => 0 end)) ltac:(first [assumption | unfold PMBRZP.aligned; lia | lia]).
destruct P as (fx1 & R1 & M1v & MG1 & FRw & _ & EX).
assert (EM : M1v = MV) by (apply functional_extensionality; exact FRw). subst M1v.
assert (MODE : (n0 + m) mod 2 ^ 64 = n) by (rewrite Z.mod_small; lia).
destruct EX as [(MS1 & KS1 & F10 & F11 & _ & F19 & F21 & F22 & F)|(MS1 & KS1 & F1 & F10 & _ & _ & F19 & F21 & F22 & _ & F)]; rewrite MODE in F.
- pose proof (PMBRZP.arec_conc fx1 R1 MV (fun j => match j with 2%nat => S | 39%nat => n0 + m | 40%nat => 8 * ((n0 + m) / 8) + 7 | _ => 0 end)) as Q.
cbn beta iota in Q.
assert (R1_2 : getr R1 (reg 2) = Z_to_bv 64 (S - 80)) by (rewrite (KS1 2%nat) by inl; exact A2).
L5SAR.feed Q ltac:(first [assumption | unfold PMBRZP.aligned; lia | lia]).
destruct Q as (fx2 & R2 & M2v & MG2 & FRw2 & _ & MS2 & KS2 & G1 & G10 & G21 & _).
assert (EM : M2v = MV) by (apply functional_extensionality; exact FRw2). subst M2v.
assert (EA' : 8 * ((n0 + m) / 8) + 7 + 1 = A) by (rewrite EA, Z.max_r by lia; rewrite <- En; lia).
exists fx2, R2. split; [eapply msteps_trans; [exact MS1| exact MS2]|].
split; [exact G1|]. split; [rewrite G10, EA'; reflexivity|]. split; [rewrite (KS2 19%nat) by inl; exact F19|].
split; [rewrite G21, EA'; reflexivity|]. split; [rewrite (KS2 22%nat) by inl; rewrite F22, En; reflexivity|].
intros x Hx. rewrite (KS2 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KS1. revert x Hx. apply sub_in. vm_compute. reflexivity.
- exists fx1, R1. split; [exact MS1|]. assert (EA' : A = 48) by (rewrite EA, Z.max_l by lia; reflexivity).
split; [exact F1|]. split; [rewrite F10, EA'; reflexivity|]. split; [exact F19|]. split; [rewrite F21, EA'; reflexivity|].
split; [rewrite F22, En; reflexivity|].
intros x Hx. apply KS1. revert x Hx. apply sub_in. vm_compute. reflexivity. }
destruct REQ as (fx2 & R2 & MS2 & B1 & B10 & B19 & B21 & B22 & KS2).
unfold PMSPA.cfg.
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK cr0 Aw M model fx fx2 R 0xd2c80 R2 0x12d21c _ K HH AM MS2 (fun x X => X) (fun a _ => eq_refl)).
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
assert (EM1 : M1 = M).
{ apply functional_extensionality. intros x. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply FR1. pose proof (bv_unsigned_in_range 64 x) as X.
change (bv_modulus 64) with (2 ^ 64) in X. exact X. }
subst M1.
destruct (grow_credit (PM.VLong A n 0) A TBOK ltac:(rewrite Es; cbn; lia) ltac:(rewrite Es; cbn; lia) eq_refl LA3 CR) as (CROK & CK & Htg).
assert (STKn : L5CA.astk ar M (S - 80) PMSPA.OPNEW_SCR).
{ apply (L5SAR.astk_sub ar M M S 14336 80 PMSPA.OPNEW_SCR STK (fun x X => X)); unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR; [lia| lia| lia|].
replace (S - 80) with (S + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
unfold PMB.opnew_spec, PMSPA.opnew_spec in OPN. cbn [pa_opnew PMB.AD ADDR_B] in OPN.
apply (OPN fx2 R2 M model1 K LB FF LK Aw cr0 A (S - 80) 0xd2d20 HH1 AM1 K0).
{ rewrite L5K.rl10. exact B10. }
{ lia. }
{ exact CROK. }
{ rewrite L5K.rl1. exact B1. }
{ split; [lia| reflexivity]. }
{ rewrite L5K.rl2. rewrite (KS2 2%nat) by inl. exact A2. }
{ rewrite L5K.rl4. rewrite (KS2 4%nat) by inl. rewrite (KP 4%nat) by (cbn; auto). exact Rtp0. }
{ exact STKn. }
intros fx3 R3 M3 model3 Aw3 B R3_10 RP3 FB HP3 MRT3 IAW3 AM3 HH3. rewrite L5K.rl10 in R3_10.
destruct FB as ((FB0 & FB1 & FB2 & FB3 & FB4 & FB5) & FBa & FBf & FBd & FBs). cbn [fst snd] in *.
assert (C3 : forall x, In x [2; 8; 9; 18; 19; 21; 22; 23]%nat -> getr R3 (reg x) = getr R2 (reg x)).
{ intros x Hx. apply (L5SAR.cs_of_preserved R2 R3 x RP3). revert x Hx. apply sub_in. vm_compute. reflexivity. }
apply (gan_short fx3 R3 M3 model3 LK Aw3 n0 m B A).
- split; [exact AM3|]. split; [exact (L5LZ.model_rt_trans model0 model1 model3 (L5LZ.model_rt_trans model0 model model1 MRT MRT1) MRT3)|].
split; [exact ILK| intros x Hx; exact (IAW3 x (IAW x Hx))].
- exact Es.
- exact En.
- exact Hm.
- exact Hn0.
- lia.
- lia.
- exact LA4.
- rewrite (C3 2%nat) by inl. rewrite (KS2 2%nat) by inl. exact A2.
- rewrite (C3 8%nat) by inl. rewrite (KS2 8%nat) by inl. exact A8.
- rewrite (C3 9%nat) by inl. rewrite (KS2 9%nat) by inl. exact A9.
- exact R3_10.
- rewrite (C3 18%nat) by inl. rewrite (KS2 18%nat) by inl. exact A18.
- rewrite (C3 19%nat) by inl. exact B19.
- rewrite (C3 21%nat) by inl. exact B21.
- rewrite (C3 22%nat) by inl. exact B22.
- rewrite (C3 23%nat) by inl. rewrite (KS2 23%nat) by inl. exact A23.
- intros x Hx. rewrite (L5SAR.cs_of_preserved R2 R3 x RP3) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
rewrite (KS2 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
- exact (saves_new M M3 LB HP3 ltac:(lia) ltac:(lia) ltac:(lia) SV).
- exact (mem_ok_new M M3 [] LK cr0 Aw model1 HH1 MO HP3).
- apply (aacc_of_block M3 B A B A FBs); [apply PMFA.mod16_8; exact FB2| lia| lia| lia].
- exact HH3.
- assert (Etg : tg = 0) by (rewrite Es in TBOK; destruct TBOK as (_ & _ & X); exact X).
rewrite Etg. split; [lia|]. split; [cbn; lia|]. split; [exact LAW| lia].
- rewrite Es. cbn. lia.
- rewrite Es in CK |- *. exact CK.
Qed.
Lemma grow_long : ltac2:(TCodec.tc2 tcn__PmBResize2 "V<'QO&Ky5'S6yR0%211%5241'9y8%611%311p061'J'7&Q6%211';'A%2211%611&QAr7r6r5%43321'='QGvS3(QBr4r3%33821%73651vRM&R8%12<5%;3C31&R9+1%221:&R:&R?r8%2215%421;'<z%:215r9%9271%5231&QEvS7%22J1+Jr;%C221&R>+2+K%3221%H261%A261&R;r<%2217%Q93QA1D&Q<&R4rAvRO+@%Q6221%64541B&QJrBr>%332=1&QM&QNvE&QD&QHvRB%2241%431QJQ1%7261vRE%:221&R0rE&S5&R=u2%211%42RM1%7261vR5+R@%QJ221%92S01%R<3S051rFu8%<11%>2S71%A241%@2S7Q5%RC3S721rGu9%C11%E2S>1%H241r?%H2S?1%RK3S?31rHu:%K11%M2SF1%Q0241%O2SFRD%S23SF21rIuB%Q211%Q42SM1%Q7241rC%Q72SN1%S:3SN31rJuG%Q:11%Q<2T51%Q?241%S02Q?S3%Q?2T61%SB3T631&Q>rK%211&Q@%113&Q?rL%211&Q7vC(6(:%14T7T7Q;LvF%43T821vBrM&Q9%11<%;8:54BR8K31'R1&Q=vR6%211&QKrQ0rO+j[T0rN%56S54321=vD%;4S7821p0=1p0J1p0N1p0Q11p0Q51p0Q>1p0QG1p0QO1p0R81p0R@1p0RN1p0S:1p0S?1p0SG1p0SL1p0T61p0T:1p0TA1p0TG1p0TK1p0U01p0U91pUHUA1pV2UB1pUNUC1pU8UD1p4UC1pQDUH1pUJUL1pQJUN1pR0V41pU@V;1").
Proof using All. intros fx R M model LK Aw c n0 p m.
intros STO Es En Hm Hn Hn0 TBOK Hc Hce W16 ACP CR A2 A8 A9 A10 A18 A23 KP SV MO HH.
pose proof MO as (EK & DK & STK & ACO). pose proof STO as (AM & MRT & ILK & IAW).
pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
destruct (bfacts _ _ _ _ _ _ p c HH (or_introl eq_refl)) as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & DP & PO).
destruct (vfacts _ _ _ _ _ _ HH STK) as (VSTK & (O1 & O2 & O5) & ODEF & OVIS & VBLK).
set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
assert (WST : L5.writable RSEGS MV (S - 80) 80).
{ apply (proj2 (L5A.writable_vis H M (S - 80) 80 (VSTK (S - 80) 80 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). apply (L5SAR.astk_writable ar M S 14336); [exact STK| lia| lia| lia]. }
assert (WOV : L5.writable RSEGS MV o 24).
{ apply (proj2 (L5A.writable_vis H M o 24 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
assert (W16v : L5.u64_at RSEGS MV (o + 16) p).
{ apply (proj2 (L5A.u64_at_vis H M (o + 16) p (L5A.avis_sub H o 24 (o + 16) 8 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact W16. }
assert (Dof : S - 80 + 80 <= o \/ o + 24 <= S - 80) by lia.
assert (Hn2' : n < 67125248) by (unfold PM.CHUNK in Hn2; lia).
assert (Hn1' : n <= c - 1 + 16384) by (pose proof Hn1 as Hn1c; rewrite Es in Hn1c; cbn [PM.vs_size] in Hn1c; unfold PM.CHUNK in Hn1c; lia).
assert (TLAW : PM.tb_law c) by (rewrite Es in TBOK; destruct TBOK as (_ & _ & X & _); exact X).
set (A := Z.lor (Z.max (2 * (c - 1)) n) 7 + 1).
destruct (PMF.tb_law_step c n A TLAW ltac:(lia) ltac:(lia) Hn1' ltac:(lia) eq_refl) as (LAW & LA1 & LA2 & LA3 & LA4).
assert (EA : A = 8 * (Z.max (2 * (c - 1)) n / 8) + 8) by (unfold A; apply PMF.lor7; lia).
assert (REQ : exists fx2 R2, msteps RSEGS (@mkst fx R (Z_to_bv 64 0xd2c80) MV (seg_rom RSEGS)) (@mkst fx2 R2 (Z_to_bv 64 0x12d21c) MV (seg_rom RSEGS))
/\ getr R2 (reg 1) = Z_to_bv 64 863520 /\ getr R2 (reg 10) = Z_to_bv 64 A /\ getr R2 (reg 19) = Z_to_bv 64 p /\ getr R2 (reg 21) = Z_to_bv 64 A
/\ getr R2 (reg 22) = Z_to_bv 64 n /\ (forall x, In x [2; 3; 4; 8; 9; 18; 23; 25; 26; 27]%nat -> getr R2 (reg x) = getr R (reg x))).
{ cfeed P (PMBRZP.agrowL_conc fx R MV (fun j => match j with 2%nat => S | 10%nat => o | 34%nat => n0 | 35%nat => p | 37%nat => c - 1 | 43%nat => m | _ => 0 end)) ltac:(first [assumption | unfold PMBRZP.aligned; lia | lia]).
destruct P as (fx1 & R1 & M1v & MG1 & FRw & _ & EX).
assert (EM : M1v = MV) by (apply functional_extensionality; exact FRw). subst M1v.
assert (MODE : (n0 + m) mod 2 ^ 64 = n) by (rewrite Z.mod_small; lia).
assert (MODC : (2 * (c - 1)) mod 2 ^ 64 = 2 * (c - 1)) by (rewrite Z.mod_small; lia).
destruct EX as [(MS1 & KS1 & F10 & F11 & _ & F19 & F21 & F22 & F)|(MS1 & KS1 & F1 & F10 & _ & _ & F19 & F21 & F22 & _ & F)]; rewrite MODE, MODC in F.
- pose proof (PMBRZP.arec_conc fx1 R1 MV (fun j => match j with 2%nat => S | 39%nat => n0 + m | 40%nat => 8 * ((n0 + m) / 8) + 7 | _ => 0 end)) as Q.
cbn beta iota in Q.
assert (R1_2 : getr R1 (reg 2) = Z_to_bv 64 (S - 80)) by (rewrite (KS1 2%nat) by inl; exact A2).
L5SAR.feed Q ltac:(first [assumption | unfold PMBRZP.aligned; lia | lia]).
destruct Q as (fx2 & R2 & M2v & MG2 & FRw2 & _ & MS2 & KS2 & G1 & G10 & G21 & _).
assert (EM : M2v = MV) by (apply functional_extensionality; exact FRw2). subst M2v.
assert (EA' : 8 * ((n0 + m) / 8) + 7 + 1 = A) by (rewrite EA, Z.max_r by lia; rewrite <- En; lia).
exists fx2, R2. split; [eapply msteps_trans; [exact MS1| exact MS2]|].
split; [exact G1|]. split; [rewrite G10, EA'; reflexivity|]. split; [rewrite (KS2 19%nat) by inl; exact F19|].
split; [rewrite G21, EA'; reflexivity|]. split; [rewrite (KS2 22%nat) by inl; rewrite F22, En; reflexivity|].
intros x Hx. rewrite (KS2 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KS1. revert x Hx. apply sub_in. vm_compute. reflexivity.
- exists fx1, R1. split; [exact MS1|]. assert (EA' : A = 8 * ((2 * (c - 1)) / 8) + 8) by (rewrite EA, Z.max_l by lia; reflexivity).
split; [exact F1|]. split; [rewrite F10, EA'; reflexivity|]. split; [exact F19|]. split; [rewrite F21, EA'; reflexivity|].
split; [rewrite F22, En; reflexivity|].
intros x Hx. apply KS1. revert x Hx. apply sub_in. vm_compute. reflexivity. }
destruct REQ as (fx2 & R2 & MS2 & B1 & B10 & B19 & B21 & B22 & KS2).
unfold PMSPA.cfg.
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK cr0 Aw M model fx fx2 R 0xd2c80 R2 0x12d21c _ K HH AM MS2 (fun x X => X) (fun a _ => eq_refl)).
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
assert (EM1 : M1 = M).
{ apply functional_extensionality. intros x. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply FR1. pose proof (bv_unsigned_in_range 64 x) as X.
change (bv_modulus 64) with (2 ^ 64) in X. exact X. }
subst M1.
destruct (grow_credit (PM.VLong A n 0) A TBOK ltac:(rewrite Es; cbn; lia) ltac:(rewrite Es; cbn; lia) eq_refl LA3 CR) as (CROK & CK & Htg).
assert (STKn : L5CA.astk ar M (S - 80) PMSPA.OPNEW_SCR).
{ apply (L5SAR.astk_sub ar M M S 14336 80 PMSPA.OPNEW_SCR STK (fun x X => X)); unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR; [lia| lia| lia|].
replace (S - 80) with (S + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
unfold PMB.opnew_spec, PMSPA.opnew_spec in OPN. cbn [pa_opnew PMB.AD ADDR_B] in OPN.
apply (OPN fx2 R2 M model1 K ((p, c) :: LB) FF LK Aw cr0 A (S - 80) 0xd2d20 HH1 AM1 K0).
{ rewrite L5K.rl10. exact B10. }
{ lia. }
{ exact CROK. }
{ rewrite L5K.rl1. exact B1. }
{ split; [lia| reflexivity]. }
{ rewrite L5K.rl2. rewrite (KS2 2%nat) by inl. exact A2. }
{ rewrite L5K.rl4. rewrite (KS2 4%nat) by inl. rewrite (KP 4%nat) by (cbn; auto). exact Rtp0. }
{ exact STKn. }
intros fx3 R3 M3 model3 Aw3 B R3_10 RP3 FB HP3 MRT3 IAW3 AM3 HH3. rewrite L5K.rl10 in R3_10.
destruct FB as ((FB0 & FB1 & FB2 & FB3 & FB4 & FB5) & FBa & FBf & FBd & FBs). cbn [fst snd] in *.
assert (C3 : forall x, In x [2; 8; 9; 18; 19; 21; 22; 23]%nat -> getr R3 (reg x) = getr R2 (reg x)).
{ intros x Hx. apply (L5SAR.cs_of_preserved R2 R3 x RP3). revert x Hx. apply sub_in. vm_compute. reflexivity. }
assert (ABp : B + A <= p \/ p + c <= B) by (exact (FBa (p, c) ltac:(left; reflexivity))).
apply (gan_long fx3 R3 M3 model3 LK Aw3 c n0 p m B A).
- split; [exact AM3|]. split; [exact (L5LZ.model_rt_trans model0 model1 model3 (L5LZ.model_rt_trans model0 model model1 MRT MRT1) MRT3)|].
split; [exact ILK| intros x Hx; exact (IAW3 x (IAW x Hx))].
- exact En.
- exact Hm.
- exact Hn0.
- lia.
- lia.
- exact LA4.
- exact Hc.
- rewrite (C3 2%nat) by inl. rewrite (KS2 2%nat) by inl. exact A2.
- rewrite (C3 8%nat) by inl. rewrite (KS2 8%nat) by inl. exact A8.
- rewrite (C3 9%nat) by inl. rewrite (KS2 9%nat) by inl. exact A9.
- exact R3_10.
- rewrite (C3 18%nat) by inl. rewrite (KS2 18%nat) by inl. exact A18.
- rewrite (C3 19%nat) by inl. exact B19.
- rewrite (C3 21%nat) by inl. exact B21.
- rewrite (C3 22%nat) by inl. exact B22.
- rewrite (C3 23%nat) by inl. rewrite (KS2 23%nat) by inl. exact A23.
- intros x Hx. rewrite (L5SAR.cs_of_preserved R2 R3 x RP3) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
rewrite (KS2 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
- exact (saves_new M M3 _ HP3 ltac:(lia) ltac:(lia) ltac:(lia) SV).
- exact (mem_ok_new M M3 [(p, c)] LK cr0 Aw model1 HH1 MO HP3).
- apply (aacc_of_block M3 B A B A FBs); [apply PMFA.mod16_8; exact FB2| lia| lia| lia].
- exact (PMFA.accA_agree M M3 p c (PMBRZK.agsh_ahpres L ar _ FF (S - 80) PMSPA.OPNEW_SCR [] M M3 p c HP3 (or_introl eq_refl) PMKB.wapp_nil ltac:(lia) ltac:(lia)) ACP).
- exact ABp.
- exact HH3.
- pose proof TBOK as (Tg0 & Tg1 & _). rewrite Es in Tg1. cbn [PM.vs_cap] in Tg1.
split; [lia|]. split; [cbn [PM.vs_cap]; rewrite Z.pow_add_r by lia; change (2 ^ 1) with 2; lia|]. split; [exact LAW| lia].
- rewrite Es. cbn. lia.
- rewrite Es in CK |- *. exact CK.
Qed.
End Call.
End WithHeap.
End PMBRZ2.
