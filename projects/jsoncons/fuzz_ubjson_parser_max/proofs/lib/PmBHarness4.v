(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceAB0 LibIface
AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA L5DefsAB0
L5CoreAB0 L5StepARB0 L5CoreBRB0 L5ADetailHRB0 L5AFrameKRB0 HeapIfaceAJx PmLayout PmLayoutA PmModel PmModelFactsA PmStatics PmStaticsA PmSpecsA PmSpecsAb PmStepAB0 PmBReset1 PmBHarnessStmts PmBHarnessKit PmBHarnessKit2 PmBHarnessSK PmBHarnessP2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBHarness4 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5DefsAB0.L5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBHarnessStmts.PMHAS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAb.PMB."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStatics.PMST."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStaticsA.PMSTA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5AFrameKRB0.L5AFKR."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0A5"; "0A6"; "1app"; "1bool"; "1list"; "1nil"; "1option"; "1prod"; "1true"; "2and"; "2eq"; "3Z"; "0F"; "0FF"; "0HI"]; ["0K"; "0L"; "0LB"; "0LK"; "0LK5"; "0LK6"; "4Model"; "4event"; "5bvmap"; "0M"; "0M5"; "0M6"; "0R"; "0R5"; "0R6"; "0RDC"]; ["6credit"; "7fframe"; "7shadow_zero"; "9u32_at"; "9u64_at"; "8SCFG"; ":cfg"; ";rinvH"; ";tfrk"; "<AADDR_B"; "<ADDR_B"; "=CHUNK"; "=cost1"; "=credit_add"; "=iss_at"; "=parser_at"]; ["=parser_own"; "=strm"; "=vs_own"; "=vstr"; "=vstr_at"; ">HV"; ">accA"; ">annA"; ">cr0"; ">credit_keep"; ">credit_le"; ">parser_init"; ">scA"; "?reader_ctor_spec"; "@st"; "@st_loc"]; ["Als_okA"; "BFPState"; "Bgetr"; "CTSet"; "Dsrealizes"; "Ebinv"; "Floaded_segments"; "0SCFG_P"; "Gadd"; "Gle"; "Glt"; "Gof_nat"; "Gpow"; "Gsub"; "0V2"; "0W"]; ["0ar"; "0b"; "0cls"; "0cr5"; "0cr6"; "0fx5"; "0fx6"; "0g"; "0model"; "0model5"; "0model6"; "0n"; "0qc"; "0s"; "0s'"; "0sm"]; ["HZ_to_bv"; "Hbv"]]).
Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module PMHA4.
Import L5A. Import L5CA. Import L5SAR. Import PMHAS.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac hsc := first [ asm | apply UR | apply U_to | rk | gmem | (arith_goal; first [asm | alia]) | assumption ].
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section Stage.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMB.ly_as0 L C LY.
Variables (M : word -> option byte) (model : Model) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z)) (R : bvmap 5 word)
(V2 cls F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (cr : credit) (W : list L5.range).
Hypothesis G : L5AFKR.gctx L ar HI LB FF LK A (V2 + cls) 36864 (V2 - 128) (V2 - 128) (V2 + cls) (tocell (V2 + cls)) (tfrk (V2 + cls) R) F fl 4 LK2 M2 model2 cr.
Hypothesis CLS : cls = 0 \/ cls = 16.
Hypothesis V2R : 140735332487360 <= V2 <= 140737488355328.
Hypothesis V2S : V2 + cls <= 140737488355328.
Hypothesis V2A : V2 mod 32 = 0.
Hypothesis GP : getr R (reg 3) = Z_to_bv 64 (pa_gp PMB.AD).
Hypothesis TP : getr R (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis FFRS : forall f, In f FF -> V2 + cls + 32 <= ff_rs f.
Hypothesis ROOM : forall LKc, incl LKc LK -> NoDup (map ff_addr ((F, 4, V2 - 128 + 32) :: FF ++ LKc)) -> PMSPA.ffroomA 11 ((F, 4, V2 - 128 + 32) :: FF) LKc.
Hypothesis STKSH : shadow_zero M (V2 + cls - 36864) 4608.
Hypothesis WAPP : PMKB.wapp W.
Hypothesis FAL : F mod 1024 = 0.
Local Notation Bv := (L5AFKR.binv L ar HI M model LB FF LK A (V2 + cls) 36864 (V2 - 128) (tfrk (V2 + cls) R) F 4).
Local Notation FF' := ((F, 4, V2 - 128 + 32) :: FF).
Lemma stage4 : ltac2:(TCodec.tc2 tcn__PmBHarness4 "[:&QMvR7vAvR@v?%544321'R1&Hy5'S1yR0%211%5241'7y8%611%311p061'F&R3'5&Q1%211&Q0'8'<%2211%711'QC'QA'QN&R5vIvRHvBv>vCv0&R8vR>vRB%3221+QTP0&R=+T0%2261&Q8vL%2271v=+4vR?&3&QBr4%211r5%411%63Q031r;r:r8r7r6%Q1FQNQMQLQ0ONMLKGFC@?>=654321&Q7r=%25D1LKB(6'G%211%<11';'4&QO%11E(9%53421&R0&R6&Q:&Q9r?%55432K1&R2rA&S0&R;u1%211%42RB1%7261+do^H%72RC1%F3RC31rBu:%:11%<2RJ1%?241+^@%QO2QD1%@2RL1%O3RL41rCu;%C11%E2S31%H241+S0%R82QM1%I2S51%Q83S541rDu<%L11%N2S<1%Q1241+m0%RA2R61%Q22S>1%QA3S>41rEu=%Q511%Q72SE1%Q:241+S8%RE2RI1%Q;2SG1%QJ3SG41rFuE%Q>11%Q@2SN1%QC241%R03SM1IrGuF%QD11%QF2T41%QI241%QH2T4R<%R73T421rHuG%QK11%QM2T;1%R0241%R=3T:1Q?rIuJ%R111%R32TA1%R6241+]@%SF2S;1%R72TC1%RF3TC41':&R9zr@%3221&R:&R<+2+R0%3221%5271%;271&QD&QFrJ+Q0%T92SN1%55S1431QO&Q>rK%27S4S371R5R2R;&QJ&QL&Q=&Q<&QE%12UGUF&Q;%4221%523>%7221%92UL1%;21Q?&Q4rM+QUik0%34SD2Q71rN+QUjUH%64SG2R?1rO+m8%U32TH1+`PPP0%;4SL421&Q3rQ0+mH%U92TN1+QP0%54T2421&Q2rQ1+1%332QI1rQ2+QA%632SC1rQ3%831S3U8rQ4+Q2%;32S?1&Q@&QKr2r1%3221%511rQ7%U@11rQ8%UB11%UD3V>31%UE3V?61r3%V<FW9W8W7V;V:V9V8V7V6V2V1UNUKUJUIUH2U=U<UCUE1r9%U<5UN1V6V5ULrQ6%U15U0TOTN13%TL2UETF+do`H%TL2W81%U;3W831r<%U121S?%U>3W;1T7%U32UES;+o0%VC2V81%U42W@1%UC3W@41r>%U921S:%UF3WC1TH%U;2U=S6+_oooooooooooH%U;2WG1%UJ3WG31rQ@%RI5UERHUBRE1rQ?%RE7UGUFRJS4TH31&Q?&QG%Q:2EV>%38UKUJRN2UEU5TL1&QIrQE&QH%342ULR@1%R?4V0U7SCR=%QN3TOSDQL+j@%W<2W11%RC4V4TI1SG%R84V5TAKSC%R33T<LS?%R43T6U8QJ%R53T15R3'R4&Q5%11XI&Q6rL+jho@%352S<1SAT8rQO%84VA621p0:1p0<1p0>1p0@1p0B1p0F1p0H1p0J1p0O1p0Q41p0Q71p0Q:1p0Q?1p0QC1p0QI1p0QM1p0R21p0R51p0R81pU4XK1pUJXL1p6XK1pU:Y01pQ<Y21pUFY71pQHY91pQNY?1pU>YF1+e^m@rQ5%Q45RIRK2RA1%Q84WAQ61S5p051p0S51p0S91p0S<1p0S@1p0SE1p0SL1p0T21p0T61p0T;1p0TH1p0TL1p0U31p0U@1p0UJ1p0V11p0V91p0V@1p0VJ1p0W41p0W>1p0WH1p0X41p0X;1p0XB1p0XG1p0XK1pU@YN1pUHZ41pV0Z11pUNZ31pULZ41p4Z61pU8Z;1pQ:Z=1pQ2ZA1pUDZC1pQFZE1pQLZK1pU<[21pR0[41").
Proof. intros RDC fx5 R5 M5 model5 K LK5 cr5 A5 s s' sm n g.
intros BI RI K0 GL LS R1a R10 R11 R12 R13 R21 R22 R23 R26 Hn VS0 IS0 CRD V432 O928 O936 O952 SZV SZP SZO SZI KONT.
pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
change (ff_bytes 4) with 1024 in *. change (1024 / 8) with 128 in *.
pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W _ M5 model5 LK5 cr5 A5 BI)
as ((VW5 & VIC5 & VSB5 & VUAR5 & VMS5) & VOWN5 & (VFD5 & VFW5 & VFSW5 & VFLC5 & VFLW5) & (FLCc5 & FLV5 & FV5 & SPV5 & FSV5)).
change (ff_bytes 4) with 1024 in *. change (1024 / 8) with 128 in *.
pose proof RI as (X2 & X8 & X9 & X18 & X19 & X20 & X24 & X25 & X3 & X4 & X27).
assert (FDEF5 : L5.defined M5 F 1024) by (apply (proj1 (L5A.defined_vis (ahid A5 model5) M5 F 1024 FV5)); exact VFD5).
assert (FM8 : F mod 8 = 0) by (pose proof (proj1 F8) as E8; clear - E8; lia).
assert (FHF : PMHAK2.hf F) by (unfold PMHAK2.hf, BIGSHADOW_LO, BIGSHADOW_HI; clear - FR FBIG FM8; lia).
pose proof LS as (LSB & LSL & LSS & LSE). rewrite GL in LSL.
unfold PMB.reader_ctor_spec, PMSPA.reader_ctor_spec in RDC. unfold PMSPA.o_p, PMSPA.o_is in RDC. cbn [pa_reader_ctor pa_off_p pa_off_is pa_vp_opts PMB.AD ADDR_A] in RDC.
apply (RDC fx5 R5 M5 model5 K ((PM.vs_own s' ++ PM.vs_own s) ++ LB) FF' LK5 A5 cr5 (V2 - 128) 0xa7dd8 F (F + 928) (V2 - 104) s' sm B1 B2 K0).
{ eapply PMHASK.callee_entry; first [exact BI | exact RI | exact R1a | eassumption | (split; [lia| reflexivity]) | lia]. }
{ eapply PMHASK.callee_room; first [exact BI | eassumption | lia]. }
{ eapply PMHASK.callee_rs; eassumption. }
{ exact (PMHASK.callee_frame FF V2 F FAL). }
{ rewrite L5K.rl10. exact R10. }
{ rewrite L5K.rl11. exact R11. }
{ rewrite L5K.rl12. exact R12. }
{ rewrite L5K.rl13. exact R13. }
{ lia. }
{ apply (L5.defined_sub M5 F 1024 (F + 464) 384 FDEF5); lia. }
{ apply (PMBRS1.acc_of_shadow_zero M5 (F + 464) 49 (F + 464) 384 SZP); [clear - FM8; lia| lia| lia]. }
{ apply (PMBRS1.acc_of_shadow_zero M5 (F + 928) 4 (F + 928) 32 SZO); [clear - FM8; lia| lia| lia]. }
{ exact O928. }
{ replace (F + 928 + 8) with (F + 936) by lia. exact O936. }
{ replace (F + 928 + 24) with (F + 952) by lia. exact O952. }
{ exact IS0. }
{ exact LSB. }
{ exact LSL. }
{ exact CRD. }
intros fx' R' M' model' LK' Aw' qc b cr' RP' PAT HP' CK' MRT' INCLK' INCA' AM' HH'.
change (PMSPA.pm_scr 6) with 24576 in HP'.
rewrite app_assoc in HH'.
assert (WFI : PMHAK2.wfi F [(F + 464, 384)]) by (apply PMHAK2.wfi_cons; [cbn [fst snd]; left; lia| apply PMHAK2.wfi_nil]).
assert (LS' : PMSTA.ls_okA RSEGS PMB.AD PMB.AAD g M').
{ apply (PMHAK.ls_ahpres L C LY g ar _ FF' (V2 - 128) _ [(F + 464, 384)] M5 M' HP'); [| exact LS].
apply PMHAK.far_cons; [cbn [fst snd]; clear - FR; lia| apply PMHAK.far_nil]. }
assert (BI' : Bv W (PM.parser_own (PMSPA.parser_init qc b) ++ PM.vs_own s' ++ PM.vs_own s) M' model' LK' cr' Aw').
{ apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W W (PM.vs_own s' ++ PM.vs_own s) (PM.vs_own s' ++ PM.vs_own s) _ M5 model5 LK5 cr5 A5 M' model' LK' cr' Aw' 24576 [(F + 464, 384)] BI HP' HH' AM' MRT' INCA' INCLK').
- lia.
- clear - CLS; lia.
- intros rr a [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. unfold tocell. split; [clear - Ha FCEIL SLO CLS; lia|]. unfold HeapIfaceA.SB. change (ff_bytes 4) with 1024. clear - Ha FR F8 FBIG. lia.
- intros a Hc _ rr [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. apply (NCF a); [left; clear - Ha; lia| exact Hc].
- intros a X. exact X. }
pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W _ M' model' LK' cr' Aw' BI')
as ((VW' & VIC' & VSB' & VUAR' & VMS') & VOWN' & (VFD' & VFW' & VFSW' & VFLC' & VFLW') & (FLCc' & FLV' & FV' & SPV' & FSV')).
change (ff_bytes 4) with 1024 in *. change (1024 / 8) with 128 in *.
set (H' := ahid Aw' model') in *. set (MV' := mrestrict H' M') in *.
assert (RI' : rinvH R R' V2 cls F) by exact (rinvH_pres R R5 R' V2 cls F RI RP').
pose proof RI' as (Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y24 & Y25 & Y3 & Y4 & Y27).
assert (Y21 : getr R' (reg 21) = Z_to_bv 64 (F + 96)) by (rewrite (cs_of_preserved R5 R' 21 RP') by inl; exact R21).
assert (Y22 : getr R' (reg 22) = Z_to_bv 64 n) by (rewrite (cs_of_preserved R5 R' 22 RP') by inl; exact R22).
assert (Y23 : getr R' (reg 23) = Z_to_bv 64 (F + 464)) by (rewrite (cs_of_preserved R5 R' 23 RP') by inl; exact R23).
assert (Y26 : getr R' (reg 26) = Z_to_bv 64 (F + 432)) by (rewrite (cs_of_preserved R5 R' 26 RP') by inl; exact R26).
assert (FIN5 : In (F, 4, V2 - 128 + 32) (FF' ++ LK5)) by (apply in_or_app; left; left; reflexivity).
assert (VS' : PM.vstr_at RSEGS PMSPA.accA M' (F + 32) s).
{ eapply PMHAK2.vstr_keep_callee; first [ exact LY | exact HIok | exact B1 | exact HP' | exact VS0 | exact FHF | exact FIN5 | exact WFI | exact (or_introl eq_refl)
| (split; reflexivity) | apply incl_refl | (intros x Hx; apply in_or_app; left; apply in_or_app; right; exact Hx)
| (apply PMHAK2.wapart_cons; [cbn [fst snd]; lia| apply PMHAK2.wapart_nil]) | lia ]. }
assert (IS' : PM.iss_at RSEGS PMB.AD PMSPA.accA M' (F + 96) s' sm).
{ eapply PMHAK2.iss_keep_callee; first [ exact LY | exact HIok | exact B1 | exact HP' | exact IS0 | exact FHF | exact FIN5 | exact WFI | exact (or_introl eq_refl)
| (split; reflexivity) | apply incl_refl | (intros x Hx; apply in_or_app; left; apply in_or_app; left; exact Hx)
| (apply PMHAK2.wapart_cons; [cbn [fst snd]; lia| apply PMHAK2.wapart_nil]) | lia ]. }
assert (AGV : PMFA.agA M5 M' (F + 432) 8).
{ apply (PMHAK2.ff_callee L ar _ FF' (V2 - 128) 24576 [(F + 464, 384)] M5 M' (F, 4, V2 - 128 + 32) F (F + 432) 8 HP' (or_introl eq_refl));
cbn [ff_addr ff_class fst snd]; change (ff_bytes 4) with 1024; [lia| lia| exact FHF| lia| lia| exact WFI|].
apply PMHAK2.wapart_cons; [cbn [fst snd]; lia| apply PMHAK2.wapart_nil]. }
assert (V432' : L5.u64_at RSEGS M' (F + 432) 1238880) by (apply (PMHAK2.u64_agA M5 M' (F + 432) 8 (F + 432) _ AGV); [lia| lia| lia| lia| exact V432]).
assert (SZV' : shadow_zero M' (F + 432) 1) by (apply (PMHAK2.shz_agA M5 M' (F + 432) 8 (F + 432) 1 AGV); [lia| lia| clear - FM8; lia| lia| exact SZV]).
assert (AGE : PMFA.agA M5 M' (F + 848) 8).
{ apply (PMHAK2.ff_callee L ar _ FF' (V2 - 128) 24576 [(F + 464, 384)] M5 M' (F, 4, V2 - 128 + 32) F (F + 848) 8 HP' (or_introl eq_refl));
cbn [ff_addr ff_class fst snd]; change (ff_bytes 4) with 1024; [lia| lia| exact FHF| lia| lia| exact WFI|].
apply PMHAK2.wapart_cons; [cbn [fst snd]; lia| apply PMHAK2.wapart_nil]. }
assert (SZE' : shadow_zero M' (F + 848) 1).
{ apply (PMHAK2.shz_agA M5 M' (F + 848) 8 (F + 848) 1 AGE); [lia| lia| clear - FM8; lia| lia|].
apply (PMKB.shadow_zero_sub M5 (F + 464) 49); [clear - FM8; lia| clear - FM8; lia| lia| lia| lia| exact SZP]. }
assert (ZE' : L5KA.zeros_at MV' (F / 8 + 2147450986) 1).
{ apply (proj2 (L5A.zeros_at_vis H' M' (F / 8 + 2147450986) 1 (PMHAK.avis_sub H' (F / 8 + HeapIfaceA.SB) 128 (F / 8 + 2147450986) 1 FSV' ltac:(unfold HeapIfaceA.SB; lia) ltac:(unfold HeapIfaceA.SB; lia)))).
replace (F / 8 + 2147450986) with (HeapIfaceA.S (F + 848)). apply PMHAK2.zeros_of_shz. exact SZE'.
unfold HeapIfaceA.S, HeapIfaceA.SB. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - FM8. lia. }
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
assert (SZI' : shadow_zero M' (F + 96) 34)
by (apply (PMHAK2.shz_callee L ar _ FF' (V2 - 128) 24576 [(F + 464, 384)] M5 M' (F, 4, V2 - 128 + 32) F (F + 96) 34 HP' (or_introl eq_refl) (conj eq_refl eq_refl) FHF WFI);
[lia| lia| clear - FM8; lia| lia| exact SZI]).
pose proof (PMBHP2.haE_conc fx' R' MV' (fun j => match j with 2%nat => V2 | 34%nat => n | 40%nat => F | 41%nat => fl | 58%nat => U R' 1 | _ => 0 end)) as P.
cbn beta iota in P.
assert (Q1 : 4096 <= F <= 140737488354304) by (clear - FR; lia).
assert (Q2 : 4096 <= fl <= 140737488355327) by (clear - FLR; lia).
assert (Q3 : V2 - 128 + 144 <= F \/ F + 1024 <= V2 - 128) by (clear - FCEIL SLO CLS; lia).
assert (Q4 : V2 - 128 + 144 <= fl \/ fl + 1 <= V2 - 128) by (clear - FLR SLO CLS; lia).
assert (Q5 : L5.writable RSEGS MV' (V2 - 128) 128) by (eapply L5.writable_sub; [exact VW'| clear; lia| clear - CLS; lia]).
assert (Q6 : L5.u64_at RSEGS MV' (F + 1016) fl) by (replace (F + 1016) with (F + 1024 - 8) by (clear; lia); exact VFLC').
feed P ltac:(first [ asm | apply UR | apply U_to | (clear - Hn; lia) | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
| exact VFD' | exact VFW' | exact VFSW' | exact VFLW' | exact Q5 | exact Q6 | exact ZE' | (unfold PMBHP2.aligned; exact V2A) ]).
destruct P as (fx6 & R6 & M6v & MG6 & eFR & eFZ & (eMS & eKS & eR1 & eR10 & eR11 & eR22 & eR26 & EQ)).
set (W6 := fun a => F + 848 <= a < F + 848 + 8 \/ F + 992 <= a < F + 992 + 4 \/ F / 8 + 2147450996 <= a < F / 8 + 2147450996 + 4
\/ F / 8 + 2147451004 <= a < F / 8 + 2147451004 + 2).
apply (apiece L ar C HI LYa HIok _ FF' LK' cr' Aw' M' model' fx' fx6 R' 0xa7dd8 R6 0xd63f0 M6v W6 K HH' AM' eMS MG6).
{ intros a Ha Hna. apply eFZ; [exact Ha|..]; intros X; apply Hna; subst W6; cbn beta; clear - X; lia. }
{ intros a Ha Wa. subst W6; cbn beta in Wa. split.
- destruct Wa as [Wa|[Wa|Wa]].
+ apply (fframe_client L ar _ _ 0 0 F 4 (V2 - 128 + 32)). left; reflexivity. change (ff_bytes 4) with 1024. clear - Wa; lia.
+ apply (fframe_client L ar _ _ 0 0 F 4 (V2 - 128 + 32)). left; reflexivity. change (ff_bytes 4) with 1024. clear - Wa; lia.
+ apply (fframe_shadow_client L ar _ _ 0 0 F 4 (V2 - 128 + 32)). left; reflexivity. change (ff_bytes 4) with 1024.
unfold in_shadow_of, HeapIfaceA.S. rewrite (proj1 (proj2 F8)). unfold HeapIfaceA.SB. clear - Wa. lia.
- unfold HeapIfaceA.SB in *. clear - Wa FR. lia. }
intros M6 model6 HH6 AM6 MRT6 HID6 VIS6 MGM6 FR6 VV6. change (mrestrict H' M6 = M6v) in VIS6.
decompose [and] EQ. clear EQ.
assert (BI6 : Bv W (PM.parser_own (PMSPA.parser_init qc b) ++ PM.vs_own s' ++ PM.vs_own s) M6 model6 LK' cr' Aw').
{ apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W _ M' model' LK' cr' Aw' M6 model6 W6 BI' HH6 AM6 MRT6 MGM6 FR6).
intros a Wa. subst W6; cbn beta in Wa. right. change (ff_bytes 4) with 1024. change (1024 / 8) with 128. unfold HeapIfaceA.SB in *. clear - Wa. lia. }
assert (RI6 : rinvH R R6 V2 cls F) by (apply (rinvH_ks R R' R6 V2 cls F PMBHP2.KS_haE RI' eKS); vm_compute; reflexivity).
assert (LS6 : PMSTA.ls_okA RSEGS PMB.AD PMB.AAD g M6).
{ apply (PMHAK.ls_piece _ M' M6 W6 FR6); [| exact LS']. intros a Wa. subst W6; cbn beta in Wa. clear - Wa FR. lia. }
assert (PF6 : PMHAK2.pfoot F (V2 - 128) V2 W6) by (intros a Wa; subst W6; cbn beta in Wa; unfold HeapIfaceA.SB; clear - Wa; lia).
assert (FIN' : In (F, 4, V2 - 128 + 32) (FF' ++ LK')) by (apply in_or_app; left; left; reflexivity).
assert (SLOW : ahl_ceil ar <= V2 - 128) by (clear - SLO CLS; lia).
assert (SHW : BIGSHADOW_HI <= V2 - 128) by (unfold BIGSHADOW_HI; clear - V2R; lia).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
assert (OA32 : PMHAK2.oav W6 (F + 32) 24) by (intros x Hx; subst W6; cbn beta; unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *; split; intros X; clear - Hx X FR FBIG FM8; lia).
assert (OA96 : PMHAK2.oav W6 (F + 96) 272) by (intros x Hx; subst W6; cbn beta; unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *; split; intros X; clear - Hx X FR FBIG FM8; lia).
assert (OA464 : PMHAK2.oav W6 (F + 464) 384) by (intros x Hx; subst W6; cbn beta; unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *; split; intros X; clear - Hx X FR FBIG FM8; lia).
assert (OA432 : PMHAK2.oav W6 (F + 432) 8) by (intros x Hx; subst W6; cbn beta; unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *; split; intros X; clear - Hx X FR FBIG FM8; lia).
assert (Q992 : (F + 992) / 8 + HeapIfaceA.SB = F / 8 + 2147451004) by (unfold HeapIfaceA.SB; clear - FM8; lia).
assert (FBD : 0 <= F / 8 /\ F / 8 + 128 <= 2 ^ 44) by (clear - FR; lia).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
assert (VS6 : PM.vstr_at RSEGS PMSPA.accA M6 (F + 32) s).
{ apply (PMHAK2.vstr_keep_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 W6 M' M6 SLOW SHW FR6 PF6 (F + 32) s);
[intros x Hx; apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; exact Hx| clear - FR; lia| clear - FR; lia| exact OA32| exact VS']. }
assert (IS6 : PM.iss_at RSEGS PMB.AD PMSPA.accA M6 (F + 96) s' sm).
{ apply (PMHAK2.iss_keep_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 W6 M' M6 SLOW SHW FR6 PF6 (F + 96) s' sm);
[intros x Hx; apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; exact Hx| clear - FR; lia| clear - FR; lia| exact OA96| exact IS']. }
assert (PA6 : PM.parser_at RSEGS PMB.AD PMSPA.accA PMSPA.annA M6 (F + 464) (F + 96) (PMSPA.parser_init qc b)).
{ apply (PMHAK2.parser_keep_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 W6 M' M6 SLOW SHW FR6 PF6 (F + 464) (F + 96));
[intros x Hx; apply in_or_app; left; apply in_or_app; left; exact Hx| clear - FR; lia| clear - FR; lia| exact OA464| exact PAT]. }
assert (AGV6 : PMFA.agA M' M6 (F + 432) 8) by (apply (PMHAK.agA_frame M' M6 W6 (F + 432) 8 FR6); [clear - FR; lia| clear - FR; lia| exact OA432]).
assert (AVF : forall d k, 0 <= d -> d + k <= 1024 -> L5A.avis H' (F + d) k) by (intros d k Hd1 Hd2; apply (PMHAK.avis_sub H' F 1024 (F + d) k FV'); lia).
assert (AVS : forall q k, F / 8 + 2147450880 <= q -> q + k <= F / 8 + 2147450880 + 128 -> L5A.avis H' q k)
by (intros q k Hd1 Hd2; apply (PMHAK.avis_sub H' (F / 8 + HeapIfaceA.SB) 128 q k FSV'); unfold HeapIfaceA.SB; lia).
apply (KONT fx6 R6 M6 model6 LK' cr' Aw' qc b BI6 RI6 LS6).
- exact eR1.
- rewrite (eKS 21%nat) by inl. exact Y21.
- exact eR22.
- rewrite (eKS 23%nat) by inl. exact Y23.
- exact eR26.
- exact VS6.
- exact IS6.
- exact PA6.
- exact CK'.
- apply (PMHAK2.u64_agA M' M6 (F + 432) 8 (F + 432) _ AGV6); [lia| lia| lia| lia| exact V432'].
- apply (PMHAK2.shz_agA M' M6 (F + 432) 8 (F + 432) 1 AGV6); [lia| lia| clear - FM8; lia| lia| exact SZV'].
- apply (PMHAK.u64_vis H' M6 M6v (F + 848) _ VV6 (AVF 848 8 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia)). asm.
- apply (PMHAK.u32_vis H' M6 M6v (F + 992) _ VV6 (AVF 992 4 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia)). asm.
- apply (PMHAK.shz_vis H' M6 M6v (F + 992) 2 (F / 8 + 2147451004) VV6 (AVS (F / 8 + 2147451004) 2 ltac:(lia) ltac:(lia)) Q992 ltac:(clear - FBD; lia) ltac:(clear - FBD; lia)).
intros j Hj. assert (J : j = 0 \/ j = 1) by (clear - Hj; lia).
destruct J as [J|J]; subst j; gmem.
- apply (PMHAK2.shz_frame M' M6 W6 (F + 96) 34 FR6); [| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| exact SZI'].
intros j Hj X. subst W6; cbn beta in X. unfold HeapIfaceA.S, HeapIfaceA.SB in X.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
assert (E96 : (F + 96) / 8 = F / 8 + 12) by (clear - FM8; lia).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
rewrite E96 in X. clear - X Hj FBD FR FBIG. lia.
- apply (PMHAK2.shz_frame M' M6 W6 (F + 848) 1 FR6); [| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| exact SZE'].
intros j Hj X. subst W6; cbn beta in X. unfold HeapIfaceA.S, HeapIfaceA.SB in X.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
assert (E848 : (F + 848) / 8 = F / 8 + 106) by (clear - FM8; lia).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
rewrite E848 in X. clear - X Hj FBD FR FBIG. lia.
Qed.
End Stage.
End SCFG_1.
End PMHA4.
