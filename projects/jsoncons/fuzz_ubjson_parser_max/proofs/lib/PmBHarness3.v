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
Ltac2 tcn__PmBHarness3 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5DefsAB0.L5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBHarnessStmts.PMHAS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAb.PMB."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStatics.PMST."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStaticsA.PMSTA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5AFrameKRB0.L5AFKR."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0A4"; "0A5"; "1app"; "1list"; "1nil"; "1option"; "1prod"; "1true"; "2and"; "2eq"; "3Z"; "0F"; "0FF"; "0HI"; "0ISS"]; ["0K"; "0L"; "0LB"; "0LK"; "0LK4"; "0LK5"; "4Model"; "4event"; "5bvmap"; "0M"; "0M4"; "0M5"; "0R"; "0R4"; "0R5"; "6credit"]; ["7fframe"; "7shadow_zero"; "9u32_at"; "9u64_at"; "8SCFG"; ":cfg"; ";rinvH"; ";tfrk"; "<AADDR_B"; "<ADDR_B"; "=VLong"; "=cost1"; "=iss_at"; "=sm_g"; "=sm_st"; "=strm"]; ["=vs_data"; "=vs_own"; "=vs_size"; "=vstr"; "=vstr_at"; ">HV"; ">accA"; ">cr0"; ">credit_keep"; ">credit_le"; ">scA"; "?iss_ctor_spec"; "@ST"; "@st"; "@st_err"; "@st_sys"]; ["Als_okA"; "BFPState"; "Bgetr"; "CTSet"; "Dsrealizes"; "Ebinv"; "Floaded_segments"; "0SCFG_P"; "Gadd"; "Gle"; "Glt"; "Gof_nat"; "Gpow"; "Gsub"; "0V2"; "0W"]; ["0ar"; "0c"; "0cls"; "0cr4"; "0cr5"; "0data"; "0fx4"; "0fx5"; "0g"; "0model"; "0model4"; "0model5"; "0n"; "0n0"; "0p"; "0s"]; ["0s'"; "0sm"; "HZ_to_bv"; "Hbv"]]).
Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module PMHA3.
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
Hypothesis WLOC : forall a, L5.outside W a -> L5.outside (PMSPA.loc_W PMB.AD) a.
Local Notation Bv := (L5AFKR.binv L ar HI M model LB FF LK A (V2 + cls) 36864 (V2 - 128) (tfrk (V2 + cls) R) F 4).
Local Notation FF' := ((F, 4, V2 - 128 + 32) :: FF).
Lemma stage3 : ltac2:(TCodec.tc2 tcn__PmBHarness3 "[J&QKvR7vAvR@v>%544321'R1&Hy5'S3yR0%211%5241'6y8%611%311p061'F&R3'4&Q0%211&O'7';%2211%711'QC'QM&R5vIvRIvBv=vCv0&R8vR>vRB%3221+QTP0&R=+T0%2261&Q7vL%2271v<+4vR?&QAr4%211r:r9r7r6r5%MFQIQHQGLKJIHGCB?<;:9654321&Q6r<%25@1HG>(5'G%211%<11&R0&R6&Q9&Q8r=%55432D1':&R2r?&S2&R;u1%211%42R81%7261+doU<%72R91%;3R931r@u:%:11%<2R@1%?241+S0%QF2Q;1%@2RB1%D3RB41rAu;%C11%E2RI1%H241+Q0%QO2QD1%I2RK1%M3RK41rBu<%L11%N2S21%Q1241+8%Q12S31%Q53S331rCuE%Q411%Q62S:1%Q9241%Q;3S91HrDuF%Q:11%Q<2S@1%Q?241r;%Q?2SA1%QC3SA31rEuG%QB11%QD2SH1%QG241%QF2SHQK%QJ3SH21&QD&QF%25R219Q2QK&QB%11QCr>%R13SA21(Q:r3r2r1%43321%R73SDK1&R9+G%2217p041pUNSL1pULSM1pU4SN1'9z%921R5&R:&R<+2+J%3221%52R;1%9271%A29QK+R0%8271%:2QN1%>241&QI&QJ&Q;&QE%12U9U8%T72R5R9%4221%62U<1rF%9221&Q1rK+Q2%332RI1'Q?&3%T41Q:rO%T611%43U031%TMFUIUHUGTLTKTJTITHTGTCTBT?T<T;T:T91T3T2T1T7Q?%T05T>T5TFTET<(QL(8&QOrN%211&QN%113%73631%T25T1T0SO1T>%SL2R<SF+do^H%SL2UN1%T03UN31%T02T=SB+^@%U72TL1%T12V31%T53V341%T52T8S>%T73V51SD%T72R8S7+m0%U>2U31%T82V:1%T<3V:41u=%T:11%T<2V@1%T?2T>1+S8%UA2UE1%T@2VB1%TD3VB41%TD2T9S<%TF3VD1T3%TF2T2S8rQ6%TF2VH1%TJ3VH31%TJ2SMS4%TL3VJ1HuJ%TJ11%TL2W01%TO2SJ1+]@%V62UK1%U02W21%U43W241rQ;%S;5U;S:T0T;1&Q<%17U=U<S<SLTFU6S8%U93VIS:4&Q=%11TO&Q@+R@%VB2TL1%321TJ%U@3W051&Q>%11TM%UC3W31S3&QHrQBrQ>%VK21TM%RH2RF1%RJ2X01&QG%746T721&Q3rI+QUik0%34V42M1rJ+QUjUH%64V72QH1+m8%W82VM1+`PPP0%:4V;RM21rL+m@%W=2W21+QUjW0%?4V@421&Q2rM+mH%WC2W81+QP0%54VF421+mL%WG2W<1%84VIRM1T4+1%S>3S7QD1rQ0+QA%SA32RF1rQ1%SC31RAWCrQ2%SE31V;SC'R4&Q4%11Y8&Q5rQ5rQ4+e^m@rQ3%554321:rQO%:4W=821p0<1p0?1p0B1p0F1p0I1p0M1p0Q41p0Q:1p0Q?1p0QC1p0QH1p0R11p0R51p0R=1p0R?1p0RB1p0RE1p0RN1p0S11p0S61p0S91p0SB1p0SH1p0SK1p0T11p0T61p0T@1p0TB1pV4TI1pV2YC1p6YE1pU:YJ1pQ<YL1pUHZ11pQHZ31pQNZ91pU@Z@1+eQTD%Q>5U0TH1R2R8%QB4XEQ@1U7p041p0U71p0U<1p0UG1p0UM1p0V81p0VF1p0VK1p0VO1p0W71p0W@1p0WG1p0X01p0X:1p0XD1p0Y11p0Y81p0Y=1p0YA1pUBZ@1pUJZE1pU<ZF1pV0ZD1p4ZF1pU8ZK1pQ:ZM1pQ2[11pUF[31pQF[51pQL[;1pU>[B1pQ0[D1").
Proof. intros ISS fx4 R4 M4 model4 K LK4 cr4 A4 s data n g.
intros BI RI K0 LS R1a R10 R11 R12 R21 R22 R23 VS0 SIZE0 LONG0 Hn Hd CRD SZI KONT.
pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
change (ff_bytes 4) with 1024 in *. change (1024 / 8) with 128 in *.
pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W (PM.vs_own s) M4 model4 LK4 cr4 A4 BI)
as ((VW4 & VIC4 & VSB4 & VUAR4 & VMS4) & VOWN4 & (VFD4 & VFW4 & VFSW4 & VFLC4 & VFLW4) & (FLCc4 & FLV4 & FV4 & SPV4 & FSV4)).
change (ff_bytes 4) with 1024 in *. change (1024 / 8) with 128 in *.
pose proof RI as (X2 & X8 & X9 & X18 & X19 & X20 & X24 & X25 & X3 & X4 & X27).
assert (FDEF4 : L5.defined M4 F 1024) by (apply (proj1 (L5A.defined_vis (ahid A4 model4) M4 F 1024 FV4)); exact VFD4).
destruct LS as (LSB & LSL & LSS & LSE).
unfold PMB.iss_ctor_spec, PMSPA.iss_ctor_spec in ISS. cbn [pa_iss_ctor PMB.AD ADDR_A] in ISS.
apply (ISS fx4 R4 M4 model4 K (PM.vs_own s ++ LB) FF' LK4 A4 cr4 (F + 96) (F + 32) (V2 - 128) 0xa7cac s (PMST.st_loc g) B1 B2 K0).
{ eapply PMHASK.callee_entry; first [exact BI | exact RI | exact R1a | eassumption | (split; [lia| reflexivity]) | lia]. }
{ eapply PMHASK.callee_room; first [exact BI | eassumption | lia]. }
{ eapply PMHASK.callee_rs; eassumption. }
{ rewrite L5K.rl10. exact R10. }
{ rewrite L5K.rl11. exact R11. }
{ rewrite L5K.rl12. exact R12. }
{ exists (F, 4, V2 - 128 + 32). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. lia. }
{ exists (F, 4, V2 - 128 + 32). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. lia. }
{ lia. }
{ replace (F + 96) with (F + 12 * 8) by (clear; lia). rewrite Z_mod_plus_full. pose proof (proj1 F8) as E8. clear - E8 FR. lia. }
{ replace (F + 32) with (F + 4 * 8) by (clear; lia). rewrite Z_mod_plus_full. pose proof (proj1 F8) as E8. clear - E8 FR. lia. }
{ apply (L5.defined_sub M4 F 1024 (F + 96) 272 FDEF4); lia. }
{ apply (PMBRS1.acc_of_shadow_zero M4 (F + 96) 34 (F + 96) 272 SZI); [| lia| lia].
replace (F + 96) with (F + 12 * 8) by (clear; lia). rewrite Z_mod_plus_full. pose proof (proj1 F8) as E8. clear - E8 FR. lia. }
{ exact VS0. }
{ apply incl_appl. apply incl_refl. }
{ lia. }
{ exact LONG0. }
{ exact LSB. }
{ exact LSL. }
{ rewrite SIZE0. exact CRD. }
intros fx' R' M' model' LK' Aw' s' sm cr' RP' ISA SZ' SMG SMST LOC' HP' CK' MRT' INCLK' INCA' AM' HH'.
change (PMSPA.pm_scr 4) with 20480 in HP'.
rewrite app_assoc in HH'.
set (Wc := (F + 96, 272) :: (if PMST.st_loc g then [] else PMSPA.loc_W PMB.AD)) in *.
assert (WcL : forall r, In r Wc -> r = (F + 96, 272) \/ In r (PMSPA.loc_W PMB.AD)).
{ intros r Hr. subst Wc. destruct Hr as [<-|Hr]; [left; reflexivity| right; destruct (PMST.st_loc g); [destruct Hr| exact Hr]]. }
assert (LOCW : forall r, In r (PMSPA.loc_W PMB.AD) -> 0x66f2f2 <= fst r /\ fst r + snd r <= 0x6701b0).
{ intros r Hr. cbn in Hr. destruct Hr as [<-|[<-|[]]]; cbn; lia. }
assert (LS' : PMSTA.ls_okA RSEGS PMB.AD PMB.AAD (PMST.ST true (PMST.st_sys g) (PMST.st_err g)) M').
{ apply (PMHAK.ls_ahpres_loc L C LY g ar (PM.vs_own s ++ LB) FF' (V2 - 128) 20480 Wc M4 M' HP'); [| split; [exact LSB| split; [exact LSL| split; [exact LSS| exact LSE]]]| exact LOC'].
intros a Ha r Hr Hin. unfold L5.in_rng in Hin. destruct (WcL r Hr) as [->|X].
- cbn [fst snd] in Hin. unfold PMHAK.bcell, PMHAK.scell, PMHAK.ecell in Ha. clear - Ha Hin FR. lia.
- cbn in X. unfold PMHAK.bcell, PMHAK.scell, PMHAK.ecell in Ha. destruct X as [<-|[<-|[]]]; cbn [fst snd] in Hin; clear - Ha Hin; lia. }
assert (BI' : Bv W (PM.vs_own s' ++ PM.vs_own s) M' model' LK' cr' Aw').
{ apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W W (PM.vs_own s) (PM.vs_own s) (PM.vs_own s' ++ PM.vs_own s) M4 model4 LK4 cr4 A4 M' model' LK' cr' Aw' 20480 Wc BI HP' HH' AM' MRT' INCA' INCLK').
- lia.
- clear - CLS; lia.
- intros rr a Hr Ha. unfold L5.in_rng in Ha. destruct (WcL rr Hr) as [->|X].
+ cbn [fst snd] in Ha. unfold tocell. split; [clear - Ha FCEIL SLO CLS; lia|]. unfold HeapIfaceA.SB. change (ff_bytes 4) with 1024. clear - Ha FR F8 FBIG. lia.
+ destruct (LOCW rr X) as (Y1 & Y2). unfold tocell. split; [clear - Ha Y1 Y2 SLO SPT; lia|]. unfold HeapIfaceA.SB. clear - Ha Y1 Y2 FR. lia.
- intros a Hc Ho rr Hr Ha. destruct (WcL rr Hr) as [->|X].
+ unfold L5.in_rng in Ha; cbn [fst snd] in Ha. apply (NCF a); [left; clear - Ha; lia| exact Hc].
+ exact (WLOC a Ho rr X Ha).
- intros a X. exact X. }
pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W (PM.vs_own s' ++ PM.vs_own s) M' model' LK' cr' Aw' BI')
as ((VW' & VIC' & VSB' & VUAR' & VMS') & VOWN' & (VFD' & VFW' & VFSW' & VFLC' & VFLW') & (FLCc' & FLV' & FV' & SPV' & FSV')).
change (ff_bytes 4) with 1024 in *. change (1024 / 8) with 128 in *.
set (H' := ahid Aw' model') in *. set (MV' := mrestrict H' M') in *.
assert (RI' : rinvH R R' V2 cls F) by exact (rinvH_pres R R4 R' V2 cls F RI RP').
pose proof RI' as (Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y24 & Y25 & Y3 & Y4 & Y27).
assert (Y21 : getr R' (reg 21) = Z_to_bv 64 (F + 96)) by (rewrite (cs_of_preserved R4 R' 21 RP') by inl; exact R21).
assert (Y22 : getr R' (reg 22) = Z_to_bv 64 n) by (rewrite (cs_of_preserved R4 R' 22 RP') by inl; exact R22).
assert (Y23 : getr R' (reg 23) = Z_to_bv 64 data) by (rewrite (cs_of_preserved R4 R' 23 RP') by inl; exact R23).
assert (VS' : PM.vstr_at RSEGS PMSPA.accA M' (F + 32) s).
{ apply (PMFA.vstr_at_agreeA RSEGS M4 M' (F + 32) s); [clear - FR; lia| clear - FR; lia| | |exact VS0].
- apply (PMHAK.agA_ahpres_ff L ar _ FF' (V2 - 128) 20480 Wc M4 M' (F, 4, V2 - 128 + 32) (F + 32) 24 HP' (or_introl eq_refl));
cbn [ff_addr ff_class fst snd]; change (ff_bytes 4) with 1024; [lia| lia| clear - FR; lia| clear - FR; lia|].
intros x Hx. split; intros rr Hr Hin; unfold L5.in_rng in Hin; destruct (WcL rr Hr) as [->|X]; cbn [fst snd] in Hin.
+ clear - Hx Hin; lia.
+ destruct (LOCW rr X) as (Z1 & Z2). clear - Hx Hin Z1 Z2 FR; lia.
+ pose proof (PMKB.S_in_shadow x ltac:(clear - Hx FR; lia)) as SX. unfold BIGSHADOW_LO, BIGSHADOW_HI in *. clear - SX Hin FBIG; lia.
+ pose proof (PMKB.S_in_shadow x ltac:(clear - Hx FR; lia)) as SX. destruct (LOCW rr X) as (Z1 & Z2). unfold BIGSHADOW_LO, BIGSHADOW_HI in *. clear - SX Hin Z1 Z2; lia.
- intros c0 n0 p0 E0. subst s. cbn [PM.vs_own app] in B1 |- *.
destruct (PMHAK.blk_facts L ar C SCFG HI HIok _ _ _ _ _ _ _ p0 c0 B1 (or_introl eq_refl)) as (P0 & P3 & P4 & P5 & PSH & P47 & PIMG & PFA).
pose proof (PFA (F, 4, V2 - 128 + 32) (in_or_app FF' LK4 _ (or_introl (or_introl eq_refl)))) as PF. cbn [ff_addr ff_class fst snd] in PF. change (ff_bytes 4) with 1024 in PF.
rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in PIMG.
apply (PMHAK.agA_ahpres_blk L ar _ FF' (V2 - 128) 20480 Wc M4 M' p0 c0 HP' (or_introl eq_refl)); [lia| lia|].
intros x Hx. split; intros rr Hr Hin; unfold L5.in_rng in Hin; destruct (WcL rr Hr) as [->|X]; cbn [fst snd] in Hin.
+ clear - Hx Hin PF; lia.
+ destruct (LOCW rr X) as (Z1 & Z2). clear - Hx Hin Z1 Z2 PIMG; lia.
+ pose proof (PMKB.S_in_shadow x ltac:(clear - Hx P47 P0; lia)) as SX. unfold BIGSHADOW_LO, BIGSHADOW_HI in *. clear - SX Hin FBIG; lia.
+ pose proof (PMKB.S_in_shadow x ltac:(clear - Hx P47 P0; lia)) as SX. destruct (LOCW rr X) as (Z1 & Z2). unfold BIGSHADOW_LO, BIGSHADOW_HI in *. clear - SX Hin Z1 Z2; lia. }
assert (FHF3 : PMHAK2.hf F) by (unfold PMHAK2.hf, BIGSHADOW_LO, BIGSHADOW_HI; pose proof (proj1 F8) as E8; clear - FR FBIG E8; lia).
assert (SZI' : shadow_zero M' (F + 96) 34).
{ assert (WFIc : PMHAK2.wfi F Wc) by (intros r Hr; destruct (WcL r Hr) as [->|X]; [left; cbn [fst snd]; lia| right; destruct (LOCW r X); lia]).
apply (PMHAK2.shz_callee L ar _ FF' (V2 - 128) 20480 Wc M4 M' (F, 4, V2 - 128 + 32) F (F + 96) 34 HP' (or_introl eq_refl) (conj eq_refl eq_refl) FHF3 WFIc);
[lia| lia| pose proof (proj1 F8) as E8; clear - E8; lia| lia| exact SZI]. }
pose proof (PMBHP2.haD_conc fx' R' MV' (fun j => match j with 2%nat => V2 | 33%nat => data | 34%nat => n | 40%nat => F | 41%nat => fl | 58%nat => U R' 1 | _ => 0 end)) as P.
cbn beta iota in P.
assert (Q1 : 4096 <= F <= 140737488354304) by (clear - FR; lia).
assert (Q2 : 4096 <= fl <= 140737488355327) by (clear - FLR; lia).
assert (Q3 : V2 - 128 + 144 <= F \/ F + 1024 <= V2 - 128) by (clear - FCEIL SLO CLS; lia).
assert (Q4 : V2 - 128 + 144 <= fl \/ fl + 1 <= V2 - 128) by (clear - FLR SLO CLS; lia).
assert (Q5 : L5.writable RSEGS MV' (V2 - 128) 128) by (eapply L5.writable_sub; [exact VW'| clear; lia| clear - CLS; lia]).
assert (Q6 : L5.u64_at RSEGS MV' (F + 1016) fl) by (replace (F + 1016) with (F + 1024 - 8) by (clear; lia); exact VFLC').
feed P ltac:(first [ asm | apply UR | apply U_to | (clear - Hn; lia) | (clear - Hd; lia) | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
| exact VFD' | exact VFW' | exact VFSW' | exact VFLW' | exact Q5 | exact Q6 | (unfold PMBHP2.aligned; exact V2A) ]).
destruct P as (fx5 & R5 & M5v & MG5 & dFR & dFZ & (dMS & dKS & dR1 & dR10 & dR11 & dR12 & dR13 & dR14 & dR15 & dR23 & dR26 & DQ)).
set (W5 := fun a => F + 432 <= a < F + 432 + 8 \/ F + 928 <= a < F + 928 + 32 \/ F / 8 + 2147450934 <= a < F / 8 + 2147450934 + 1
\/ F / 8 + 2147450938 <= a < F / 8 + 2147450938 + 49 \/ F / 8 + 2147450996 <= a < F / 8 + 2147450996 + 4).
apply (apiece L ar C HI LYa HIok _ FF' LK' cr' Aw' M' model' fx' fx5 R' 0xa7cac R5 0xabbb0 M5v W5 K HH' AM' dMS MG5).
{ intros a Ha Hna. apply dFZ; [exact Ha|..]; intros X; apply Hna; subst W5; cbn beta; clear - X; lia. }
{ intros a Ha Wa. subst W5; cbn beta in Wa. split.
- destruct Wa as [Wa|[Wa|Wa]].
+ apply (fframe_client L ar _ _ 0 0 F 4 (V2 - 128 + 32)). left; reflexivity. change (ff_bytes 4) with 1024. clear - Wa; lia.
+ apply (fframe_client L ar _ _ 0 0 F 4 (V2 - 128 + 32)). left; reflexivity. change (ff_bytes 4) with 1024. clear - Wa; lia.
+ apply (fframe_shadow_client L ar _ _ 0 0 F 4 (V2 - 128 + 32)). left; reflexivity. change (ff_bytes 4) with 1024.
unfold in_shadow_of, HeapIfaceA.S. rewrite (proj1 (proj2 F8)). unfold HeapIfaceA.SB. clear - Wa. lia.
- unfold HeapIfaceA.SB in *. clear - Wa FR. lia. }
intros M5 model5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5 VV5. change (mrestrict H' M5 = M5v) in VIS5.
decompose [and] DQ. clear DQ.
assert (BI5 : Bv W (PM.vs_own s' ++ PM.vs_own s) M5 model5 LK' cr' Aw').
{ apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W (PM.vs_own s' ++ PM.vs_own s) M' model' LK' cr' Aw' M5 model5 W5 BI' HH5 AM5 MRT5 MGM5 FR5).
intros a Wa. subst W5; cbn beta in Wa. right. change (ff_bytes 4) with 1024. change (1024 / 8) with 128. unfold HeapIfaceA.SB in *. clear - Wa. lia. }
assert (RI5 : rinvH R R5 V2 cls F) by (apply (rinvH_ks R R' R5 V2 cls F PMBHP2.KS_haD RI' dKS); vm_compute; reflexivity).
assert (LS5 : PMSTA.ls_okA RSEGS PMB.AD PMB.AAD (PMST.ST true (PMST.st_sys g) (PMST.st_err g)) M5).
{ apply (PMHAK.ls_piece _ M' M5 W5 FR5); [| exact LS']. intros a Wa. subst W5; cbn beta in Wa. clear - Wa FR. lia. }
assert (WPF : forall a, W5 a -> (F <= a < F + 1024) \/ (F / 8 + HeapIfaceA.SB <= a < F / 8 + HeapIfaceA.SB + 128) \/ (V2 - 128 <= a < V2)).
{ intros a Wa. subst W5; cbn beta in Wa. unfold HeapIfaceA.SB. clear - Wa. lia. }
assert (FIN : In (F, 4, V2 - 128 + 32) (FF' ++ LK')) by (apply in_or_app; left; left; reflexivity).
assert (FM8 : F mod 8 = 0) by (pose proof (proj1 F8) as E8; clear - E8; lia).
assert (SLOW : ahl_ceil ar <= V2 - 128) by (clear - SLO CLS; lia).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
assert (VS5 : PM.vstr_at RSEGS PMSPA.accA M5 (F + 32) s).
{ apply (PMFA.vstr_at_agreeA RSEGS M' M5 (F + 32) s); [clear - FR; lia| clear - FR; lia| | |exact VS'].
- apply (PMHAK.agA_frame M' M5 W5 (F + 32) 24 FR5); [clear - FR; lia| clear - FR; lia|].
intros x Hx. subst W5; cbn beta. unfold HeapIfaceA.S, HeapIfaceA.SB. split; intros X.
+ clear - Hx X FR FBIG F8. unfold BIGSHADOW_LO, BIGSHADOW_HI in *. lia.
+ clear - Hx X FR FBIG FM8. unfold BIGSHADOW_LO, BIGSHADOW_HI in *. lia.
- intros c0 n0 p0 E0. apply (PMHAK.blk_agA L ar C SCFG HI HIok _ _ _ _ _ _ _ p0 c0 F (V2 - 128 + 32) (V2 - 128) V2 W5 M' M5 HH');
[ rewrite E0; apply in_or_app; left; apply in_or_app; right; left; reflexivity | exact FIN | exact FM8 | clear - FR; lia | clear - FR; lia
| unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - FBIG; lia | exact SLOW | unfold BIGSHADOW_HI; clear - V2R; lia | exact FR5 | exact WPF ]. }
assert (IS5 : PM.iss_at RSEGS PMB.AD PMSPA.accA M5 (F + 96) s' sm).
{ apply (PMFA.iss_at_agreeA RSEGS PMB.AD M' M5 (F + 96) s' sm); [clear - FR; lia| clear - FR; lia| | |exact ISA].
- apply (PMHAK.agA_frame M' M5 W5 (F + 96) 272 FR5); [clear - FR; lia| clear - FR; lia|].
intros x Hx. subst W5; cbn beta. unfold HeapIfaceA.S, HeapIfaceA.SB. split; intros X.
+ clear - Hx X FR FBIG F8. unfold BIGSHADOW_LO, BIGSHADOW_HI in *. lia.
+ clear - Hx X FR FBIG FM8. unfold BIGSHADOW_LO, BIGSHADOW_HI in *. lia.
- intros c0 n0 p0 E0. apply (PMHAK.blk_agA L ar C SCFG HI HIok _ _ _ _ _ _ _ p0 c0 F (V2 - 128 + 32) (V2 - 128) V2 W5 M' M5 HH');
[ rewrite E0; apply in_or_app; left; apply in_or_app; left; left; reflexivity | exact FIN | exact FM8 | clear - FR; lia | clear - FR; lia
| unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - FBIG; lia | exact SLOW | unfold BIGSHADOW_HI; clear - V2R; lia | exact FR5 | exact WPF ]. }
assert (Q432 : (F + 432) / 8 + HeapIfaceA.SB = F / 8 + 2147450934) by (unfold HeapIfaceA.SB; clear - FM8; lia).
assert (Q464 : (F + 464) / 8 + HeapIfaceA.SB = F / 8 + 2147450938) by (unfold HeapIfaceA.SB; clear - FM8; lia).
assert (Q928 : (F + 928) / 8 + HeapIfaceA.SB = F / 8 + 2147450996) by (unfold HeapIfaceA.SB; clear - FM8; lia).
assert (FBD : 0 <= F / 8 /\ F / 8 + 128 <= 2 ^ 44) by (clear - FR; lia).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
assert (AVF : forall d k, 0 <= d -> d + k <= 1024 -> L5A.avis H' (F + d) k) by (intros d k Hd1 Hd2; apply (PMHAK.avis_sub H' F 1024 (F + d) k FV'); lia).
assert (AVS : forall q k, F / 8 + 2147450880 <= q -> q + k <= F / 8 + 2147450880 + 128 -> L5A.avis H' q k)
by (intros q k Hd1 Hd2; apply (PMHAK.avis_sub H' (F / 8 + HeapIfaceA.SB) 128 q k FSV'); unfold HeapIfaceA.SB; lia).
apply (KONT fx5 R5 M5 model5 LK' cr' Aw' s' sm BI5 RI5 LS5).
- exact dR1.
- exact dR10.
- exact dR11.
- exact dR12.
- exact dR13.
- rewrite (dKS 21%nat) by inl. exact Y21.
- rewrite (dKS 22%nat) by inl. exact Y22.
- exact dR23.
- exact dR26.
- exact VS5.
- exact IS5.
- rewrite SZ'. exact SIZE0.
- exact SMG.
- exact SMST.
- rewrite SIZE0 in CK'. exact CK'.
- apply (PMHAK.u64_vis H' M5 M5v (F + 432) _ VV5 (AVF 432 8 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia)). asm.
- apply (PMHAK.u64_vis H' M5 M5v (F + 928) _ VV5 (AVF 928 8 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia)). asm.
- apply (PMHAK.u64_vis H' M5 M5v (F + 936) _ VV5 (AVF 936 8 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia)). asm.
- apply (PMHAK.u64_vis H' M5 M5v (F + 944) _ VV5 (AVF 944 8 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia)). asm.
- apply (PMHAK.u32_vis H' M5 M5v (F + 952) _ VV5 (AVF 952 4 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia)). asm.
- apply (PMHAK.u32_vis H' M5 M5v (F + 956) _ VV5 (AVF 956 4 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia)). asm.
- apply (PMHAK.shz_vis H' M5 M5v (F + 432) 1 (F / 8 + 2147450934) VV5 (AVS (F / 8 + 2147450934) 1 ltac:(lia) ltac:(lia)) Q432 ltac:(clear - FBD; lia) ltac:(clear - FBD; lia)).
intros j Hj. assert (J : j = 0) by (clear - Hj; lia). subst j. gmem.
- apply (PMHAK.shz_vis H' M5 M5v (F + 464) 49 (F / 8 + 2147450938) VV5 (AVS (F / 8 + 2147450938) 49 ltac:(lia) ltac:(lia)) Q464 ltac:(clear - FBD; lia) ltac:(clear - FBD; lia)).
intros j Hj. assert (J : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 13 \/ j = 14 \/ j = 15 \/ j = 16 \/ j = 17 \/ j = 18 \/ j = 19 \/ j = 20 \/ j = 21 \/ j = 22 \/ j = 23 \/ j = 24 \/ j = 25 \/ j = 26 \/ j = 27 \/ j = 28 \/ j = 29 \/ j = 30 \/ j = 31 \/ j = 32 \/ j = 33 \/ j = 34 \/ j = 35 \/ j = 36 \/ j = 37 \/ j = 38 \/ j = 39 \/ j = 40 \/ j = 41 \/ j = 42 \/ j = 43 \/ j = 44 \/ j = 45 \/ j = 46 \/ j = 47 \/ j = 48) by (clear - Hj; lia).
repeat (destruct J as [J|J]; [subst j; gmem|]). subst j; gmem.
- apply (PMHAK.shz_vis H' M5 M5v (F + 928) 4 (F / 8 + 2147450996) VV5 (AVS (F / 8 + 2147450996) 4 ltac:(lia) ltac:(lia)) Q928 ltac:(clear - FBD; lia) ltac:(clear - FBD; lia)).
intros j Hj. assert (J : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by (clear - Hj; lia).
repeat (destruct J as [J|J]; [subst j; gmem|]). subst j; gmem.
- apply (PMHAK2.shz_frame M' M5 W5 (F + 96) 34 FR5); [| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| exact SZI'].
intros j Hj X. subst W5; cbn beta in X. unfold HeapIfaceA.S, HeapIfaceA.SB in X.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
assert (E96 : (F + 96) / 8 = F / 8 + 12) by (clear - FM8; lia).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
rewrite E96 in X. clear - X Hj FBD FR FBIG. lia.
Qed.
End Stage.
End SCFG_1.
End PMHA3.
