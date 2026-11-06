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
L5CoreAB0 L5StepARB0 L5CoreBRB0 L5ADetailHRB0 L5AFrameKRB0 HeapIfaceAJx PmLayout PmLayoutA PmModel PmModelFactsA PmStatics PmStaticsA PmSpecsA PmSpecsAb PmStepAB0 PmBReset1 PmBHarnessStmts PmBHarnessKit PmBHarnessP2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBHarness2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5DefsAB0.L5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBHarnessStmts.PMHAS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAb.PMB."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStatics.PMST."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStaticsA.PMSTA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5AFrameKRB0.L5AFKR."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0A4"; "0B"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2ex"; "2or"; "3Z"; "0F"; "0FF"; "0HI"]; ["0K"; "0L"; "0LB"; "0LK"; "0LK2"; "0LK4"; "4Model"; "4event"; "5bvmap"; "0M"; "0M3"; "0M4"; "0R"; "0R3"; "0R4"; "6credit"]; ["7aacc"; "7fframe"; "7shadow_zero"; "8SCFG"; "9cfg"; ":rinvH"; ":tfrk"; ";AADDR_B"; ";ADDR_B"; "<VLong"; "<VShort"; "<cost1"; "<vs_own"; "<vs_size"; "<vstr"; "<vstr_at"]; ["=HV"; "=accA"; "=cr0"; "=credit_keep"; "=credit_le"; "=scA"; "=str_count"; ">str_ctor_spec"; "?st"; "@ls_okA"; "AFPState"; "Agetr"; "BTSet"; "Csrealizes"; "Dbinv"; "Eloaded_segments"]; ["0SCFG_P"; "0STR"; "FIn"; "Gadd"; "Gle"; "Glt"; "Gof_nat"; "Gpow"; "Gsub"; "0V2"; "0W"; "0ar"; "0cls"; "0cr"; "0cr4"; "0data"]; ["0fx3"; "0fx4"; "0g"; "0m"; "0model"; "0model3"; "0model4"; "0n"; "0p"; "0s"; "HZ_to_bv"; "Hbv"]]).
Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module PMHA2.
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
Local Notation Bv := (L5AFKR.binv L ar HI M model LB FF LK A (V2 + cls) 36864 (V2 - 128) (tfrk (V2 + cls) R) F 4).
Local Notation FF' := ((F, 4, V2 - 128 + 32) :: FF).
Lemma stage2 : ltac2:(TCodec.tc2 tcn__PmBHarness2 "YI&QGvR0vAvR;v?%544321'QJ&Hy5'RKyR0%211%5241'5y8%611%311p061'F&QL'<'QH&QNvIvRDvBv>vCv0&R3vR9vR<%3221+QTP0&R8+T0%2261&Q6vL%2271v=+4vR:(4'7%12II%311r6r5vDvR=%MFQAQ@Q?LKJIHGCB?<;:954321G&Q5r8%25@1HG>'G%=11%:11&QI&QO&Q8&Q7r4r9%6554321'9&QKr;&RJ&R6u1%211%42R01%7261+doPD%72R11%;3R131r<u:%:11%<2R81%?241+Q0%QF2Q;1%@2R:1%D3R:41r=u;%C11%E2RA1%H241%G2RAL%K3RA21r>u<%J11%L2RH1%O241%Q13RG17r?uE%Q011%Q22RN1%Q5241+S0%R<2R11%Q62S01%Q:3S041r@uF%Q911%Q;2S71%Q>241%Q=2S7Q>%QA3S721rAuG%Q@11%QB2S>1%QE241%QD2S>Q2%QH3S>21&Q2+3%239Q91'8&R4z%221Q3&R5&R7+2+J%3221%52Q91%:271%:29L+R0%8271%:2O1%?241';%R=3SJQ2?':&R2(6r2r1%34T0T021%53S81SLrC%I251rB%SL231%SM287%M221%O251%Q0281qU8T:1%@2T;1q6T<1%B2T=1%E2D1&Q0rE%231=QB&QD&QE&Q;&Q@%12U8U7+@%T?2D1%5231%72U<1%921SM'3&Q1%211&O%41T7'Q>&Q<%11Q4r3%U3FUGUFUEU2U1U0TOTNTMTITHTETBTAT@T?2T:T9SK1Q7%SH2SKSB+doU<%SH2UB1%SL3UB31r:%SM21S?%SO3UE1RF%SO2SNS8%T13UG1S>%T12SFS3+8%T12UK1%T53UK31%T52SAS1%T73UM1RN%T72S<RJrQ2%T72V11%T;3V131%T;2S:RGrQ4%T;2V51%T?3V531&Q?&QA%25TH1S@T0E&Q=%11TBrQ5%TF3V321rQ6+F%RL221(Q:rQ7%211%TM3Q9T81p051+G%S3215(Q9&QFrQ9%211%4312RC%U63QBT41qUBVD1%RJ2VE1p091&QCrQ8%V@21R2%R62R41%R82W=1&QB%64UOT521rD+Q2%SJ32T;1%UK5UJUIUHARA'QM&Q3%11WG&Q4rHrG+eQTDrF%554321RJrQ=%:4V5821p0<1p0>1p0B1p0J1p0Q61p0Q?1p0QD1p0QH1p0QM1p0R21p0R51p0R:1p0R=1p0RA1p0VI1p0RG1pUDRL1p4RN1pTNS01pQ<S21pU>X31pQHX51pQNX;1pU4XB1rJrI+ePi<%Q35321Q2Q1%Q74W2Q51Q0p061p0S@1p0SK1p0SO1p0TF1p0TL1p0U81p0U<1p0UD1p0UL1p0V61p0V=1p0VE1p0VO1p0W<1p0WD1p0WH1p0WL1pU6XK1pU@XM1pU0XN1pQ2Y01pU<Y21pQFY41pQLY:1pU2YA1pT4YC1").
Proof. intros STR fx3 R3 M3 model3 K data n g.
intros BI RI K0 LS R1a R10 R11 R12 R21 R22 R23 SZS Hn Hd SRCB ACCd CRD KONT.
pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
change (ff_bytes 4) with 1024 in *. change (1024 / 8) with 128 in *.
pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10). cbn [app] in B1.
pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W [] M3 model3 LK2 cr A BI)
as ((VW3 & VIC3 & VSB3 & VUAR3 & VMS3) & VOWN3 & (VFD3 & VFW3 & VFSW3 & VFLC3 & VFLW3) & (FLCc3 & FLV3 & FV3 & SPV3 & FSV3)).
change (ff_bytes 4) with 1024 in *. change (1024 / 8) with 128 in *.
set (H3 := ahid A model3) in *. set (MV3 := mrestrict H3 M3) in *.
pose proof RI as (X2 & X8 & X9 & X18 & X19 & X20 & X24 & X25 & X3 & X4 & X27).
assert (FDEF3 : L5.defined M3 F 1024) by (apply (proj1 (L5A.defined_vis H3 M3 F 1024 FV3)); exact VFD3).
assert (SZ3 : shadow_zero M3 (V2 - 128 - 12288) 1536).
{ apply (PMKB.shadow_zero_sub M3 (V2 + cls - 36864) 4608); [| | clear - CLS; lia| clear - CLS; lia| lia|].
- replace (V2 + cls - 36864) with ((V2 - 36864) + cls) by (clear; lia). destruct CLS as [E|E]; subst cls; [rewrite Z.add_0_r|].
+ apply PMKB.mod16_8'. replace (V2 - 36864) with (V2 + (-2304) * 16) by (clear; lia). rewrite Z_mod_plus_full. apply Z.mod_divide; [lia|].
destruct (proj1 (Z.mod_divide V2 32 ltac:(lia)) V2A) as (q & ->). exists (2 * q). lia.
+ apply PMKB.mod16_8'. replace (V2 - 36864 + 16) with (V2 + (-2303) * 16) by (clear; lia). rewrite Z_mod_plus_full. apply Z.mod_divide; [lia|].
destruct (proj1 (Z.mod_divide V2 32 ltac:(lia)) V2A) as (q & ->). exists (2 * q). lia.
- apply PMKB.mod16_8'. replace (V2 - 128 - 12288) with (V2 + (-776) * 16) by (clear; lia). rewrite Z_mod_plus_full. apply Z.mod_divide; [lia|].
destruct (proj1 (Z.mod_divide V2 32 ltac:(lia)) V2A) as (q & ->). exists (2 * q). lia.
- apply (PMKB.stksh_keepA L ar LB FF (V2 + cls) 36864 W M M3 B7 WAPP); [clear - SLO SPT; lia| clear - SLO SPT; lia| clear - V2S CLS; lia| | lia| exact STKSH].
replace (V2 + cls - 36864) with ((V2 - 36864) + cls) by (clear; lia). destruct CLS as [E|E]; subst cls; [rewrite Z.add_0_r|].
+ apply PMKB.mod16_8'. replace (V2 - 36864) with (V2 + (-2304) * 16) by (clear; lia). rewrite Z_mod_plus_full. apply Z.mod_divide; [lia|].
destruct (proj1 (Z.mod_divide V2 32 ltac:(lia)) V2A) as (q & ->). exists (2 * q). lia.
+ apply PMKB.mod16_8'. replace (V2 - 36864 + 16) with (V2 + (-2303) * 16) by (clear; lia). rewrite Z_mod_plus_full. apply Z.mod_divide; [lia|].
destruct (proj1 (Z.mod_divide V2 32 ltac:(lia)) V2A) as (q & ->). exists (2 * q). lia. }
assert (ASTKc : L5CA.astk ar M3 (V2 - 128) 12288).
{ replace (V2 - 128) with ((V2 + cls) - (128 + cls)) by (clear; lia).
apply (L5SAR.astk_sub ar M3 M3 (V2 + cls) 36864 (128 + cls) 12288 B6 (fun _ X => X)); [clear - CLS; lia| lia| clear - CLS; lia|].
replace (V2 + cls - (128 + cls)) with (V2 + (-8) * 16) by (clear; lia). rewrite Z_mod_plus_full. apply Z.mod_divide; [lia|].
destruct (proj1 (Z.mod_divide V2 32 ltac:(lia)) V2A) as (q & ->). exists (2 * q). lia. }
assert (NDF : NoDup (map ff_addr (FF' ++ LK2))).
{ pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). exact X. }
unfold PMB.str_ctor_spec, PMSPA.str_ctor_spec in STR. cbn [pa_str_ctor PMB.AD ADDR_A] in STR.
apply (STR fx3 R3 M3 model3 K LB FF' LK2 A cr (F + 32) data n (V2 - 128) 0xa7c14 B1 B2 K0).
{ split; [rewrite L5K.rl1; exact R1a|]. split; [split; [lia| reflexivity]|]. split; [rewrite L5K.rl2; exact X2|].
split; [rewrite L5K.rl3, X3; exact GP|]. split; [rewrite L5K.rl4, X4; exact TP|].
change (PMSPA.pm_scr 0) with 12288. split; [exact ASTKc|]. change (12288 / 8) with 1536. exact SZ3. }
{ intros k0 Hk0. specialize (ROOM LK2 LKI2 NDF k0 Hk0). lia. }
{ intros f [<-|Hf]; [cbn [ff_rs fst snd]; lia| specialize (FFRS f Hf); lia]. }
{ rewrite L5K.rl10. exact R10. }
{ rewrite L5K.rl11. exact R11. }
{ rewrite L5K.rl12. exact R12. }
{ exact Hn. }
{ exists (F, 4, V2 - 128 + 32). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. lia. }
{ replace (F + 32) with (F + 4 * 8) by (clear; lia). rewrite Z_mod_plus_full. pose proof (proj1 F8) as E8. clear - E8 FR. lia. }
{ apply (L5.defined_sub M3 F 1024 (F + 32) 24 FDEF3); lia. }
{ apply (PMBRS1.acc_of_shadow_zero M3 (F + 32) 3 (F + 32) 24 SZS); [| lia| lia].
replace (F + 32) with (F + 4 * 8) by (clear; lia). rewrite Z_mod_plus_full. pose proof (proj1 F8) as E8. clear - E8 FR. lia. }
{ exact SRCB. }
{ exact ACCd. }
{ exact CRD. }
intros fx' R' M' model' LK' Aw' s cr' RP' VSTR SIZE SSH SLG HP' CK' MRT' INCLK' INCA' AM' HH'.
assert (LS' : PMSTA.ls_okA RSEGS PMB.AD PMB.AAD g M').
{ apply (PMHAK.ls_ahpres L C LY g ar LB FF' (V2 - 128) _ [(F + 32, 24)] M3 M' HP'); [| exact LS].
apply PMHAK.far_cons; [cbn [fst snd]; clear - FR; lia| apply PMHAK.far_nil]. }
change (PMSPA.pm_scr 0) with 12288 in HP'.
assert (BI' : Bv W (PM.vs_own s) M' model' LK' cr' Aw').
{ apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W W [] [] (PM.vs_own s) M3 model3 LK2 cr A M' model' LK' cr' Aw' 12288 [(F + 32, 24)] BI HP' HH' AM' MRT' INCA' INCLK').
- lia.
- clear - CLS; lia.
- intros rr a [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. unfold tocell. split; [clear - Ha FCEIL SLO CLS; lia|]. unfold HeapIfaceA.SB. change (ff_bytes 4) with 1024. clear - Ha FR F8 FBIG. lia.
- intros a Hc _ rr [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. apply (NCF a); [left; clear - Ha; lia| exact Hc].
- intros a X. exact X. }
pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W (PM.vs_own s) M' model' LK' cr' Aw' BI')
as ((VW' & VIC' & VSB' & VUAR' & VMS') & VOWN' & (VFD' & VFW' & VFSW' & VFLC' & VFLW') & (FLCc' & FLV' & FV' & SPV' & FSV')).
change (ff_bytes 4) with 1024 in *. change (1024 / 8) with 128 in *.
set (H' := ahid Aw' model') in *. set (MV' := mrestrict H' M') in *.
assert (RI' : rinvH R R' V2 cls F) by exact (rinvH_pres R R3 R' V2 cls F RI RP').
pose proof RI' as (Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y24 & Y25 & Y3 & Y4 & Y27).
assert (Y21 : getr R' (reg 21) = Z_to_bv 64 (F + 96)) by (rewrite (cs_of_preserved R3 R' 21 RP') by inl; exact R21).
assert (Y22 : getr R' (reg 22) = Z_to_bv 64 n) by (rewrite (cs_of_preserved R3 R' 22 RP') by inl; exact R22).
assert (Y23 : getr R' (reg 23) = Z_to_bv 64 data) by (rewrite (cs_of_preserved R3 R' 23 RP') by inl; exact R23).
pose proof (PMBHP2.haC_conc fx' R' MV' (fun j => match j with 2%nat => V2 | 33%nat => data | 34%nat => n | 40%nat => F | 41%nat => fl | 58%nat => U R' 1 | _ => 0 end)) as P.
cbn beta iota in P.
assert (Q1 : 4096 <= F <= 140737488354304) by (clear - FR; lia).
assert (Q2 : 4096 <= fl <= 140737488355327) by (clear - FLR; lia).
assert (Q3 : V2 - 128 + 144 <= F \/ F + 1024 <= V2 - 128) by (clear - FCEIL SLO CLS; lia).
assert (Q4 : V2 - 128 + 144 <= fl \/ fl + 1 <= V2 - 128) by (clear - FLR SLO CLS; lia).
assert (Q5 : L5.writable RSEGS MV' (V2 - 128) 128) by (eapply L5.writable_sub; [exact VW'| clear; lia| clear - CLS; lia]).
assert (Q6 : L5.u64_at RSEGS MV' (F + 1016) fl) by (replace (F + 1016) with (F + 1024 - 8) by (clear; lia); exact VFLC').
feed P ltac:(first [ asm | apply UR | apply U_to | (clear - Hn; lia) | (clear - Hd; lia) | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
| exact VFD' | exact VFW' | exact VFSW' | exact VFLW' | exact Q5 | exact Q6 | (unfold PMBHP2.aligned; exact V2A) ]).
destruct P as (fx4 & R4 & M4v & MG4 & cFR & cFZ & (cMS & cKS & cR1 & cR10 & cR11 & cR12 & CQ)).
set (W4 := fun a => F / 8 + 2147450880 + 12 <= a < F / 8 + 2147450880 + 12 + 34).
apply (apiece L ar C HI LYa HIok _ FF' LK' cr' Aw' M' model' fx' fx4 R' 0xa7c14 R4 0xa8494 M4v W4 K HH' AM' cMS MG4).
{ intros a Ha Hna. apply cFZ. exact Ha. intros X; apply Hna; subst W4; cbn beta; clear - X; lia. }
{ intros a Ha Wa. subst W4; cbn beta in Wa. split.
- apply (fframe_shadow_client L ar _ _ 0 0 F 4 (V2 - 128 + 32)). left; reflexivity. change (ff_bytes 4) with 1024.
unfold in_shadow_of, HeapIfaceA.S. rewrite (proj1 (proj2 F8)). unfold HeapIfaceA.SB. clear - Wa. lia.
- clear - Wa FR. lia. }
intros M4 model4 HH4 AM4 MRT4 HID4 VIS4 MGM4 FR4 VV4. change (mrestrict H' M4 = M4v) in VIS4.
assert (LS4 : PMSTA.ls_okA RSEGS PMB.AD PMB.AAD g M4).
{ apply (PMHAK.ls_piece g M' M4 W4 FR4); [| exact LS']. intros a Wa. subst W4; cbn beta in Wa. clear - Wa FR. lia. }
decompose [and] CQ. clear CQ.
assert (BI4 : Bv W (PM.vs_own s) M4 model4 LK' cr' Aw').
{ apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W (PM.vs_own s) M' model' LK' cr' Aw' M4 model4 W4 BI' HH4 AM4 MRT4 MGM4 FR4).
intros a Wa. subst W4; cbn beta in Wa. right; right. change (ff_bytes 4) with 1024. change (1024 / 8) with 128. unfold HeapIfaceA.SB in *. clear - Wa. lia. }
assert (RI4 : rinvH R R4 V2 cls F) by (apply (rinvH_ks R R' R4 V2 cls F PMBHP2.KS_haC RI' cKS); vm_compute; reflexivity).
assert (SZ4 : shadow_zero M4 (F + 96) 34).
{ intros j Hj. unfold byte_at, HeapIfaceA.S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
assert (E96 : (F + 96) / 8 = F / 8 + 12) by (pose proof (proj1 (proj2 F8)) as E8; clear - E8; lia).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
rewrite E96. rewrite VV4.
- assert (X : L5.u8_at RSEGS M4v (F / 8 + 2147450892 + j) 0).
{ assert (J : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 13 \/ j = 14 \/ j = 15 \/ j = 16 \/ j = 17 \/ j = 18 \/ j = 19 \/ j = 20 \/ j = 21 \/ j = 22 \/ j = 23 \/ j = 24 \/ j = 25 \/ j = 26 \/ j = 27 \/ j = 28 \/ j = 29 \/ j = 30 \/ j = 31 \/ j = 32 \/ j = 33) by (clear - Hj; lia).
repeat (destruct J as [J|J]; [subst j; gmem|]). subst j; gmem. }
replace (F / 8 + 12 + HeapIfaceA.SB + j) with (F / 8 + 2147450892 + j) by (unfold HeapIfaceA.SB; clear; lia).
apply (L5ADHR.byte_of_u8 M4v _ 0 X). right. clear - Hj FR F8. lia. clear - Hj FR F8. lia.
- replace (F / 8 + 12 + HeapIfaceA.SB + j) with ((F / 8 + HeapIfaceA.SB) + (12 + j)) by (clear; lia). apply FSV'. clear - Hj. lia. }
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
assert (VSTR4 : PM.vstr_at RSEGS PMSPA.accA M4 (F + 32) s).
{ apply (PMFA.vstr_at_agreeA RSEGS M' M4 (F + 32) s); [clear - FR; lia| clear - FR; lia| | |].
- split.
+ intros i Hi. apply FR4; [clear - Hi FR; lia| subst W4; cbn beta; intros X; clear - Hi X FR F8 FBIG; unfold HeapIfaceA.SB in *; lia].
+ intros x Hx. pose proof (PMKB.S_in_shadow x ltac:(clear - Hx FR; lia)) as SX. apply FR4; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; clear - SX; lia|].
subst W4; cbn beta. intros X. unfold HeapIfaceA.S, HeapIfaceA.SB in X. clear - Hx X F8. lia.
- intros c0 n0 p0 E0. subst s. cbn [PM.vs_own app] in HH'.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH') as (WB' & _).
pose proof (WB' (p0, c0) (or_introl eq_refl)) as ((P0 & _ & _ & P3 & _ & P5) & _ & _ & _ & _ & PFA & _). cbn [fst snd] in P0, P3, P5, PFA. unfold app_mem in P5.
pose proof (PFA (F, 4, V2 - 128 + 32) (in_or_app FF' LK' (F, 4, V2 - 128 + 32) (or_introl (or_introl eq_refl)))) as PF. cbn [ff_addr ff_class fst snd] in PF. change (ff_bytes 4) with 1024 in PF.
split.
+ intros i Hi. apply FR4; [clear - Hi P5; lia| subst W4; cbn beta; intros X; clear - Hi X P5 FR; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; lia].
+ intros x Hx. pose proof (PMKB.S_in_shadow x ltac:(clear - Hx P5; lia)) as SX. apply FR4; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; clear - SX; lia|].
subst W4; cbn beta. intros X. unfold HeapIfaceA.S in X.
unfold HeapIfaceA.SB in X. clear - Hx X PF F8 P3. lia.
- exact VSTR. }
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
apply (KONT fx4 R4 M4 model4 LK' cr' Aw' s BI4 RI4).
- exact cR1.
- exact cR10.
- exact cR11.
- exact cR12.
- rewrite (cKS 21%nat) by inl. exact Y21.
- rewrite (cKS 22%nat) by inl. exact Y22.
- rewrite (cKS 23%nat) by inl. exact Y23.
- exact VSTR4.
- exact SIZE.
- exact SSH.
- exact SLG.
- exact CK'.
- exact SZ4.
- exact LS4.
Qed.
End Stage.
End SCFG_1.
End PMHA2.
