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
L5CoreAB0 L5StepARB0 L5CoreBRB0 L5ADetailHRB0 L5AFrameKRB0 HeapIfaceAJx PmLayout PmLayoutA PmModel PmModelFacts PmModelFactsA PmStatics PmStaticsA PmSpecsA PmSpecsAb PmStepAB0 PmBReset1 PmBHarnessStmts PmBHarnessKit PmBHarnessKit2 PmBHarnessSK PmBHarnessP3 PmBHarnessP4.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBHarness10 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5DefsAB0.L5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBHarnessKit2.PMHAK2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBHarnessStmts.PMHAS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAb.PMB."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStatics.PMST."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStaticsA.PMSTA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5AFrameKRB0.L5AFKR."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0A11"; "0A12"; "1list"; "1nil"; "1option"; "1prod"; "2eq"; "3Z"; "0F"; "0FF"; "0HI"; "0IOD"; "0K"; "0L"; "0LB"]; ["0LCD"; "0LK"; "0LK11"; "0LK12"; "4Model"; "4event"; "5bvmap"; "0M"; "0M11"; "0M12"; "0OPD"; "0R"; "0R11"; "0R12"; "6credit"; "7fframe"]; ["8SCFG"; "9cfg"; ":hfin"; ";rinvH"; ";tfrk"; "<AADDR_B"; "<ADDR_B"; "=vs_own"; "=vstr"; ">ios_dtor_spec"; ">locale_dtor_spec"; ">opdel_spec"; "?st"; "@ls_okA"; "AFPState"; "Agetr"]; ["BTSet"; "Csrealizes"; "Dbinv"; "Eloaded_segments"; "0SCFG_P"; "Fadd"; "Fof_nat"; "Fsub"; "0V2"; "0W"; "0ar"; "0cls"; "0cr11"; "0fx11"; "0fx12"; "0g"]; ["0model"; "0model11"; "0model12"; "0s"; "0st"; "GZ_to_bv"; "Gbv"]]).
Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module PMHA10.
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
Ltac hsolve := first [ exact LY | exact HIok | eassumption | exact (or_introl eq_refl) | (split; reflexivity) | apply incl_refl
| (apply PMHAK2.wapart_cons; [cbn [fst snd]; lia| first [apply PMHAK2.wapart_nil | (apply PMHAK2.wapart_cons; [cbn [fst snd]; lia| apply PMHAK2.wapart_nil])]])
| (apply PMHAK2.wapart_nil) | lia ].
Lemma stage10 : ltac2:(TCodec.tc2 tcn__PmBHarness10 "V<&Q:vQDv>vQJv;%544321&Q9%146543&Q;%148765'Q>&Fy5'R6yR0%211%5241'5y8%611%311p061'D&Q@'3&O%211&N'6'8%2211%711'Q8'Q<&QBvGvR0v?v:vAv0&QEvQHvQK%3221+QTP0&QG+T0%2261&Q4vK%2271v9+4vQI&Q7r3%211r9r8r6r5r4%MFQMQLQKLKJIHGCB?<;:9654321&Q3r;%25@1HG>(4'E%211%<11&Q=&QC&Q6&Q5r<%55432>1'7&Q?r>&R5&QFu1%211%42R81%7261+doo8%72R91%;3R931r?u:%:11%<2R@1%?241+SH%QF2Q;1%@2RB1%D3RB41r@uE%C11%E2RI1%H241+S0%QO2QD1%I2RK1%M3RK41rAuF%L11%N2S21%Q1241+QVXR8%Q12S31%Q53S331rBuG%Q411%Q62S:1%Q9241+^@%R@2R51%Q:2S<1%Q>3S<41rCuJ%Q=11%Q?2SC1%QB241+_oooooooooooH%QB2SD1%QF3SD31&Q2r=%24RB:1QK%R41S9r2rFr1%S9FT9T8T7S8S7S6S5S4S3RORNRKRHRGRFRE4R=RC321%R<5RJR@S2S1RHrD%R75R6R5R41RB%R12RDQ:%R33T11>%R32RGQ3%R53T31Q1r:%R621N%R83T61K%R82REG%R:3T81E'QA&Q0%11TI&Q1+ePU4%25HRB1RL:rO%74RG521p091p0<1p0@1p0C1p0F1p0I1p0K1p6T81pQ8T>1pT6TC1pQDTE1pQLTK1pSNU21rG+o_a4rE%E53Q721Q3%I4S9G1QEp061p0Q=1p0QA1p0QJ1p0R41p0R=1p0RG1p0S11p0S>1p0SE1p0SJ1p0SN1pT0TM1pT:U21pT8U01p4U21pSJU71pQ6U91pLU=1pT4U?1pQBUA1pQJUG1pSLUN1pQFV01pJV31pQ2V61").
Proof. intros LCD IOD OPD fx11 R11 M11 model11 K LK11 cr11 A11 s st g.
intros BI RI K0 LS R1a R10a R21 R22 R23 R26 HF0 KONT.
pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
change (ff_bytes 4) with 1024 in *. change (1024 / 8) with 128 in *.
pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
pose proof RI as (X2 & X8 & X9 & X18 & X19 & X20 & X24 & X25 & X3 & X4 & X27).
assert (FM8 : F mod 8 = 0) by (pose proof (proj1 F8) as E8; clear - E8; lia).
assert (FHF : PMHAK2.hf F) by (unfold PMHAK2.hf, BIGSHADOW_LO, BIGSHADOW_HI; clear - FR FBIG FM8; lia).
pose proof HF0 as (VS0 & LC0 & IO0). pose proof LS as (LSB & LSL & LSS & LSE).
assert (SLOW : ahl_ceil ar <= V2 - 128) by (clear - SLO CLS; lia).
assert (SHW : BIGSHADOW_HI <= V2 - 128) by (unfold BIGSHADOW_HI; clear - V2R; lia).
unfold PMB.locale_dtor_spec, PMSPA.locale_dtor_spec in LCD. cbn [pa_locale_dtor pa_classic_imp PMB.AD ADDR_A] in LCD.
apply (LCD fx11 R11 M11 model11 K _ FF' LK11 A11 cr11 (F + 120) (V2 - 128) 0xa7fe8 B1 B2 K0).
{ eapply PMHASK.callee_entry; first [exact BI | exact RI | exact R1a | eassumption | (split; [lia| reflexivity]) | lia]. }
{ eapply PMHASK.callee_room; first [exact BI | eassumption | lia]. }
{ eapply PMHASK.callee_rs; eassumption. }
{ rewrite L5K.rl10. exact R10a. }
{ exists (F, 4, V2 - 128 + 32). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. lia. }
{ cbn [pa_classic_imp PMB.AD ADDR_A] in LC0. exact LC0. }
intros fx' R' model11d RP' MRTd AMd HHd.
assert (BId : Bv W (PM.vs_own s) M11 model11d LK11 cr11 A11).
{ apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W _ M11 model11 LK11 cr11 A11 M11 model11d (fun _ => False) BI HHd AMd MRTd
(mem_grows_refl M11) (fun a _ _ => eq_refl)). intros a []. }
clear BI B1 B2 B3 B4 B5 B6 B7 B8 B9 B10 MRTd AMd HHd. clear model11. rename model11d into model11. rename BId into BI.
pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
assert (RI' : rinvH R R' V2 cls F) by exact (rinvH_pres R R11 R' V2 cls F RI RP').
pose proof RI' as (Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y24 & Y25 & Y3 & Y4 & Y27).
assert (Y21 : getr R' (reg 21) = Z_to_bv 64 (F + 96)) by (rewrite (cs_of_preserved R11 R' 21 RP') by inl; exact R21).
assert (Y22 : getr R' (reg 22) = Z_to_bv 64 1253448) by (rewrite (cs_of_preserved R11 R' 22 RP') by inl; exact R22).
assert (Y23 : getr R' (reg 23) = Z_to_bv 64 (F + 464)) by (rewrite (cs_of_preserved R11 R' 23 RP') by inl; exact R23).
assert (Y26 : getr R' (reg 26) = Z_to_bv 64 18446744073709551608) by (rewrite (cs_of_preserved R11 R' 26 RP') by inl; exact R26).
pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W _ M11 model11 LK11 cr11 A11 BI)
as ((VW1 & VIC1 & VSB1 & VUAR1 & VMS1) & VOWN1 & (VFD1 & VFW1 & VFSW1 & VFLC1 & VFLW1) & (FLCc1 & FLV1 & FV1 & SPV1 & FSV1)).
change (ff_bytes 4) with 1024 in *. change (1024 / 8) with 128 in *.
set (H1 := ahid A11 model11) in *. set (MV1 := mrestrict H1 M11) in *.
assert (Q1 : 4096 <= F <= 140737488354304) by (clear - FR; lia).
assert (Q2 : 4096 <= fl <= 140737488355327) by (clear - FLR; lia).
assert (Q3 : V2 - 128 + 144 <= F \/ F + 1024 <= V2 - 128) by (clear - FCEIL SLO CLS; lia).
assert (Q4 : V2 - 128 + 144 <= fl \/ fl + 1 <= V2 - 128) by (clear - FLR SLO CLS; lia).
assert (Q5 : L5.writable RSEGS MV1 (V2 - 128) 128) by (eapply L5.writable_sub; [exact VW1| clear; lia| clear - CLS; lia]).
assert (Q6 : L5.u64_at RSEGS MV1 (F + 1016) fl) by (replace (F + 1016) with (F + 1024 - 8) by (clear; lia); exact VFLC1).
pose proof (PMBHP3.haM_conc fx' R' MV1 (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U R' 1 | _ => 0 end)) as P.
cbn beta iota in P.
feed P ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
| exact VFD1 | exact VFW1 | exact VFSW1 | exact VFLW1 | exact Q5 | exact Q6 | (unfold PMBHP3.aligned; exact V2A) ]).
destruct P as (fx2 & R2 & M2v & MG2 & mFR & mFZ & (mMS & mKS & mR1 & mR10 & mR11)).
apply (apiece L ar C HI LYa HIok _ FF' LK11 cr11 A11 M11 model11 fx' fx2 R' 0xa7fe8 R2 0xd7640 M2v (fun _ => False) K B1 B2 mMS MG2).
{ intros a Ha Hna. apply mFZ; exact Ha. }
{ intros a Ha []. }
intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
assert (BI3 : Bv W (PM.vs_own s) M3 model3 LK11 cr11 A11).
{ apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W _ M11 model11 LK11 cr11 A11 M3 model3 (fun _ => False) BI HH3 AM3 MRT3 MGM3 FR3).
intros a []. }
assert (RI3 : rinvH R R2 V2 cls F) by (apply (rinvH_ks R R' R2 V2 cls F PMBHP3.KS_haM RI' mKS); vm_compute; reflexivity).
assert (LS3 : PMSTA.ls_okA RSEGS PMB.AD PMB.AAD g M3) by (apply (PMHAK.ls_piece _ M11 M3 (fun _ => False) FR3); [intros a []| exact LS]).
assert (FIN1 : In (F, 4, V2 - 128 + 32) (FF' ++ LK11)) by (apply in_or_app; left; left; reflexivity).
assert (PF3 : PMHAK2.pfoot F (V2 - 128) V2 (fun _ => False)) by (intros a []).
assert (OAX : forall o n, PMHAK2.oav (fun _ => False) o n) by (intros o n x Hx; split; intros []).
assert (HF3 : PMHAK2.hfin F M3 s st).
{ apply (PMHAK2.hfin_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) B1 FIN1 FHF (V2 - 128) V2 (fun _ => False) M11 M3 SLOW SHW FR3 PF3 s st);
[intros x Hx; apply in_or_app; left; exact Hx| apply OAX| apply OAX| apply OAX| exact HF0]. }
pose proof HF3 as (VS3 & LC3 & IO3).
pose proof BI3 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
unfold PMB.ios_dtor_spec, PMSPA.ios_dtor_spec in IOD. cbn [pa_ios_dtor PMB.AD ADDR_A] in IOD.
apply (IOD fx2 R2 M3 model3 K _ FF' LK11 A11 cr11 (F + 216) 1253432 (F + 112) st (V2 - 128) 0xa7ffc C1 C2 K0).
{ eapply PMHASK.callee_entry; first [exact BI3 | exact RI3 | exact mR1 | eassumption | (split; [lia| reflexivity]) | lia]. }
{ eapply PMHASK.callee_room; first [exact BI3 | eassumption | lia]. }
{ eapply PMHASK.callee_rs; eassumption. }
{ rewrite L5K.rl10. exact mR10. }
{ exists (F, 4, V2 - 128 + 32). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. lia. }
{ clear - FM8. lia. }
{ exact IO3. }
{ exact (proj1 LS3). }
intros fx4 R4 M4 model4 LK4 Aw4 RP4 HP4 MRT4 INCLK4 INCA4 AM4 HH4.
change (PMSPA.pm_scr 1) with 14336 in HP4.
assert (WFI : PMHAK2.wfi F [(F + 216, 152)]) by (apply PMHAK2.wfi_cons; [cbn [fst snd]; left; lia| apply PMHAK2.wfi_nil]).
assert (LS4 : PMSTA.ls_okA RSEGS PMB.AD PMB.AAD g M4).
{ apply (PMHAK.ls_ahpres L C LY g ar _ FF' (V2 - 128) 14336 [(F + 216, 152)] M3 M4 HP4); [| exact LS3].
apply PMHAK.far_cons; [cbn [fst snd]; clear - FR; lia| apply PMHAK.far_nil]. }
assert (BI4 : Bv W (PM.vs_own s) M4 model4 LK4 cr11 Aw4).
{ apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W W _ (PM.vs_own s) _ M3 model3 LK11 cr11 A11 M4 model4 LK4 cr11 Aw4 14336 [(F + 216, 152)] BI3 HP4 HH4 AM4 MRT4 INCA4 INCLK4).
- lia.
- clear - CLS; lia.
- intros rr a [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. unfold tocell. split; [clear - Ha FCEIL SLO CLS; lia|]. unfold HeapIfaceA.SB. change (ff_bytes 4) with 1024. clear - Ha FR F8 FBIG. lia.
- intros a Hc _ rr [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. apply (NCF a); [left; clear - Ha; lia| exact Hc].
- intros a X0. exact X0. }
assert (VS4 : PM.vstr_at RSEGS PMSPA.accA M4 (F + 32) s).
{ eapply PMHAK2.vstr_keep_callee; first [ exact LY | exact HIok | exact C1 | exact HP4 | exact VS3 | exact FHF | exact FIN1 | exact WFI | exact (or_introl eq_refl)
| (split; reflexivity) | (intros x Hx; apply in_or_app; left; exact Hx) | (apply PMHAK2.wapart_cons; [cbn [fst snd]; lia| apply PMHAK2.wapart_nil]) | lia ]. }
pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W _ M4 model4 LK4 cr11 Aw4 BI4)
as ((VW4 & VIC4 & VSB4 & VUAR4 & VMS4) & VOWN4 & (VFD4 & VFW4 & VFSW4 & VFLC4 & VFLW4) & (FLCc4 & FLV4 & FV4 & SPV4 & FSV4)).
change (ff_bytes 4) with 1024 in *. change (1024 / 8) with 128 in *.
set (H4 := ahid Aw4 model4) in *. set (MV4 := mrestrict H4 M4) in *.
assert (RI4 : rinvH R R4 V2 cls F) by exact (rinvH_pres R R2 R4 V2 cls F RI3 RP4).
pose proof RI4 as (Z2 & Z8 & Z9 & Z18 & Z19 & Z20 & Z24 & Z25 & Z3 & Z4 & Z27).
assert (S21 : getr R4 (reg 21) = Z_to_bv 64 (F + 96)) by (rewrite (cs_of_preserved R2 R4 21 RP4) by inl; rewrite (mKS 21%nat) by inl; exact Y21).
assert (S22 : getr R4 (reg 22) = Z_to_bv 64 1253448) by (rewrite (cs_of_preserved R2 R4 22 RP4) by inl; rewrite (mKS 22%nat) by inl; exact Y22).
assert (S23 : getr R4 (reg 23) = Z_to_bv 64 (F + 464)) by (rewrite (cs_of_preserved R2 R4 23 RP4) by inl; rewrite (mKS 23%nat) by inl; exact Y23).
assert (S26 : getr R4 (reg 26) = Z_to_bv 64 18446744073709551608) by (rewrite (cs_of_preserved R2 R4 26 RP4) by inl; rewrite (mKS 26%nat) by inl; exact Y26).
assert (Q5b : L5.writable RSEGS MV4 (V2 - 128) 128) by (eapply L5.writable_sub; [exact VW4| clear; lia| clear - CLS; lia]).
assert (Q6b : L5.u64_at RSEGS MV4 (F + 1016) fl) by (replace (F + 1016) with (F + 1024 - 8) by (clear; lia); exact VFLC4).
assert (AV32 : L5A.avis H4 (F + 32) 8) by (apply (PMHAK.avis_sub H4 F 1024 (F + 32) 8 FV4); lia).
assert (AV48 : L5A.avis H4 (F + 48) 8) by (apply (PMHAK.avis_sub H4 F 1024 (F + 48) 8 FV4); lia).
pose proof BI4 as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10).
set (W5 := fun a => F / 8 + 2147450892 <= a < F / 8 + 2147450892 + 34).
assert (WC5 : forall a, 0 <= a < 2 ^ 64 -> W5 a -> aclientw L ar (PM.vs_own s ++ LB) FF' 0 0 a /\ ~ (65536 <= a < 6893568)).
{ intros a Ha Wa. subst W5; cbn beta in Wa. split.
- apply (fframe_shadow_client L ar _ _ 0 0 F 4 (V2 - 128 + 32)). left; reflexivity. change (ff_bytes 4) with 1024.
unfold in_shadow_of, HeapIfaceA.S. rewrite (proj1 (proj2 F8)). unfold HeapIfaceA.SB. clear - Wa. lia.
- unfold HeapIfaceA.SB in *. clear - Wa FR. lia. }
destruct s as [n | c n p].
-
destruct VS4 as (_ & _ & (Hn & SB0)).
assert (SBv : L5.u8_at RSEGS MV4 (F + 32) (2 * n))
by (apply (proj2 (L5A.u8_at_vis H4 M4 (F + 32) (2 * n) (PMHAK.avis_sub H4 (F + 32) 8 (F + 32) 1 AV32 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact SB0).
pose proof (PMF.even_byte n) as EVB.
pose proof (PMBHP4.haNs_conc fx4 R4 MV4 (fun j => match j with 2%nat => V2 | 36%nat => 2 * n | 40%nat => F | 41%nat => fl | 58%nat => U R4 1 | _ => 0 end)) as P.
cbn beta iota in P.
feed P ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | (clear - Hn; lia) | exact F32
| exact VFD4 | exact VFW4 | exact VFSW4 | exact VFLW4 | exact Q5b | exact Q6b | exact SBv | exact EVB | (unfold PMBHP4.aligned; exact V2A) ]).
destruct P as (fx5 & R5 & M5v & MG5 & nFR & nFZ & (nMS & nKS & nR10 & nR21 & NQ)). clear NQ.
apply (apiece L ar C HI LYa HIok _ FF' LK4 cr11 Aw4 M4 model4 fx4 fx5 R4 0xa7ffc R5 0xa80a4 M5v W5 K D1 D2 nMS MG5).
{ intros a Ha Hna. apply nFZ; [exact Ha|..]; intros X0; apply Hna; subst W5; cbn beta; clear - X0; lia. }
{ exact WC5. }
intros M5 model5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5 VV5.
apply (KONT fx5 R5 M5 model5 LK4 Aw4).
+ apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W _ M4 model4 LK4 cr11 Aw4 M5 model5 W5 BI4 HH5 AM5 MRT5 MGM5 FR5).
intros a Wa. subst W5; cbn beta in Wa. right; right. change (ff_bytes 4) with 1024. change (1024 / 8) with 128. unfold HeapIfaceA.SB in *. clear - Wa. lia.
+ apply (rinvH_ks R R4 R5 V2 cls F PMBHP4.KS_haNs RI4 nKS); vm_compute; reflexivity.
+ apply (PMHAK.ls_piece _ M4 M5 W5 FR5); [intros a Wa; subst W5; cbn beta in Wa; clear - Wa FR; lia| exact LS4].
+ exact nR21.
+ rewrite (nKS 22%nat) by inl. exact S22.
+ rewrite (nKS 23%nat) by inl. exact S23.
+ rewrite (nKS 26%nat) by inl. exact S26.
-
destruct VS4 as (_ & _ & (TW0 & TW8 & TW16 & Hn & Hc & Hc2 & TBP & _)).
replace (F + 32 + 16) with (F + 48) in TW16 by lia.
assert (Hc64 : 0 <= c + 1 < 2 ^ 64) by lia.
pose proof (PMF.u8_of_u64 RSEGS M4 _ _ Hc64 TW0) as SB0.
pose proof (PMF.odd_byte c Hc2 ltac:(lia)) as ODB.
pose proof (Z.mod_pos_bound (c + 1) 256 ltac:(lia)) as HVB.
assert (SBv : L5.u8_at RSEGS MV4 (F + 32) ((c + 1) mod 256))
by (apply (proj2 (L5A.u8_at_vis H4 M4 (F + 32) _ (PMHAK.avis_sub H4 (F + 32) 8 (F + 32) 1 AV32 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact SB0).
assert (TW0v : L5.u64_at RSEGS MV4 (F + 32) (c + 1)) by (apply (proj2 (L5A.u64_at_vis H4 M4 (F + 32) _ AV32 ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact TW0).
assert (TW16v : L5.u64_at RSEGS MV4 (F + 48) p) by (apply (proj2 (L5A.u64_at_vis H4 M4 (F + 48) _ AV48 ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact TW16).
assert (INP : In (p, c) (PM.vs_own (PM.VLong c n p) ++ LB)) by (left; reflexivity).
destruct (PMHAK.blk_facts L ar C SCFG HI HIok _ _ _ _ _ _ _ p c D1 INP) as (P0 & _ & _ & _ & _ & P47 & _).
pose proof (PMBHP4.haNl_conc fx4 R4 MV4 (fun j => match j with 2%nat => V2 | 36%nat => (c + 1) mod 256 | 37%nat => c + 1 | 38%nat => p
| 40%nat => F | 41%nat => fl | 58%nat => U R4 1 | _ => 0 end)) as P.
cbn beta iota in P.
feed P ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | (clear - HVB; lia) | (clear - Hc64; lia) | (clear - P0 P47 Hc; lia)
| exact F32 | exact VFD4 | exact VFW4 | exact VFSW4 | exact VFLW4 | exact Q5b | exact Q6b | exact SBv | exact TW0v | exact TW16v | exact ODB
| (unfold PMBHP4.aligned; exact V2A) ]).
destruct P as (fx5 & R5 & M5v & MG5 & nFR & nFZ & (nMS & nKS & nR1 & nR10 & nR11 & nR21 & NQ)). clear NQ.
apply (apiece L ar C HI LYa HIok _ FF' LK4 cr11 Aw4 M4 model4 fx4 fx5 R4 0xa7ffc R5 0xd0890 M5v W5 K D1 D2 nMS MG5).
{ intros a Ha Hna. apply nFZ; [exact Ha|..]; intros X0; apply Hna; subst W5; cbn beta; clear - X0; lia. }
{ exact WC5. }
intros M5 model5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5 VV5.
assert (BI5 : Bv W (PM.vs_own (PM.VLong c n p)) M5 model5 LK4 cr11 Aw4).
{ apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W _ M4 model4 LK4 cr11 Aw4 M5 model5 W5 BI4 HH5 AM5 MRT5 MGM5 FR5).
intros a Wa. subst W5; cbn beta in Wa. right; right. change (ff_bytes 4) with 1024. change (1024 / 8) with 128. unfold HeapIfaceA.SB in *. clear - Wa. lia. }
assert (RI5 : rinvH R R5 V2 cls F) by (apply (rinvH_ks R R4 R5 V2 cls F PMBHP4.KS_haNl RI4 nKS); vm_compute; reflexivity).
assert (LS5 : PMSTA.ls_okA RSEGS PMB.AD PMB.AAD g M5) by (apply (PMHAK.ls_piece _ M4 M5 W5 FR5); [intros a Wa; subst W5; cbn beta in Wa; clear - Wa FR; lia| exact LS4]).
pose proof BI5 as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10).
assert (ASX : L5CA.astk ar M5 (V2 - 128) (PMSPA.pm_scr 0) /\ shadow_zero M5 (V2 - 128 - PMSPA.pm_scr 0) (PMSPA.pm_scr 0 / 8))
by (eapply PMHASK.callee_stack; first [exact BI5 | eassumption | lia]).
destruct ASX as (AS0 & _). change (PMSPA.pm_scr 0) with 12288 in AS0.
pose proof RI5 as (U2 & U8 & U9 & U18 & U19 & U20 & U24 & U25 & U3 & U4 & U27).
unfold PMB.opdel_spec, PMSPA.opdel_spec, PMSPA.opdel_spec_at in OPD. cbn [pa_opdel PMB.AD ADDR_A] in OPD.
apply (OPD fx5 R5 M5 model5 K _ FF' LK4 Aw4 cr11 p c (V2 - 128) 0xa80a4 E1 E2 K0 INP).
{ rewrite L5K.rl10. exact nR10. }
{ rewrite L5K.rl1. exact nR1. }
{ split; [lia| reflexivity]. }
{ rewrite L5K.rl2. exact U2. }
{ rewrite L5K.rl4. rewrite U4. exact TP. }
{ replace (V2 - 128) with (V2 - 128 - 0) by lia. apply (L5SAR.astk_sub ar M5 M5 (V2 - 128) 12288 0 PMSPA.OPDEL_SCR AS0 (fun _ X0 => X0));
[lia| unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR; lia| unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR; lia|].
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - V2A. lia. }
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
intros fx6 R6 M6 model6 Aw6 RP6 HPo MRT6 INCA6 AM6 HHo.
cbn [PM.vs_own app] in HPo, HHo.
rewrite L5ADHR.lb_remove_head in HPo, HHo.
unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR in HPo.
apply (KONT fx6 R6 M6 model6 LK4 Aw6).
+ apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W W _ [] [] M5 model5 LK4 cr11 Aw4 M6 model6 LK4 cr11 Aw6 4096 [] BI5 HPo HHo AM6 MRT6 INCA6 (incl_refl _)).
* lia.
* clear - CLS; lia.
* intros rr a [].
* intros a _ _ rr [].
* intros a X0. exact X0.
+ exact (rinvH_pres R R5 R6 V2 cls F RI5 RP6).
+ apply (PMHAK.ls_ahpres L C LY g ar _ FF' (V2 - 128) 4096 [] M5 M6 HPo PMHAK.far_nil LS5).
+ rewrite (cs_of_preserved R5 R6 21 RP6) by inl. exact nR21.
+ rewrite (cs_of_preserved R5 R6 22 RP6) by inl. rewrite (nKS 22%nat) by inl. exact S22.
+ rewrite (cs_of_preserved R5 R6 23 RP6) by inl. rewrite (nKS 23%nat) by inl. exact S23.
+ rewrite (cs_of_preserved R5 R6 26 RP6) by inl. rewrite (nKS 26%nat) by inl. exact S26.
Qed.
End Stage.
End SCFG_1.
End PMHA10.
