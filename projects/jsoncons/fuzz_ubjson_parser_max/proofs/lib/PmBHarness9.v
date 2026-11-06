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
L5CoreAB0 L5StepARB0 L5CoreBRB0 L5ADetailHRB0 L5AFrameKRB0 HeapIfaceAJx PmLayout PmLayoutA PmModel PmModelFacts PmModelFactsA PmStatics PmStaticsA PmSpecsA PmSpecsAb PmStepAB0 PmBReset1 PmBHarnessStmts PmBHarnessKit PmBHarnessKit2 PmBHarnessSK PmBSrcKit PmBHarnessP3.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBHarness9 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5DefsAB0.L5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBHarnessKit2.PMHAK2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBHarnessStmts.PMHAS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAb.PMB."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStatics.PMST."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStaticsA.PMSTA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5AFrameKRB0.L5AFKR."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0A10"; "0A11"; "1app"; "1cons"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "2eq"; "3Z"; "0F"; "0FF"; "0HI"; "0K"]; ["0L"; "0LB"; "0LK"; "0LK10"; "0LK11"; "4Model"; "4event"; "5bvmap"; "0M"; "0M10"; "0M11"; "0OPD"; "0R"; "0R10"; "0R11"; "6credit"]; ["7fframe"; "8SCFG"; "9cfg"; ":hbase"; ":hfin"; ":hsrc"; ";rinvH"; ";tfrk"; "<AADDR_B"; "<ADDR_B"; "=CHUNK"; "=sm_st"; "=sr_qc"; "=srcst"; "=strm"; "=vs_own"]; ["=vstr"; ">opdel_spec"; ">src_dtor_spec"; "?st"; "@ls_okA"; "AFPState"; "Agetr"; "BTSet"; "Csrealizes"; "Dbinv"; "Eloaded_segments"; "0SCFG_P"; "0SRCD"; "Fadd"; "Fof_nat"; "Fsub"]; ["0V2"; "0W"; "0ar"; "0cls"; "0cr10"; "0fx10"; "0fx11"; "0g"; "0model"; "0model10"; "0model11"; "0s"; "0sm"; "0src"; "GZ_to_bv"; "Gbv"]; ["0str"]]).
Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module PMHA9.
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
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Local Notation Bv := (L5AFKR.binv L ar HI M model LB FF LK A (V2 + cls) 36864 (V2 - 128) (tfrk (V2 + cls) R) F 4).
Local Notation FF' := ((F, 4, V2 - 128 + 32) :: FF).
Ltac hsolve := first [ exact LY | exact HIok | eassumption | exact (or_introl eq_refl) | (split; reflexivity) | apply incl_refl
| (apply PMHAK2.wapart_cons; [cbn [fst snd]; lia| first [apply PMHAK2.wapart_nil | (apply PMHAK2.wapart_cons; [cbn [fst snd]; lia| apply PMHAK2.wapart_nil])]])
| (apply PMHAK2.wapart_nil) | lia ].
Lemma stage9 : ltac2:(TCodec.tc2 tcn__PmBHarness9 "WC&QBvQKv@vR2v>%544321&QA%146543'QE&Gy5'R?yR0%211%5241'7y8%611%311p061'E&QG'5&Q0%211&O'9';%2211%711'Q@'Q>'Q='QC&QIvHvR8vAv=vBv0&QMvR0vR3%3221+QTP0&QO+T0%2261&Q7vL%2271v<+4vR1(4(8&Q<r2%211&Q:%54Q2Q221&3&Q?r4%211r5%411%63Q831%>3Q981r;r:r8r7r6%Q9FR9R8R7Q8Q7Q6Q5Q4Q3ONKHGFE654321&Q6r=%25L1Q4Q3J(6'F%211%<11&QD&QJ&Q9&Q8r>%55432H1':&QFr@&R>&QNu1%211%42RF1%7261+doc@%72RG1%;3RG31rAu:%:11%<2RN1%?241+_8%R22QG1%@2S01%D3S041rBuE%C11%E2S71%H241+S0%R;2R01%I2S91%M3S941rCuF%L11%N2S@1%Q1241+o0%RD2R91%Q22SB1%Q63SB41rDuG%Q511%Q72SI1%Q:241+^@%RM2RB1%Q;2SK1%Q?3SK41rEuJ%Q>11%Q@2T21%QC241+_oooooooooooH%QC2T31%QG3T331&Q3r?%25RO:1QLR6&Q5rF%23S21R9rG%RI11r3rIr1%SJFTJTITHSISHSGSFSESDS@S?S<S9S8S7S64RL3S221%RA5S;RCSCSBS9%R;5R:R9R8ERD%R52RGQO+doo8%R52TE1%R93TE31r9%R:21QL+SH%SM2SB1%R;2TK1%R?3TK41%R?2S2QH%RA3TM1QE%RA2S5QA+QVXR8%RA2U11%RE3U131r<%RF21Q=%RH3U41Q:%RH2S5Q6%RJ3U61Q4&Q4rQ0&Q;rN%211%54T5S<41'QH&Q1%11UK&Q2+o_a4%25S4Q=1S8SBrQ5%74S=521p091p0@1p0C1p0G1p0L1p0O1p0Q61p0Q;1p0Q=1p0Q?1p6U?1pQ:UE1pTFUJ1pQFUL1pQNV21pT>V91rJ+eZkLrH%H53QK21QN%L4T2J1R1p061p0R21p0R61p0R:1p0RC1p0RM1p0S71p0SA1p0SK1p0T81p0T?1p0TD1p0TH1pT@V31pTLV51pTJV71pU2V91pTHV:1p4V<1pT:VA1pQ8VC1pQ0VG1pTDVI1pQDVK1pQLW11pT<W81pQHW:1pSJW=1").
Proof. intros SRCD OPD fx10 R10 M10 model10 K LK10 cr10 A10 s str sm src g.
intros BI RI K0 LS R1a R10a R21 R22 R23 R26 HB0 HS0 KONT.
pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
change (ff_bytes 4) with 1024 in *. change (1024 / 8) with 128 in *.
pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
pose proof RI as (X2 & X8 & X9 & X18 & X19 & X20 & X24 & X25 & X3 & X4 & X27).
assert (FM8 : F mod 8 = 0) by (pose proof (proj1 F8) as E8; clear - E8; lia).
assert (FHF : PMHAK2.hf F) by (unfold PMHAK2.hf, BIGSHADOW_LO, BIGSHADOW_HI; clear - FR FBIG FM8; lia).
set (X := PM.vs_own str ++ PM.vs_own s) in *.
cbn [app] in B1.
pose proof HS0 as (SF0 & NI0). pose proof LS as (LSB & LSL & LSS & LSE).
unfold PMB.src_dtor_spec, PMSPA.src_dtor_spec in SRCD. cbn [pa_src_dtor PMB.AD ADDR_A] in SRCD.
apply (SRCD fx10 R10 M10 model10 K _ FF' LK10 A10 cr10 (F + 488) (F + 96) (F + 112) (V2 - 128) 0xa7e70 src B1 B2 K0).
{ eapply PMHASK.callee_entry; first [exact BI | exact RI | exact R1a | eassumption | (split; [lia| reflexivity]) | lia]. }
{ eapply PMHASK.callee_room; first [exact BI | eassumption | lia]. }
{ eapply PMHASK.callee_rs; eassumption. }
{ rewrite L5K.rl10. exact R10a. }
{ exists (F, 4, V2 - 128 + 32). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. lia. }
{ clear - FM8. lia. }
{ exact SF0. }
{ replace (F + 488 + 8) with (F + 496) by lia. exact NI0. }
{ left. reflexivity. }
{ exact LSB. }
intros fx' R' M' model' LK' Aw' RP' HP' MRT' INCLK' INCA' AM' HH'.
change (PMSPA.pm_scr 2) with 16384 in HP'.
rewrite L5ADHR.lb_remove_head in HP', HH'.
assert (WFI : PMHAK2.wfi F [(F + 488, 296)]) by (apply PMHAK2.wfi_cons; [cbn [fst snd]; left; lia| apply PMHAK2.wfi_nil]).
assert (LS' : PMSTA.ls_okA RSEGS PMB.AD PMB.AAD g M').
{ apply (PMHAK.ls_ahpres L C LY g ar _ FF' (V2 - 128) 16384 [(F + 488, 296)] M10 M' HP'); [| exact LS].
apply PMHAK.far_cons; [cbn [fst snd]; clear - FR; lia| apply PMHAK.far_nil]. }
assert (BI' : Bv W X M' model' LK' cr10 Aw').
{ apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W W _ X X M10 model10 LK10 cr10 A10 M' model' LK' cr10 Aw' 16384 [(F + 488, 296)] BI HP' HH' AM' MRT' INCA' INCLK').
- lia.
- clear - CLS; lia.
- intros rr a [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. unfold tocell. split; [clear - Ha FCEIL SLO CLS; lia|]. unfold HeapIfaceA.SB. change (ff_bytes 4) with 1024. clear - Ha FR F8 FBIG. lia.
- intros a Hc _ rr [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. apply (NCF a); [left; clear - Ha; lia| exact Hc].
- intros a X0. exact X0. }
pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W _ M' model' LK' cr10 Aw' BI')
as ((VW' & VIC' & VSB' & VUAR' & VMS') & VOWN' & (VFD' & VFW' & VFSW' & VFLC' & VFLW') & (FLCc' & FLV' & FV' & SPV' & FSV')).
change (ff_bytes 4) with 1024 in *. change (1024 / 8) with 128 in *.
set (H' := ahid Aw' model') in *. set (MV' := mrestrict H' M') in *.
assert (RI' : rinvH R R' V2 cls F) by exact (rinvH_pres R R10 R' V2 cls F RI RP').
pose proof RI' as (Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y24 & Y25 & Y3 & Y4 & Y27).
assert (Y21 : getr R' (reg 21) = Z_to_bv 64 (F + 96)) by (rewrite (cs_of_preserved R10 R' 21 RP') by inl; exact R21).
assert (Y22 : getr R' (reg 22) = Z_to_bv 64 (F + 992)) by (rewrite (cs_of_preserved R10 R' 22 RP') by inl; exact R22).
assert (Y23 : getr R' (reg 23) = Z_to_bv 64 (F + 464)) by (rewrite (cs_of_preserved R10 R' 23 RP') by inl; exact R23).
assert (Y26 : getr R' (reg 26) = Z_to_bv 64 18446744073709551608) by (rewrite (cs_of_preserved R10 R' 26 RP') by inl; exact R26).
assert (FIN10 : In (F, 4, V2 - 128 + 32) (FF' ++ LK10)) by (apply in_or_app; left; left; reflexivity).
assert (HB' : PMHAK2.hbase F M' s str sm).
{ eapply PMHAK2.hbase_callee; first [ exact LY | exact HIok | exact B1 | exact HP' | exact HB0 | exact FHF | exact FIN10 | exact WFI | exact (or_introl eq_refl)
| (split; reflexivity) | (intros x Hx; right; apply in_or_app; left; exact Hx) | (intros x Hx; apply in_or_app; left; exact Hx)
| (apply PMHAK2.wapart_cons; [cbn [fst snd]; lia| apply PMHAK2.wapart_nil]) | lia ]. }
pose proof HB' as (VS' & IS' & VV' & VZ' & VI').
assert (Q1 : 4096 <= F <= 140737488354304) by (clear - FR; lia).
assert (Q2 : 4096 <= fl <= 140737488355327) by (clear - FLR; lia).
assert (Q3 : V2 - 128 + 144 <= F \/ F + 1024 <= V2 - 128) by (clear - FCEIL SLO CLS; lia).
assert (Q4 : V2 - 128 + 144 <= fl \/ fl + 1 <= V2 - 128) by (clear - FLR SLO CLS; lia).
assert (Q7 : 65536 + 6828032 <= F \/ F + 1024 <= 65536) by (clear - FR; lia).
assert (Q8 : 65536 + 6828032 <= fl \/ fl + 1 <= 65536) by (clear - FLR; lia).
assert (Q5 : L5.writable RSEGS MV' (V2 - 128) 128) by (eapply L5.writable_sub; [exact VW'| clear; lia| clear - CLS; lia]).
assert (Q6 : L5.u64_at RSEGS MV' (F + 1016) fl) by (replace (F + 1016) with (F + 1024 - 8) by (clear; lia); exact VFLC').
pose proof (PMBHP3.haK1_conc fx' R' MV' (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U R' 1 | _ => 0 end)) as P.
cbn beta iota in P.
feed P ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
| exact VFD' | exact VFW' | exact VFSW' | exact VFLW' | exact Q5 | exact Q6 | exact VSB' | exact VUAR' | exact VIC' | (unfold PMBHP3.aligned; exact V2A) ]).
destruct P as (fx1 & R1 & M1v & MG1 & kFR & kFZ & (kMS & kKS & kR10 & kR11 & kR22 & KQ)). clear KQ.
assert (kR23 : getr R1 (reg 23) = Z_to_bv 64 (F + 464)) by (rewrite (kKS 23%nat) by inl; exact Y23).
set (W1 := fun a => F / 8 + 2147450934 <= a < F / 8 + 2147450934 + 1 \/ F / 8 + 2147450938 <= a < F / 8 + 2147450938 + 49).
apply (apiece L ar C HI LYa HIok _ FF' LK' cr10 Aw' M' model' fx' fx1 R' 0xa7e70 R1 0xa7f44 M1v W1 K HH' AM' kMS MG1).
{ intros a Ha Hna. apply kFZ; [exact Ha|..]; intros X0; apply Hna; subst W1; cbn beta; clear - X0; lia. }
{ intros a Ha Wa. subst W1; cbn beta in Wa. split.
- apply (fframe_shadow_client L ar _ _ 0 0 F 4 (V2 - 128 + 32)). left; reflexivity. change (ff_bytes 4) with 1024.
unfold in_shadow_of, HeapIfaceA.S. rewrite (proj1 (proj2 F8)). unfold HeapIfaceA.SB. clear - Wa. lia.
- unfold HeapIfaceA.SB in *. clear - Wa FR. lia. }
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
assert (BI1 : Bv W X M1 model1 LK' cr10 Aw').
{ apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W _ M' model' LK' cr10 Aw' M1 model1 W1 BI' HH1 AM1 MRT1 MGM1 FR1).
intros a Wa. subst W1; cbn beta in Wa. right; right. change (ff_bytes 4) with 1024. change (1024 / 8) with 128. unfold HeapIfaceA.SB in *. clear - Wa. lia. }
assert (RI1 : rinvH R R1 V2 cls F) by (apply (rinvH_ks R R' R1 V2 cls F PMBHP3.KS_haK1 RI' kKS); vm_compute; reflexivity).
assert (LS1 : PMSTA.ls_okA RSEGS PMB.AD PMB.AAD g M1) by (apply (PMHAK.ls_piece _ M' M1 W1 FR1); [intros a Wa; subst W1; cbn beta in Wa; clear - Wa FR; lia| exact LS']).
assert (PF1 : PMHAK2.pfoot F (V2 - 128) V2 W1) by (intros a Wa; subst W1; cbn beta in Wa; unfold HeapIfaceA.SB; clear - Wa; lia).
assert (FIN' : In (F, 4, V2 - 128 + 32) (FF' ++ LK')) by (apply in_or_app; left; left; reflexivity).
assert (SLOW : ahl_ceil ar <= V2 - 128) by (clear - SLO CLS; lia).
assert (SHW : BIGSHADOW_HI <= V2 - 128) by (unfold BIGSHADOW_HI; clear - V2R; lia).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
assert (OA1 : forall o n, F + 32 <= o -> o + n <= F + 368 -> PMHAK2.oav W1 o n).
{ intros o n H1 H2 x Hx. subst W1; cbn beta. pose proof (PMKB.S_in_shadow x ltac:(clear - Hx H1 H2 FR; lia)) as SX.
unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *. split; intros X0; clear - Hx X0 H1 H2 SX FBIG FR FM8; lia. }
assert (E96 : (F + 96) / 8 = F / 8 + 12) by (clear - FM8; lia).
assert (FBD : 0 <= F / 8 /\ F / 8 + 128 <= 2 ^ 44) by (clear - FR; lia).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
assert (INS : incl (PM.vs_own s) (X ++ LB)) by (intros x Hx; apply in_or_app; left; subst X; apply in_or_app; right; exact Hx).
assert (INT : incl (PM.vs_own str) (X ++ LB)) by (intros x Hx; apply in_or_app; left; subst X; apply in_or_app; left; exact Hx).
assert (VS1 : PM.vstr_at RSEGS PMSPA.accA M1 (F + 32) s)
by (apply (PMHAK2.vstr_keep_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 W1 M' M1 SLOW SHW FR1 PF1 (F + 32) s INS); [clear - FR; lia| clear - FR; lia| apply OA1; lia| exact VS']).
assert (IS1 : PM.iss_at RSEGS PMB.AD PMSPA.accA M1 (F + 96) str sm)
by (apply (PMHAK2.iss_keep_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 W1 M' M1 SLOW SHW FR1 PF1 (F + 96) str sm INT); [clear - FR; lia| clear - FR; lia| apply OA1; lia| exact IS']).
assert (VI1 : shadow_zero M1 (F + 96) 34).
{ apply (PMHAK2.shz_frame M' M1 W1 (F + 96) 34 FR1); [| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| exact VI'].
intros j Hj X0. subst W1; cbn beta in X0. unfold HeapIfaceA.S, HeapIfaceA.SB in X0. rewrite E96 in X0. clear - X0 Hj. lia. }
pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W _ M1 model1 LK' cr10 Aw' BI1)
as ((VW1 & VIC1 & VSB1 & VUAR1 & VMS1) & VOWN1 & (VFD1 & VFW1 & VFSW1 & VFLC1 & VFLW1) & (FLCc1 & FLV1 & FV1 & SPV1 & FSV1)).
change (ff_bytes 4) with 1024 in *. change (1024 / 8) with 128 in *.
set (H1' := ahid Aw' model1) in *. set (MV1 := mrestrict H1' M1) in *.
assert (Q5b : L5.writable RSEGS MV1 (V2 - 128) 128) by (eapply L5.writable_sub; [exact VW1| clear; lia| clear - CLS; lia]).
assert (Q6b : L5.u64_at RSEGS MV1 (F + 1016) fl) by (replace (F + 1016) with (F + 1024 - 8) by (clear; lia); exact VFLC1).
assert (ZI : L5KA.zeros_at MV1 (F / 8 + 2147450892) 34).
{ apply (proj2 (L5A.zeros_at_vis H1' M1 (F / 8 + 2147450892) 34 (PMHAK.avis_sub H1' (F / 8 + HeapIfaceA.SB) 128 (F / 8 + 2147450892) 34 FSV1 ltac:(unfold HeapIfaceA.SB; lia) ltac:(unfold HeapIfaceA.SB; lia)))).
replace (F / 8 + 2147450892) with (HeapIfaceA.S (F + 96)) by (unfold HeapIfaceA.S, HeapIfaceA.SB; rewrite E96; lia). apply PMHAK2.zeros_of_shz. exact VI1. }
assert (ZV1 : L5KA.zeros_at MV1 2147607561 1).
{ pose proof (PMBSK.img_shz_vis L ar C HI LY IL ICok ILY _ _ _ _ _ M1 model1 0x132048 1 HH1 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(first [left; lia | right; left; lia | right; right; lia])) as Z0.
exact Z0. }
assert (ZV2 : L5KA.zeros_at MV1 2147607564 1).
{ pose proof (PMBSK.img_shz_vis L ar C HI LY IL ICok ILY _ _ _ _ _ M1 model1 0x132060 1 HH1 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(first [left; lia | right; left; lia | right; right; lia])) as Z0.
exact Z0. }
assert (ZV3 : L5KA.zeros_at MV1 2147607551 1).
{ pose proof (PMBSK.img_shz_vis L ar C HI LY IL ICok ILY _ _ _ _ _ M1 model1 0x131ff8 1 HH1 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(first [left; lia | right; left; lia | right; right; lia])) as Z0.
exact Z0. }
pose proof IS1 as (IH0 & ID & IC & IH16 & IH24 & IH32 & IH40 & IH48 & IH64 & IVS & IH104 & IH112 & IOS & IE1 & IE2).
replace (F + 96 + 24) with (F + 120) in IH24 by lia. replace (F + 96 + 80) with (F + 176) in IVS by lia.
replace (F + 96 + 120) with (F + 216) in IOS by lia. replace (F + 96 + 16) with (F + 112) in IOS by lia.
assert (FDEF1 : L5.defined M1 F 1024) by (apply (proj1 (L5A.defined_vis H1' M1 F 1024 FV1)); exact VFD1).
assert (AV176 : L5A.avis H1' (F + 176) 8) by (apply (PMHAK.avis_sub H1' F 1024 (F + 176) 8 FV1); lia).
assert (AV192 : L5A.avis H1' (F + 192) 8) by (apply (PMHAK.avis_sub H1' F 1024 (F + 192) 8 FV1); lia).
set (W2 := fun a => F + 96 <= a < F + 96 + 8 \/ F + 112 <= a < F + 112 + 8 \/ F + 216 <= a < F + 216 + 8).
assert (WC2 : forall a, 0 <= a < 2 ^ 64 -> W2 a -> aclientw L ar (X ++ LB) FF' 0 0 a /\ ~ (65536 <= a < 6893568)).
{ intros a Ha Wa. subst W2; cbn beta in Wa. split.
- apply (fframe_client L ar _ _ 0 0 F 4 (V2 - 128 + 32)). left; reflexivity. change (ff_bytes 4) with 1024. clear - Wa; lia.
- clear - Wa FR. lia. }
assert (PF2 : PMHAK2.pfoot F (V2 - 128) V2 W2) by (intros a Wa; subst W2; cbn beta in Wa; clear - Wa; lia).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
assert (OA2 : forall o n, (F + 32 <= o /\ o + n <= F + 96) \/ (F + 120 <= o /\ o + n <= F + 216) \/ (F + 224 <= o /\ o + n <= F + 1016) -> PMHAK2.oav W2 o n).
{ intros o n H12 x Hx. subst W2; cbn beta. pose proof (PMKB.S_in_shadow x ltac:(clear - Hx H12 FR; lia)) as SX.
unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *. split; intros X0; clear - Hx X0 H12 SX FBIG FR FM8; lia. }
assert (SH2 : forall x, F + 216 <= x < F + 368 -> ~ W2 (HeapIfaceA.S x)).
{ intros x Hx. subst W2; cbn beta. pose proof (PMKB.S_in_shadow x ltac:(clear - Hx FR; lia)) as SX.
unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *. intros X0; clear - Hx X0 SX FBIG FR FM8; lia. }
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
destruct str as [nt | c nt p].
-
destruct IVS as (_ & _ & (Hnt & SB0)).
assert (SBv : L5.u8_at RSEGS MV1 (F + 176) (2 * nt))
by (apply (proj2 (L5A.u8_at_vis H1' M1 (F + 176) (2 * nt) (PMHAK.avis_sub H1' (F + 176) 8 (F + 176) 1 AV176 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact SB0).
pose proof (PMF.even_byte nt) as EVB.
pose proof (PMBHP3.haK2s_conc fx1 R1 MV1 (fun j => match j with 2%nat => V2 | 36%nat => 2 * nt | 40%nat => F | 41%nat => fl | 58%nat => U R1 1 | _ => 0 end)) as P.
cbn beta iota in P.
pose proof RI1 as (Z2 & Z8 & Z9 & Z18 & Z19 & Z20 & Z24 & Z25 & Z3 & Z4 & Z27).
assert (T21 : getr R1 (reg 21) = Z_to_bv 64 (F + 96)) by (rewrite (kKS 21%nat) by inl; exact Y21).
assert (T22 : getr R1 (reg 22) = Z_to_bv 64 1253448) by exact kR22.
assert (T26 : getr R1 (reg 26) = Z_to_bv 64 18446744073709551608) by (rewrite (kKS 26%nat) by inl; exact Y26).
feed P ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | (clear - Hnt; lia) | exact F32
| exact VFD1 | exact VFW1 | exact VFSW1 | exact VFLW1 | exact Q5b | exact Q6b | exact VSB1 | exact VUAR1 | exact VIC1 | exact ZI | exact ZV1 | exact ZV2 | exact ZV3
| exact SBv | exact EVB | (unfold PMBHP3.aligned; exact V2A) ]).
destruct P as (fx2 & R2 & M2v & MG2 & sFR & sFZ & (sMS & sKS & sR1 & sR10 & sR11 & sR12 & sU112 & sU216 & sU96 & sD1 & sD2 & sD3 & sD4)).
apply (apiece L ar C HI LYa HIok _ FF' LK' cr10 Aw' M1 model1 fx1 fx2 R1 0xa7f44 R2 0xfbe24 M2v W2 K HH1 AM1 sMS MG2).
{ intros a Ha Hna. apply sFZ; [exact Ha|..]; intros X0; apply Hna; subst W2; cbn beta; clear - X0; lia. }
{ exact WC2. }
intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
assert (FDEF3 : L5.defined M3 F 1024) by (eapply L5.defined_grows; [exact MGM3| exact FDEF1]).
apply (KONT fx2 R2 M3 model3 LK' Aw').
+ apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W _ M1 model1 LK' cr10 Aw' M3 model3 W2 BI1 HH3 AM3 MRT3 MGM3 FR3).
intros a Wa. subst W2; cbn beta in Wa. right; left. change (ff_bytes 4) with 1024. clear - Wa. lia.
+ apply (rinvH_ks R R1 R2 V2 cls F PMBHP3.KS_haK2s RI1 sKS); vm_compute; reflexivity.
+ apply (PMHAK.ls_piece _ M1 M3 W2 FR3); [intros a Wa; subst W2; cbn beta in Wa; clear - Wa FR; lia| exact LS1].
+ exact sR1.
+ exact sR10.
+ rewrite (sKS 21%nat) by inl. exact T21.
+ rewrite (sKS 22%nat) by inl. exact T22.
+ rewrite (sKS 23%nat) by inl. exact kR23.
+ rewrite (sKS 26%nat) by inl. exact T26.
+ split; [|split].
* apply (PMHAK2.vstr_keep_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH1 FIN' FHF (V2 - 128) V2 W2 M1 M3 SLOW SHW FR3 PF2 (F + 32) s INS);
[clear - FR; lia| clear - FR; lia| apply OA2; lia| exact VS1].
* apply (PMHAK2.u64_agA M1 M3 (F + 120) 8 (F + 120) _ (PMHAK.agA_frame M1 M3 W2 (F + 120) 8 FR3 ltac:(clear - FR; lia) ltac:(clear - FR; lia) (OA2 (F + 120) 8 ltac:(lia))));
[lia| lia| lia| lia| cbn [pa_classic_imp PMB.AD ADDR_A]; exact IH24].
* apply (PMHAK2.iosb_revptr M1 M3 (F + 216) _ 1253432 (F + 112) (PM.sm_st sm) IOS).
-- apply (PMHAK.u64_vis H1' M3 M2v (F + 216) _ VV3 (PMHAK.avis_sub H1' F 1024 (F + 216) 8 FV1 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia)). exact sU216.
-- intros i Hi. apply FR3; [clear - Hi FR; lia| subst W2; cbn beta; clear - Hi; lia].
-- intros x Hx. apply FR3; [pose proof (PMKB.S_in_shadow x ltac:(clear - Hx FR; lia)) as SX; unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; clear - SX; lia| apply SH2; lia].
-- apply (L5.defined_sub M3 F 1024 (F + 216) 8 FDEF3); lia.
-- clear - FR; lia.
-- clear - FR; lia.
-
destruct IVS as (_ & _ & (TW0 & TW8 & TW16 & Hnt & Hc & Hc2 & TBP & _)).
replace (F + 176 + 16) with (F + 192) in TW16 by lia.
assert (Hc64 : 0 <= c + 1 < 2 ^ 64) by lia.
pose proof (PMF.u8_of_u64 RSEGS M1 _ _ Hc64 TW0) as SB0.
pose proof (PMF.odd_byte c Hc2 ltac:(lia)) as ODB.
pose proof (Z.mod_pos_bound (c + 1) 256 ltac:(lia)) as HVB.
assert (SBv : L5.u8_at RSEGS MV1 (F + 176) ((c + 1) mod 256))
by (apply (proj2 (L5A.u8_at_vis H1' M1 (F + 176) _ (PMHAK.avis_sub H1' (F + 176) 8 (F + 176) 1 AV176 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact SB0).
assert (TW0v : L5.u64_at RSEGS MV1 (F + 176) (c + 1)) by (apply (proj2 (L5A.u64_at_vis H1' M1 (F + 176) _ AV176 ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact TW0).
assert (TW16v : L5.u64_at RSEGS MV1 (F + 192) p) by (apply (proj2 (L5A.u64_at_vis H1' M1 (F + 192) _ AV192 ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact TW16).
assert (INP : In (p, c) (X ++ LB)) by (subst X; cbn [PM.vs_own app]; left; reflexivity).
destruct (PMHAK.blk_facts L ar C SCFG HI HIok _ _ _ _ _ _ _ p c HH1 INP) as (P0 & _ & _ & _ & _ & P47 & _).
pose proof (PMBHP3.haK2l_conc fx1 R1 MV1 (fun j => match j with 2%nat => V2 | 36%nat => (c + 1) mod 256 | 37%nat => c + 1 | 38%nat => p
| 40%nat => F | 41%nat => fl | 58%nat => U R1 1 | _ => 0 end)) as P.
cbn beta iota in P.
pose proof RI1 as (Z2 & Z8 & Z9 & Z18 & Z19 & Z20 & Z24 & Z25 & Z3 & Z4 & Z27).
assert (T21 : getr R1 (reg 21) = Z_to_bv 64 (F + 96)) by (rewrite (kKS 21%nat) by inl; exact Y21).
assert (T22 : getr R1 (reg 22) = Z_to_bv 64 1253448) by exact kR22.
assert (T26 : getr R1 (reg 26) = Z_to_bv 64 18446744073709551608) by (rewrite (kKS 26%nat) by inl; exact Y26).
feed P ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | (clear - HVB; lia) | (clear - Hc64; lia) | (clear - P0 P47 Hc; lia)
| exact F32 | exact VFD1 | exact VFW1 | exact VFSW1 | exact VFLW1 | exact Q5b | exact Q6b | exact VSB1 | exact VUAR1 | exact VIC1 | exact ZI | exact ZV1 | exact ZV2 | exact ZV3
| exact SBv | exact TW0v | exact TW16v | exact ODB | (unfold PMBHP3.aligned; exact V2A) ]).
destruct P as (fx2 & R2 & M2v & MG2 & lFR & lFZ & (lMS & lKS & lR1 & lR10 & lR11 & lR12 & lU112 & lU216 & lU96 & lD1 & lD2 & lD3 & lD4)).
apply (apiece L ar C HI LYa HIok _ FF' LK' cr10 Aw' M1 model1 fx1 fx2 R1 0xa7f44 R2 0xd0890 M2v W2 K HH1 AM1 lMS MG2).
{ intros a Ha Hna. apply lFZ; [exact Ha|..]; intros X0; apply Hna; subst W2; cbn beta; clear - X0; lia. }
{ exact WC2. }
intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
assert (FDEF3 : L5.defined M3 F 1024) by (eapply L5.defined_grows; [exact MGM3| exact FDEF1]).
assert (BI3 : Bv W X M3 model3 LK' cr10 Aw').
{ apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W _ M1 model1 LK' cr10 Aw' M3 model3 W2 BI1 HH3 AM3 MRT3 MGM3 FR3).
intros a Wa. subst W2; cbn beta in Wa. right; left. change (ff_bytes 4) with 1024. clear - Wa. lia. }
assert (RI3 : rinvH R R2 V2 cls F) by (apply (rinvH_ks R R1 R2 V2 cls F PMBHP3.KS_haK2l RI1 lKS); vm_compute; reflexivity).
assert (LS3 : PMSTA.ls_okA RSEGS PMB.AD PMB.AAD g M3) by (apply (PMHAK.ls_piece _ M1 M3 W2 FR3); [intros a Wa; subst W2; cbn beta in Wa; clear - Wa FR; lia| exact LS1]).
assert (HF3 : PMHAK2.hfin F M3 s (PM.sm_st sm)).
{ split; [|split].
* apply (PMHAK2.vstr_keep_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH1 FIN' FHF (V2 - 128) V2 W2 M1 M3 SLOW SHW FR3 PF2 (F + 32) s INS);
[clear - FR; lia| clear - FR; lia| apply OA2; lia| exact VS1].
* apply (PMHAK2.u64_agA M1 M3 (F + 120) 8 (F + 120) _ (PMHAK.agA_frame M1 M3 W2 (F + 120) 8 FR3 ltac:(clear - FR; lia) ltac:(clear - FR; lia) (OA2 (F + 120) 8 ltac:(lia))));
[lia| lia| lia| lia| cbn [pa_classic_imp PMB.AD ADDR_A]; exact IH24].
* apply (PMHAK2.iosb_revptr M1 M3 (F + 216) _ 1253432 (F + 112) (PM.sm_st sm) IOS).
-- apply (PMHAK.u64_vis H1' M3 M2v (F + 216) _ VV3 (PMHAK.avis_sub H1' F 1024 (F + 216) 8 FV1 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia)). exact lU216.
-- intros i Hi. apply FR3; [clear - Hi FR; lia| subst W2; cbn beta; clear - Hi; lia].
-- intros x Hx. apply FR3; [pose proof (PMKB.S_in_shadow x ltac:(clear - Hx FR; lia)) as SX; unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; clear - SX; lia| apply SH2; lia].
-- apply (L5.defined_sub M3 F 1024 (F + 216) 8 FDEF3); lia.
-- clear - FR; lia.
-- clear - FR; lia. }
pose proof BI3 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
assert (ASX : L5CA.astk ar M3 (V2 - 128) (PMSPA.pm_scr 0) /\ shadow_zero M3 (V2 - 128 - PMSPA.pm_scr 0) (PMSPA.pm_scr 0 / 8))
by (eapply PMHASK.callee_stack; first [exact BI3 | eassumption | lia]).
destruct ASX as (AS0 & _). change (PMSPA.pm_scr 0) with 12288 in AS0.
pose proof RI3 as (U2 & U8 & U9 & U18 & U19 & U20 & U24 & U25 & U3 & U4 & U27).
unfold PMB.opdel_spec, PMSPA.opdel_spec, PMSPA.opdel_spec_at in OPD. cbn [pa_opdel PMB.AD ADDR_A] in OPD.
apply (OPD fx2 R2 M3 model3 K _ FF' LK' Aw' cr10 p c (V2 - 128) 0xa7fd0 C1 C2 K0 INP).
{ rewrite L5K.rl10. exact lR10. }
{ rewrite L5K.rl1. exact lR1. }
{ split; [lia| reflexivity]. }
{ rewrite L5K.rl2. exact U2. }
{ rewrite L5K.rl4. rewrite U4. exact TP. }
{ replace (V2 - 128) with (V2 - 128 - 0) by lia. apply (L5SAR.astk_sub ar M3 M3 (V2 - 128) 12288 0 PMSPA.OPDEL_SCR AS0 (fun _ X0 => X0));
[lia| unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR; lia| unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR; lia|].
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - V2A. lia. }
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
intros fx3 R3 M4 model4 Aw4 RP4 HPo MRT4 INCA4 AM4 HHo.
subst X. cbn [PM.vs_own app] in HPo, HHo, BI3, C1.
rewrite L5ADHR.lb_remove_head in HPo, HHo.
unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR in HPo.
assert (BI4 : Bv W (PM.vs_own s) M4 model4 LK' cr10 Aw4).
{ apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W W _ (PM.vs_own s) _ M3 model3 LK' cr10 Aw' M4 model4 LK' cr10 Aw4 4096 [] BI3 HPo HHo AM4 MRT4 INCA4 (incl_refl _)).
- lia.
- clear - CLS; lia.
- intros rr a [].
- intros a _ _ rr [].
- intros a X0. exact X0. }
assert (LS4 : PMSTA.ls_okA RSEGS PMB.AD PMB.AAD g M4) by (apply (PMHAK.ls_ahpres L C LY g ar _ FF' (V2 - 128) 4096 [] M3 M4 HPo PMHAK.far_nil LS3)).
assert (FIN3 : In (F, 4, V2 - 128 + 32) (FF' ++ LK')) by (apply in_or_app; left; left; reflexivity).
assert (HF4 : PMHAK2.hfin F M4 s (PM.sm_st sm)).
{ eapply PMHAK2.hfin_callee; first [ exact LY | exact HIok | exact C1 | exact HPo | exact HF3 | exact FHF | exact FIN3 | apply PMHAK2.wfi_nil | exact (or_introl eq_refl)
| (split; reflexivity) | (intros x Hx; right; apply in_or_app; left; exact Hx) | (intros x Hx; apply in_or_app; left; exact Hx) | apply PMHAK2.wapart_nil | lia ]. }
pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W _ M4 model4 LK' cr10 Aw4 BI4)
as ((VW4 & VIC4 & VSB4 & VUAR4 & VMS4) & VOWN4 & (VFD4 & VFW4 & VFSW4 & VFLC4 & VFLW4) & (FLCc4 & FLV4 & FV4 & SPV4 & FSV4)).
change (ff_bytes 4) with 1024 in *. change (1024 / 8) with 128 in *.
set (H4' := ahid Aw4 model4) in *. set (MV4 := mrestrict H4' M4) in *.
assert (RI4 : rinvH R R3 V2 cls F) by exact (rinvH_pres R R2 R3 V2 cls F RI3 RP4).
assert (S21 : getr R3 (reg 21) = Z_to_bv 64 (F + 96)) by (rewrite (cs_of_preserved R2 R3 21 RP4) by inl; rewrite (lKS 21%nat) by inl; exact T21).
assert (S22 : getr R3 (reg 22) = Z_to_bv 64 1253448) by (rewrite (cs_of_preserved R2 R3 22 RP4) by inl; rewrite (lKS 22%nat) by inl; exact T22).
assert (S23 : getr R3 (reg 23) = Z_to_bv 64 (F + 464)) by (rewrite (cs_of_preserved R2 R3 23 RP4) by inl; rewrite (lKS 23%nat) by inl; exact kR23).
assert (S26 : getr R3 (reg 26) = Z_to_bv 64 18446744073709551608) by (rewrite (cs_of_preserved R2 R3 26 RP4) by inl; rewrite (lKS 26%nat) by inl; exact T26).
pose proof RI4 as (V2r & V8r & V9r & V18r & V19r & V20r & V24r & V25r & V3r & V4r & V27r).
assert (Q5c : L5.writable RSEGS MV4 (V2 - 128) 128) by (eapply L5.writable_sub; [exact VW4| clear; lia| clear - CLS; lia]).
assert (Q6c : L5.u64_at RSEGS MV4 (F + 1016) fl) by (replace (F + 1016) with (F + 1024 - 8) by (clear; lia); exact VFLC4).
pose proof (PMBHP3.haL_conc fx3 R3 MV4 (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U R3 1 | _ => 0 end)) as P.
cbn beta iota in P.
feed P ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
| exact VFD4 | exact VFW4 | exact VFSW4 | exact VFLW4 | exact Q5c | exact Q6c | exact VSB4 | exact VUAR4 | exact VIC4 | (unfold PMBHP3.aligned; exact V2A) ]).
destruct P as (fx4 & R4 & M5v & MG5 & hFR & hFZ & (hMS & hKS & hR1 & hR10 & hU112 & hD1 & hD2)).
set (W5 := fun a => F + 112 <= a < F + 112 + 8).
apply (apiece L ar C HI LYa HIok _ FF' LK' cr10 Aw4 M4 model4 fx3 fx4 R3 0xa7fd0 R4 0xfbe24 M5v W5 K HHo AM4 hMS MG5).
{ intros a Ha Hna. apply hFZ; [exact Ha|..]; intros X0; apply Hna; subst W5; cbn beta; clear - X0; lia. }
{ intros a Ha Wa. subst W5; cbn beta in Wa. split.
- apply (fframe_client L ar _ _ 0 0 F 4 (V2 - 128 + 32)). left; reflexivity. change (ff_bytes 4) with 1024. clear - Wa; lia.
- clear - Wa FR. lia. }
intros M5 model5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5 VV5.
assert (PF5 : PMHAK2.pfoot F (V2 - 128) V2 W5) by (intros a Wa; subst W5; cbn beta in Wa; clear - Wa; lia).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
assert (OA5 : forall o n, (F + 32 <= o /\ o + n <= F + 112) \/ (F + 120 <= o /\ o + n <= F + 1016) -> PMHAK2.oav W5 o n).
{ intros o n H12 x Hx. subst W5; cbn beta. pose proof (PMKB.S_in_shadow x ltac:(clear - Hx H12 FR; lia)) as SX.
unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *. split; intros X0; clear - Hx X0 H12 SX FBIG FR FM8; lia. }
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
apply (KONT fx4 R4 M5 model5 LK' Aw4).
+ apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W _ M4 model4 LK' cr10 Aw4 M5 model5 W5 BI4 HH5 AM5 MRT5 MGM5 FR5).
intros a Wa. subst W5; cbn beta in Wa. right; left. change (ff_bytes 4) with 1024. clear - Wa. lia.
+ apply (rinvH_ks R R3 R4 V2 cls F PMBHP3.KS_haL RI4 hKS); vm_compute; reflexivity.
+ apply (PMHAK.ls_piece _ M4 M5 W5 FR5); [intros a Wa; subst W5; cbn beta in Wa; clear - Wa FR; lia| exact LS4].
+ exact hR1.
+ exact hR10.
+ rewrite (hKS 21%nat) by inl. exact S21.
+ rewrite (hKS 22%nat) by inl. exact S22.
+ rewrite (hKS 23%nat) by inl. exact S23.
+ rewrite (hKS 26%nat) by inl. exact S26.
+ apply (PMHAK2.hfin_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HHo FIN3 FHF (V2 - 128) V2 W5 M4 M5 SLOW SHW FR5 PF5 s (PM.sm_st sm));
[intros x Hx; apply in_or_app; left; exact Hx| apply OA5; lia| apply OA5; lia| apply OA5; lia| exact HF4].
Qed.
End Stage.
End SCFG_1.
End PMHA9.
