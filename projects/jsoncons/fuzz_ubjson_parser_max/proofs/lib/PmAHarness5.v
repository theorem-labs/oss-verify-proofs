(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceA LibIface
AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA L5DefsA
L5CoreA L5StepAR L5CoreBR L5ADetailHR L5AFrameKR HeapIfaceAJx PmLayout PmLayoutA PmModel PmModelFactsA PmStatics PmStaticsA PmSpecsA PmSpecsAa PmStepA PmAReset1 PmAHarnessStmts PmAHarnessKit PmAHarnessKit2 PmAHarnessSK PmAHarnessP2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmAHarness5 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5DefsA.L5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmAHarnessKit2.PMHAK2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmAHarnessStmts.PMHAS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayout."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAa.PMA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStatics.PMST."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStaticsA.PMSTA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5AFrameKR.L5AFKR."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0A6"; "0A7"; "1app"; "1list"; "1nil"; "1option"; "1prod"; "1true"; "2eq"; "3Z"; "0F"; "0FF"; "0HI"; "0K"; "0L"]; ["0LB"; "0LK"; "0LK6"; "0LK7"; "4Model"; "4event"; "5bvmap"; "0M"; "0M6"; "0M7"; "0R"; "0R6"; "0R7"; "6credit"; "7fframe"; "7shadow_zero"]; ["9u32_at"; "8SCFG"; ":cfg"; ";hbase"; ";hec"; ";hpar"; "<rinvH"; "<tfrk"; "=pa_syscat_obj"; ">AADDR_A"; ">ADDR_A"; "?parser_own"; "?pst"; "?strm"; "?vs_own"; "?vstr"]; ["@syscat_spec"; "AST"; "Ast"; "Ast_err"; "Ast_loc"; "Bls_okA"; "CFPState"; "Cgetr"; "DTSet"; "Esrealizes"; "Fbinv"; "Gloaded_segments"; "0SCFG_P"; "0SYS"; "Hadd"; "Hof_nat"]; ["Hsub"; "0V2"; "0W"; "0ar"; "0cls"; "0cr6"; "0fx6"; "0fx7"; "0g"; "0model"; "0model6"; "0model7"; "0ps"; "0s"; "0s'"; "0sm"]; ["IZ_to_bv"; "Ibv"]]).
Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module PMHA5.
Import L5A. Import L5CA. Import L5SAR. Import PMHAS.
Abbreviation RSEGS := Asan.M.loaded_segments.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac hsc := first [ asm | apply UR | apply U_to | rk | gmem | (arith_goal; first [asm | alia]) | assumption ].
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section Stage.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.
Variables (M : word -> option byte) (model : Model) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z)) (R : bvmap 5 word)
(V2 cls F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (cr : credit) (W : list L5.range).
Hypothesis G : L5AFKR.gctx L ar HI LB FF LK A (V2 + cls) 36864 (V2 - 128) (V2 - 128) (V2 + cls) (tocell (V2 + cls)) (tfrk (V2 + cls) R) F fl 4 LK2 M2 model2 cr.
Hypothesis CLS : cls = 0 \/ cls = 16.
Hypothesis V2R : 140735332487360 <= V2 <= 140737488355328.
Hypothesis V2S : V2 + cls <= 140737488355328.
Hypothesis V2A : V2 mod 32 = 0.
Hypothesis GP : getr R (reg 3) = Z_to_bv 64 (pa_gp PMA.AD).
Hypothesis TP : getr R (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis FFRS : forall f, In f FF -> V2 + cls + 32 <= ff_rs f.
Hypothesis ROOM : forall LKc, incl LKc LK -> NoDup (map ff_addr ((F, 4, V2 - 128 + 32) :: FF ++ LKc)) -> PMSPA.ffroomA 11 ((F, 4, V2 - 128 + 32) :: FF) LKc.
Hypothesis STKSH : shadow_zero M (V2 + cls - 36864) 4608.
Hypothesis WAPP : PMKA.wapp W.
Hypothesis WSYS : forall a, L5.outside W a -> L5.outside [(0x66d5b0, 2)] a.
Local Notation Bv := (L5AFKR.binv L ar HI M model LB FF LK A (V2 + cls) 36864 (V2 - 128) (tfrk (V2 + cls) R) F 4).
Local Notation FF' := ((F, 4, V2 - 128 + 32) :: FF).
Ltac hsolve := first [ exact LY | exact HIok | eassumption | exact (or_introl eq_refl) | (split; reflexivity) | apply incl_refl
| (apply PMHAK2.wapart_cons; [cbn [fst snd]; lia| first [apply PMHAK2.wapart_nil | (apply PMHAK2.wapart_cons; [cbn [fst snd]; lia| apply PMHAK2.wapart_nil])]])
| (apply PMHAK2.wapart_nil) | lia ].
Lemma stage5 : ltac2:(TCodec.tc2 tcn__PmAHarness5 "WJ&Q@vQLv?vR3v=%544321'QF&Fy5'RAyR0%211%5241'6y8%611%311p061'D&QH'4&N%211&M'7':%2211%711'Q?'Q='Q<'QB&QJvGvR9v@v<vAv0&QNvR1vR4%3221+QTP0&R0+T0%2261&Q7vJ%2271v;+4vR2&3&Q;r2%211&Q>r4%211r5%411%93Q431%:3Q571r;r:r8r7r6%Q5FR3R2R1Q4Q3Q2Q1Q0OKJGDCBA654321&Q6r=%25H1Q0OF(5'E%211%<11&QE&QK&Q:&Q9r>%55432H1'9&QGr@&R@&QOu1%211%42RB1%7261+dnj8%72RC1%;3RC31rAuE%:11%<2RJ1%?241+S0%QN2QC1%@2RL1%D3RL41rBuF%C11%E2S31%H241+o0%R72QL1%I2S51%M3S541rCuG%L11%N2S<1%Q1241+^@%R@2R51%Q22S>1%Q63S>41rDuJ%Q511%Q72SE1%Q:241+_oooooooooooH%Q:2SF1%Q>3SF31&Q3r<%25RB:QCQM1&Q5rE%23RE14&Q0rFz%34QM2M1&OrG+2%332Q11%RJ1:%RH14rH%RJ11%RO3SJ31%S03SK51r3rJr1%SIFTGTFTESHSGSFSESDSCS?S>S;S8S7S6S54RO3S221%RD5S:RFSBSAS8(QA&QD%11D(8&QC%11G%63431%RE5RDRCRB1RN%R?2S1R9+dnjD%R?2TK1%RC3TK31r9u:%RB11%RD2U21%RG241%RI3U11QD%RI2S<R;%RK3U31R8%RK2S?R4%RM3U51R1%RM2Q>QM%RO3U71QJ%RO2S<QF%S13U91QDrQ1rQ0rO%QF5T6SA321%QD3T7S82&Q4r?&Q8%11S>%44T<3QD1'QI&Q1%11V0&Q2+e_l4%25RLS51S?9rQ8%74SH521p091p0?1p0A1p0F1p0I1p0L1p0O1p0Q21p0Q91p0Q>1p0QG1p0QI1p6UH1pQ8UN1pTHV31pQDV51pQJV;1pT@VB1rK+ja]HrI%J53R521R:%N4T?L1R@p061p0R@1p0RE1p0RJ1p0RN1p0S21p0S;1p0SE1p0SO1p0T91p0TF1p0TM1p0U21p0U61pTBV=1pTJV?1pU0VA1pTNVC1pTLVD1p4VF1pT<VK1pQ6VM1pNW11pTFW31pQBW51pQHW;1pT>WB1pSLWD1").
Proof. intros SYS fx6 R6 M6 model6 K LK6 cr6 A6 s s' sm ps g.
intros BI RI K0 LS R1a R21 R22 R23 R26 HB0 HP0 EC0 SZE0 KONT.
pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
change (ff_bytes 4) with 1024 in *. change (1024 / 8) with 128 in *.
pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
pose proof RI as (X2 & X8 & X9 & X18 & X19 & X20 & X24 & X25 & X3 & X4 & X27).
assert (FM8 : F mod 8 = 0) by (pose proof (proj1 F8) as E8; clear - E8; lia).
assert (FHF : PMHAK2.hf F) by (unfold PMHAK2.hf, BIGSHADOW_LO, BIGSHADOW_HI; clear - FR FBIG FM8; lia).
pose proof LS as (LSB & LSL & LSS & LSE).
unfold PMA.syscat_spec, PMSPA.syscat_spec in SYS. cbn [pa_syscat pa_syscat_guard pa_syscat_obj PMA.AD ADDR_A] in SYS.
apply (SYS fx6 R6 M6 model6 K ((PM.parser_own ps ++ PM.vs_own s' ++ PM.vs_own s) ++ LB) FF' LK6 A6 cr6 (V2 - 128) 0xa7b48 (PMST.st_sys g) B1 B2 K0).
{ eapply PMHASK.callee_entry; first [exact BI | exact RI | exact R1a | eassumption | (split; [lia| reflexivity]) | lia]. }
{ eapply PMHASK.callee_room; first [exact BI | eassumption | lia]. }
{ eapply PMHASK.callee_rs; eassumption. }
{ exact LSB. }
{ exact LSS. }
intros fx' R' M' model' LK' Aw' RP' RV' SYS' HP' MRT' INCLK' INCA' AM' HH'.
change (PMSPA.pm_scr 1) with 14336 in HP'.
set (Wc := if PMST.st_sys g then [] else [(6739376, 2)]) in *.
assert (WcL : forall r, In r Wc -> r = (6739376, 2)) by (intros r Hr; subst Wc; destruct (PMST.st_sys g); [destruct Hr| destruct Hr as [<-|[]]; reflexivity]).
assert (WFI : PMHAK2.wfi F Wc) by (intros r Hr; rewrite (WcL r Hr); right; cbn [fst snd]; lia).
assert (WA : forall o n, F <= o -> PMHAK2.wapart Wc o n) by (intros o n Ho r Hr; rewrite (WcL r Hr); cbn [fst snd]; clear - Ho FR; lia).
assert (LS' : PMSTA.ls_okA RSEGS PMA.AD PMA.AAD (PMST.ST (PMST.st_loc g) true (PMST.st_err g)) M').
{ apply (PMHAK.ls_ahpres_sys L C LY g ar _ FF' (V2 - 128) 14336 Wc M6 M' HP'); [| exact LS| exact SYS'].
intros a Ha r Hr Hin. rewrite (WcL r Hr) in Hin. unfold L5.in_rng in Hin; cbn [fst snd] in Hin.
unfold PMHAK.bcell, PMHAK.lcell, PMHAK.ecell in Ha. clear - Ha Hin. lia. }
assert (BI' : Bv W (PM.parser_own ps ++ PM.vs_own s' ++ PM.vs_own s) M' model' LK' cr6 Aw').
{ apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W W _ _ _ M6 model6 LK6 cr6 A6 M' model' LK' cr6 Aw' 14336 Wc BI HP' HH' AM' MRT' INCA' INCLK').
- lia.
- clear - CLS; lia.
- intros rr a Hr Ha. rewrite (WcL rr Hr) in Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. unfold tocell. split; [clear - Ha SLO SPT; lia|].
unfold HeapIfaceA.SB. change (ff_bytes 4) with 1024. clear - Ha FR F8. lia.
- intros a Hc Ho rr Hr Ha. pose proof (WcL rr Hr) as E. subst rr. exact (WSYS a Ho _ (or_introl eq_refl) Ha).
- intros a X. exact X. }
pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W _ M' model' LK' cr6 Aw' BI')
as ((VW' & VIC' & VSB' & VUAR' & VMS') & VOWN' & (VFD' & VFW' & VFSW' & VFLC' & VFLW') & (FLCc' & FLV' & FV' & SPV' & FSV')).
change (ff_bytes 4) with 1024 in *. change (1024 / 8) with 128 in *.
set (H' := ahid Aw' model') in *. set (MV' := mrestrict H' M') in *.
assert (RI' : rinvH R R' V2 cls F) by exact (rinvH_pres R R6 R' V2 cls F RI RP').
pose proof RI' as (Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y24 & Y25 & Y3 & Y4 & Y27).
assert (Y21 : getr R' (reg 21) = Z_to_bv 64 (F + 96)) by (rewrite (cs_of_preserved R6 R' 21 RP') by inl; exact R21).
assert (Y22 : getr R' (reg 22) = Z_to_bv 64 (F + 992)) by (rewrite (cs_of_preserved R6 R' 22 RP') by inl; exact R22).
assert (Y23 : getr R' (reg 23) = Z_to_bv 64 (F + 464)) by (rewrite (cs_of_preserved R6 R' 23 RP') by inl; exact R23).
assert (Y26 : getr R' (reg 26) = Z_to_bv 64 18446744073709551608) by (rewrite (cs_of_preserved R6 R' 26 RP') by inl; exact R26).
assert (FIN6 : In (F, 4, V2 - 128 + 32) (FF' ++ LK6)) by (apply in_or_app; left; left; reflexivity).
assert (HB' : PMHAK2.hbase F M' s s' sm).
{ eapply PMHAK2.hbase_callee; first [ exact B1 | exact HP0 | exact HB0 | exact FHF | exact FIN6 | exact WFI | apply WA; lia
| (intros x Hx; apply in_or_app; left; apply in_or_app; right; exact Hx) | hsolve ]. }
assert (HQ' : PMHAK2.hpar F M' ps).
{ eapply PMHAK2.hpar_callee; first [ exact B1 | exact HP0 | exact FHF | exact FIN6 | exact WFI | apply WA; lia
| (intros x Hx; apply in_or_app; left; apply in_or_app; left; exact Hx) | hsolve ]. }
assert (AGE : PMFA.agA M6 M' (F + 992) 16).
{ apply (PMHAK2.ff_callee L ar _ FF' (V2 - 128) 14336 Wc M6 M' (F, 4, V2 - 128 + 32) F (F + 992) 16 HP' (or_introl eq_refl));
cbn [ff_addr ff_class fst snd]; change (ff_bytes 4) with 1024; [lia| lia| exact FHF| lia| lia| exact WFI| apply WA; lia]. }
assert (EC' : L5.u32_at RSEGS M' (F + 992) 0) by (apply (PMHAK2.u32_agA M6 M' (F + 992) 16 (F + 992) _ AGE); [lia| lia| lia| lia| exact EC0]).
assert (SZE' : shadow_zero M' (F + 992) 2) by (apply (PMHAK2.shz_agA M6 M' (F + 992) 16 (F + 992) 2 AGE); [lia| lia| clear - FM8; lia| lia| exact SZE0]).
pose proof (PMAHP2.haF_conc fx' R' MV' (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U R' 1 | _ => 0 end)) as P.
cbn beta iota in P.
assert (Q1 : 4096 <= F <= 140737488354304) by (clear - FR; lia).
assert (Q2 : 4096 <= fl <= 140737488355327) by (clear - FLR; lia).
assert (Q3 : V2 - 128 + 144 <= F \/ F + 1024 <= V2 - 128) by (clear - FCEIL SLO CLS; lia).
assert (Q4 : V2 - 128 + 144 <= fl \/ fl + 1 <= V2 - 128) by (clear - FLR SLO CLS; lia).
assert (Q5 : L5.writable RSEGS MV' (V2 - 128) 128) by (eapply L5.writable_sub; [exact VW'| clear; lia| clear - CLS; lia]).
assert (Q6 : L5.u64_at RSEGS MV' (F + 1016) fl) by (replace (F + 1016) with (F + 1024 - 8) by (clear; lia); exact VFLC').
feed P ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
| exact VFD' | exact VFW' | exact VFSW' | exact VFLW' | exact Q5 | exact Q6 | (unfold PMAHP2.aligned; exact V2A) ]).
destruct P as (fx7 & R7 & M7v & MG7 & fFR & fFZ & (fMS & fKS & fR1 & fR10 & fC & fD1 & fD2)).
set (W7 := fun a => F + 1000 <= a < F + 1000 + 8).
apply (apiece L ar C HI LYa HIok _ FF' LK' cr6 Aw' M' model' fx' fx7 R' 0xa7b48 R7 0xabf84 M7v W7 K HH' AM' fMS MG7).
{ intros a Ha Hna. apply fFZ; [exact Ha|..]; intros X; apply Hna; subst W7; cbn beta; clear - X; lia. }
{ intros a Ha Wa. subst W7; cbn beta in Wa. split.
- apply (fframe_client L ar _ _ 0 0 F 4 (V2 - 128 + 32)). left; reflexivity. change (ff_bytes 4) with 1024. clear - Wa; lia.
- clear - Wa FR. lia. }
intros M7 model7 HH7 AM7 MRT7 HID7 VIS7 MGM7 FR7 VV7. change (mrestrict H' M7 = M7v) in VIS7.
assert (BI7 : Bv W (PM.parser_own ps ++ PM.vs_own s' ++ PM.vs_own s) M7 model7 LK' cr6 Aw').
{ apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W _ M' model' LK' cr6 Aw' M7 model7 W7 BI' HH7 AM7 MRT7 MGM7 FR7).
intros a Wa. subst W7; cbn beta in Wa. right. left. change (ff_bytes 4) with 1024. clear - Wa. lia. }
assert (RI7 : rinvH R R7 V2 cls F) by (apply (rinvH_ks R R' R7 V2 cls F PMAHP2.KS_haF RI' fKS); vm_compute; reflexivity).
assert (LS7 : PMSTA.ls_okA RSEGS PMA.AD PMA.AAD (PMST.ST (PMST.st_loc g) true (PMST.st_err g)) M7).
{ apply (PMHAK.ls_piece _ M' M7 W7 FR7); [| exact LS']. intros a Wa. subst W7; cbn beta in Wa. clear - Wa FR. lia. }
assert (PF7 : PMHAK2.pfoot F (V2 - 128) V2 W7) by (intros a Wa; subst W7; cbn beta in Wa; clear - Wa; lia).
assert (FIN' : In (F, 4, V2 - 128 + 32) (FF' ++ LK')) by (apply in_or_app; left; left; reflexivity).
assert (SLOW : ahl_ceil ar <= V2 - 128) by (clear - SLO CLS; lia).
assert (SHW : BIGSHADOW_HI <= V2 - 128) by (unfold BIGSHADOW_HI; clear - V2R; lia).
assert (OAX : forall o n, F <= o -> o + n <= F + 1000 -> PMHAK2.oav W7 o n).
{ intros o n H1 H2 x Hx. subst W7; cbn beta. pose proof (PMKA.S_in_shadow x ltac:(clear - Hx H1 H2 FR; lia)) as SX.
unfold BIGSHADOW_LO, BIGSHADOW_HI in *. split; intros X; clear - Hx X H1 H2 SX FBIG FR; lia. }
assert (HB7 : PMHAK2.hbase F M7 s s' sm).
{ apply (PMHAK2.hbase_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 W7 M' M7 SLOW SHW FR7 PF7 s s' sm);
[intros x Hx; apply in_or_app; left; apply in_or_app; right; exact Hx| apply OAX; lia| apply OAX; lia| apply OAX; lia| exact HB']. }
assert (HQ7 : PMHAK2.hpar F M7 ps).
{ apply (PMHAK2.hpar_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 W7 M' M7 SLOW SHW FR7 PF7 ps);
[intros x Hx; apply in_or_app; left; apply in_or_app; left; exact Hx| apply OAX; lia| exact HQ']. }
assert (U10 : bv_unsigned (getr R' (reg 10)) = 1273256) by (rewrite <- L5K.rl10, RV'; apply L5.unsigned_lit; lia).
rewrite U10 in fC.
assert (HE7 : PMHAK2.hec F M7 0 (pa_syscat_obj PMA.AD)).
{ cbn [pa_syscat_obj PMA.AD ADDR_A]. split; [|split].
- apply (PMHAK.u32_agree M' M7 (F + 992) 0); [intros i Hi; apply FR7; [clear - Hi FR; lia| subst W7; cbn beta; clear - Hi; lia]| clear - FR; lia| clear - FR; lia| exact EC'].
- apply (PMHAK.u64_vis H' M7 M7v (F + 1000) _ VV7 (PMHAK.avis_sub H' F 1024 (F + 1000) 8 FV' ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia)). exact fC.
- apply (PMHAK2.shz_frame M' M7 W7 (F + 992) 2 FR7); [| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FR; lia| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FR; lia| exact SZE'].
intros j Hj X. subst W7; cbn beta in X. pose proof (PMKA.S_in_shadow (F + 992) ltac:(clear - FR; lia)) as SX.
unfold BIGSHADOW_LO, BIGSHADOW_HI in *. clear - Hj X SX FBIG FR. lia. }
apply (KONT fx7 R7 M7 model7 LK' Aw' BI7 RI7 LS7).
- exact fR1.
- exact fR10.
- rewrite (fKS 21%nat) by inl. exact Y21.
- rewrite (fKS 22%nat) by inl. exact Y22.
- rewrite (fKS 23%nat) by inl. exact Y23.
- rewrite (fKS 26%nat) by inl. exact Y26.
- exact HB7.
- exact HQ7.
- exact HE7.
Qed.
End Stage.
End SCFG_1.
End PMHA5.
