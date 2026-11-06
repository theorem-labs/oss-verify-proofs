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
Ltac2 tcn__PmAHarness6 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5DefsA.L5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmAHarnessKit2.PMHAK2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmAHarnessStmts.PMHAS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAa.PMA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStatics.PMST."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStaticsA.PMSTA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5AFrameKR.L5AFKR."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0A7"; "0A8"; "1app"; "1length"; "1list"; "1nil"; "1option"; "1prod"; "2eq"; "3le"; "4Z"; "0F"; "0FF"; "0HI"; "0K"]; ["0L"; "0LB"; "0LK"; "0LK7"; "0LK8"; "5Model"; "5event"; "6bvmap"; "0M"; "0M7"; "0M8"; "0R"; "0R7"; "0R8"; "0RST"; "7credit"]; ["8fframe"; "9SCFG"; ":cfg"; ";hbase"; ";hec"; ";hpar"; "<rinvH"; "<tfrk"; "=AADDR_A"; "=ADDR_A"; ">p_stk"; ">parser_own"; ">pst"; ">pstate"; ">strm"; ">vs_own"]; [">vstr"; "?pst_reset"; "@reset_spec"; "Ast"; "Bls_okA"; "CFPState"; "Cgetr"; "DTSet"; "Esrealizes"; "Fbinv"; "Gloaded_segments"; "0SCFG_P"; "Hadd"; "Hof_nat"; "Hsub"; "0V2"]; ["0W"; "0ar"; "0c"; "0cls"; "0cr7"; "0fx7"; "0fx8"; "0g"; "0model"; "0model7"; "0model8"; "0ps"; "0s"; "0s'"; "0sm"; "IZ_to_bv"]; ["Ibv"; "0v"]]).
Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module PMHA6.
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
Hypothesis FAL : F mod 1024 = 0.
Local Notation Bv := (L5AFKR.binv L ar HI M model LB FF LK A (V2 + cls) 36864 (V2 - 128) (tfrk (V2 + cls) R) F 4).
Local Notation FF' := ((F, 4, V2 - 128 + 32) :: FF).
Ltac hsolve := first [ exact LY | exact HIok | eassumption | exact (or_introl eq_refl) | (split; reflexivity) | apply incl_refl
| (apply PMHAK2.wapart_cons; [cbn [fst snd]; lia| first [apply PMHAK2.wapart_nil | (apply PMHAK2.wapart_cons; [cbn [fst snd]; lia| apply PMHAK2.wapart_nil])]])
| (apply PMHAK2.wapart_nil) | lia ].
Lemma stage6 : ltac2:(TCodec.tc2 tcn__PmAHarness6 "X=&QBvQKv@vR1v>%544321'QE&Gy5'R@yR0%211%5241'7y8%611%311p061'E&QG'5&Q0%211&O'8';%2211%711'Q@'Q>'Q<'QC&QIvHvR8vAv=vBv0&QLvQOvR3%3221+QTP0&QN+T0%2261&Q7vK%2271v<+4vR0&3&Q;r4%211&Q?r6%211r7%411%93Q431%:3Q571r=r<r:r9r8%Q5FR3R2R1Q4Q3Q2Q1Q0OKJGDCBA654321&Q6r?%25H1Q0OF(6'F%211%<11&QD&QJ&Q9&Q8r@%55432H1'9&QFrB&R?&QMu1%211%42RB1%7261+dnjD%72RC1%;3RC31rCu:%:11%<2RJ1%?241+^@%QN2QC1%@2RL1%D3RL41rDuE%C11%E2S31%H241+S0%R72QL1%I2S51%M3S541rEuF%L11%N2S<1%Q1241+o0%R@2R51%Q22S>1%Q63S>41rFuG%Q511%Q72SE1%Q:241%Q<3SD1IrGuJ%Q;11%Q=2SK1%Q@241+_oooooooooooH%Q@2SL1%QD3SL31':&4'Q=&Q:r>%211%5241%72QG1&Q3rHrA%35S12QN1R2&Q5rI%23S41R5&Q4rJ%24S71RB=%S419%S213rK%S411%S93T431%S:3T551r3r2rMr1%T4FU2U1U0T3T2T1T0SOSNSJSISFSCSBSAS@5S=4321%RO5SES;SMSLSC%RI5RHRGRFAS<%RC2S3R=+dnk4%RC2TO1%RG3TO31%RG2S8R9%RI3U11R6u;%RG11%RI2U71%RL2S>1+]@%T;2T01%RM2U91%S13U941r;u<%S011%S22U@1%S5241%S73U?1R2%S72SJR@%S93UA1R=%S92SMR9%S;3UC1R6%S;2QCR2%S=3UE1RJ%S=2SJQN%S?3UG1QLrQ6rQ5rQ4%QF5TDSO321&QA%113%QE3TGSH1rQ3rQ2%QE4TJQJ21'QH&Q1%11V>&Q2+e`[<%25S:SC1SMR0rQ=%74T6521p091p0=1p0A1p0F1p0I1p0L1p0O1p0Q21p0Q91p0QB1p0QE1p0QJ1p0QL1p0QN1p6V81pQ:V>1pTFVC1pQFVE1pQLVK1pT>W21rN+e_l4rL%L53R:21R@%Q04TON1REp061p0RF1p0RJ1p0RN1p0S31p0S<1p0SE1p0SL1p0T61p0T@1p0TJ1p0U71p0U>1p0UC1p0UG1pT6W41pU4W51pT@W01pTHW21pTNW41pTLW61pTJW71p4W91pT:W>1pQ8W@1pQ0WD1pTDWF1pQDWH1pQJWN1pT<X51pQNX71").
Proof. intros RST fx7 R7 M7 model7 K LK7 cr7 A7 s s' sm ps g v c.
intros BI RI K0 LS R1a R10 R21 R22 R23 R26 STK1 HB0 HP0 HE0 KONT.
pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
change (ff_bytes 4) with 1024 in *. change (1024 / 8) with 128 in *.
pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
pose proof RI as (X2 & X8 & X9 & X18 & X19 & X20 & X24 & X25 & X3 & X4 & X27).
assert (FM8 : F mod 8 = 0) by (pose proof (proj1 F8) as E8; clear - E8; lia).
assert (FHF : PMHAK2.hf F) by (unfold PMHAK2.hf, BIGSHADOW_LO, BIGSHADOW_HI; clear - FR FBIG FM8; lia).
assert (B1' : ri_inv HI (PM.parser_own ps ++ ((PM.vs_own s' ++ PM.vs_own s) ++ LB)) FF' LK7 cr7 A7 M7 (vml_of model7)) by (rewrite app_assoc; exact B1).
pose proof HP0 as (PA0 & REF0).
unfold PMA.reset_spec, PMSPA.reset_spec in RST. unfold PMSPA.o_p, PMSPA.o_is, PMSPA.o_tb, PMSPA.o_vec in RST. cbn [pa_reset pa_off_p pa_off_is PMA.AD ADDR_A] in RST.
apply (RST fx7 R7 M7 model7 K ((PM.vs_own s' ++ PM.vs_own s) ++ LB) FF' LK7 A7 cr7 (V2 - 128) 0xa7b54 F ps B1' B2 K0).
{ eapply PMHASK.callee_entry; first [exact BI | exact RI | exact R1a | eassumption | (split; [lia| reflexivity]) | lia]. }
{ eapply PMHASK.callee_room; first [exact BI | eassumption | lia]. }
{ eapply PMHASK.callee_rs; eassumption. }
{ exact (PMHASK.callee_frame FF V2 F FAL). }
{ rewrite L5K.rl10. exact R10. }
{ exact PA0. }
{ exact STK1. }
intros fx' R' M' model' LK' Aw' RP' PA' HP' MRT' INCLK' INCA' AM' HH'.
change (PMSPA.pm_scr 1) with 14336 in HP'.
rewrite app_assoc in HH'.
set (Wc := [(F + 464 + 8, 8); (F + 464 + 336, 24); (F + 464 + 360, 24)]) in *.
assert (WcF : forall r, In r Wc -> F + 464 <= fst r /\ fst r + snd r <= F + 848) by (intros r Hr; subst Wc; destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd]; lia).
assert (WFI : PMHAK2.wfi F Wc) by (intros r Hr; destruct (WcF r Hr); left; lia).
assert (WA : forall o n, (o + n <= F + 464 \/ F + 848 <= o) -> PMHAK2.wapart Wc o n) by (intros o n Ho r Hr; destruct (WcF r Hr); lia).
assert (LS' : PMSTA.ls_okA RSEGS PMA.AD PMA.AAD g M').
{ apply (PMHAK.ls_ahpres L C LY g ar _ FF' (V2 - 128) 14336 Wc M7 M' HP'); [| exact LS].
intros r Hr. destruct (WcF r Hr). right. clear - H H0 FR. lia. }
assert (BI' : Bv W (PM.parser_own ps ++ PM.vs_own s' ++ PM.vs_own s) M' model' LK' cr7 Aw').
{ apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W W _ (PM.vs_own s' ++ PM.vs_own s) _ M7 model7 LK7 cr7 A7 M' model' LK' cr7 Aw' 14336 Wc BI HP' HH' AM' MRT' INCA' INCLK').
- lia.
- clear - CLS; lia.
- intros rr a Hr Ha. destruct (WcF rr Hr) as (Z1 & Z2). unfold L5.in_rng in Ha. unfold tocell. split; [clear - Ha Z1 Z2 FCEIL SLO CLS; lia|].
unfold HeapIfaceA.SB. change (ff_bytes 4) with 1024. clear - Ha Z1 Z2 FR F8 FBIG. lia.
- intros a Hc _ rr Hr Ha. destruct (WcF rr Hr) as (Z1 & Z2). unfold L5.in_rng in Ha. apply (NCF a); [left; clear - Ha Z1 Z2; lia| exact Hc].
- intros a X. exact X. }
pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W _ M' model' LK' cr7 Aw' BI')
as ((VW' & VIC' & VSB' & VUAR' & VMS') & VOWN' & (VFD' & VFW' & VFSW' & VFLC' & VFLW') & (FLCc' & FLV' & FV' & SPV' & FSV')).
change (ff_bytes 4) with 1024 in *. change (1024 / 8) with 128 in *.
set (H' := ahid Aw' model') in *. set (MV' := mrestrict H' M') in *.
assert (RI' : rinvH R R' V2 cls F) by exact (rinvH_pres R R7 R' V2 cls F RI RP').
pose proof RI' as (Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y24 & Y25 & Y3 & Y4 & Y27).
assert (Y21 : getr R' (reg 21) = Z_to_bv 64 (F + 96)) by (rewrite (cs_of_preserved R7 R' 21 RP') by inl; exact R21).
assert (Y22 : getr R' (reg 22) = Z_to_bv 64 (F + 992)) by (rewrite (cs_of_preserved R7 R' 22 RP') by inl; exact R22).
assert (Y23 : getr R' (reg 23) = Z_to_bv 64 (F + 464)) by (rewrite (cs_of_preserved R7 R' 23 RP') by inl; exact R23).
assert (Y26 : getr R' (reg 26) = Z_to_bv 64 18446744073709551608) by (rewrite (cs_of_preserved R7 R' 26 RP') by inl; exact R26).
assert (FIN7 : In (F, 4, V2 - 128 + 32) (FF' ++ LK7)) by (apply in_or_app; left; left; reflexivity).
assert (HB' : PMHAK2.hbase F M' s s' sm).
{ eapply PMHAK2.hbase_callee; first [ exact B1 | exact HP' | exact HB0 | exact FHF | exact FIN7 | exact WFI | (apply WA; lia)
| (intros x Hx; apply in_or_app; left; apply in_or_app; right; exact Hx) | (intros x Hx; apply in_or_app; left; exact Hx) | hsolve ]. }
assert (HE' : PMHAK2.hec F M' v c).
{ eapply PMHAK2.hec_callee; first [ exact B1 | exact HP' | exact HE0 | exact FHF | exact FIN7 | exact WFI | (apply WA; lia) | hsolve ]. }
assert (AGR : PMFA.agA M7 M' (F + 848) 8).
{ apply (PMHAK2.ff_callee L ar _ FF' (V2 - 128) 14336 Wc M7 M' (F, 4, V2 - 128 + 32) F (F + 848) 8 HP' (or_introl eq_refl));
cbn [ff_addr ff_class fst snd]; change (ff_bytes 4) with 1024; [lia| lia| exact FHF| lia| lia| exact WFI| apply WA; lia]. }
assert (REF' : L5.u64_at RSEGS M' (F + 848) (F + 432)) by (apply (PMHAK2.u64_agA M7 M' (F + 848) 8 (F + 848) _ AGR); [lia| lia| lia| lia| exact REF0]).
pose proof (PMAHP2.haG_conc fx' R' MV' (fun j => match j with 2%nat => V2 | 35%nat => F + 432 | 40%nat => F | 41%nat => fl | 58%nat => U R' 1 | _ => 0 end)) as P.
cbn beta iota in P.
assert (Q1 : 4096 <= F <= 140737488354304) by (clear - FR; lia).
assert (Q2 : 4096 <= fl <= 140737488355327) by (clear - FLR; lia).
assert (Q3 : V2 - 128 + 144 <= F \/ F + 1024 <= V2 - 128) by (clear - FCEIL SLO CLS; lia).
assert (Q4 : V2 - 128 + 144 <= fl \/ fl + 1 <= V2 - 128) by (clear - FLR SLO CLS; lia).
assert (Q5 : L5.writable RSEGS MV' (V2 - 128) 128) by (eapply L5.writable_sub; [exact VW'| clear; lia| clear - CLS; lia]).
assert (Q6 : L5.u64_at RSEGS MV' (F + 1016) fl) by (replace (F + 1016) with (F + 1024 - 8) by (clear; lia); exact VFLC').
assert (Q7 : L5.u64_at RSEGS MV' (F + 848) (F + 432))
by (apply (proj2 (L5A.u64_at_vis H' M' (F + 848) (F + 432) (PMHAK.avis_sub H' F 1024 (F + 848) 8 FV' ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact REF').
feed P ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
| exact VFD' | exact VFW' | exact VFSW' | exact VFLW' | exact Q5 | exact Q6 | exact Q7 | (unfold PMAHP2.aligned; exact V2A) ]).
destruct P as (fx8 & R8 & M8v & MG8 & gFR & gFZ & (gMS & gKS & gR1 & gR10 & gR11 & gR12)).
set (W8 := fun a : Z => False).
apply (apiece L ar C HI LYa HIok _ FF' LK' cr7 Aw' M' model' fx' fx8 R' 0xa7b54 R8 0xac16c M8v W8 K HH' AM' gMS MG8).
{ intros a Ha Hna. apply gFZ; exact Ha. }
{ intros a Ha Wa. destruct Wa. }
intros M8 model8 HH8 AM8 MRT8 HID8 VIS8 MGM8 FR8 VV8.
assert (BI8 : Bv W (PM.parser_own ps ++ PM.vs_own s' ++ PM.vs_own s) M8 model8 LK' cr7 Aw').
{ apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W _ M' model' LK' cr7 Aw' M8 model8 W8 BI' HH8 AM8 MRT8 MGM8 FR8).
intros a Wa. destruct Wa. }
assert (RI8 : rinvH R R8 V2 cls F) by (apply (rinvH_ks R R' R8 V2 cls F PMAHP2.KS_haG RI' gKS); vm_compute; reflexivity).
assert (LS8 : PMSTA.ls_okA RSEGS PMA.AD PMA.AAD g M8) by (apply (PMHAK.ls_piece _ M' M8 W8 FR8); [intros a []| exact LS']).
assert (PF8 : PMHAK2.pfoot F (V2 - 128) V2 W8) by (intros a []).
assert (FIN' : In (F, 4, V2 - 128 + 32) (FF' ++ LK')) by (apply in_or_app; left; left; reflexivity).
assert (SLOW : ahl_ceil ar <= V2 - 128) by (clear - SLO CLS; lia).
assert (SHW : BIGSHADOW_HI <= V2 - 128) by (unfold BIGSHADOW_HI; clear - V2R; lia).
assert (OAX : forall o n, PMHAK2.oav W8 o n) by (intros o n x Hx; split; intros []).
apply (KONT fx8 R8 M8 model8 LK' Aw' BI8 RI8 LS8).
- exact gR1.
- exact gR10.
- exact gR11.
- exact gR12.
- rewrite (gKS 21%nat) by inl. exact Y21.
- rewrite (gKS 22%nat) by inl. exact Y22.
- rewrite (gKS 23%nat) by inl. exact Y23.
- rewrite (gKS 26%nat) by inl. exact Y26.
- apply (PMHAK2.hbase_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 W8 M' M8 SLOW SHW FR8 PF8 s s' sm);
[intros x Hx; apply in_or_app; left; apply in_or_app; right; exact Hx| apply OAX| apply OAX| apply OAX| exact HB'].
- apply (PMHAK2.hpar_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 W8 M' M8 SLOW SHW FR8 PF8 (PMSPA.pst_reset ps));
[| apply OAX| split; [exact PA'| exact REF']].
intros x Hx. apply in_or_app. left. apply in_or_app. left. unfold PM.parser_own, PMSPA.pst_reset in Hx |- *. cbn [PM.p_src PM.p_b PM.p_k PM.p_tb] in Hx.
destruct (PM.p_tb ps); exact Hx.
- eapply PMHAK2.hec_piece; first [exact FHF | exact FR8 | exact HE' | apply OAX].
Qed.
End Stage.
End SCFG_1.
End PMHA6.
