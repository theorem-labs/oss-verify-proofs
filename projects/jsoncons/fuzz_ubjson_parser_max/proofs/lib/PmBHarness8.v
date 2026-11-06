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
L5CoreAB0 L5StepARB0 L5CoreBRB0 L5ADetailHRB0 L5AFrameKRB0 HeapIfaceAJx PmLayout PmLayoutA PmModel PmModelFacts PmModelFactsA PmStatics PmStaticsA PmSpecsA PmSpecsAb PmStepAB0 PmBReset1 PmBHarnessStmts PmBHarnessKit PmBHarnessKit2 PmBHarnessSK PmBHarnessP3.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBHarness8 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5DefsAB0.L5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBHarnessKit2.PMHAK2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBHarnessStmts.PMHAS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAb.PMB."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStatics.PMST."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStaticsA.PMSTA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5AFrameKRB0.L5AFKR."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0A10"; "0A9"; "1app"; "1cons"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "2eq"; "3Z"; "0F"; "0FF"; "0HI"; "0K"]; ["0L"; "0LB"; "0LK"; "0LK10"; "0LK9"; "4Model"; "4event"; "5bvmap"; "0M"; "0M10"; "0M9"; "0OPD"; "0R"; "0R10"; "0R9"; "6credit"]; ["7fframe"; "9u64_at"; "8SCFG"; ":cfg"; ";hbase"; ";hsrc"; ";hvec"; "<rinvH"; "<tfrk"; "=AADDR_B"; "=ADDR_B"; ">CHUNK"; ">pstate"; ">sr_qc"; ">srcst"; ">strm"]; [">vs_own"; ">vstr"; ">vstr_at"; "?accA"; "@opdel_spec"; "@vec_dtor_spec"; "Ast"; "Bls_okA"; "CFPState"; "Cgetr"; "DTSet"; "Esrealizes"; "Fbinv"; "Gloaded_segments"; "0SCFG_P"; "Hadd"]; ["Hmul"; "Hof_nat"; "Hpow"; "Hsub"; "0V2"; "0VDT"; "0W"; "0ar"; "0b"; "0cls"; "0cr9"; "0fx10"; "0fx9"; "0g"; "0k"; "0model"]; ["0model10"; "0model9"; "0s"; "0sm"; "0src"; "IZ_to_bv"; "Ibv"; "0stk"; "0str"; "0tb"]]).
Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module PMHA8.
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
Lemma stage8 : ltac2:(TCodec.tc2 tcn__PmBHarness8 "XK&QEvQNv@vR7v>%544321&QD%146543'QH&Gy5'RFyR0%211%5241'7y8%611%311p061'E&QJ'5&Q0%211&O'9';%2211%711'QA'Q?'Q>'Q<%<11'QF&QLvHvR?vAv=vBv0&QOvR4vR9%3221+QTP0&R3+T0%2261&Q8vL%2271v<+4vR6(4(8&Q=r5%211&Q;%54Q4Q421r4&R0+Q0&R2+2r3%3221%6251%>4Q=Q=81&3&Q@r7%211r8%411r9%611%83QE31%93QF61%J3QG;1%K3QHE1r?r>r<r;r:%QFFRHRGRFQEQDQCQBQAQ@Q<Q;Q8Q5Q4Q3Q2654321&Q7rA%25Q91QAQ@Q7(6'F%211%<11&QG&QM&Q:&Q9rB%55432Q71':&QIrD&RE&R1u1%211%42S51%7261+dob<%72S61%;3S631rEu:%:11%<2S=1%?241+S8%R:2R>1%@2S?1%D3S?41rFuE%C11%E2SF1%H241+S0%RH2R=1%I2SH1%M3SH41rGuF%L11%N2SO1%Q1241+o0%S12RF1%Q22T11%Q63T141rHuG%Q511%Q72T81%Q:241+^@%S:2RO1%Q;2T:1%Q?3T:41rIuJ%Q>11%Q@2TA1%QC241+_oooooooooooH%QC2TB1%QG3TB31&Q4rCr@%35S=;2QM1&Q5rJ%23S@14&QB&QCrK+i0%T02SE1%55R9431;&Q6rL%25SI1RC=RJ&Q1rM+iH%T82SM1%44RA3QJ1%SJ1@%SL4TKTK1SH%S=16rN%S?11%SA3TN31%T23TO51r2rQ0r1%TKFUMULUKTJTITHTGTFTETAT@T=T:T9T8T74SOSJ321r6%S65T=1TETDT;%S05RORNRMQC2%RJ2SFRD+doc@%RJ2UI1%RN3UI31%RN2SHR@+_8%TN2TC1%RO2UN1%S33UN41%S32SCR<%S53V01R9%S52SFR5%S73V21R2%S72SIQN%S93V41QKr=%S:21QH%S<3V71QFrQ7rQ6rQ4%QH5U26321%QE3U3T32'QK&Q2%11VK&Q3+eZkL%25T3QM1T:T9rQ=%74SN521p091p0;1p0@1p0D1p0G1p0J1p0M1p0Q31p0Q81p0Q:1p0Q=1p4V@1pQ8VF1pU2VK1pQDVM1pQLW31pTHW:1rQ1+e[_4rO%I53QI21QN%M4TDK1R6p061p0R51p0R;1p0R?1p0RF1p0RJ1p0RO1p0S81p0SB1p0SL1p0T61p0T@1p0TM1p0U41p0U91p0U=1pTLW51pU@W71pTNW?1pTBW@1pU:W<1pU8W>1pUDW@1pUBWA1pU6WB1p6WD1pTFWI1pQ:WK1pQ0WO1pU4X11pQFX31pQNX91pTJX@1pQHXB1pT<XE1").
Proof. intros VDT OPD fx9 R9 M9 model9 K LK9 cr9 A9 s str tb sm src b k stk g.
intros BI RI K0 LS R1a R10 R21 R22 R23 R26 HB0 HS0 TB0 HV0 FT0 KONT.
pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
change (ff_bytes 4) with 1024 in *. change (1024 / 8) with 128 in *.
pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
pose proof RI as (X2 & X8 & X9 & X18 & X19 & X20 & X24 & X25 & X3 & X4 & X27).
assert (FM8 : F mod 8 = 0) by (pose proof (proj1 F8) as E8; clear - E8; lia).
assert (FHF : PMHAK2.hf F) by (unfold PMHAK2.hf, BIGSHADOW_LO, BIGSHADOW_HI; clear - FR FBIG FM8; lia).
set (X := PM.vs_own tb ++ PM.vs_own str ++ PM.vs_own s) in *.
cbn [app] in B1.
assert (NQB : PM.sr_qc src <> b).
{ pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & _). cbn [map fst] in ND.
intros E. rewrite E in ND. inversion ND as [|x0 l0 NI ND1]. apply NI. constructor. }
assert (OSZ : shadow_zero M9 (V2 - 128) 16) by (eapply PMHASK.own_shz; first [exact BI | eassumption]).
pose proof HV0 as (VE0 & VD0 & VA0).
unfold PMB.vec_dtor_spec, PMSPA.vec_dtor_spec in VDT. cbn [pa_vec_dtor PMB.AD ADDR_A] in VDT.
apply (VDT fx9 R9 M9 model9 K _ FF' LK9 A9 cr9 (V2 - 104) (F + 824) b k (V2 - 128) 0xa7e4c stk B1 B2 K0).
{ eapply PMHASK.callee_entry; first [exact BI | exact RI | exact R1a | eassumption | (split; [lia| reflexivity]) | lia]. }
{ eapply PMHASK.callee_room; first [exact BI | eassumption | lia]. }
{ eapply PMHASK.callee_rs; eassumption. }
{ rewrite L5K.rl10. exact R10. }
{ lia. }
{ clear - SHI CLS SPT. lia. }
{ Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - V2A. lia. }
{ Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
apply (PMBRS1.acc_of_shadow_zero M9 (V2 - 128) 16 (V2 - 104) 8 OSZ); [| lia| lia].
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - V2A. lia. }
{ Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). exact FT0. }
{ exists (F, 4, V2 - 128 + 32). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. lia. }
{ clear - FM8. lia. }
{ exact VD0. }
{ exact VA0. }
{ exact VE0. }
{ right. left. reflexivity. }
intros fx' R' M' model' LK' Aw' RP' HP' MRT' INCLK' INCA' AM' HH'.
change (PMSPA.pm_scr 1) with 14336 in HP'.
rewrite (L5ADHR.lb_remove_skip b (PM.sr_qc src) PM.CHUNK _ NQB), L5ADHR.lb_remove_head in HP', HH'.
assert (WFI : PMHAK2.wfi F [(F + 824, 24)]) by (apply PMHAK2.wfi_cons; [cbn [fst snd]; left; lia| apply PMHAK2.wfi_nil]).
assert (LS' : PMSTA.ls_okA RSEGS PMB.AD PMB.AAD g M').
{ apply (PMHAK.ls_ahpres L C LY g ar _ FF' (V2 - 128) 14336 [(F + 824, 24)] M9 M' HP'); [| exact LS].
apply PMHAK.far_cons; [cbn [fst snd]; clear - FR; lia| apply PMHAK.far_nil]. }
assert (HH'' : ri_inv HI (((PM.sr_qc src, PM.CHUNK) :: X) ++ LB) FF' LK' cr9 Aw' M' (vml_of model')) by exact HH'.
assert (BI' : Bv W ((PM.sr_qc src, PM.CHUNK) :: X) M' model' LK' cr9 Aw').
{ apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W W _ ((PM.sr_qc src, PM.CHUNK) :: X) _ M9 model9 LK9 cr9 A9 M' model' LK' cr9 Aw' 14336 [(F + 824, 24)] BI HP' HH'' AM' MRT' INCA' INCLK').
- lia.
- clear - CLS; lia.
- intros rr a [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. unfold tocell. split; [clear - Ha FCEIL SLO CLS; lia|]. unfold HeapIfaceA.SB. change (ff_bytes 4) with 1024. clear - Ha FR F8 FBIG. lia.
- intros a Hc _ rr [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. apply (NCF a); [left; clear - Ha; lia| exact Hc].
- intros a X0. exact X0. }
pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W _ M' model' LK' cr9 Aw' BI')
as ((VW' & VIC' & VSB' & VUAR' & VMS') & VOWN' & (VFD' & VFW' & VFSW' & VFLC' & VFLW') & (FLCc' & FLV' & FV' & SPV' & FSV')).
change (ff_bytes 4) with 1024 in *. change (1024 / 8) with 128 in *.
set (H' := ahid Aw' model') in *. set (MV' := mrestrict H' M') in *.
assert (RI' : rinvH R R' V2 cls F) by exact (rinvH_pres R R9 R' V2 cls F RI RP').
pose proof RI' as (Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y24 & Y25 & Y3 & Y4 & Y27).
assert (Y21 : getr R' (reg 21) = Z_to_bv 64 (F + 96)) by (rewrite (cs_of_preserved R9 R' 21 RP') by inl; exact R21).
assert (Y22 : getr R' (reg 22) = Z_to_bv 64 (F + 992)) by (rewrite (cs_of_preserved R9 R' 22 RP') by inl; exact R22).
assert (Y23 : getr R' (reg 23) = Z_to_bv 64 (F + 464)) by (rewrite (cs_of_preserved R9 R' 23 RP') by inl; exact R23).
assert (Y26 : getr R' (reg 26) = Z_to_bv 64 18446744073709551608) by (rewrite (cs_of_preserved R9 R' 26 RP') by inl; exact R26).
assert (FIN9 : In (F, 4, V2 - 128 + 32) (FF' ++ LK9)) by (apply in_or_app; left; left; reflexivity).
assert (INX : forall x, In x X -> In x ((PM.sr_qc src, PM.CHUNK) :: (b, 32 * 2 ^ k) :: X ++ LB) /\ In x ((PM.sr_qc src, PM.CHUNK) :: X ++ LB)).
{ intros x Hx. split; [right; right; apply in_or_app; left; exact Hx| right; apply in_or_app; left; exact Hx]. }
assert (HB' : PMHAK2.hbase F M' s str sm).
{ eapply PMHAK2.hbase_callee; first [ exact LY | exact HIok | exact B1 | exact HP' | exact HB0 | exact FHF | exact FIN9 | exact WFI | exact (or_introl eq_refl)
| (split; reflexivity) | (intros x Hx; apply INX; subst X; apply in_or_app; right; exact Hx) | (intros x Hx; apply INX; subst X; apply in_or_app; right; exact Hx)
| (apply PMHAK2.wapart_cons; [cbn [fst snd]; lia| apply PMHAK2.wapart_nil]) | lia ]. }
assert (HS' : PMHAK2.hsrc F M' src).
{ eapply PMHAK2.hsrc_callee; first [ exact LY | exact HIok | exact B1 | exact HP' | exact HS0 | exact FHF | exact FIN9 | exact WFI | exact (or_introl eq_refl)
| (split; reflexivity) | (left; reflexivity) | (apply PMHAK2.wapart_cons; [cbn [fst snd]; lia| apply PMHAK2.wapart_nil]) | lia ]. }
assert (TB' : PM.vstr_at RSEGS PMSPA.accA M' (F + 800) tb).
{ eapply PMHAK2.vstr_keep_callee; first [ exact LY | exact HIok | exact B1 | exact HP' | exact TB0 | exact FHF | exact FIN9 | exact WFI | exact (or_introl eq_refl)
| (split; reflexivity) | (intros x Hx; apply INX; subst X; apply in_or_app; left; exact Hx) | (intros x Hx; apply INX; subst X; apply in_or_app; left; exact Hx)
| (apply PMHAK2.wapart_cons; [cbn [fst snd]; lia| apply PMHAK2.wapart_nil]) | lia ]. }
assert (SLOW : ahl_ceil ar <= V2 - 128) by (clear - SLO CLS; lia).
assert (SHW : BIGSHADOW_HI <= V2 - 128) by (unfold BIGSHADOW_HI; clear - V2R; lia).
assert (Q1 : 4096 <= F <= 140737488354304) by (clear - FR; lia).
assert (Q2 : 4096 <= fl <= 140737488355327) by (clear - FLR; lia).
assert (Q3 : V2 - 128 + 144 <= F \/ F + 1024 <= V2 - 128) by (clear - FCEIL SLO CLS; lia).
assert (Q4 : V2 - 128 + 144 <= fl \/ fl + 1 <= V2 - 128) by (clear - FLR SLO CLS; lia).
assert (Q5 : L5.writable RSEGS MV' (V2 - 128) 128) by (eapply L5.writable_sub; [exact VW'| clear; lia| clear - CLS; lia]).
assert (Q6 : L5.u64_at RSEGS MV' (F + 1016) fl) by (replace (F + 1016) with (F + 1024 - 8) by (clear; lia); exact VFLC').
assert (AV800 : L5A.avis H' (F + 800) 8) by (apply (PMHAK.avis_sub H' F 1024 (F + 800) 8 FV'); lia).
assert (AV816 : L5A.avis H' (F + 816) 8) by (apply (PMHAK.avis_sub H' F 1024 (F + 816) 8 FV'); lia).
destruct tb as [nt | c nt p].
-
destruct TB' as (_ & _ & (Hnt & TBB)).
assert (TBv : L5.u8_at RSEGS MV' (F + 800) (2 * nt))
by (apply (proj2 (L5A.u8_at_vis H' M' (F + 800) (2 * nt) (PMHAK.avis_sub H' (F + 800) 8 (F + 800) 1 AV800 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact TBB).
pose proof (PMF.even_byte nt) as EVB.
pose proof (PMBHP3.haIs_conc fx' R' MV' (fun j => match j with 2%nat => V2 | 34%nat => F + 992 | 36%nat => 2 * nt | 40%nat => F | 41%nat => fl | 58%nat => U R' 1 | _ => 0 end)) as P.
cbn beta iota in P.
feed P ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | (clear - Hnt; lia) | exact F32
| exact VFD' | exact VFW' | exact VFSW' | exact VFLW' | exact Q5 | exact Q6 | exact TBv | exact EVB | (unfold PMBHP3.aligned; exact V2A) ]).
destruct P as (fx10 & R10' & M10v & MG10 & iFR & iFZ & (iMS & iKS & iR1 & iR10)).
apply (apiece L ar C HI LYa HIok _ FF' LK' cr9 Aw' M' model' fx' fx10 R' 0xa7e4c R10' 0xaab7c M10v (fun _ => False) K HH' AM' iMS MG10).
{ intros a Ha Hna. apply iFZ; exact Ha. }
{ intros a Ha []. }
intros M10 model10 HH10 AM10 MRT10 HID10 VIS10 MGM10 FR10 VV10.
assert (BI10 : Bv W ((PM.sr_qc src, PM.CHUNK) :: X) M10 model10 LK' cr9 Aw').
{ apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W _ M' model' LK' cr9 Aw' M10 model10 (fun _ => False) BI' HH10 AM10 MRT10 MGM10 FR10).
intros a []. }
assert (FIN' : In (F, 4, V2 - 128 + 32) (FF' ++ LK')) by (apply in_or_app; left; left; reflexivity).
assert (PF10 : PMHAK2.pfoot F (V2 - 128) V2 (fun _ => False)) by (intros a []).
assert (OAX : forall o n, PMHAK2.oav (fun _ => False) o n) by (intros o n x Hx; split; intros []).
apply (KONT fx10 R10' M10 model10 LK' Aw').
+ subst X. cbn [PM.vs_own app] in BI10. exact BI10.
+ apply (rinvH_ks R R' R10' V2 cls F PMBHP3.KS_haIs RI' iKS); vm_compute; reflexivity.
+ apply (PMHAK.ls_piece _ M' M10 (fun _ => False) FR10); [intros a []| exact LS'].
+ exact iR1.
+ exact iR10.
+ rewrite (iKS 21%nat) by inl. exact Y21.
+ rewrite (iKS 22%nat) by inl. exact Y22.
+ rewrite (iKS 23%nat) by inl. exact Y23.
+ rewrite (iKS 26%nat) by inl. exact Y26.
+ apply (PMHAK2.hbase_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 (fun _ => False) M' M10 SLOW SHW FR10 PF10 s str sm);
[intros x Hx; right; apply in_or_app; left; subst X; apply in_or_app; right; exact Hx| apply OAX| apply OAX| apply OAX| exact HB'].
+ apply (PMHAK2.hsrc_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 (fun _ => False) M' M10 SLOW SHW FR10 PF10 src);
[left; reflexivity| apply OAX| exact HS'].
-
destruct TB' as (_ & _ & (TW0 & TW8 & TW16 & Hnt & Hc & Hc2 & TBP & _)).
assert (Hc64 : 0 <= c + 1 < 2 ^ 64) by lia.
pose proof (PMF.u8_of_u64 RSEGS M' _ _ Hc64 TW0) as TBB.
pose proof (PMF.odd_byte c Hc2 ltac:(lia)) as ODB.
pose proof (Z.mod_pos_bound (c + 1) 256 ltac:(lia)) as HVB.
assert (TBv : L5.u8_at RSEGS MV' (F + 800) ((c + 1) mod 256))
by (apply (proj2 (L5A.u8_at_vis H' M' (F + 800) _ (PMHAK.avis_sub H' (F + 800) 8 (F + 800) 1 AV800 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact TBB).
assert (TW0v : L5.u64_at RSEGS MV' (F + 800) (c + 1)) by (apply (proj2 (L5A.u64_at_vis H' M' (F + 800) _ AV800 ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact TW0).
assert (TW16v : L5.u64_at RSEGS MV' (F + 816) p)
by (apply (proj2 (L5A.u64_at_vis H' M' (F + 816) _ AV816 ltac:(clear - FR; lia) ltac:(clear - FR; lia))); replace (F + 816) with (F + 800 + 16) by lia; exact TW16).
assert (INP : In (p, c) (((PM.sr_qc src, PM.CHUNK) :: X) ++ LB)) by (subst X; right; left; reflexivity).
destruct (PMHAK.blk_facts L ar C SCFG HI HIok _ _ _ _ _ _ _ p c HH' INP) as (P0 & _ & _ & _ & _ & P47 & _).
pose proof (PMBHP3.haIl_conc fx' R' MV' (fun j => match j with 2%nat => V2 | 34%nat => F + 992 | 36%nat => (c + 1) mod 256 | 37%nat => c + 1 | 38%nat => p
| 40%nat => F | 41%nat => fl | 58%nat => U R' 1 | _ => 0 end)) as P.
cbn beta iota in P.
feed P ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | (clear - HVB; lia) | (clear - Hc64; lia) | (clear - P0 P47 Hc; lia)
| exact F32 | exact VFD' | exact VFW' | exact VFSW' | exact VFLW' | exact Q5 | exact Q6 | exact TBv | exact TW0v | exact TW16v | exact ODB
| (unfold PMBHP3.aligned; exact V2A) ]).
destruct P as (fx10 & R10' & M10v & MG10 & iFR & iFZ & (iMS & iKS & iR1 & iR10 & iR11)).
apply (apiece L ar C HI LYa HIok _ FF' LK' cr9 Aw' M' model' fx' fx10 R' 0xa7e4c R10' 0xd0890 M10v (fun _ => False) K HH' AM' iMS MG10).
{ intros a Ha Hna. apply iFZ; exact Ha. }
{ intros a Ha []. }
intros M10 model10 HH10 AM10 MRT10 HID10 VIS10 MGM10 FR10 VV10.
assert (BI10 : Bv W ((PM.sr_qc src, PM.CHUNK) :: X) M10 model10 LK' cr9 Aw').
{ apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W _ M' model' LK' cr9 Aw' M10 model10 (fun _ => False) BI' HH10 AM10 MRT10 MGM10 FR10).
intros a []. }
assert (RI10 : rinvH R R10' V2 cls F) by (apply (rinvH_ks R R' R10' V2 cls F PMBHP3.KS_haIl RI' iKS); vm_compute; reflexivity).
assert (LS10 : PMSTA.ls_okA RSEGS PMB.AD PMB.AAD g M10) by (apply (PMHAK.ls_piece _ M' M10 (fun _ => False) FR10); [intros a []| exact LS']).
assert (FIN' : In (F, 4, V2 - 128 + 32) (FF' ++ LK')) by (apply in_or_app; left; left; reflexivity).
assert (PF10 : PMHAK2.pfoot F (V2 - 128) V2 (fun _ => False)) by (intros a []).
assert (OAX : forall o n, PMHAK2.oav (fun _ => False) o n) by (intros o n x Hx; split; intros []).
assert (HB10 : PMHAK2.hbase F M10 s str sm).
{ apply (PMHAK2.hbase_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 (fun _ => False) M' M10 SLOW SHW FR10 PF10 s str sm);
[intros x Hx; right; apply in_or_app; left; subst X; cbn [PM.vs_own app]; right; exact Hx| apply OAX| apply OAX| apply OAX| exact HB']. }
assert (HS10 : PMHAK2.hsrc F M10 src).
{ apply (PMHAK2.hsrc_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 (fun _ => False) M' M10 SLOW SHW FR10 PF10 src);
[left; reflexivity| apply OAX| exact HS']. }
pose proof BI10 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
assert (NQP : PM.sr_qc src <> p).
{ pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ C1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & _). subst X. cbn [PM.vs_own app map fst] in ND.
intros E. rewrite E in ND. inversion ND as [|x0 l0 NI ND1]. apply NI. constructor. }
assert (ASX : L5CA.astk ar M10 (V2 - 128) (PMSPA.pm_scr 0) /\ shadow_zero M10 (V2 - 128 - PMSPA.pm_scr 0) (PMSPA.pm_scr 0 / 8))
by (eapply PMHASK.callee_stack; first [exact BI10 | eassumption | lia]).
destruct ASX as (AS0 & _).
change (PMSPA.pm_scr 0) with 12288 in AS0.
unfold PMB.opdel_spec, PMSPA.opdel_spec, PMSPA.opdel_spec_at in OPD. cbn [pa_opdel PMB.AD ADDR_A] in OPD.
apply (OPD fx10 R10' M10 model10 K _ FF' LK' Aw' cr9 p c (V2 - 128) 0xa7e68 C1 C2 K0 INP).
{ rewrite L5K.rl10. exact iR10. }
{ rewrite L5K.rl1. exact iR1. }
{ split; [lia| reflexivity]. }
{ rewrite L5K.rl2. rewrite (iKS 2%nat) by inl. exact Y2. }
{ rewrite L5K.rl4. rewrite (iKS 4%nat) by inl. rewrite Y4. exact TP. }
{ replace (V2 - 128) with (V2 - 128 - 0) by lia. apply (L5SAR.astk_sub ar M10 M10 (V2 - 128) 12288 0 PMSPA.OPDEL_SCR AS0 (fun _ X0 => X0)); [lia| unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR; lia| unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR; lia|].
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - V2A. lia. }
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
intros fx2 R2' M2' model2' Aw2 RP2 HPo MRT2 INCA2 AM2 HHo.
subst X. cbn [PM.vs_own app] in HPo, HHo.
rewrite (L5ADHR.lb_remove_skip p (PM.sr_qc src) PM.CHUNK _ NQP), L5ADHR.lb_remove_head in HPo, HHo.
unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR in HPo.
assert (HHo' : ri_inv HI (((PM.sr_qc src, PM.CHUNK) :: PM.vs_own str ++ PM.vs_own s) ++ LB) FF' LK' cr9 Aw2 M2' (vml_of model2')) by exact HHo.
assert (BI2 : Bv W ((PM.sr_qc src, PM.CHUNK) :: PM.vs_own str ++ PM.vs_own s) M2' model2' LK' cr9 Aw2).
{ apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W W _ ((PM.sr_qc src, PM.CHUNK) :: PM.vs_own str ++ PM.vs_own s) _ M10 model10 LK' cr9 Aw' M2' model2' LK' cr9 Aw2 4096 [] BI10 HPo HHo' AM2 MRT2 INCA2 (incl_refl _)).
- lia.
- clear - CLS; lia.
- intros rr a [].
- intros a _ _ rr [].
- intros a X0. exact X0. }
assert (LS2 : PMSTA.ls_okA RSEGS PMB.AD PMB.AAD g M2') by (apply (PMHAK.ls_ahpres L C LY g ar _ FF' (V2 - 128) 4096 [] M10 M2' HPo PMHAK.far_nil LS10)).
assert (FINX : In (F, 4, V2 - 128 + 32) (FF' ++ LK')) by (apply in_or_app; left; left; reflexivity).
assert (WFN : PMHAK2.wfi F []) by apply PMHAK2.wfi_nil.
assert (HB2 : PMHAK2.hbase F M2' s str sm).
{ eapply PMHAK2.hbase_callee; first [ exact LY | exact HIok | exact C1 | exact HPo | exact HB10 | exact FHF | exact FINX | exact WFN | exact (or_introl eq_refl)
| (split; reflexivity) | (intros x Hx; right; right; apply in_or_app; left; exact Hx) | (intros x Hx; right; apply in_or_app; left; exact Hx)
| apply PMHAK2.wapart_nil | lia ]. }
assert (HS2 : PMHAK2.hsrc F M2' src).
{ eapply PMHAK2.hsrc_callee; first [ exact LY | exact HIok | exact C1 | exact HPo | exact HS10 | exact FHF | exact FINX | exact WFN | exact (or_introl eq_refl)
| (split; reflexivity) | (left; reflexivity) | apply PMHAK2.wapart_nil | lia ]. }
pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W _ M2' model2' LK' cr9 Aw2 BI2)
as ((VW2 & VIC2 & VSB2 & VUAR2 & VMS2) & VOWN2 & (VFD2 & VFW2 & VFSW2 & VFLC2 & VFLW2) & (FLCc2 & FLV2 & FV2 & SPV2 & FSV2)).
change (ff_bytes 4) with 1024 in *. change (1024 / 8) with 128 in *.
set (H2' := ahid Aw2 model2') in *. set (MV2 := mrestrict H2' M2') in *.
assert (RI2 : rinvH R R2' V2 cls F) by exact (rinvH_pres R R10' R2' V2 cls F RI10 RP2).
assert (Z21 : getr R2' (reg 21) = Z_to_bv 64 (F + 96)) by (rewrite (cs_of_preserved R10' R2' 21 RP2) by inl; rewrite (iKS 21%nat) by inl; exact Y21).
assert (Z22 : getr R2' (reg 22) = Z_to_bv 64 (F + 992)) by (rewrite (cs_of_preserved R10' R2' 22 RP2) by inl; rewrite (iKS 22%nat) by inl; exact Y22).
assert (Z23 : getr R2' (reg 23) = Z_to_bv 64 (F + 464)) by (rewrite (cs_of_preserved R10' R2' 23 RP2) by inl; rewrite (iKS 23%nat) by inl; exact Y23).
assert (Z26 : getr R2' (reg 26) = Z_to_bv 64 18446744073709551608) by (rewrite (cs_of_preserved R10' R2' 26 RP2) by inl; rewrite (iKS 26%nat) by inl; exact Y26).
pose proof RI2 as (W2r & W8r & W9r & W18r & W19r & W20r & W24r & W25r & W3r & W4r & W27r).
assert (Q5b : L5.writable RSEGS MV2 (V2 - 128) 128) by (eapply L5.writable_sub; [exact VW2| clear; lia| clear - CLS; lia]).
assert (Q6b : L5.u64_at RSEGS MV2 (F + 1016) fl) by (replace (F + 1016) with (F + 1024 - 8) by (clear; lia); exact VFLC2).
pose proof (PMBHP3.haJ_conc fx2 R2' MV2 (fun j => match j with 2%nat => V2 | 34%nat => F + 992 | 40%nat => F | 41%nat => fl | 58%nat => U R2' 1 | _ => 0 end)) as P.
cbn beta iota in P.
feed P ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
| exact VFD2 | exact VFW2 | exact VFSW2 | exact VFLW2 | exact Q5b | exact Q6b | (unfold PMBHP3.aligned; exact V2A) ]).
destruct P as (fx11 & R11 & M11v & MG11 & jFR & jFZ & (jMS & jKS & jR1 & jR10)).
apply (apiece L ar C HI LYa HIok _ FF' LK' cr9 Aw2 M2' model2' fx2 fx11 R2' 0xa7e68 R11 0xaab7c M11v (fun _ => False) K HHo' AM2 jMS MG11).
{ intros a Ha Hna. apply jFZ; exact Ha. }
{ intros a Ha []. }
intros M11 model11 HH11 AM11 MRT11 HID11 VIS11 MGM11 FR11 VV11.
assert (FIN2 : In (F, 4, V2 - 128 + 32) (FF' ++ LK')) by (apply in_or_app; left; left; reflexivity).
apply (KONT fx11 R11 M11 model11 LK' Aw2).
+ apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W _ M2' model2' LK' cr9 Aw2 M11 model11 (fun _ => False) BI2 HH11 AM11 MRT11 MGM11 FR11).
intros a [].
+ apply (rinvH_ks R R2' R11 V2 cls F PMBHP3.KS_haJ RI2 jKS); vm_compute; reflexivity.
+ apply (PMHAK.ls_piece _ M2' M11 (fun _ => False) FR11); [intros a []| exact LS2].
+ exact jR1.
+ exact jR10.
+ rewrite (jKS 21%nat) by inl. exact Z21.
+ rewrite (jKS 22%nat) by inl. exact Z22.
+ rewrite (jKS 23%nat) by inl. exact Z23.
+ rewrite (jKS 26%nat) by inl. exact Z26.
+ apply (PMHAK2.hbase_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HHo' FIN2 FHF (V2 - 128) V2 (fun _ => False) M2' M11 SLOW SHW FR11 PF10 s str sm);
[intros x Hx; right; apply in_or_app; left; exact Hx| apply OAX| apply OAX| apply OAX| exact HB2].
+ apply (PMHAK2.hsrc_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HHo' FIN2 FHF (V2 - 128) V2 (fun _ => False) M2' M11 SLOW SHW FR11 PF10 src);
[left; reflexivity| apply OAX| exact HS2].
Qed.
End Stage.
End SCFG_1.
End PMHA8.
