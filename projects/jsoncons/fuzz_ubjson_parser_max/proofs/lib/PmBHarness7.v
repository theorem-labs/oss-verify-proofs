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
L5CoreAB0 L5StepARB0 L5CoreBRB0 L5ADetailHRB0 L5AFrameKRB0 HeapIfaceAJx PmLayout PmLayoutA PmModel PmModelFactsA PmStatics PmStaticsA PmSpecsA PmSpecsAb PmSpecsBX PmStepAB0 PmBReset1 PmBHarnessStmts PmBHarnessKit PmBHarnessKit2 PmBHarnessSK PmBHarnessP2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBHarness7 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5DefsAB0.L5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBHarnessKit2.PMHAK2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBHarnessStmts.PMHAS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsBX.PMBX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStatics.PMST."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStaticsA.PMSTA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5AFrameKRB0.L5AFKR."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0A8"; "0A9"; "1app"; "1bool"; "1length"; "1list"; "1nil"; "1option"; "1prod"; "1true"; "2eq"; "3le"; "4Z"; "0F"; "0FF"]; ["0HI"; "0K"; "0L"; "0LB"; "0LK"; "0LK8"; "0LK9"; "5Model"; "5event"; "6bvmap"; "0M"; "0M8"; "0M9"; "0R"; "0R8"; "0R9"]; ["0RRD"; "7credit"; "8fframe"; "8shadow_zero"; ":u64_at"; "9SCFG"; ";cfg"; "<hbase"; "<hec"; "<hpar"; "<hsrc"; "<hvec"; "=rinvH"; "=tfrk"; ">AADDR_B"; ">ADDR_B"]; ["?p_b"; "?p_k"; "?p_src"; "?p_stk"; "?p_tb"; "?p_tg"; "?parser_own"; "?pot_parser"; "?pst"; "?pstate"; "?strm"; "?tb_ok"; "?unread"; "?vs_own"; "?vstr"; "?vstr_at"]; ["@HV"; "@accA"; "@cr0"; "@credit_keep"; "@credit_le"; "@pst_reset"; "@scA"; "Areader_read_spec"; "BST"; "Bst"; "Bst_err"; "Bst_loc"; "Bst_sys"; "Cls_okA"; "DFPState"; "Dgetr"]; ["ETSet"; "Fsrealizes"; "Gbinv"; "Hloaded_segments"; "0SCFG_P"; "Iadd"; "Ilt"; "Iof_nat"; "Ipow"; "Isub"; "0V2"; "0W"; "0ar"; "0c"; "0cls"; "0cr8"]; ["0cr9"; "0e'"; "0fx8"; "0fx9"; "0g"; "0model"; "0model8"; "0model9"; "0ps"; "0ps'"; "0s"; "0sm"; "0sm'"; "JZ_to_bv"; "Jbv"; "0str"]]).
Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module PMHA7.
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
Hypothesis WERR : forall a, L5.outside W a -> L5.outside [(0x66f0c0, 2); (0x690b10, 544)] a.
Local Notation Bv := (L5AFKR.binv L ar HI M model LB FF LK A (V2 + cls) 36864 (V2 - 128) (tfrk (V2 + cls) R) F 4).
Local Notation FF' := ((F, 4, V2 - 128 + 32) :: FF).
Ltac hsolve := first [ exact LY | exact HIok | eassumption | exact (or_introl eq_refl) | (split; reflexivity) | apply incl_refl
| (apply PMHAK2.wapart_cons; [cbn [fst snd]; lia| first [apply PMHAK2.wapart_nil | (apply PMHAK2.wapart_cons; [cbn [fst snd]; lia| apply PMHAK2.wapart_nil])]])
| (apply PMHAK2.wapart_nil) | lia ].
Lemma stage7 : ltac2:(TCodec.tc2 tcn__PmBHarness7 "ZE&R7vRDvBvRLv@%544321'R>&Iy5'S>yR0%211%5241'8y8%611%311p061'G&R@'6&Q2%211&Q1'9'=%2211%711'QN'QJ'QH'R9&RBvJvS5vCv?vDv0&REvRJvRN%3221+QTP0&RI+T0%2261&Q=vM%2271v>+4vRK&3&QFr3%211&QMr5%211r6%411%93Q431%:3Q571r<r;r9r8r7%Q5FR3R2R1Q4Q3Q2Q1Q0OKJGDCBA654321&Q<r>%25H1Q0OF(7'H%211%<11&R=&RC&Q?&Q>r?%55432H1';&R?rA&S=&RGu1%211%42RB1%7261+doa8%72RC1%;3RC31rBu:%:11%<2RJ1%?241+^@%QN2QC1%@2RL1%D3RL41rCu;%C11%E2S31%H241+o0%R72QL1%I2S51%M3S541rDuE%L11%N2S<1%Q1241+S0%R@2R51%Q22S>1%Q63S>41rEuF%Q511%Q72SE1%Q:241%Q<3SD1@rFuG%Q;11%Q=2SK1%Q@241%QB3SJ1OrGuJ%QA11%QC2T11%QF241+_oooooooooooH%QF2T21%QJ3T231&Q7r@%25RN:QK1QO&Q9rH%23S11R2&Q8rIz%34S521R@'<&5'QI&QC%11R7%4231%62R61&Q3rK+j@%SK2S@1+1%53421&RF&QL&QB%11R0%321QH&RH+2+J%3221%9251&QK&QD%11R0&QE%11R2%5231&R4&R6&QG&R0%12UGUF&R5%11R1%5231%72UK1rJ%:221'4rQ2%T911rQ3%T;11%T@3U;31%TA3U<T>1r4%U8FV6V5V4U7U6U5U4U3U2TNTMTJTGTFTETD2T5T4T<T>1r:%T45TJ1U2U1TH(R8&R;rQ1%211&R<%113%6331TJ%T55T4T3T219&R:%11C(:%T33F21%T43GTM2p021r=%T621T0+dob<%T62VB1%T:3VB31%T:2TGSL+S8%UD2UH1%T;2VG1%T?3VG41%T?2TBS?%TA3VI1S<%TA2RFS8%TC3VK1SG%TC2TBS4%TE3VM1T2%TE2T:S0%TG3VO1RNrQ=rQ<%RO5UKT>21U=&Q:%R81U8%23UNT81&QO&R1+i0%V=2V21%R51U4%55U84T521&Q;&Q@%11S:&QA%11S<%S11S=%65V;T3421&Q4+iH%VI2V>1%34UCT1Q11&R3rQDrQ?%R;11%R?2R=1%RA2X51&R2%746TH21'RA&Q5%11X;&Q6+e[_4%25RASJ1SMT9rQG%74V3521p091p0B1p0G1p0O1p0Q61p0Q:1p0Q>1p0QA1p0QD1p0QG1p0QJ1p0R01p0R61p0R=1p0RF1p0RI1pV4S21pVJX61pVDX61p6X:1pV2X?1pQ>XA1pV@XF1pQJXH1pR0XN1pV8Y51+eQiHrQ0rO%Q25S>S2321rN%Q74W3Q521p071p0SD1p0T01p0T71p0TB1p0TI1p0U11p0U61p0U:1p0U>1p0UG1p0UN1p0V51p0V?1p0VI1p0W31p0W@1p0WG1p0WL1p0X01pULY=1pV:Y81pVBY:1pVHY<1pW0Y>1pVFY?1p4YA1pV0YF1pQ<YH1pQ4YL1pV>YN1pQHZ01pQNZ61pV6Z=1pR2Z?1").
Proof. intros RRD fx8 R8 M8 model8 K LK8 cr8 A8 s str sm ps g c.
intros BI RI K0 LS R1a R10 R11 R21 R22 R23 R26 HB0 HP0 HE0 LEN SZR UNR TBOK CRD KONT.
pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
change (ff_bytes 4) with 1024 in *. change (1024 / 8) with 128 in *.
pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
pose proof RI as (X2 & X8 & X9 & X18 & X19 & X20 & X24 & X25 & X3 & X4 & X27).
assert (FM8 : F mod 8 = 0) by (pose proof (proj1 F8) as E8; clear - E8; lia).
assert (FHF : PMHAK2.hf F) by (unfold PMHAK2.hf, BIGSHADOW_LO, BIGSHADOW_HI; clear - FR FBIG FM8; lia).
assert (FDEF8 : L5.defined M8 F 1024).
{ pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W _ M8 model8 LK8 cr8 A8 BI) as (_ & _ & (VFD & _) & (_ & _ & FV & _)).
apply (proj1 (L5A.defined_vis (ahid A8 model8) M8 F 1024 FV)); exact VFD. }
assert (B1' : ri_inv HI (PM.parser_own ps ++ ((PM.vs_own str ++ PM.vs_own s) ++ LB)) FF' LK8 cr8 A8 M8 (vml_of model8)) by (rewrite app_assoc; exact B1).
pose proof HB0 as (VS0 & IS0 & VV0 & VZ0 & VI0). pose proof HP0 as (PA0 & REF0). pose proof HE0 as (EV0 & EC0 & EZ0).
pose proof LS as (LSB & LSL & LSS & LSE).
unfold PMBX.reader_read_spec, PMSBX.reader_read_spec in RRD.
unfold PMSPA.run_pre, PMSPA.parse_post, PMSPA.ec_at, PMSPA.visitor_at, PMSPA.W_run, PMSPA.W_srcf, PMSPA.err_W,
PMSPA.o_src, PMSPA.o_tb, PMSPA.o_vec, PMSPA.o_p, PMSPA.o_is, PMSPA.o_ec, PMSPA.o_v in RRD.
cbn [app pa_reader_read pa_off_p pa_off_is pa_off_ec pa_off_v pa_errcat_guard pa_atexit pa_vp_visitor PMB.AD ADDR_B] in RRD.
apply (RRD fx8 R8 M8 model8 K ((PM.vs_own str ++ PM.vs_own s) ++ LB) FF' LK8 A8 cr8 (V2 - 128) 0xa7e28 F c ps str sm (PMST.st_err g) B1' B2 K0).
{ eapply PMHASK.callee_entry; first [exact BI | exact RI | exact R1a | eassumption | (split; [lia| reflexivity]) | lia]. }
{ eapply PMHASK.callee_room; first [exact BI | eassumption | lia]. }
{ eapply PMHASK.callee_rs; eassumption. }
{ exact (PMHASK.callee_frame FF V2 F FAL). }
{ Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - V2A. lia. }
{ Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). rewrite L5K.rl10; exact R10. }
{ rewrite L5K.rl11; exact R11. }
{ split; [exact PA0|]. split; [exact IS0|]. split.
{ split; [cbn [pa_vp_visitor PMB.AD ADDR_A] in VV0; exact VV0|].
apply (PMBRS1.acc_of_shadow_zero M8 (F + 432) 1 (F + 432) 8 VZ0); [clear - FM8; lia| lia| lia]. }
split; [replace (F + 464 + 384) with (F + 848) by lia; exact REF0|]. split; [exact LSB|]. split; [exact LSE| exact TBOK]. }
{ intros x Hx. apply in_or_app. left. apply in_or_app. left. exact Hx. }
{ exact LEN. }
{ split; [exact EV0|]. split; [replace (F + 992 + 8) with (F + 1000) by lia; exact EC0|]. split.
- apply (L5.defined_sub M8 F 1024 (F + 992) 16 FDEF8); lia.
- apply (PMBRS1.acc_of_shadow_zero M8 (F + 992) 2 (F + 992) 16 EZ0); [clear - FM8; lia| lia| lia]. }
{ replace (F + 464 + 384) with (F + 848) by lia. apply (PMBRS1.acc_of_shadow_zero M8 (F + 848) 1 (F + 848) 8 SZR); [clear - FM8; lia| lia| lia]. }
{ exact UNR. }
{ exact CRD. }
intros fx' R' M' model' LK' Aw' ps' sm' e' cr' RP' PP HP' CK' MRT' INCLK' INCA' AM' HH'.
change (PMSPA.pm_scr 11) with 34816 in HP'.
rewrite app_assoc in HH'.
destruct PP as ((PA' & IS' & (VV' & VA') & REF' & BASE' & ERR' & TBOK') & SST & EIMP & DEC').
set (Wc := [(F + 464 + 8, 8); (F + 464 + 24 + 256, 40); (F + 96 + 40, 8); (F + 96 + 152, 4); (F + 464 + 336, 24); (F + 464 + 360, 24); (F + 992, 16);
(6746304, 2); (6884112, 544)]) in *.
assert (WcL : forall r, In r Wc -> (F + 96 <= fst r /\ fst r + snd r <= F + 1008) \/ r = (6746304, 2) \/ r = (6884112, 544)).
{ intros r Hr. subst Wc. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; cbn [fst snd]; (left; lia) || (right; left; reflexivity) || (right; right; reflexivity). }
assert (WFI : PMHAK2.wfi F Wc).
{ intros r Hr. destruct (WcL r Hr) as [X|[-> | ->]]; [left; lia| right; cbn [fst snd]; lia| right; cbn [fst snd]; lia]. }
assert (WAF : forall o n, F <= o -> o + n <= F + 1024 -> (forall r, In r Wc -> F + 96 <= fst r -> fst r + snd r <= F + 1008 -> fst r + snd r <= o \/ o + n <= fst r) -> PMHAK2.wapart Wc o n).
{ intros o n H1 H2 H r Hr. destruct (WcL r Hr) as [(Z1 & Z2)|[-> | ->]]; [exact (H r Hr Z1 Z2)| cbn [fst snd]; left; clear - H1 FR; lia| cbn [fst snd]; left; clear - H1 FR; lia]. }
assert (LS' : PMSTA.ls_okA RSEGS PMB.AD PMB.AAD (PMST.ST (PMST.st_loc g) (PMST.st_sys g) e') M').
{ apply (PMHAK.ls_ahpres_err L C LY g e' ar _ FF' (V2 - 128) 34816 Wc M8 M' HP'); [| exact LS| exact ERR'].
intros a Ha r Hr Hin. unfold L5.in_rng in Hin. unfold PMHAK.bcell, PMHAK.lcell, PMHAK.scell in Ha.
destruct (WcL r Hr) as [(Z1 & Z2)|[-> | ->]]; cbn [fst snd] in Hin; [clear - Ha Hin Z1 Z2 FR; lia| clear - Ha Hin; lia| clear - Ha Hin; lia]. }
assert (BI' : Bv W (PM.parser_own ps' ++ PM.vs_own str ++ PM.vs_own s) M' model' LK' cr' Aw').
{ apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W W _ (PM.vs_own str ++ PM.vs_own s) _ M8 model8 LK8 cr8 A8 M' model' LK' cr' Aw' 34816 Wc BI HP' HH' AM' MRT' INCA' INCLK').
- lia.
- clear - CLS; lia.
- intros rr a Hr Ha. unfold L5.in_rng in Ha. unfold tocell. destruct (WcL rr Hr) as [(Z1 & Z2)|[-> | ->]]; cbn [fst snd] in Ha.
+ split; [clear - Ha Z1 Z2 FCEIL SLO CLS; lia|]. unfold HeapIfaceA.SB. change (ff_bytes 4) with 1024. clear - Ha Z1 Z2 FR F8 FBIG. lia.
+ split; [clear - Ha SLO SPT; lia|]. unfold HeapIfaceA.SB. change (ff_bytes 4) with 1024. clear - Ha FR F8. lia.
+ split; [clear - Ha SLO SPT; lia|]. unfold HeapIfaceA.SB. change (ff_bytes 4) with 1024. clear - Ha FR F8. lia.
- intros a Hc Ho rr Hr Ha. unfold L5.in_rng in Ha. destruct (WcL rr Hr) as [(Z1 & Z2)|[-> | ->]].
+ apply (NCF a); [left; clear - Ha Z1 Z2; lia| exact Hc].
+ exact (WERR a Ho _ (or_introl eq_refl) Ha).
+ exact (WERR a Ho _ (or_intror (or_introl eq_refl)) Ha).
- intros a X. exact X. }
pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W _ M' model' LK' cr' Aw' BI')
as ((VW' & VIC' & VSB' & VUAR' & VMS') & VOWN' & (VFD' & VFW' & VFSW' & VFLC' & VFLW') & (FLCc' & FLV' & FV' & SPV' & FSV')).
change (ff_bytes 4) with 1024 in *. change (1024 / 8) with 128 in *.
set (H' := ahid Aw' model') in *. set (MV' := mrestrict H' M') in *.
assert (RI' : rinvH R R' V2 cls F) by exact (rinvH_pres R R8 R' V2 cls F RI RP').
pose proof RI' as (Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y24 & Y25 & Y3 & Y4 & Y27).
assert (Y21 : getr R' (reg 21) = Z_to_bv 64 (F + 96)) by (rewrite (cs_of_preserved R8 R' 21 RP') by inl; exact R21).
assert (Y22 : getr R' (reg 22) = Z_to_bv 64 (F + 992)) by (rewrite (cs_of_preserved R8 R' 22 RP') by inl; exact R22).
assert (Y23 : getr R' (reg 23) = Z_to_bv 64 (F + 464)) by (rewrite (cs_of_preserved R8 R' 23 RP') by inl; exact R23).
assert (Y26 : getr R' (reg 26) = Z_to_bv 64 18446744073709551608) by (rewrite (cs_of_preserved R8 R' 26 RP') by inl; exact R26).
assert (FIN8 : In (F, 4, V2 - 128 + 32) (FF' ++ LK8)) by (apply in_or_app; left; left; reflexivity).
assert (VS' : PM.vstr_at RSEGS PMSPA.accA M' (F + 32) s).
{ eapply PMHAK2.vstr_keep_callee; first [ exact LY | exact HIok | exact B1 | exact HP' | exact VS0 | exact FHF | exact FIN8 | exact WFI | exact (or_introl eq_refl)
| (split; reflexivity) | (intros x Hx; apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; exact Hx)
| (intros x Hx; apply in_or_app; left; apply in_or_app; right; exact Hx)
| (apply WAF; [lia| lia| intros r Hr Z1 Z2; clear - Z1; lia]) | lia ]. }
assert (AGV : PMFA.agA M8 M' (F + 432) 8).
{ apply (PMHAK2.ff_callee L ar _ FF' (V2 - 128) 34816 Wc M8 M' (F, 4, V2 - 128 + 32) F (F + 432) 8 HP' (or_introl eq_refl));
cbn [ff_addr ff_class fst snd]; change (ff_bytes 4) with 1024; [lia| lia| exact FHF| lia| lia| exact WFI|].
apply WAF; [lia| lia|]. intros r Hr Z1 Z2. subst Wc. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; cbn [fst snd] in *; clear - Z1 Z2 FR; lia. }
assert (VZ' : shadow_zero M' (F + 432) 1) by (apply (PMHAK2.shz_agA M8 M' (F + 432) 8 (F + 432) 1 AGV); [lia| lia| clear - FM8; lia| lia| exact VZ0]).
assert (VI' : shadow_zero M' (F + 96) 34)
by (apply (PMHAK2.shz_callee L ar _ FF' (V2 - 128) 34816 Wc M8 M' (F, 4, V2 - 128 + 32) F (F + 96) 34 HP' (or_introl eq_refl) (conj eq_refl eq_refl) FHF WFI);
[lia| lia| clear - FM8; lia| lia| exact VI0]).
destruct (PMHAK2.hdead_of_parser M' F ps' PA') as (HS' & TB' & HV').
pose proof (PMBHP2.haH_conc fx' R' MV' (fun j => match j with 2%nat => V2 | 34%nat => F + 992 | 40%nat => F | 41%nat => fl | 58%nat => U R' 1 | _ => 0 end)) as P.
cbn beta iota in P.
assert (Q1 : 4096 <= F <= 140737488354304) by (clear - FR; lia).
assert (Q2 : 4096 <= fl <= 140737488355327) by (clear - FLR; lia).
assert (Q3 : V2 - 128 + 144 <= F \/ F + 1024 <= V2 - 128) by (clear - FCEIL SLO CLS; lia).
assert (Q4 : V2 - 128 + 144 <= fl \/ fl + 1 <= V2 - 128) by (clear - FLR SLO CLS; lia).
assert (Q5 : L5.writable RSEGS MV' (V2 - 128) 128) by (eapply L5.writable_sub; [exact VW'| clear; lia| clear - CLS; lia]).
assert (Q6 : L5.u64_at RSEGS MV' (F + 1016) fl) by (replace (F + 1016) with (F + 1024 - 8) by (clear; lia); exact VFLC').
feed P ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
| exact VFD' | exact VFW' | exact VFSW' | exact VFLW' | exact Q5 | exact Q6 | (unfold PMBHP2.aligned; exact V2A) ]).
destruct P as (fx9 & R9 & M9v & MG9 & hFR & hFZ & (hMS & hKS & hR1 & hR10 & hT & hVP & HQ)).
set (W9 := fun a => V2 - 104 <= a < V2 - 104 + 8 \/ F + 464 <= a < F + 464 + 8 \/ F / 8 + 2147451004 <= a < F / 8 + 2147451004 + 2).
apply (apiece L ar C HI LYa HIok _ FF' LK' cr' Aw' M' model' fx' fx9 R' 0xa7e28 R9 0xaade4 M9v W9 K HH' AM' hMS MG9).
{ intros a Ha Hna. apply hFZ; [exact Ha|..]; intros X; apply Hna; subst W9; cbn beta; clear - X; lia. }
{ intros a Ha Wa. subst W9; cbn beta in Wa. split.
- destruct Wa as [Wa|[Wa|Wa]].
+ apply stack_client; clear - Wa SLO SHI SPT CLS V2R; lia.
+ apply (fframe_client L ar _ _ 0 0 F 4 (V2 - 128 + 32)). left; reflexivity. change (ff_bytes 4) with 1024. clear - Wa; lia.
+ apply (fframe_shadow_client L ar _ _ 0 0 F 4 (V2 - 128 + 32)). left; reflexivity. change (ff_bytes 4) with 1024.
unfold in_shadow_of, HeapIfaceA.S. rewrite (proj1 (proj2 F8)). unfold HeapIfaceA.SB. clear - Wa. lia.
- unfold HeapIfaceA.SB in *. clear - Wa FR V2R. lia. }
intros M9 model9 HH9 AM9 MRT9 HID9 VIS9 MGM9 FR9 VV9. change (mrestrict H' M9 = M9v) in VIS9.
assert (BI9 : Bv W (PM.parser_own ps' ++ PM.vs_own str ++ PM.vs_own s) M9 model9 LK' cr' Aw').
{ apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W _ M' model' LK' cr' Aw' M9 model9 W9 BI' HH9 AM9 MRT9 MGM9 FR9).
intros a Wa. subst W9; cbn beta in Wa. change (ff_bytes 4) with 1024. change (1024 / 8) with 128. destruct Wa as [Wa|[Wa|Wa]].
- left. split; [clear - Wa CLS; lia|]. unfold tocell. clear - Wa CLS. lia.
- right; left. clear - Wa. lia.
- right; right. unfold HeapIfaceA.SB. clear - Wa. lia. }
assert (RI9 : rinvH R R9 V2 cls F) by (apply (rinvH_ks R R' R9 V2 cls F PMBHP2.KS_haH RI' hKS); vm_compute; reflexivity).
assert (LS9 : PMSTA.ls_okA RSEGS PMB.AD PMB.AAD (PMST.ST (PMST.st_loc g) (PMST.st_sys g) e') M9).
{ apply (PMHAK.ls_piece _ M' M9 W9 FR9); [| exact LS']. intros a Wa. subst W9; cbn beta in Wa. clear - Wa FR V2R. lia. }
assert (PF9 : PMHAK2.pfoot F (V2 - 128) V2 W9) by (intros a Wa; subst W9; cbn beta in Wa; unfold HeapIfaceA.SB; clear - Wa; lia).
assert (FIN' : In (F, 4, V2 - 128 + 32) (FF' ++ LK')) by (apply in_or_app; left; left; reflexivity).
assert (SLOW : ahl_ceil ar <= V2 - 128) by (clear - SLO CLS; lia).
assert (SHW : BIGSHADOW_HI <= V2 - 128) by (unfold BIGSHADOW_HI; clear - V2R; lia).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
assert (OAX : forall o n, F + 472 <= o -> o + n <= F + 992 -> PMHAK2.oav W9 o n).
{ intros o n H1 H2 x Hx. subst W9; cbn beta. pose proof (PMKB.S_in_shadow x ltac:(clear - Hx H1 H2 FR; lia)) as SX.
unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *. split; intros X; clear - Hx X H1 H2 SX FBIG FR FM8 V2R SLO FCEIL CLS; lia. }
assert (OAY : forall o n, F + 32 <= o -> o + n <= F + 464 -> PMHAK2.oav W9 o n).
{ intros o n H1 H2 x Hx. subst W9; cbn beta. pose proof (PMKB.S_in_shadow x ltac:(clear - Hx H1 H2 FR; lia)) as SX.
unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *. split; intros X; clear - Hx X H1 H2 SX FBIG FR FM8 V2R SLO FCEIL CLS; lia. }
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
assert (INCP : incl (PM.parser_own ps') ((PM.parser_own ps' ++ PM.vs_own str ++ PM.vs_own s) ++ LB)) by (intros x Hx; apply in_or_app; left; apply in_or_app; left; exact Hx).
apply (KONT fx9 R9 M9 model9 LK' cr' Aw' ps' sm' e' BI9 RI9 LS9 (EIMP)).
- exact hR1.
- exact hR10.
- rewrite (hKS 21%nat) by inl. exact Y21.
- rewrite (hKS 22%nat) by inl. rewrite (cs_of_preserved R8 R' 22 RP') by inl. exact R22.
- rewrite (hKS 23%nat) by inl. exact Y23.
- rewrite (hKS 26%nat) by inl. exact Y26.
- apply (PMHAK2.hbase_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 W9 M' M9 SLOW SHW FR9 PF9 s str sm');
[intros x Hx; apply in_or_app; left; apply in_or_app; right; exact Hx| apply OAY; lia| apply OAY; lia| apply OAY; lia|].
split; [exact VS'|]. split; [exact IS'|]. split; [cbn [pa_vp_visitor PMB.AD ADDR_A]; exact VV'| split; [exact VZ'| exact VI']].
- apply (PMHAK2.hsrc_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 W9 M' M9 SLOW SHW FR9 PF9 (PM.p_src ps'));
[apply INCP; left; reflexivity| apply OAX; lia| exact HS'].
- apply (PMHAK2.vstr_keep_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 W9 M' M9 SLOW SHW FR9 PF9 (F + 800) (PM.p_tb ps'));
[intros x Hx; apply INCP; unfold PM.parser_own; apply in_or_app; right; apply in_or_app; right; exact Hx| clear - FR; lia| clear - FR; lia| apply OAX; lia| exact TB'].
- apply (PMHAK2.hvec_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 W9 M' M9 SLOW SHW FR9 PF9 (PM.p_b ps') (PM.p_k ps') (PM.p_stk ps'));
[apply INCP; unfold PM.parser_own; apply in_or_app; right; left; reflexivity| apply OAX; lia| exact HV'].
- apply (PMHAK.u64_vis H' M9 M9v (V2 - 104) _ VV9); [| clear - V2R; lia| clear - V2R; lia| exact hT].
apply (PMHAK.avis_sub H' (V2 - 128) (V2 + cls - (V2 - 128)) (V2 - 104) 8 SPV'); clear - CLS; lia.
- exact CK'.
Qed.
End Stage.
End SCFG_1.
End PMHA7.
