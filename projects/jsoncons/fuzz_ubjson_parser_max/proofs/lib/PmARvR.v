(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceA LibIface AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreA L5CoreSpecsA L5StepAR L5CoreBR L5ADetailHR PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAa PmModelFactsA PmStepA PmStep PmParStep PmParKit PmASrcKit PmAParKit PmAReset1 PmAUarK PmAUar PmARvK PmARvF PmARvS PmARvC PmARdValP1 PmARdValP2 PmARdValP3 PmARdValP4 PmARdValP5 PmARdValP6 PmARdValP7 PmARdValP8 PmSRdValD.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmARvR () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5KnA.L5KA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmARvK.PMARVK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmParKit.PMPK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSRdValD.PMSRVD."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Ac"; "1list"; "1option"; "1prod"; "2eq"; "2ex"; "3Z"; "0E"; "0HI"; "0L"; "0LKc"; "4Model"; "5bvmap"; "0M"; "0Mc"; "0R"]; ["0Rc"; "6msteps"; "7credit"; "8fframe"; ":u8_at"; "9SCFG"; ";zeros_at"; "<rvc"; "<rve"; "<rvst"; "<vK"; "<vcat"; "<ve0"; "<vs0"; "<vsm0"; "=inv"]; ["=p_more"; "=pst"; "=srcst"; "=strm"; ">set_more"; "?rvR"; "@cfg"; "@prog_value"; "@with_src"; "AFPState"; "Agetr"; "Amkst"; "Aseg_rom"; "Bsrealizes"; "Cloaded_segments"; "0SCFG_P"]; ["Dadd"; "Dle"; "Dof_nat"; "Dpow"; "0X"; "0a"; "0ar"; "0crc"; "0fx"; "0fx'"; "0modelc"; "0s"; "0s0"; "0sm'"; "0sm0"; "0src'"]; ["EZ_to_bv"; "Ebv"; "0t"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia.
Module PMARVR.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Lemma inv_ws : ltac2:(TCodec.tc2 tcn__PmARvR "@'Q1'Q2&Or2%211&Q4&Q8r3+1%4221%4217%6213%:11p091pT0=1pSH?1").
Proof. intros s src'. destruct s as [mo dn dp src tb tg vb vk stk]. intros INV. pose proof INV as (IM & _). cbn [PM.p_more] in IM. subst mo. exact INV. Qed.
Lemma prog_ws : ltac2:(TCodec.tc2 tcn__PmARvR "C'Q1'Q2'Q3&Q7r4&Q4&Q8+1%3241r3%4221%6214r2r1%;4:321pSL=1pSN>1pT0@1pSJB1").
Proof. intros s0 src' sm0 sm'. unfold PMSPA.prog_value, PMSPA.push_rel. left. destruct s0; reflexivity. Qed.
Lemma more_ws : ltac2:(TCodec.tc2 tcn__PmARvR "@'Q1'Q2'4'6&Q0&Q8&Q4r2+1%3221r1%6221%811%;3:15pT0=1pSH?1").
Proof. intros s src'. destruct s; reflexivity. Qed.
Lemma fp_d : ltac2:(TCodec.tc2 tcn__PmARvR "Q3'Q9&<y5'R1yR0%211%5241'2y8%611%311p061'5'A&Q>&Q;r4r3&R0+egn@%22@1r2&Q<%119%9587431r1+egnH%92G1%=53;175%@3?51qSDN1%C2O1pLE1pQ0K1pSBQ21").
Proof. intros fx R M.
destruct (PMPX.fmv_fx_run RSEGS fx R M 0xadfd0 (ltac:(oW' 0xadfd0%Z)) FMT_S 15%bv 11%bv (ltac:(oF' 0xadfd0%Z)) eq_refl (ltac:(oD' 0xadfd0%Z)) (or_introl eq_refl) ltac:(lia) ltac:(lia)) as (fx1 & MS1).
destruct (PMPX.fcvt_f_run RSEGS fx1 R M 0xadfd4 (ltac:(oW' 0xadfd4%Z)) FC_D FC_S 10%bv 15%bv 0%bv (ltac:(oF' 0xadfd4%Z)) eq_refl (ltac:(oD' 0xadfd4%Z)) (or_intror eq_refl) ltac:(vm_compute; discriminate) ltac:(lia) ltac:(lia))
as (fx2 & MS2).
exists fx2. change (0xadfd0 + 4) with 0xadfd4 in MS1. change (0xadfd4 + 4) with 0xadfd8 in MS2. eapply msteps_trans; [exact MS1| exact MS2].
Qed.
Lemma fp_D : ltac2:(TCodec.tc2 tcn__PmARvR "Q3'Q9&<y5'R1yR0%211%5241'2y8%611%311p061'5'A&Q>&Q;r4r3&R0+egb@%22@1r2&Q<%119%9587431r1+egbD%92G1%=53;175%@3?51qSDN1%C2O1pLE1pQ0K1pSBQ21").
Proof. intros fx R M.
destruct (PMPX.fmv_fx_run RSEGS fx R M 0xade50 (ltac:(oW' 0xade50%Z)) FMT_D 10%bv 11%bv (ltac:(oF' 0xade50%Z)) eq_refl (ltac:(oD' 0xade50%Z)) (or_intror eq_refl) ltac:(lia) ltac:(lia)) as (fx1 & MS1).
exists fx1. change (0xade50 + 4) with 0xade54 in MS1. exact MS1.
Qed.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithHeap.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis MKE : PMA.make_ec_spec L ar HI.
Hypothesis SR : PMA.src_read_spec L ar HI.
Hypothesis VAL : PMA.validate_spec L ar HI.
Let LYa := PMA.ly_as0 L C LY.
Ltac Vof E := constr:(fun j : nat => match j with 2%nat => PMARVK.vsp E | 36%nat => PMARVK.op E | 37%nat => PMARVK.ov E
| 38%nat => PMARVK.oec E | 47%nat => PMARVK.vF E | 48%nat => PMARVK.vfl E | _ => 0 end).
Local Ltac ztail P :=
lazymatch goal with ST : PMARVK.rvst _ _ _ ?E ?Rc ?Mc ?modelc ?LKc ?crc ?Ac ?s ?sm true ?w _, X : PMARVK.rvc _ _ _ ?E |- srealizes _ _ (@PMSPA.cfg _ ?fx _ ?pc _ _) _ =>
PMARVK.rvfacts L ar C HI LY HIok E X ST;
pose proof (P fx Rc (mrestrict (ahid Ac modelc) Mc) (fun j : nat => match j with 2%nat => PMARVK.vsp E | 36%nat => PMARVK.op E | 37%nat => PMARVK.ov E
| 38%nat => PMARVK.oec E | 47%nat => PMARVK.vF E | 48%nat => PMARVK.vfl E | 50%nat => w | _ => 0 end)) as PP;
cbn beta iota in PP; L5SAR.feed PP ltac:(first [PMARVK.rvsc | lia]);
let fx1 := fresh "fz" in let R1 := fresh "Rz" in let M1v := fresh "Mz" in let MG1 := fresh "MGz" in let FZ1 := fresh "FZz" in let EX := fresh "EXz" in
destruct PP as (fx1 & R1 & M1v & MG1 & _ & FZ1 & EX);
let MS1 := fresh "MSz" in let KS1 := fresh "KSz" in let Z1 := fresh "Zr1" in let Z10 := fresh "Zr10" in let Z11 := fresh "Zr11" in
destruct EX as (MS1 & KS1 & Z1 & Z10 & Z11 & EX);
apply (PMARVF.rv_fin L ar C HI LY HIok E X fx Rc pc Mc modelc LKc crc Ac s sm true w (pa_errcat_obj PMA.AD) 0 fx1 R1 M1v ST MS1 MG1);
[ let a := fresh "a" in let Ha := fresh "Ha" in let N1 := fresh "N1" in let N2 := fresh "N2" in let N3 := fresh "N3" in
intros a Ha N1 N2 N3; apply FZ1;
first [ exact Ha | (let Y := fresh "Y" in intros Y; first [ (apply N1; clear - Y; lia) | (apply N2; clear - Y; lia) | (apply N3; clear - Y; lia) ]) ]
| decompose [and] EX; assumption
| left; reflexivity
| exact Z1 | exact Z10 | exact Z11
| apply (PMARVK.mid_keep E Rc R1); [pose proof ST as (_ & ?MD0 & _); assumption| PMARVK.kks KS1]
| left; split; [lia|]; split; [reflexivity|]; split; reflexivity ]
end.
Local Ltac direct T N V Z off j w vb sak rar ramk :=
lazymatch goal with ST : PMARVK.rvst _ _ _ ?E ?Rc ?Mc ?modelc ?LKc ?crc ?Ac _ _ _ _ _, X : PMARVK.rvc _ _ _ ?E |- srealizes _ _ (@PMSPA.cfg _ ?fx _ _ _ _) _ =>
PMARVK.rvfacts L ar C HI LY HIok E X ST; PMARVK.rvfactsv L ar C HI LY HIok IL ICok ILY E X ST;
pose proof (PMARVK.rvmore_of L ar C HI LY HIok E X _ _ _ _ _ _ _ _ _ _ _ ST) as MO0;
pose proof (PMARVK.c_INV L ar HI E X) as INV0; let IM0 := fresh "IM0" in pose proof INV0 as (IM0 & _); rewrite IM0 in MO0;
pose proof (T fx Rc (mrestrict (ahid Ac modelc) Mc) ltac:(let v := Vof E in exact v)) as PP;
cbn beta iota in PP; L5SAR.feed PP ltac:(PMARVK.rvsc);
let fx1 := fresh "fx" in let R1 := fresh "R" in let M1v := fresh "M" in let MG1 := fresh "MG" in let FZ1 := fresh "FZ" in
let MS1 := fresh "MS" in let KS1 := fresh "KS" in let EXT := fresh "EXT" in
destruct PP as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & EXT); decompose [and] EXT; clear EXT;
apply (PMARVS.rv_step L ar C HI LY HIok E X fx Rc 0xad76c Mc modelc LKc crc Ac _ _ _ 0 (PMARVK.vcat E) fx1 R1 0xaf334 M1v
(fun a => PMARVK.vF E / 8 + 2147450880 <= a < PMARVK.vF E / 8 + 2147450880 + 64) 1 ST MS1 MG1);
[ let a := fresh "a" in let Ha := fresh "Ha" in let Na := fresh "Na" in intros a Ha Na; apply FZ1; [exact Ha| let Y := fresh "Y" in intros Y; apply Na; clear - Y; lia]
| let a := fresh "a" in let Wa := fresh "Wa" in intros a Wa; right; left; exact Wa
| match goal with HO : 6885376 <= PMARVK.op _ <= _, HO3 : (_ <= PMARVK.op _ \/ PMARVK.op _ + 384 <= _), HF : 6885376 <= PMARVK.vF _ <= _ |- _ =>
apply (L5C.u8_at_agree RSEGS (mrestrict (ahid Ac modelc) Mc) M1v); [| clear - HO; lia| clear - HO; lia| exact MO0];
let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; apply FZ1; [clear - Hi HO; lia| clear - Hi HO HO3 HF; lia] end
| right; reflexivity
| apply (PMARVK.mid_keep E Rc R1); [pose proof ST as (_ & ?MD0 & _); assumption| PMARVK.kks KS1]
| ];
let M1 := fresh "M" in let model1 := fresh "model" in let ST1 := fresh "ST" in let VIS1 := fresh "VIS" in intros M1 model1 ST1 VIS1;
let ACC1 := fresh "ACC" in
assert (ACC1 : aacc M1 (PMARVK.vF E + 8 * j) w)
by (apply (PMARVC.rv_local_acc L ar C HI LY HIok E X _ _ _ _ _ _ _ _ _ _ _ j w vb (PMARVK.vF E / 8 + sak) ST1);
[clear; lia| clear; lia| first [left; split; [reflexivity| clear; lia] | right; split; reflexivity]| clear; lia| rewrite VIS1; assumption]);
replace (PMARVK.vF E + 8 * j) with (PMARVK.vF E + off) in ACC1 by (clear; lia);
apply (PMARVC.rv_sread L ar C HI LY HIok SR E X fx1 R1 M1 model1 LKc crc Ac _ _ _ 0 (PMARVK.vcat E) rar (PMARVK.vF E + off) w ST1);
[ assumption | split; [clear; lia| reflexivity] | assumption | assumption | assumption | clear; lia | clear; lia | clear; lia | exact ACC1 | ];
let fx2 := fresh "fx" in let R2 := fresh "R" in let M2 := fresh "M" in let model2 := fresh "model" in let LK2 := fresh "LK" in let Ac2 := fresh "Ac" in
let src2 := fresh "src" in let sm2 := fresh "sm" in let d := fresh "d" in let ST2 := fresh "ST" in let RP2 := fresh "RP" in
let Yd := fresh "Yd" in let Hd := fresh "Hd" in let DEFd := fresh "DEFd" in let SHK := fresh "SHK" in
intros fx2 R2 M2 model2 LK2 Ac2 src2 sm2 d ST2 RP2 Yd Hd DEFd SHK;
let R223 := fresh "R223" in
assert (R223 : getr R2 (reg 23) = Z_to_bv 64 (PMARVK.vF E + off)) by (rewrite (L5SAR.cs_of_preserved R1 R2 23 RP2) by inl; assumption);
try (let R224 := fresh "R224" in assert (R224 : getr R2 (reg 24) = Z_to_bv 64 w) by (rewrite (L5SAR.cs_of_preserved R1 R2 24 RP2) by inl; assumption));
clear MO0;
PMARVK.rvfacts L ar C HI LY HIok E X ST2; PMARVK.rvfactsv L ar C HI LY HIok IL ICok ILY E X ST2;
let Dw := fresh "Dw" in destruct (Z.eq_dec d w) as [Dw|Dw];
[
subst d;
let DEFv := fresh "DEFv" in
pose proof (PMARVC.rv_local_def L ar C HI LY HIok E X _ _ _ _ _ _ _ _ _ _ _ (PMARVK.vF E + off) w ST2 ltac:(clear; lia) ltac:(clear; lia) DEFd) as DEFv;
pose proof (V fx2 R2 (mrestrict (ahid Ac2 model2) M2) ltac:(let v := Vof E in exact v)) as PP;
cbn beta iota in PP; L5SAR.feed PP ltac:(PMARVK.rvsc);
let fx3 := fresh "fx" in let R3 := fresh "R" in let M3v := fresh "M" in let MG3 := fresh "MG" in let FZ3 := fresh "FZ" in
let MS3 := fresh "MS" in let KS3 := fresh "KS" in let EXT := fresh "EXT" in
destruct PP as (fx3 & R3 & M3v & MG3 & _ & FZ3 & MS3 & KS3 & EXT);
apply (PMARVS.rv_step L ar C HI LY HIok E X fx2 R2 rar M2 model2 LK2 crc Ac2 _ _ _ 0 (PMARVK.vcat E) fx3 R3 0xae110 M3v
(fun a => (PMARVK.vF E / 8 + 2147450880 <= a < PMARVK.vF E / 8 + 2147450880 + 64) \/ (PMARVK.op E + 8 <= a < PMARVK.op E + 9)) 1 ST2 MS3 MG3);
[ let a := fresh "a" in let Ha := fresh "Ha" in let Na := fresh "Na" in intros a Ha Na; apply FZ3;
first [ exact Ha | (let Y := fresh "Y" in intros Y; apply Na; first [ (right; clear - Y; lia) | (left; clear - Y; lia) ]) ]
| let a := fresh "a" in let Wa := fresh "Wa" in intros a [Wa|Wa]; [right; left; exact Wa| right; right; exact Wa]
| decompose [and] EXT; assumption
| right; reflexivity
| apply (PMARVK.mid_keep E R2 R3); [pose proof ST2 as (_ & ?MD0 & _); assumption| PMARVK.kks KS3]
| let M3 := fresh "M" in let model3 := fresh "model" in let ST3 := fresh "ST" in intros M3 model3 ST3 _;
apply (PMARVS.rv_j0 L ar C HI LY HIok E X fx3 R3 M3 model3 LK2 crc Ac2 _ _ _ ST3); [apply inv_ws; exact INV0| apply prog_ws] ]
|
first [ (let Ed := fresh "Ed" in assert (Ed : d = 0) by (clear - Hd Dw; lia); rewrite Ed in Yd) | idtac ];
pose proof (N fx2 R2 (mrestrict (ahid Ac2 model2) M2)
(fun jj : nat => match jj with 2%nat => PMARVK.vsp E | 36%nat => PMARVK.op E | 37%nat => PMARVK.ov E
| 38%nat => PMARVK.oec E | 47%nat => PMARVK.vF E | 48%nat => PMARVK.vfl E | 49%nat => d | _ => 0 end)) as PP;
cbn beta iota in PP; L5SAR.feed PP ltac:(first [PMARVK.rvsc | clear - Hd Dw; lia]);
let fx3 := fresh "fx" in let R3 := fresh "R" in let M3v := fresh "M" in let MG3 := fresh "MG" in let FRW3 := fresh "FRW" in let FZ3 := fresh "FZ" in
let MS3 := fresh "MS" in let KS3 := fresh "KS" in let B1 := fresh "B1" in let B10 := fresh "B10" in let B11 := fresh "B11" in
destruct PP as (fx3 & R3 & M3v & MG3 & FRW3 & FZ3 & MS3 & KS3 & B1 & B10 & B11);
assert (M3v = mrestrict (ahid Ac2 model2) M2) by (apply functional_extensionality; exact FRW3); subst M3v;
apply (PMARVC.rv_ro L ar C HI LY HIok E X fx2 R2 rar M2 model2 LK2 crc Ac2 _ _ _ 0 (PMARVK.vcat E) fx3 R3 0xae974 ST2 MS3
(PMARVK.mid_keep E R2 R3 ltac:(pose proof ST2 as (_ & ?MD0 & _); assumption) ltac:(PMARVK.kks KS3)));
let model3 := fresh "model" in let ST3 := fresh "ST" in intros model3 ST3 _;
apply (PMARVC.rv_mkec L ar C HI LY HIok MKE E X fx3 R3 M2 model3 LK2 crc Ac2 _ _ _ 0 (PMARVK.vcat E) 1 ramk ST3 B1 ltac:(split; [clear; lia| reflexivity]) B10 B11 ltac:(clear; lia));
let fx4 := fresh "fx" in let R4 := fresh "R" in let M4 := fresh "M" in let model4 := fresh "model" in let LK4 := fresh "LK" in let Ac4 := fresh "Ac" in
let ST4 := fresh "ST" in intros fx4 R4 M4 model4 LK4 Ac4 ST4 _;
clear ST ST1 ST2 ST3;
ztail Z ]
end.
Local Ltac directfp T N V V2 FPL pcv pcv2 Z off j w vb sak rar ramk :=
lazymatch goal with ST : PMARVK.rvst _ _ _ ?E ?Rc ?Mc ?modelc ?LKc ?crc ?Ac _ _ _ _ _, X : PMARVK.rvc _ _ _ ?E |- srealizes _ _ (@PMSPA.cfg _ ?fx _ _ _ _) _ =>
PMARVK.rvfacts L ar C HI LY HIok E X ST; PMARVK.rvfactsv L ar C HI LY HIok IL ICok ILY E X ST;
pose proof (PMARVK.rvmore_of L ar C HI LY HIok E X _ _ _ _ _ _ _ _ _ _ _ ST) as MO0;
pose proof (PMARVK.c_INV L ar HI E X) as INV0; let IM0 := fresh "IM0" in pose proof INV0 as (IM0 & _); rewrite IM0 in MO0;
pose proof (T fx Rc (mrestrict (ahid Ac modelc) Mc) ltac:(let v := Vof E in exact v)) as PP;
cbn beta iota in PP; L5SAR.feed PP ltac:(PMARVK.rvsc);
let fx1 := fresh "fx" in let R1 := fresh "R" in let M1v := fresh "M" in let MG1 := fresh "MG" in let FZ1 := fresh "FZ" in
let MS1 := fresh "MS" in let KS1 := fresh "KS" in let EXT := fresh "EXT" in
destruct PP as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & EXT); decompose [and] EXT; clear EXT;
apply (PMARVS.rv_step L ar C HI LY HIok E X fx Rc 0xad76c Mc modelc LKc crc Ac _ _ _ 0 (PMARVK.vcat E) fx1 R1 0xaf334 M1v
(fun a => PMARVK.vF E / 8 + 2147450880 <= a < PMARVK.vF E / 8 + 2147450880 + 64) 1 ST MS1 MG1);
[ let a := fresh "a" in let Ha := fresh "Ha" in let Na := fresh "Na" in intros a Ha Na; apply FZ1; [exact Ha| let Y := fresh "Y" in intros Y; apply Na; clear - Y; lia]
| let a := fresh "a" in let Wa := fresh "Wa" in intros a Wa; right; left; exact Wa
| match goal with HO : 6885376 <= PMARVK.op _ <= _, HO3 : (_ <= PMARVK.op _ \/ PMARVK.op _ + 384 <= _), HF : 6885376 <= PMARVK.vF _ <= _ |- _ =>
apply (L5C.u8_at_agree RSEGS (mrestrict (ahid Ac modelc) Mc) M1v); [| clear - HO; lia| clear - HO; lia| exact MO0];
let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; apply FZ1; [clear - Hi HO; lia| clear - Hi HO HO3 HF; lia] end
| right; reflexivity
| apply (PMARVK.mid_keep E Rc R1); [pose proof ST as (_ & ?MD0 & _); assumption| PMARVK.kks KS1]
| ];
let M1 := fresh "M" in let model1 := fresh "model" in let ST1 := fresh "ST" in let VIS1 := fresh "VIS" in intros M1 model1 ST1 VIS1;
let ACC1 := fresh "ACC" in
assert (ACC1 : aacc M1 (PMARVK.vF E + 8 * j) w)
by (apply (PMARVC.rv_local_acc L ar C HI LY HIok E X _ _ _ _ _ _ _ _ _ _ _ j w vb (PMARVK.vF E / 8 + sak) ST1);
[clear; lia| clear; lia| first [left; split; [reflexivity| clear; lia] | right; split; reflexivity]| clear; lia| rewrite VIS1; assumption]);
replace (PMARVK.vF E + 8 * j) with (PMARVK.vF E + off) in ACC1 by (clear; lia);
apply (PMARVC.rv_sread L ar C HI LY HIok SR E X fx1 R1 M1 model1 LKc crc Ac _ _ _ 0 (PMARVK.vcat E) rar (PMARVK.vF E + off) w ST1);
[ assumption | split; [clear; lia| reflexivity] | assumption | assumption | assumption | clear; lia | clear; lia | clear; lia | exact ACC1 | ];
let fx2 := fresh "fx" in let R2 := fresh "R" in let M2 := fresh "M" in let model2 := fresh "model" in let LK2 := fresh "LK" in let Ac2 := fresh "Ac" in
let src2 := fresh "src" in let sm2 := fresh "sm" in let d := fresh "d" in let ST2 := fresh "ST" in let RP2 := fresh "RP" in
let Yd := fresh "Yd" in let Hd := fresh "Hd" in let DEFd := fresh "DEFd" in let SHK := fresh "SHK" in
intros fx2 R2 M2 model2 LK2 Ac2 src2 sm2 d ST2 RP2 Yd Hd DEFd SHK;
let R223 := fresh "R223" in
assert (R223 : getr R2 (reg 23) = Z_to_bv 64 (PMARVK.vF E + off)) by (rewrite (L5SAR.cs_of_preserved R1 R2 23 RP2) by inl; assumption);
try (let R224 := fresh "R224" in assert (R224 : getr R2 (reg 24) = Z_to_bv 64 w) by (rewrite (L5SAR.cs_of_preserved R1 R2 24 RP2) by inl; assumption));
clear MO0;
PMARVK.rvfacts L ar C HI LY HIok E X ST2; PMARVK.rvfactsv L ar C HI LY HIok IL ICok ILY E X ST2;
let Dw := fresh "Dw" in destruct (Z.eq_dec d w) as [Dw|Dw];
[
subst d;
let DEFv := fresh "DEFv" in
pose proof (PMARVC.rv_local_def L ar C HI LY HIok E X _ _ _ _ _ _ _ _ _ _ _ (PMARVK.vF E + off) w ST2 ltac:(clear; lia) ltac:(clear; lia) DEFd) as DEFv;
pose proof (V fx2 R2 (mrestrict (ahid Ac2 model2) M2) ltac:(let v := Vof E in exact v)) as PP;
cbn beta iota in PP; L5SAR.feed PP ltac:(PMARVK.rvsc);
let fx3 := fresh "fx" in let R3 := fresh "R" in let M3v := fresh "M" in let MG3 := fresh "MG" in let FRW3 := fresh "FRW" in let FZ3 := fresh "FZ" in
let MS3 := fresh "MS" in let KS3 := fresh "KS" in let EXT := fresh "EXT" in
destruct PP as (fx3 & R3 & M3v & MG3 & FRW3 & FZ3 & MS3 & KS3 & EXT);
assert (M3v = mrestrict (ahid Ac2 model2) M2) by (apply functional_extensionality; exact FRW3); subst M3v;
let fx4 := fresh "fx" in let MSf := fresh "MSf" in destruct (FPL fx3 R3 (mrestrict (ahid Ac2 model2) M2)) as (fx4 & MSf);
apply (PMARVC.rv_ro L ar C HI LY HIok E X fx2 R2 rar M2 model2 LK2 crc Ac2 _ _ _ 0 (PMARVK.vcat E) fx4 R3 pcv2 ST2
ltac:(eapply msteps_trans; [exact MS3| exact MSf])
(PMARVK.mid_keep E R2 R3 ltac:(pose proof ST2 as (_ & ?MD0 & _); assumption) ltac:(PMARVK.kks KS3)));
let model3 := fresh "model" in let ST3 := fresh "ST" in let HID3 := fresh "HID" in intros model3 ST3 HID3;
decompose [and] EXT; clear EXT;
let R323 := fresh "R323" in assert (R323 : getr R3 (reg 23) = Z_to_bv 64 (PMARVK.vF E + off)) by (rewrite (KS3 23%nat) by inl; exact R223);
let R324 := fresh "R324" in assert (R324 : getr R3 (reg 24) = Z_to_bv 64 w) by (rewrite (KS3 24%nat) by inl; assumption);
PMARVK.rvfacts L ar C HI LY HIok E X ST3; PMARVK.rvfactsv L ar C HI LY HIok IL ICok ILY E X ST3;
pose proof (V2 fx4 R3 (mrestrict (ahid Ac2 model3) M2) ltac:(let v := Vof E in exact v)) as PP;
cbn beta iota in PP; L5SAR.feed PP ltac:(PMARVK.rvsc);
let fx5 := fresh "fx" in let R5 := fresh "R" in let M5v := fresh "M" in let MG5 := fresh "MG" in let FZ5 := fresh "FZ" in
let MS5 := fresh "MS" in let KS5 := fresh "KS" in let EXT := fresh "EXT" in
destruct PP as (fx5 & R5 & M5v & MG5 & _ & FZ5 & MS5 & KS5 & EXT);
apply (PMARVS.rv_step L ar C HI LY HIok E X fx4 R3 pcv2 M2 model3 LK2 crc Ac2 _ _ _ 0 (PMARVK.vcat E) fx5 R5 0xae110 M5v
(fun a => (PMARVK.vF E / 8 + 2147450880 <= a < PMARVK.vF E / 8 + 2147450880 + 64) \/ (PMARVK.op E + 8 <= a < PMARVK.op E + 9)) 1 ST3 MS5 MG5);
[ let a := fresh "a" in let Ha := fresh "Ha" in let Na := fresh "Na" in intros a Ha Na; apply FZ5;
first [ exact Ha | (let Y := fresh "Y" in intros Y; apply Na; first [ (right; clear - Y; lia) | (left; clear - Y; lia) ]) ]
| let a := fresh "a" in let Wa := fresh "Wa" in intros a [Wa|Wa]; [right; left; exact Wa| right; right; exact Wa]
| decompose [and] EXT; assumption
| right; reflexivity
| apply (PMARVK.mid_keep E R3 R5); [pose proof ST3 as (_ & ?MD0 & _); assumption| PMARVK.kks KS5]
| let M5 := fresh "M" in let model5 := fresh "model" in let ST5 := fresh "ST" in intros M5 model5 ST5 _;
apply (PMARVS.rv_j0 L ar C HI LY HIok E X fx5 R5 M5 model5 LK2 crc Ac2 _ _ _ ST5); [apply inv_ws; exact INV0| apply prog_ws] ]
|
first [ (let Ed := fresh "Ed" in assert (Ed : d = 0) by (clear - Hd Dw; lia); rewrite Ed in Yd) | idtac ];
pose proof (N fx2 R2 (mrestrict (ahid Ac2 model2) M2)
(fun jj : nat => match jj with 2%nat => PMARVK.vsp E | 36%nat => PMARVK.op E | 37%nat => PMARVK.ov E
| 38%nat => PMARVK.oec E | 47%nat => PMARVK.vF E | 48%nat => PMARVK.vfl E | 49%nat => d | _ => 0 end)) as PP;
cbn beta iota in PP; L5SAR.feed PP ltac:(first [PMARVK.rvsc | clear - Hd Dw; lia]);
let fx3 := fresh "fx" in let R3 := fresh "R" in let M3v := fresh "M" in let MG3 := fresh "MG" in let FRW3 := fresh "FRW" in let FZ3 := fresh "FZ" in
let MS3 := fresh "MS" in let KS3 := fresh "KS" in let B1 := fresh "B1" in let B10 := fresh "B10" in let B11 := fresh "B11" in
destruct PP as (fx3 & R3 & M3v & MG3 & FRW3 & FZ3 & MS3 & KS3 & B1 & B10 & B11);
assert (M3v = mrestrict (ahid Ac2 model2) M2) by (apply functional_extensionality; exact FRW3); subst M3v;
apply (PMARVC.rv_ro L ar C HI LY HIok E X fx2 R2 rar M2 model2 LK2 crc Ac2 _ _ _ 0 (PMARVK.vcat E) fx3 R3 0xae974 ST2 MS3
(PMARVK.mid_keep E R2 R3 ltac:(pose proof ST2 as (_ & ?MD0 & _); assumption) ltac:(PMARVK.kks KS3)));
let model3 := fresh "model" in let ST3 := fresh "ST" in intros model3 ST3 _;
apply (PMARVC.rv_mkec L ar C HI LY HIok MKE E X fx3 R3 M2 model3 LK2 crc Ac2 _ _ _ 0 (PMARVK.vcat E) 1 ramk ST3 B1 ltac:(split; [clear; lia| reflexivity]) B10 B11 ltac:(clear; lia));
let fx4 := fresh "fx" in let R4 := fresh "R" in let M4 := fresh "M" in let model4 := fresh "model" in let LK4 := fresh "LK" in let Ac4 := fresh "Ac" in
let ST4 := fresh "ST" in intros fx4 R4 M4 model4 LK4 Ac4 ST4 _;
clear ST ST1 ST2 ST3;
ztail Z ]
end.
Lemma armI : ltac2:(TCodec.tc2 tcn__PmARvR "RJ'H'GvQ?v9vQFv8r1%6554321'Q9&<y5'R1yR0%211%5241'2y8%611%311p061';'1&C%211&B'3'6%2211%711&Ir9r6r5r4r3r2&M%117&N%119&L%11;z&K%11>%@?Q:Q9Q8?>=<;:Q786431'4&Q:r7&R0&QBuG%211%42Q;1%7261+R9%72Q<1%;3Q<31r8u<%:11%<2QC1%?241+S3%?2QD1%C3QD31'Q=&Q>&E%11R3&Q6r:+eek<%3662Q;1?I&Jr<%211%;4:841p0=1p0F1p0Q31p2QE1pS@QJ1pFQL1pSFR01pNR21pQ2R81pSBR?1pS:RA1p@RI1").
Proof. intros E X fx Rc Mc modelc LKc crc Ac.
intros ST R23 R12.
direct PMARVP1.arvTI_conc PMARVP4.arvIN_conc PMARVP4.arvIV_conc PMARVP8.arvZI_conc 64 8 2 2 2147450888 0xadbe0 0xae23c.
Qed.
Lemma armL : ltac2:(TCodec.tc2 tcn__PmARvR "RJ'H'GvQ?v9vQFv8r1%6554321'Q9&<y5'R1yR0%211%5241'2y8%611%311p061';'1&C%211&B'3'6%2211%711&Ir9r6r5r4r3r2&M%117&N%119&L%11;z&K%11>%@?Q:Q9Q8?>=<;:Q786431'4&Q:r7&R0&QBuG%211%42Q;1%7261+R<%72Q<1%;3Q<31r8u<%:11%<2QC1%?241+S3%?2QD1%C3QD31'Q=&Q>&E%11R3&Q6r:+eek<%3662Q;1?I&Jr<%211%;4:841p0=1p0F1p0Q31p2QE1pS@QJ1pFQL1pSFR01pNR21pQ2R81pSBR?1pS:RA1p@RI1").
Proof. intros E X fx Rc Mc modelc LKc crc Ac.
intros ST R23 R12.
direct PMARVP1.arvTL_conc PMARVP4.arvLN_conc PMARVP5.arvLV_conc PMARVP8.arvZL_conc 96 12 8 0 2147450892 0xadc98 0xae26c.
Qed.
Lemma armU : ltac2:(TCodec.tc2 tcn__PmARvR "RJ'H'GvQ?v9vQFv8r1%6554321'Q9&<y5'R1yR0%211%5241'2y8%611%311p061';'1&C%211&B'3'6%2211%711&Ir9r6r5r4r3r2&M%117&N%119&L%11;z&K%11>%@?Q:Q9Q8?>=<;:Q786431'4&Q:r7&R0&QBuG%211%42Q;1%7261+RE%72Q<1%;3Q<31r8u<%:11%<2QC1%?241+S3%?2QD1%C3QD31'Q=&Q>&E%11R3&Q6r:+eek<%3662Q;1?I&Jr<%211%;4:841p0=1p0F1p0Q31p2QE1pS@QJ1pFQL1pSFR01pNR21pQ2R81pSBR?1pS:RA1p@RI1").
Proof. intros E X fx Rc Mc modelc LKc crc Ac.
intros ST R23 R12.
direct PMARVP2.arvTU_conc PMARVP4.arvUN_conc PMARVP4.arvUV_conc PMARVP8.arvZU_conc 48 6 1 1 2147450886 0xadec8 0xae3b0.
Qed.
Lemma armi : ltac2:(TCodec.tc2 tcn__PmARvR "RJ'H'GvQ?v9vQFv8r1%6554321'Q9&<y5'R1yR0%211%5241'2y8%611%311p061';'1&C%211&B'3'6%2211%711&Ir9r6r5r4r3r2&M%117&N%119&L%11;z&K%11>%@?Q:Q9Q8?>=<;:Q786431'4&Q:r7&R0&QBuG%211%42Q;1%7261+S9%72Q<1%;3Q<31r8u<%:11%<2QC1%?241+S3%?2QD1%C3QD31'Q=&Q>&E%11R3&Q6r:+eek<%3662Q;1?I&Jr<%211%;4:841p0=1p0F1p0Q31p2QE1pS@QJ1pFQL1pSFR01pNR21pQ2R81pSBR?1pS:RA1p@RI1").
Proof. intros E X fx Rc Mc modelc LKc crc Ac.
intros ST R23 R12.
direct PMARVP2.arvTi_conc PMARVP4.arviN_conc PMARVP4.arviV_conc PMARVP8.arvZi_conc 32 4 1 1 2147450884 0xad838 0xae380.
Qed.
Lemma arml : ltac2:(TCodec.tc2 tcn__PmARvR "RJ'H'GvQ?v9vQFv8r1%6554321'Q9&<y5'R1yR0%211%5241'2y8%611%311p061';'1&C%211&B'3'6%2211%711&Ir9r6r5r4r3r2&M%117&N%119&L%11;z&K%11>%@?Q:Q9Q8?>=<;:Q786431'4&Q:r7&R0&QBuG%211%42Q;1%7261+S<%72Q<1%;3Q<31r8u<%:11%<2QC1%?241+S3%?2QD1%C3QD31'Q=&Q>&E%11R3&Q6r:+eek<%3662Q;1?I&Jr<%211%;4:841p0=1p0F1p0Q31p2QE1pS@QJ1pFQL1pSFR01pNR21pQ2R81pSBR?1pS:RA1p@RI1").
Proof. intros E X fx Rc Mc modelc LKc crc Ac.
intros ST R23 R12.
direct PMARVP2.arvTl_conc PMARVP5.arvlN_conc PMARVP5.arvlV_conc PMARVP8.arvZl_conc 80 10 4 4 2147450890 0xae04c 0xae350.
Qed.
Lemma armd : ltac2:(TCodec.tc2 tcn__PmARvR "RJ'H'GvQ?v9vQFv8r1%6554321'Q9&<y5'R1yR0%211%5241'2y8%611%311p061';'1&C%211&B'3'6%2211%711&Ir9r6r5r4r3r2&M%117&N%119&L%11;z&K%11>%@?Q:Q9Q8?>=<;:Q786431'4&Q:r7&R0&QBuG%211%42Q;1%7261+S4%72Q<1%;3Q<31r8u<%:11%<2QC1%?241+S3%?2QD1%C3QD31'Q=&Q>&E%11R3&Q6r:+eek<%3662Q;1?I&Jr<%211%;4:841p0=1p0F1p0Q31p2QE1pS@QJ1pFQL1pSFR01pNR21pQ2R81pSBR?1pS:RA1p@RI1").
Proof. intros E X fx Rc Mc modelc LKc crc Ac.
intros ST R23 R12.
directfp PMARVP2.arvTd_conc PMARVP5.arvdN_conc PMARVP5.arvdV_conc PMARVP5.arvdV2_conc fp_d 0xadfd0 0xadfd8 PMARVP8.arvZd_conc 128 16 4 4 2147450896 0xadf70 0xae320.
Qed.
Lemma armD : ltac2:(TCodec.tc2 tcn__PmARvR "RJ'H'GvQ?v9vQFv8r1%6554321'Q9&<y5'R1yR0%211%5241'2y8%611%311p061';'1&C%211&B'3'6%2211%711&Ir9r6r5r4r3r2&M%117&N%119&L%11;z&K%11>%@?Q:Q9Q8?>=<;:Q786431'4&Q:r7&R0&QBuG%211%42Q;1%7261+R4%72Q<1%;3Q<31r8u<%:11%<2QC1%?241+S3%?2QD1%C3QD31'Q=&Q>&E%11R3&Q6r:+eek<%3662Q;1?I&Jr<%211%;4:841p0=1p0F1p0Q31p2QE1pS@QJ1pFQL1pSFR01pNR21pQ2R81pSBR?1pS:RA1p@RI1").
Proof. intros E X fx Rc Mc modelc LKc crc Ac.
intros ST R23 R12.
directfp PMARVP1.arvTD_conc PMARVP5.arvDN_conc PMARVP5.arvDV_conc PMARVP5.arvDV2_conc fp_D 0xade50 0xade54 PMARVP8.arvZD_conc 144 18 8 0 2147450898 0xaddb8 0xae29c.
Qed.
Lemma zeros2 : ltac2:(TCodec.tc2 tcn__PmARvR "Q8'R1yR0%211'2y8%511%311p051'6&D&Q>r2r1z%544321r3&Q@+1%2271%:49416&QA+QoooPP0%2217r4+2%9221&QC+Q?%2241%9241&Fr6r5%33219p051p0=1p0A1p0G1pS<N1pLQ01").
Proof. intros M a.
intros U0 U1 H1 H2 i Hi. assert (i = 0 \/ i = 1) as [->| ->] by lia.
- rewrite Z.add_0_r. apply (L5ADHR.byte_of_u8 M a 0 U0); lia.
- apply (L5ADHR.byte_of_u8 M (a + 1) 0 U1); lia.
Qed.
Lemma armC : ltac2:(TCodec.tc2 tcn__PmARvR "RJ'H'GvQ?v9vQFv8r1%6554321'Q9&<y5'R1yR0%211%5241'2y8%611%311p061';'1&C%211&B'3'6%2211%711&Ir9r6r5r4r3r2&M%117&N%119&L%11;z&K%11>%@?Q:Q9Q8?>=<;:Q786431'4&Q:r7&R0&QBuG%211%42Q;1%7261+R3%72Q<1%;3Q<31r8u<%:11%<2QC1%?241+S3%?2QD1%C3QD31'Q=&Q>&E%11R3&Q6r:+eek<%3662Q;1?I&Jr<%211%;4:841p0=1p0F1p0Q31p2QE1pS@QJ1pFQL1pSFR01pNR21pQ2R81pSBR?1pS:RA1p@RI1").
Proof. intros E X fx Rc Mc modelc LKc crc Ac.
intros ST R23 R12.
PMARVK.rvfacts L ar C HI LY HIok E X ST. PMARVK.rvfactsv L ar C HI LY HIok IL ICok ILY E X ST.
pose proof (PMARVK.rvmore_of L ar C HI LY HIok E X _ _ _ _ _ _ _ _ _ _ _ ST) as MO0.
pose proof (PMARVK.c_INV L ar HI E X) as INV0. pose proof INV0 as (IM0 & _). rewrite IM0 in MO0.
cfeed PP (PMARVP1.arvTC_conc fx Rc (mrestrict (ahid Ac modelc) Mc) ltac:(let v := Vof E in exact v)) ltac:(PMARVK.rvsc).
destruct PP as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & A1 & A10 & A11 & A12 & A23 & A24 & U176 & SH1 & _).
apply (PMARVS.rv_step L ar C HI LY HIok E X fx Rc 0xad76c Mc modelc LKc crc Ac _ _ _ 0 (PMARVK.vcat E) fx1 R1 0xaf334 M1v
(fun a => (PMARVK.vF E / 8 + 2147450880 <= a < PMARVK.vF E / 8 + 2147450880 + 64) \/ (PMARVK.vF E + 176 <= a < PMARVK.vF E + 177)) 1 ST MS1 MG1).
{ intros a Ha Na. apply FZ1; [exact Ha| intros Y; apply Na; left; clear - Y; lia| intros Y; apply Na; right; clear - Y; lia]. }
{ intros a [Wa|Wa]; [right; left; exact Wa| left; clear - Wa; lia]. }
{ apply (L5C.u8_at_agree RSEGS (mrestrict (ahid Ac modelc) Mc) M1v); [| clear - AO1; lia| clear - AO1; lia| exact MO0].
intros i Hi. apply FZ1; [clear - Hi AO1; lia| clear - Hi AO1 AO3 AF1; lia| clear - Hi AO1 AF9; lia]. }
{ right; reflexivity. }
{ apply (PMARVK.mid_keep E Rc R1); [pose proof ST as (_ & MD0 & _); exact MD0| PMARVK.kks KS1]. }
intros M1 model1 ST1 VIS1.
assert (ACC1 : aacc M1 (PMARVK.vF E + 8 * 22) 1).
{ apply (PMARVC.rv_local_acc L ar C HI LY HIok E X _ _ _ _ _ _ _ _ _ _ _ 22 1 1 (PMARVK.vF E / 8 + 2147450902) ST1); [clear; lia| clear; lia| left; split; [reflexivity| clear; lia]| clear; lia|].
rewrite VIS1. exact SH1. }
replace (PMARVK.vF E + 8 * 22) with (PMARVK.vF E + 176) in ACC1 by (clear; lia).
pose proof ST1 as (BI1 & _).
destruct (PMAUK.vis_facts L ar C HI LYa HIok (PMARVK.vM E) (PMARVK.vmodel E) (PMARVK.vLBX E) (PMARVK.vFF E) (PMARVK.vLK E) (PMARVK.vAw E) (PMARVK.vsp E) PMARVK.SCR
(PMARVK.vsp E - 128) (PMARVK.vsp E - 104) (PMARVK.vsp E) (PMARVK.ocell (PMARVK.vsp E)) (PMARVK.own (PMARVK.vsp E) (PMARVK.vR E)) (PMARVK.vF E) (PMARVK.vfl E) 3
(PMARVK.vLK2 E) (PMARVK.vM2 E) (PMARVK.vmodel2 E) (PMARVK.vcr E) (PM.parser_own (PMARVK.vs0 E)) (PMARVK.c_G L ar HI E X)
(PMARVK.WR E) _ M1 model1 LKc crc Ac BI1) as (_ & _ & _ & (_ & _ & _ & _ & VSH1)).
change (ff_bytes 3 / 8) with 64 in VSH1.
assert (DF1 : 0 <= PMARVK.vF E / 8) by (apply Z.div_pos; clear - AF1; lia).
assert (DF2 : PMARVK.vF E / 8 <= 17592186044352) by (apply Z.div_le_upper_bound; clear - AF1; lia).
assert (SHf1 : L5.u8_at RSEGS M1 (PMARVK.vF E / 8 + 2147450902) 1).
{ apply (proj1 (L5A.u8_at_vis _ M1 (PMARVK.vF E / 8 + 2147450902) 1 (L5A.avis_sub _ (PMARVK.vF E / 8 + SB) 64 (PMARVK.vF E / 8 + 2147450902) 1 VSH1 ltac:(unfold SB; clear; lia) ltac:(unfold SB; clear; lia)) ltac:(clear - DF1; lia) ltac:(clear - DF2; lia))).
rewrite VIS1. exact SH1. }
apply (PMARVC.rv_sread L ar C HI LY HIok SR E X fx1 R1 M1 model1 LKc crc Ac _ _ _ 0 (PMARVK.vcat E) 0xad7b8 (PMARVK.vF E + 176) 1 ST1 A1
ltac:(split; [clear; lia| reflexivity]) A10 A11 A12 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ACC1).
intros fx2 R2 M2 model2 LK2 Ac2 src2 sm2 d ST2 RP2 Yd Hd DEFd SHK.
assert (R223 : getr R2 (reg 23) = Z_to_bv 64 (PMARVK.vF E + 176)) by (rewrite (L5SAR.cs_of_preserved R1 R2 23 RP2) by inl; exact A23).
assert (R224 : getr R2 (reg 24) = Z_to_bv 64 1) by (rewrite (L5SAR.cs_of_preserved R1 R2 24 RP2) by inl; exact A24).
assert (SHf2 : L5.u8_at RSEGS M2 (PMARVK.vF E / 8 + 2147450902) 1).
{ apply (L5C.u8_at_agree RSEGS M1 M2); [| clear - DF1; lia| clear - DF2; lia| exact SHf1]. intros i Hi. apply SHK. clear - Hi; lia. }
clear MO0.
PMARVK.rvfacts L ar C HI LY HIok E X ST2. PMARVK.rvfactsv L ar C HI LY HIok IL ICok ILY E X ST2.
destruct (Z.eq_dec d 1) as [D1|D1].
-
subst d.
cfeed PP (PMARVP5.arvCV_conc fx2 R2 (mrestrict (ahid Ac2 model2) M2) ltac:(let v := Vof E in exact v)) ltac:(PMARVK.rvsc).
destruct PP as (fx3 & R3 & M3v & MGq3 & FRWq3 & FZq3 & MSq3 & KSq3 & B1 & B10 & B11).
assert (M3v = mrestrict (ahid Ac2 model2) M2) by (apply functional_extensionality; exact FRWq3). subst M3v.
apply (PMARVC.rv_ro L ar C HI LY HIok E X fx2 R2 0xad7b8 M2 model2 LK2 crc Ac2 _ _ _ 0 (PMARVK.vcat E) fx3 R3 0xafa88 ST2 MSq3
(PMARVK.mid_keep E R2 R3 ltac:(pose proof ST2 as (_ & MD0 & _); exact MD0) ltac:(PMARVK.kks KSq3))).
intros model3 ST3 _.
assert (ACC2 : aacc M2 (PMARVK.vF E + 8 * 22) 1)
by (apply (PMARVC.rv_local_acc_full M2 (PMARVK.vF E) 22 1 1 (PMARVK.vF E / 8 + 2147450902) AF1 AF2); [clear; lia| clear; lia| left; split; [reflexivity| clear; lia]| clear; lia| exact SHf2]).
replace (PMARVK.vF E + 8 * 22) with (PMARVK.vF E + 176) in ACC2 by (clear; lia).
pose proof VAL as SC. unfold PMA.validate_spec, PMSPA.validate_spec in SC. change (pa_validate PMA.AD) with 0xafa88 in SC.
pose proof (PMARVK.c_G L ar HI E X) as G'. destruct G' as [_ GSPT GSLO _ _ _ _ GFS1 GFS2 GFCEIL _ _ _ _ _ _ _ _ _ _ _ _ _ _].
change (ff_bytes 3) with 512 in *. unfold PMARVK.SCR in GSLO.
apply (PMARVC.rv_scan L ar C HI LY HIok 0xafa88 SC E X fx3 R3 M2 model3 LK2 crc Ac2 _ _ _ 0 (PMARVK.vcat E) 0xad7c8 (PMARVK.vF E + 176) 1 ST3 B1
ltac:(split; [clear; lia| reflexivity]) B10 B11 ltac:(clear; lia) ltac:(clear - AF1; lia) ltac:(right; clear - AF1; lia) ltac:(clear - AF1; lia) DEFd ACC2).
{ right; left. split; [clear - GFS1; lia| clear - GFS2; lia]. }
{ right; right. clear - GFCEIL GSLO GSPT AF1. lia. }
intros fx4 R4 M4 model4 ST4 RP4.
assert (R423 : getr R4 (reg 23) = Z_to_bv 64 (PMARVK.vF E + 176)) by (rewrite (L5SAR.cs_of_preserved R3 R4 23 RP4) by inl; rewrite (KSq3 23%nat) by inl; exact R223).
assert (R424 : getr R4 (reg 24) = Z_to_bv 64 1) by (rewrite (L5SAR.cs_of_preserved R3 R4 24 RP4) by inl; rewrite (KSq3 24%nat) by inl; exact R224).
PMARVK.rvfacts L ar C HI LY HIok E X ST4. PMARVK.rvfactsv L ar C HI LY HIok IL ICok ILY E X ST4.
pose proof (bv_unsigned_in_range 64 (getr R4 (reg 11))) as Hr11. change (bv_modulus 64) with (2 ^ 64) in Hr11.
assert (R411 : getr R4 (reg 11) = Z_to_bv 64 (bv_unsigned (getr R4 (reg 11)))) by (symmetry; apply Z_to_bv_bv_unsigned).
cfeed PP (PMARVP6.arvCW_conc fx4 R4 (mrestrict (ahid Ac2 model4) M4)
(fun j : nat => match j with 2%nat => PMARVK.vsp E | 36%nat => PMARVK.op E | 37%nat => PMARVK.ov E
| 38%nat => PMARVK.oec E | 47%nat => PMARVK.vF E | 48%nat => PMARVK.vfl E | 51%nat => bv_unsigned (getr R4 (reg 11)) | _ => 0 end)) ltac:(PMARVK.rvsc).
destruct PP as (fx5 & R5 & M5v & MGq5 & FRWq5 & FZq5 & [(MSq5 & KSq5)|(MSq5 & KSq5 & C1 & C10 & C11 & C24)]);
(assert (M5v = mrestrict (ahid Ac2 model4) M4) by (apply functional_extensionality; exact FRWq5)); subst M5v.
+
apply (PMARVC.rv_ro L ar C HI LY HIok E X fx4 R4 0xad7c8 M4 model4 LK2 crc Ac2 _ _ _ 0 (PMARVK.vcat E) fx5 R5 0xae468 ST4 MSq5
(PMARVK.mid_keep E R4 R5 ltac:(pose proof ST4 as (_ & MD0 & _); exact MD0) ltac:(PMARVK.kks KSq5))).
intros model5 ST5 _.
assert (R523 : getr R5 (reg 23) = Z_to_bv 64 (PMARVK.vF E + 176)) by (rewrite (KSq5 23%nat) by inl; exact R423).
assert (R524 : getr R5 (reg 24) = Z_to_bv 64 1) by (rewrite (KSq5 24%nat) by inl; exact R424).
pose proof (PMARVK.rvmore_of L ar C HI LY HIok E X _ _ _ _ _ _ _ _ _ _ _ ST5) as MO5. rewrite more_ws in MO5.
PMARVK.rvfacts L ar C HI LY HIok E X ST5. PMARVK.rvfactsv L ar C HI LY HIok IL ICok ILY E X ST5.
cfeed PP (PMARVP6.arvCK1_conc fx5 R5 (mrestrict (ahid Ac2 model5) M4) ltac:(let v := Vof E in exact v)) ltac:(PMARVK.rvsc).
destruct PP as (fx6 & R6 & M6v & MGq6 & _ & FZq6 & MSq6 & KSq6 & K11 & S25 & S24).
apply (PMARVS.rv_step L ar C HI LY HIok E X fx5 R5 0xae468 M4 model5 LK2 crc Ac2 _ _ _ 0 (PMARVK.vcat E) fx6 R6 0xae474 M6v
(fun a => PMARVK.vF E / 8 + 2147450880 <= a < PMARVK.vF E / 8 + 2147450880 + 64) 1 ST5 MSq6 MGq6).
{ intros a Ha Na. apply FZq6; [exact Ha| intros Y; apply Na; clear - Y; lia]. }
{ intros a Wa. right; left; exact Wa. }
{ apply (L5C.u8_at_agree RSEGS (mrestrict (ahid Ac2 model5) M4) M6v); [| clear - AO1; lia| clear - AO1; lia| exact MO5].
intros i Hi. apply FZq6; [clear - Hi AO1; lia| clear - Hi AO1 AO3 AF1; lia]. }
{ right; reflexivity. }
{ apply (PMARVK.mid_keep E R5 R6); [pose proof ST5 as (_ & MD0 & _); exact MD0| PMARVK.kks KSq6]. }
intros M6 model6 ST6 VIS6.
assert (R623 : getr R6 (reg 23) = Z_to_bv 64 (PMARVK.vF E + 176)) by (rewrite (KSq6 23%nat) by inl; exact R523).
assert (R624 : getr R6 (reg 24) = Z_to_bv 64 1) by (rewrite (KSq6 24%nat) by inl; exact R524).
assert (Z192 : L5KA.zeros_at (mrestrict (ahid Ac2 model6) M6) (((PMARVK.vF E + 192) / 8) + 2147450880) 2).
{ assert (E192 : ((PMARVK.vF E + 192) / 8) + 2147450880 = PMARVK.vF E / 8 + 2147450904).
{ replace (PMARVK.vF E + 192) with (24 * 8 + PMARVK.vF E) by (clear; lia). rewrite Z.div_add_l by lia. clear; lia. }
rewrite E192. rewrite VIS6. apply zeros2; [exact S24| replace (PMARVK.vF E / 8 + 2147450904 + 1) with (PMARVK.vF E / 8 + 2147450905) by (clear; lia); exact S25| clear - DF1; lia| clear - DF2; lia]. }
pose proof (PMARVK.rvmore_of L ar C HI LY HIok E X _ _ _ _ _ _ _ _ _ _ _ ST6) as MO6.
assert (MO6' : PM.p_more (PMPK.set_more (PMSPA.with_src (PMPK.set_more (PMARVK.vs0 E) 1) src2) 1) = 1) by (destruct (PMARVK.vs0 E); reflexivity).
rewrite MO6' in MO6.
PMARVK.rvfacts L ar C HI LY HIok E X ST6. PMARVK.rvfactsv L ar C HI LY HIok IL ICok ILY E X ST6.
cfeed PP (PMARVP6.arvCK2_conc fx6 R6 (mrestrict (ahid Ac2 model6) M6) ltac:(let v := Vof E in exact v)) ltac:(PMARVK.rvsc).
destruct PP as (fx7 & R7 & M7v & MGq7 & _ & FZq7 & MSq7 & KSq7 & EXT7).
apply (PMARVS.rv_step L ar C HI LY HIok E X fx6 R6 0xae474 M6 model6 LK2 crc Ac2 _ _ _ 0 (PMARVK.vcat E) fx7 R7 0xae110 M7v
(fun a => (PMARVK.vF E / 8 + 2147450880 <= a < PMARVK.vF E / 8 + 2147450880 + 64) \/ (PMARVK.op E + 8 <= a < PMARVK.op E + 9)
\/ (PMARVK.vF E + 192 <= a < PMARVK.vF E + 208)) 1 ST6 MSq7 MGq7).
{ intros a Ha Na. apply FZq7; [exact Ha| intros Y; apply Na; right; left; clear - Y; lia| intros Y; apply Na; left; clear - Y; lia| intros Y; apply Na; right; right; clear - Y; lia]. }
{ intros a [Wa|[Wa|Wa]]; [right; left; exact Wa| right; right; exact Wa| left; clear - Wa; lia]. }
{ decompose [and] EXT7. assumption. }
{ right; reflexivity. }
{ apply (PMARVK.mid_keep E R6 R7); [pose proof ST6 as (_ & MD0 & _); exact MD0| PMARVK.kks KSq7]. }
intros M7 model7 ST7 _.
apply (PMARVS.rv_j0 L ar C HI LY HIok E X fx7 R7 M7 model7 LK2 crc Ac2 _ _ _ ST7).
* destruct (PMARVK.vs0 E) as [mo dn dp src tb tg vb vk stk]. pose proof INV0 as (IM & _). cbn [PM.p_more] in IM. subst mo. exact INV0.
* unfold PMSPA.prog_value, PMSPA.push_rel. left. destruct (PMARVK.vs0 E); reflexivity.
+
apply (PMARVC.rv_ro L ar C HI LY HIok E X fx4 R4 0xad7c8 M4 model4 LK2 crc Ac2 _ _ _ 0 (PMARVK.vcat E) fx5 R5 0xae974 ST4 MSq5
(PMARVK.mid_keep E R4 R5 ltac:(pose proof ST4 as (_ & MD0 & _); exact MD0) ltac:(PMARVK.kks KSq5))).
intros model5 ST5 _.
apply (PMARVC.rv_mkec L ar C HI LY HIok MKE E X fx5 R5 M4 model5 LK2 crc Ac2 _ _ _ 0 (PMARVK.vcat E) 7 0xad7e0 ST5 C1 ltac:(split; [clear; lia| reflexivity]) C10 C11 ltac:(clear; lia)).
intros fx6 R6 M6 model6 LK6 Ac6 ST6 _.
clear ST ST1 ST2 ST3 ST4 ST5.
ztail PMARVP7.arvZC_conc.
-
assert (Ed : d = 0) by (clear - Hd D1; lia). rewrite Ed in Yd.
cfeed PP (PMARVP5.arvCN_conc fx2 R2 (mrestrict (ahid Ac2 model2) M2) ltac:(let v := Vof E in exact v)) ltac:(PMARVK.rvsc).
destruct PP as (fx3 & R3 & M3v & MGq3 & FRWq3 & FZq3 & MSq3 & KSq3 & B1 & B10 & B11).
assert (M3v = mrestrict (ahid Ac2 model2) M2) by (apply functional_extensionality; exact FRWq3). subst M3v.
apply (PMARVC.rv_ro L ar C HI LY HIok E X fx2 R2 0xad7b8 M2 model2 LK2 crc Ac2 _ _ _ 0 (PMARVK.vcat E) fx3 R3 0xae974 ST2 MSq3
(PMARVK.mid_keep E R2 R3 ltac:(pose proof ST2 as (_ & MD0 & _); exact MD0) ltac:(PMARVK.kks KSq3))).
intros model3 ST3 _.
apply (PMARVC.rv_mkec L ar C HI LY HIok MKE E X fx3 R3 M2 model3 LK2 crc Ac2 _ _ _ 0 (PMARVK.vcat E) 1 0xad7e0 ST3 B1 ltac:(split; [clear; lia| reflexivity]) B10 B11 ltac:(clear; lia)).
intros fx4 R4 M4 model4 LK4 Ac4 ST4 _.
clear ST ST1 ST2 ST3.
ztail PMARVP7.arvZC_conc.
Qed.
Theorem rv_partR : ltac2:(TCodec.tc2 tcn__PmARvR "RN'H'GvQ?v9vQFv8r1%6554321'Q9&<y5'R1yR0%211%5241'2y8%611%311p061';'1&C%211&B'3'6%2211%711&Ir:r7r6r5r4r3r2&M%118&N%11:&L%11<z&K%11?%A?Q;Q:Q9@?>=<;:86431&Q5%11<'4&Q:r9&R0&QBuG%211%42Q>1%7261%62Q>G%:3Q>21u<%811%:2QD1%=2Q11+S3%=2QE1%A3QE31'Q=&Q>&E%11R4&Q6r<r;+eek<%467321Q=H&Jr>%211%<4;941p0>1p0F1p0Q21p0Q51pT6QJ1p2QI1pS@QN1pFR01pSFR41pNR61pQ2R<1pSBRC1pS:RE1p@RM1").
Proof. intros E X fx Rc Mc modelc LKc crc Ac t.
intros ST TG R23 R12. unfold PMSRVD.rvR in TG.
destruct TG as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]].
- exact (armC E X fx Rc Mc modelc LKc crc Ac ST R23 R12).
- exact (armD E X fx Rc Mc modelc LKc crc Ac ST R23 R12).
- exact (armI E X fx Rc Mc modelc LKc crc Ac ST R23 R12).
- exact (armL E X fx Rc Mc modelc LKc crc Ac ST R23 R12).
- exact (armU E X fx Rc Mc modelc LKc crc Ac ST R23 R12).
- exact (armd E X fx Rc Mc modelc LKc crc Ac ST R23 R12).
- exact (armi E X fx Rc Mc modelc LKc crc Ac ST R23 R12).
- exact (arml E X fx Rc Mc modelc LKc crc Ac ST R23 R12).
Qed.
End WithHeap.
End SCFG_1.
End PMARVR.
