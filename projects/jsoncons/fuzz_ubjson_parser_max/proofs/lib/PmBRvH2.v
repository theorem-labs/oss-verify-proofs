(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0 LibIface
AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0 L5CoreSpecsAB0 L5StepARB0 L5CoreBRB0 L5ADetailHRB0
PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAb
PmModelFactsA PmStepAB0 PmStep PmParStep PmParKit PmBSrcKit PmBParKit PmBReset1 PmBUarK PmBUar PmBRvK PmBRvF PmBRvS PmBRvC PmBRvG
PmBRdValP1 PmBRdValP6 PmBRdValP7 PmBRdValP8 PmBRdValP9 PmSRdValD PmBRvH.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBRvH2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBRvK.PMBRVK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSRdValD.PMSRVD."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Ac"; "1list"; "1option"; "1prod"; "2eq"; "3Z"; "0E"; "0HI"; "0L"; "0LKc"; "4Model"; "5bvmap"; "0Mc"; "0Rc"; "6credit"; "7fframe"]; ["8SCFG"; "9rvc"; "9rve"; "9rvst"; "9vK"; "9vcat"; "9ve0"; "9vs0"; "9vsm0"; ":rvS"; ";cfg"; "<FPState"; "<getr"; "=srealizes"; ">loaded_segments"; "0SCFG_P"]; ["?of_nat"; "0X"; "0ar"; "0crc"; "0fx"; "0modelc"; "@Z_to_bv"; "@bv"; "0t"]]).
Local Ltac lia := L5FastLia.plia.
Module PMBRVH2.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithHeap.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis MKE : PMB.make_ec_spec L ar HI.
Hypothesis GL : PMB.get_length_spec L ar HI.
Hypothesis RS : PMB.read_span_spec L ar HI.
Hypothesis VAL : PMB.validate_spec L ar HI.
Hypothesis B10 : PMB.is_base10_spec L ar HI.
Let LYa := PMB.ly_as0 L C LY.
Ltac Vof E := constr:(fun j : nat => match j with 2%nat => PMBRVK.vsp E | 36%nat => PMBRVK.op E | 37%nat => PMBRVK.ov E
| 38%nat => PMBRVK.oec E | 47%nat => PMBRVK.vF E | 48%nat => PMBRVK.vfl E | _ => 0 end).
Local Ltac ztail P :=
lazymatch goal with ST : PMBRVK.rvst _ _ _ ?E ?Rc ?Mc ?modelc ?LKc ?crc ?Ac ?s ?sm true ?w _, X : PMBRVK.rvc _ _ _ ?E |- srealizes _ _ (@PMSPA.cfg _ ?fx _ ?pc _ _) _ =>
PMBRVK.rvfacts L ar C HI LY HIok E X ST;
pose proof (P fx Rc (mrestrict (ahid Ac modelc) Mc) (fun j : nat => match j with 2%nat => PMBRVK.vsp E | 36%nat => PMBRVK.op E | 37%nat => PMBRVK.ov E
| 38%nat => PMBRVK.oec E | 47%nat => PMBRVK.vF E | 48%nat => PMBRVK.vfl E | 50%nat => w | _ => 0 end)) as PP;
cbn beta iota in PP; L5SAR.feed PP ltac:(first [PMBRVK.rvsc | lia]);
let fx1 := fresh "fz" in let R1 := fresh "Rz" in let M1v := fresh "Mz" in let MG1 := fresh "MGz" in let FZ1 := fresh "FZz" in let EX := fresh "EXz" in
destruct PP as (fx1 & R1 & M1v & MG1 & _ & FZ1 & EX);
let MT1 := fresh "MSz" in let KT1 := fresh "KSz" in let Z1 := fresh "Zr1" in let Z10 := fresh "Zr10" in let Z11 := fresh "Zr11" in
destruct EX as (MT1 & KT1 & Z1 & Z10 & Z11 & EX);
apply (PMBRVF.rv_fin L ar C HI LY HIok E X fx Rc pc Mc modelc LKc crc Ac s sm true w (pa_errcat_obj PMB.AD) 0 fx1 R1 M1v ST MT1 MG1);
[ let a := fresh "a" in let Ha := fresh "Ha" in let N1 := fresh "N1" in let N2 := fresh "N2" in let N3 := fresh "N3" in
intros a Ha N1 N2 N3; apply FZ1;
first [ exact Ha | (let Y := fresh "Y" in intros Y; first [ (apply N1; clear - Y; lia) | (apply N2; clear - Y; lia) | (apply N3; clear - Y; lia) ]) ]
| decompose [and] EX; assumption
| left; reflexivity
| exact Z1 | exact Z10 | exact Z11
| apply (PMBRVK.mid_keep E Rc R1); [pose proof ST as (_ & ?MD0 & _); assumption| PMBRVK.kks KT1]
| left; split; [lia|]; split; [reflexivity|]; split; reflexivity ]
end.
Local Ltac glfail P :=
lazymatch goal with ST : PMBRVK.rvst _ _ _ ?E ?Rc ?Mc ?modelc ?LKc ?crc ?Ac ?s ?sm true ?w _, X : PMBRVK.rvc _ _ _ ?E,
MO : PM.p_more ?s = 0 |- srealizes _ _ (@PMSPA.cfg _ ?fx _ ?pc _ _) _ =>
PMBRVK.rvfacts L ar C HI LY HIok E X ST;
let MOv := fresh "MOv" in pose proof (PMBRVK.rvmore_of L ar C HI LY HIok E X _ _ _ _ _ _ _ _ _ _ _ ST) as MOv; rewrite MO in MOv;
let B := fresh "B" in pose proof (bv_unsigned_in_range 64 (getr Rc (reg 10))) as B; change (bv_modulus 64) with (2 ^ 64) in B;
let RA := fresh "RA" in assert (RA : getr Rc (reg 10) = Z_to_bv 64 (bv_unsigned (getr Rc (reg 10)))) by (symmetry; apply Z_to_bv_bv_unsigned);
pose proof (P fx Rc (mrestrict (ahid Ac modelc) Mc) (fun j : nat => match j with 2%nat => PMBRVK.vsp E | 36%nat => PMBRVK.op E | 37%nat => PMBRVK.ov E
| 38%nat => PMBRVK.oec E | 47%nat => PMBRVK.vF E | 48%nat => PMBRVK.vfl E | 49%nat => bv_unsigned (getr Rc (reg 10)) | 50%nat => w | _ => 0 end)) as PP;
cbn beta iota in PP; L5SAR.feed PP ltac:(first [PMBRVK.rvsc | lia]);
let fx1 := fresh "fz" in let R1 := fresh "Rz" in let M1v := fresh "Mz" in let MG1 := fresh "MGz" in let FZ1 := fresh "FZz" in
let MT1 := fresh "MSz" in let KT1 := fresh "KSz" in let Z1 := fresh "Zr1" in let Z10 := fresh "Zr10" in let Z11 := fresh "Zr11" in
destruct PP as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MT1 & KT1 & Z1 & Z10 & Z11 & _);
apply (PMBRVF.rv_fin L ar C HI LY HIok E X fx Rc pc Mc modelc LKc crc Ac s sm true w (pa_errcat_obj PMB.AD) 0 fx1 R1 M1v ST MT1 MG1);
[ let a := fresh "a" in let Ha := fresh "Ha" in let N1 := fresh "N1" in let N2 := fresh "N2" in let N3 := fresh "N3" in
intros a Ha N1 N2 N3; apply FZ1; [exact Ha| let Y := fresh "Y" in intros Y; apply N1; clear - Y; lia]
| match goal with HO : 6893568 <= PMBRVK.op _ <= _, HF : (PMBRVK.op _ + 384 <= PMBRVK.vF _ \/ PMBRVK.vF _ + 512 <= PMBRVK.op _) |- _ =>
apply (L5C.u8_at_agree RSEGS (mrestrict (ahid Ac modelc) Mc) M1v); [| clear - HO; lia| clear - HO; lia| exact MOv];
let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; apply FZ1; [clear - Hi HO; lia| clear - Hi HF; lia] end
| left; reflexivity
| exact Z1 | exact Z10 | exact Z11
| apply (PMBRVK.mid_keep E Rc R1); [pose proof ST as (_ & ?MD0 & _); assumption| PMBRVK.kks KT1]
| left; split; [lia|]; split; [reflexivity|]; split; reflexivity ]
end.
Lemma armH : ltac2:(TCodec.tc2 tcn__PmBRvH2 "RJ'B'AvOv8vQ2v7r1%6554321'K&;y5'Q7yR0%211%5241'2y8%611%311p061':'1&?%211&>'3'5%2211%711&Cr9r6r5r4r3r2&G%117&H%119&F%11;z&E%11>%@?Q:Q9Q8?>=<;:Q786431'4&Lr7&Q6&Q0uG%211%42Q;1%7261+R8%72Q<1%;3Q<31r8u<%:11%<2QC1%?241+S3%?2QD1%C3QD31'M&N&@%11R3&Jr:+eim8%3662Q;1?I&Dr<%211%;4:841p0=1p0F1p0Q31p2QE1pR8QJ1pDQL1pR<R01pJR21pLR81pR:R?1pR4RA1p>RI1").
Proof. intros E X fx Rc Mc modelc LKc crc Ac.
intros ST R23 R12.
PMBRVK.rvfacts L ar C HI LY HIok E X ST. PMBRVK.rvfactsv L ar C HI LY HIok IL ICok ILY E X ST.
cfeed PP (PMBRVP1.arvTH_conc fx Rc (mrestrict (ahid Ac modelc) Mc) ltac:(let v := Vof E in exact v)) ltac:(PMBRVK.rvsc).
destruct PP as (fx1 & R1 & M1v & MG1 & FRW1 & _ & MT1 & KT1 & A1 & A10 & A11).
assert (M1v = mrestrict (ahid Ac modelc) Mc) by (apply functional_extensionality; exact FRW1). subst M1v.
apply (PMBRVC.rv_ro L ar C HI LY HIok E X fx Rc 0xae7a8 Mc modelc LKc crc Ac _ _ _ 0 (PMBRVK.vcat E) fx1 R1 0xb160c ST MT1
(PMBRVK.mid_keep E Rc R1 ltac:(pose proof ST as (_ & MD0 & _); exact MD0) ltac:(PMBRVK.kks KT1))).
intros model1 ST1 _.
pose proof (GL 0 ltac:(lia)) as GL0. apply PMBRVG.rd0_r in GL0.
apply (PMBRVG.rv_run L ar C HI HIok 0xb160c 5 _ _ GL0 E X fx1 R1 Mc model1 LKc crc Ac _ _ _ (PMBRVK.vcat E) 0xae9bc ST1 A1
ltac:(split; [clear; lia| reflexivity]) ltac:(lia)).
{ split; [rewrite L5K.rl10; exact A10| rewrite L5K.rl11; exact A11]. }
{ exact (PMBRVK.c_INV L ar HI E X). }
intros fx2 R2 M2 model2 LK2 Ac2 s2 sm2 e2 cr2 v2 c2 ST2 RP2 ALT2.
destruct ALT2 as [(Hv & Ec & MO2 & E2)|(Ev & Ec & INV2 & PL2)].
-
subst c2 e2. clear ST ST1. glfail PMBRVP6.arvHGe_conc.
- subst v2 c2. destruct PL2 as (STK2 & UN2 & (len & Hlen & Rlen)). rewrite L5K.rl10 in Rlen.
PMBRVK.rvfacts L ar C HI LY HIok E X ST2.
cfeed PP (PMBRVP6.arvHG0_conc fx2 R2 (mrestrict (ahid Ac2 model2) M2)
(fun j : nat => match j with 2%nat => PMBRVK.vsp E | 36%nat => PMBRVK.op E | 37%nat => PMBRVK.ov E
| 38%nat => PMBRVK.oec E | 47%nat => PMBRVK.vF E | 48%nat => PMBRVK.vfl E | 49%nat => len | _ => 0 end)) ltac:(PMBRVK.rvsc).
destruct PP as (fx3 & R3 & M3v & MG3 & FRW3 & _ & MT3 & KT3 & B1 & B10' & B11 & B12 & B25).
assert (M3v = mrestrict (ahid Ac2 model2) M2) by (apply functional_extensionality; exact FRW3). subst M3v.
apply (PMBRVC.rv_ro L ar C HI LY HIok E X fx2 R2 0xae9bc M2 model2 LK2 cr2 Ac2 _ _ _ 0 (PMBRVK.vcat E) fx3 R3 0xb1c08 ST2 MT3
(PMBRVK.mid_keep E R2 R3 ltac:(pose proof ST2 as (_ & MD0 & _); exact MD0) ltac:(PMBRVK.kks KT3))).
intros model3 ST3 _.
apply (PMBRVG.rv_rspan L ar C HI LY HIok RS E X fx3 R3 M2 model3 LK2 cr2 Ac2 _ _ _ (PMBRVK.vcat E) 0xae9e8 len ST3 B1
ltac:(split; [clear; lia| reflexivity]) B10' B11 B12 Hlen).
intros fx4 R4 M4 model4 LK4 Ac4 s4 sm4 cr4 ptr n ST4 RP4 Rptr Rn Hn Hn26 DEF4 ACC4 LOC4 P0 P1 P2 P3 STK4 INV4.
assert (R425 : getr R4 (reg 24) = Z_to_bv 64 len) by (rewrite (L5SAR.cs_of_preserved R3 R4 24 RP4) by inl; exact B25).
assert (QP : 0 <= ptr < 2 ^ 64) by (clear - P0 P2 Hn; lia). assert (QN : 0 <= n < 2 ^ 64) by (clear - Hn Hlen; lia).
PMBRVK.rvfacts L ar C HI LY HIok E X ST4.
cfeed PP (PMBRVP6.arvHF_conc fx4 R4 (mrestrict (ahid Ac4 model4) M4)
(fun j : nat => match j with 2%nat => PMBRVK.vsp E | 36%nat => PMBRVK.op E | 37%nat => PMBRVK.ov E
| 38%nat => PMBRVK.oec E | 47%nat => PMBRVK.vF E | 48%nat => PMBRVK.vfl E | 49%nat => len | 51%nat => ptr | 52%nat => n | _ => 0 end)) ltac:(PMBRVK.rvsc).
destruct PP as (fx5 & R5 & M5v & MG5 & FRW5 & _ & [(MT5 & KT5 & C1 & C11 & C23 & CN)|(MT5 & KT5 & C1 & C10 & C11 & CN)]);
(assert (M5v = mrestrict (ahid Ac4 model4) M4) by (apply functional_extensionality; exact FRW5)); subst M5v.
+
pose proof (PMBRVH.n_eq_len n len Hn ltac:(clear - Hlen; lia) CN) as NL. subst n.
apply (PMBRVC.rv_ro L ar C HI LY HIok E X fx4 R4 0xae9e8 M4 model4 LK4 cr4 Ac4 _ _ _ 0 (PMBRVK.vcat E) fx5 R5 0xb1f28 ST4 MT5
(PMBRVK.mid_keep E R4 R5 ltac:(pose proof ST4 as (_ & MD0 & _); exact MD0) ltac:(PMBRVK.kks KT5))).
intros model5 ST5 _.
pose proof B10 as SC. unfold PMB.is_base10_spec, PMSPA.is_base10_spec in SC. change (pa_is_base10 PMB.AD) with 0xb1f28 in SC.
apply (PMBRVC.rv_scan L ar C HI LY HIok 0xb1f28 SC E X fx5 R5 M4 model5 LK4 cr4 Ac4 _ _ _ 0 (PMBRVK.vcat E) 0xae9f8 ptr len ST5 C1
ltac:(split; [clear; lia| reflexivity]) ltac:(rewrite (KT5 10%nat) by inl; exact Rptr) C11 ltac:(clear - Hn Hn26; lia) P0 P1 P2 DEF4 ACC4 LOC4 P3).
intros fx6 R6 M6 model6 ST6 RP6.
assert (R623 : getr R6 (reg 25) = Z_to_bv 64 ptr) by (rewrite (L5SAR.cs_of_preserved R5 R6 25 RP6) by inl; exact C23).
assert (R625 : getr R6 (reg 24) = Z_to_bv 64 len) by (rewrite (L5SAR.cs_of_preserved R5 R6 24 RP6) by inl; rewrite (KT5 24%nat) by inl; exact R425).
PMBRVK.rvfacts L ar C HI LY HIok E X ST6. PMBRVK.rvfactsv L ar C HI LY HIok IL ICok ILY E X ST6.
pose proof (bv_unsigned_in_range 64 (getr R6 (reg 10))) as Hr10. change (bv_modulus 64) with (2 ^ 64) in Hr10.
assert (R610 : getr R6 (reg 10) = Z_to_bv 64 (bv_unsigned (getr R6 (reg 10)))) by (symmetry; apply Z_to_bv_bv_unsigned).
cfeed PP (PMBRVP9.arvHBx_conc fx6 R6 (mrestrict (ahid Ac4 model6) M6)
(fun j : nat => match j with 2%nat => PMBRVK.vsp E | 36%nat => PMBRVK.op E | 37%nat => PMBRVK.ov E
| 38%nat => PMBRVK.oec E | 47%nat => PMBRVK.vF E | 48%nat => PMBRVK.vfl E | 49%nat => len | 51%nat => ptr
| 53%nat => bv_unsigned (getr R6 (reg 10)) | _ => 0 end)) ltac:(PMBRVK.rvsc).
destruct PP as (fx7 & R7 & M7v & MG7 & FRW7 & _ & [(MT7 & KT7 & D23 & _)|(MT7 & KT7 & D23 & _)]);
(assert (M7v = mrestrict (ahid Ac4 model6) M6) by (apply functional_extensionality; exact FRW7)); subst M7v.
*
apply (PMBRVC.rv_ro L ar C HI LY HIok E X fx6 R6 0xae9f8 M6 model6 LK4 cr4 Ac4 _ _ _ 0 (PMBRVK.vcat E) fx7 R7 0xaea00 ST6 MT7
(PMBRVK.mid_keep E R6 R7 ltac:(pose proof ST6 as (_ & MD0 & _); exact MD0) ltac:(PMBRVK.kks KT7))).
intros model7 ST7 _.
assert (R723 : getr R7 (reg 25) = Z_to_bv 64 ptr) by (rewrite (KT7 25%nat) by inl; exact R623).
assert (R725 : getr R7 (reg 24) = Z_to_bv 64 len) by (rewrite (KT7 24%nat) by inl; exact R625).
PMBRVK.rvfacts L ar C HI LY HIok E X ST7. PMBRVK.rvfactsv L ar C HI LY HIok IL ICok ILY E X ST7.
cfeed PP (PMBRVP7.arvHK2_conc fx7 R7 (mrestrict (ahid Ac4 model7) M6)
(fun j : nat => match j with 2%nat => PMBRVK.vsp E | 36%nat => PMBRVK.op E | 37%nat => PMBRVK.ov E
| 38%nat => PMBRVK.oec E | 47%nat => PMBRVK.vF E | 48%nat => PMBRVK.vfl E | 49%nat => len | 51%nat => ptr | _ => 0 end)) ltac:(PMBRVK.rvsc).
destruct PP as (fx8 & R8 & M8v & MG8 & _ & FZ8 & MT8 & KT8 & EXT8).
apply (PMBRVS.rv_step L ar C HI LY HIok E X fx7 R7 0xaea00 M6 model7 LK4 cr4 Ac4 _ _ _ 0 (PMBRVK.vcat E) fx8 R8 0xaf19c M8v
(fun a => (PMBRVK.vF E / 8 + 2147450880 <= a < PMBRVK.vF E / 8 + 2147450880 + 64) \/ (PMBRVK.op E + 8 <= a < PMBRVK.op E + 9)
\/ (PMBRVK.vF E + 256 <= a < PMBRVK.vF E + 272)) 1 ST7 MT8 MG8).
{ intros a Ha Na. apply FZ8; [exact Ha| intros Y; apply Na; right; left; clear - Y; lia| intros Y; apply Na; left; clear - Y; lia| intros Y; apply Na; right; right; clear - Y; lia]. }
{ intros a [Wa|[Wa|Wa]]; [right; left; exact Wa| right; right; exact Wa| left; clear - Wa; lia]. }
{ decompose [and] EXT8. assumption. }
{ right; reflexivity. }
{ apply (PMBRVK.mid_keep E R7 R8); [pose proof ST7 as (_ & MD0 & _); exact MD0| PMBRVK.kks KT8]. }
intros M8 model8 ST8 _.
apply (PMBRVS.rv_j0 L ar C HI LY HIok E X fx8 R8 M8 model8 LK4 cr4 Ac4 _ _ _ ST8).
-- apply PMBRVH.inv_more1. exact (INV4 INV2).
-- apply PMBRVH.prog_stk. rewrite STK4. exact STK2.
*
apply (PMBRVC.rv_ro L ar C HI LY HIok E X fx6 R6 0xae9f8 M6 model6 LK4 cr4 Ac4 _ _ _ 0 (PMBRVK.vcat E) fx7 R7 0xaf460 ST6 MT7
(PMBRVK.mid_keep E R6 R7 ltac:(pose proof ST6 as (_ & MD0 & _); exact MD0) ltac:(PMBRVK.kks KT7))).
intros model7 ST7 _.
assert (R723 : getr R7 (reg 25) = Z_to_bv 64 ptr) by (rewrite (KT7 25%nat) by inl; exact R623).
assert (R725 : getr R7 (reg 24) = Z_to_bv 64 len) by (rewrite (KT7 24%nat) by inl; exact R625).
PMBRVK.rvfacts L ar C HI LY HIok E X ST7. PMBRVK.rvfactsv L ar C HI LY HIok IL ICok ILY E X ST7.
cfeed PP (PMBRVP7.arvHK3_conc fx7 R7 (mrestrict (ahid Ac4 model7) M6)
(fun j : nat => match j with 2%nat => PMBRVK.vsp E | 36%nat => PMBRVK.op E | 37%nat => PMBRVK.ov E
| 38%nat => PMBRVK.oec E | 47%nat => PMBRVK.vF E | 48%nat => PMBRVK.vfl E | 49%nat => len | 51%nat => ptr | _ => 0 end)) ltac:(PMBRVK.rvsc).
destruct PP as (fx8 & R8 & M8v & MG8 & _ & FZ8 & MT8 & KT8 & EXT8).
apply (PMBRVS.rv_step L ar C HI LY HIok E X fx7 R7 0xaf460 M6 model7 LK4 cr4 Ac4 _ _ _ 0 (PMBRVK.vcat E) fx8 R8 0xaf19c M8v
(fun a => (PMBRVK.vF E / 8 + 2147450880 <= a < PMBRVK.vF E / 8 + 2147450880 + 64) \/ (PMBRVK.op E + 8 <= a < PMBRVK.op E + 9)
\/ (PMBRVK.vF E + 288 <= a < PMBRVK.vF E + 304)) 1 ST7 MT8 MG8).
{ intros a Ha Na. apply FZ8; [exact Ha| intros Y; apply Na; right; left; clear - Y; lia| intros Y; apply Na; left; clear - Y; lia| intros Y; apply Na; right; right; clear - Y; lia]. }
{ intros a [Wa|[Wa|Wa]]; [right; left; exact Wa| right; right; exact Wa| left; clear - Wa; lia]. }
{ decompose [and] EXT8. assumption. }
{ right; reflexivity. }
{ apply (PMBRVK.mid_keep E R7 R8); [pose proof ST7 as (_ & MD0 & _); exact MD0| PMBRVK.kks KT8]. }
intros M8 model8 ST8 _.
apply (PMBRVS.rv_j0 L ar C HI LY HIok E X fx8 R8 M8 model8 LK4 cr4 Ac4 _ _ _ ST8).
-- apply PMBRVH.inv_more1. exact (INV4 INV2).
-- apply PMBRVH.prog_stk. rewrite STK4. exact STK2.
+
apply (PMBRVC.rv_ro L ar C HI LY HIok E X fx4 R4 0xae9e8 M4 model4 LK4 cr4 Ac4 _ _ _ 0 (PMBRVK.vcat E) fx5 R5 0xafa18 ST4 MT5
(PMBRVK.mid_keep E R4 R5 ltac:(pose proof ST4 as (_ & MD0 & _); exact MD0) ltac:(PMBRVK.kks KT5))).
intros model5 ST5 _.
apply (PMBRVC.rv_mkec L ar C HI LY HIok MKE E X fx5 R5 M4 model5 LK4 cr4 Ac4 _ _ _ 0 (PMBRVK.vcat E) 1 0xaf384 ST5 C1 ltac:(split; [clear; lia| reflexivity]) C10 C11 ltac:(clear; lia)).
intros fx6 R6 M6 model6 LK6 Ac6 ST6 _.
clear ST ST1 ST2 ST3 ST4 ST5.
ztail PMBRVP8.arvZHc_conc.
Qed.
Theorem rv_partS : ltac2:(TCodec.tc2 tcn__PmBRvH2 "RN'B'AvOv8vQ2v7r1%6554321'K&;y5'Q7yR0%211%5241'2y8%611%311p061':'1&?%211&>'3'5%2211%711&Cr:r7r6r5r4r3r2&G%118&H%11:&F%11<z&E%11?%A?Q;Q:Q9@?>=<;:86431&I%11<'4&Lr9&Q6&Q0uG%211%42Q>1%7261%62Q>G%:3Q>21u<%811%:2QD1%=2Q11+S3%=2QE1%A3QE31'M&N&@%11R4&Jr<r;+eim8%467321Q=H&Dr>%211%<4;941p0>1p0F1p0Q21p0Q51pRBQJ1p2QI1pR8QN1pDR01pR<R41pJR61pLR<1pR:RC1pR4RE1p>RM1").
Proof. intros E X fx Rc Mc modelc LKc crc Ac t.
intros ST TG R23 R12. unfold PMSRVD.rvS in TG.
destruct TG as [->| ->].
- exact (armH E X fx Rc Mc modelc LKc crc Ac ST R23 R12).
- exact (PMBRVH.armS L ar C HI LY HIok IL ICok ILY MKE GL RS VAL E X fx Rc Mc modelc LKc crc Ac ST R23 R12).
Qed.
End WithHeap.
End SCFG_1.
End PMBRVH2.
