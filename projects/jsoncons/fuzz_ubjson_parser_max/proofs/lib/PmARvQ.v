(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceA LibIface
AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreA L5CoreSpecsA L5StepAR L5CoreBR L5ADetailHR
PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAa
PmModelFactsA PmStepA PmStep PmParStep PmParKit PmASrcKit PmAParKit PmAReset1 PmAUarK PmAUar PmARvK PmARvF PmARvS PmARvC PmARdValP1 PmARdValP2 PmARdValP3 PmARdValP4 PmSRdValD.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmARvQ () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmARvK.PMARVK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmParKit.PMPK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSRdValD.PMSRVD."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Ac"; "1list"; "1option"; "1prod"; "2eq"; "3Z"; "0E"; "0HI"; "0L"; "0LKc"; "4Model"; "5bvmap"; "0Mc"; "0Rc"; "6credit"; "7fframe"]; ["8SCFG"; "9rvc"; "9rve"; "9rvst"; "9vK"; "9vcat"; "9ve0"; "9vs0"; "9vsm0"; ":inv"; ":pst"; ":strm"; ";set_more"; "<rvQ"; "=cfg"; "=prog_value"]; [">FPState"; ">getr"; "?srealizes"; "@loaded_segments"; "0SCFG_P"; "Aof_nat"; "0X"; "0ar"; "0crc"; "0fx"; "0m"; "0modelc"; "0s"; "0s0"; "0sm"; "0sm0"]; ["BZ_to_bv"; "Bbv"; "0t"]]).
Local Ltac lia := L5FastLia.plia.
Module PMARVQ.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
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
Let LYa := PMA.ly_as0 L C LY.
Lemma inv_more1 : ltac2:(TCodec.tc2 tcn__PmARvQ ";'J&Ir1%211&Lr2+1%3221%711p061pRJ:1").
Proof. intros s. destruct s as [mo dn dp src tb tg vb vk stk]. intros INV. pose proof INV as (IM & _). cbn [PM.p_more] in IM. subst mo. exact INV. Qed.
Lemma prog_more : ltac2:(TCodec.tc2 tcn__PmARvQ "D'J'5'K&Or5r4r2r1%544321r6&L%1276r3%:44217p061pRN=1pS0>1pRF@1pRJB1pRLC1").
Proof. intros s0 s m sm0 sm. unfold PMSPA.prog_value, PMSPA.push_rel. unfold PMPK.set_more. cbn [PM.p_stk PM.p_src]. intros X. exact X. Qed.
Lemma prog_refl : ltac2:(TCodec.tc2 tcn__PmARvQ "8'J'K&Or2r1%342211pRN51pRJ71").
Proof. intros s sm. unfold PMSPA.prog_value, PMSPA.push_rel. left. reflexivity. Qed.
Local Ltac quick P :=
lazymatch goal with ST : PMARVK.rvst _ _ _ ?E ?Rc ?Mc ?modelc ?LKc ?crc ?Ac ?s ?sm ?e _ _, X : PMARVK.rvc _ _ _ ?E |- srealizes _ _ (@PMSPA.cfg _ ?fx _ _ _ _) _ =>
PMARVK.rvfacts L ar C HI LY HIok E X ST; PMARVK.rvfactsv L ar C HI LY HIok IL ICok ILY E X ST;
pose proof (PMARVK.rvmore_of L ar C HI LY HIok E X _ _ _ _ _ _ _ _ _ _ _ ST) as MO0;
pose proof (PMARVK.c_INV L ar HI E X) as INV0; pose proof INV0 as (IM0 & _); rewrite IM0 in MO0;
pose proof (P fx Rc (mrestrict (ahid Ac modelc) Mc) (fun j => match j with 2%nat => PMARVK.vsp E | 36%nat => PMARVK.op E | 37%nat => PMARVK.ov E
| 38%nat => PMARVK.oec E | 47%nat => PMARVK.vF E | 48%nat => PMARVK.vfl E | _ => 0 end)) as PP;
cbn beta iota in PP; L5SAR.feed PP ltac:(PMARVK.rvsc);
let fx1 := fresh "fx" in let R1 := fresh "R" in let M1v := fresh "M" in let MG1 := fresh "MG" in let FZ1 := fresh "FZ" in let EX := fresh "EX" in
destruct PP as (fx1 & R1 & M1v & MG1 & _ & FZ1 & EX);
let MS1 := fresh "MS" in let KS1 := fresh "KS" in destruct EX as (MS1 & KS1 & EX);
apply (PMARVS.rv_step L ar C HI LY HIok E X fx Rc 0xad76c Mc modelc LKc crc Ac s sm e 0 (PMARVK.vcat E) fx1 R1 0xae110 M1v
(fun a => PMARVK.op E + 8 <= a < PMARVK.op E + 9) 1 ST MS1 MG1);
[ intros a Ha Na; first [ (apply FZ1; [exact Ha| let Y := fresh "Y" in intros Y; apply Na; clear - Y; lia]) | (apply FZ1; exact Ha) ]
| intros a Wa; right; right; exact Wa
| first [ (decompose [and] EX; assumption)
| (lazymatch goal with HO : 6885376 <= PMARVK.op _ <= _ |- _ =>
apply (L5C.u8_at_agree RSEGS (mrestrict (ahid Ac modelc) Mc) M1v);
[intros i Hi; apply FZ1; clear - Hi HO; lia| clear - HO; lia| clear - HO; lia| exact MO0] end) ]
| right; reflexivity
| apply (PMARVK.mid_keep E Rc R1); [pose proof ST as (_ & MD0 & _); exact MD0| PMARVK.kks KS1]
| intros M1 model1 ST1 _;
apply (PMARVS.rv_j0 L ar C HI LY HIok E X fx1 R1 M1 model1 LKc crc Ac (PMPK.set_more s 1) sm e ST1);
[ apply inv_more1; exact INV0 | apply prog_more; apply prog_refl ] ]
end.
Local Ltac nonmark P tv :=
lazymatch goal with ST : PMARVK.rvst _ _ _ ?E ?Rc ?Mc ?modelc ?LKc ?crc ?Ac ?s ?sm ?e _ _, X : PMARVK.rvc _ _ _ ?E |- srealizes _ _ (@PMSPA.cfg _ ?fx _ _ _ _) _ =>
PMARVK.rvfacts L ar C HI LY HIok E X ST; PMARVK.rvfactsv L ar C HI LY HIok IL ICok ILY E X ST;
pose proof (P fx Rc (mrestrict (ahid Ac modelc) Mc) (fun j => match j with 2%nat => PMARVK.vsp E | 33%nat => tv | 36%nat => PMARVK.op E | 37%nat => PMARVK.ov E
| 38%nat => PMARVK.oec E | 47%nat => PMARVK.vF E | 48%nat => PMARVK.vfl E | _ => 0 end)) as PP;
cbn beta iota in PP; L5SAR.feed PP ltac:(first [PMARVK.rvsc | lia]);
let fx1 := fresh "fx" in let R1 := fresh "R" in let M1v := fresh "M" in let MG1 := fresh "MG" in let FRW := fresh "FRW" in let FZ1 := fresh "FZ" in let EX := fresh "EX" in
destruct PP as (fx1 & R1 & M1v & MG1 & FRW & FZ1 & EX);
let MS1 := fresh "MS" in let KS1 := fresh "KS" in let A1 := fresh "A1" in let A10 := fresh "A10" in let A11 := fresh "A11" in
destruct EX as (MS1 & KS1 & A1 & A10 & A11);
assert (M1v = mrestrict (ahid Ac modelc) Mc) by (apply functional_extensionality; exact FRW); subst M1v;
apply (PMARVC.rv_ro L ar C HI LY HIok E X fx Rc 0xad76c Mc modelc LKc crc Ac s sm e 0 (PMARVK.vcat E) fx1 R1 0xae974 ST MS1
(PMARVK.mid_keep E Rc R1 ltac:(pose proof ST as (_ & MD0 & _); exact MD0) ltac:(PMARVK.kks KS1)));
let model1 := fresh "model" in let ST1 := fresh "ST" in intros model1 ST1 _;
apply (PMARVC.rv_mkec L ar C HI LY HIok MKE E X fx1 R1 Mc model1 LKc crc Ac s sm e 0 (PMARVK.vcat E) 6 0xae110 ST1 A1 ltac:(split; [lia| reflexivity]) A10 A11 ltac:(lia));
let fx2 := fresh "fx" in let R2 := fresh "R" in let M2 := fresh "M" in let model2 := fresh "model" in let LK2 := fresh "LK" in let Ac2 := fresh "Ac" in
let ST2 := fresh "ST" in intros fx2 R2 M2 model2 LK2 Ac2 ST2 _;
apply (PMARVS.rv_je L ar C HI LY HIok E X fx2 R2 M2 model2 LK2 crc Ac2 s sm 6 ST2); lia
end.
Theorem rv_partQ : ltac2:(TCodec.tc2 tcn__PmARvQ "RN'B'AvQ4v8vQ7v7r1%6554321'Q0&;y5'QAyR0%211%5241'2y8%611%311p061':'1&?%211&>'3'5%2211%711&Cr:r7r6r5r4r3r2&G%118&H%11:&F%11<z&E%11?%A?Q;Q:Q9@?>=<;:86431&M%11<'4&Q1r9&Q@&Q5uG%211%42Q>1%7261%62Q>G%:3Q>21u<%811%:2QD1%=2Q11+S3%=2QE1%A3QE31'Q2&Q3&@%11R4&Nr<r;+eek<%467321Q=H&Dr>%211%<4;941p0>1p0F1p0Q21p0Q51pS6QJ1p2QI1pRBQN1pDR01pRHR41pJR61pLR<1pRDRC1pR>RE1p>RM1").
Proof. intros E X fx Rc Mc modelc LKc crc Ac t.
intros ST TG R23 R12. unfold PMSRVD.rvQ in TG.
destruct TG as [E0|[E0|[E0|[E0|[E0|[E0|[E0|[E0|[E0|[E0|[E0|[E0|[E0|[E0|[E0|[E0|[E0|[E0|[E0|[E0|[E0|[E0|E0]]]]]]]]]]]]]]]]]]]]]].
- subst t. quick PMARVP1.arvTF_conc.
- subst t. quick PMARVP1.arvTN_conc.
- subst t. quick PMARVP1.arvTT_conc.
- subst t. quick PMARVP2.arvTZ_conc.
- subst t. nonmark PMARVP2.arvX69_conc 0.
- subst t. nonmark PMARVP2.arvX71_conc 0.
- subst t. nonmark PMARVP2.arvX74_conc 0.
- subst t. nonmark PMARVP2.arvX75_conc 0.
- subst t. nonmark PMARVP3.arvX77_conc 0.
- subst t. nonmark PMARVP3.arvX79_conc 0.
- subst t. nonmark PMARVP3.arvX80_conc 0.
- subst t. nonmark PMARVP3.arvX81_conc 0.
- subst t. nonmark PMARVP3.arvX82_conc 0.
- subst t. nonmark PMARVP3.arvX86_conc 0.
- subst t. nonmark PMARVP3.arvX87_conc 0.
- subst t. nonmark PMARVP3.arvX88_conc 0.
- subst t. nonmark PMARVP3.arvX89_conc 0.
- nonmark PMARVP3.arvY0_conc t.
- nonmark PMARVP3.arvY92_conc t.
- nonmark PMARVP4.arvY101_conc t.
- nonmark PMARVP4.arvY106_conc t.
- nonmark PMARVP4.arvY109_conc t.
- nonmark PMARVP4.arvY124_conc t.
Qed.
End WithHeap.
End SCFG_1.
End PMARVQ.
