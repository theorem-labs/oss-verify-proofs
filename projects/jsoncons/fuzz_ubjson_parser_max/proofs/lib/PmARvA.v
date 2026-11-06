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
PmModelFactsA PmStepA PmStep PmParStep PmParKit PmASrcKit PmAParKit PmAReset1 PmAUarK PmAUar PmARvK PmARvF PmARvS PmARvC PmARvG
PmARdValP2 PmARdValP7 PmSRdValD.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmARvA () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmARvK.PMARVK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSRdValD.PMSRVD."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Ac"; "1list"; "1option"; "1prod"; "2eq"; "3Z"; "0E"; "0HI"; "0L"; "0LKc"; "4Model"; "5bvmap"; "0Mc"; "0Rc"; "6credit"; "7fframe"]; ["8SCFG"; "9rvc"; "9rve"; "9rvst"; "9vK"; "9vcat"; "9ve0"; "9vs0"; "9vsm0"; ":rvA"; ";cfg"; "<FPState"; "<getr"; "=srealizes"; ">loaded_segments"; "0SCFG_P"]; ["?of_nat"; "0X"; "0ar"; "0crc"; "0fx"; "0modelc"; "@Z_to_bv"; "@bv"; "0t"]]).
Local Ltac lia := L5FastLia.plia.
Module PMARVA.
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
Hypothesis BA : PMA.begin_array_spec L ar HI.
Hypothesis BO : PMA.begin_object_spec L ar HI.
Let LYa := PMA.ly_as0 L C LY.
Ltac Vof E := constr:(fun j : nat => match j with 2%nat => PMARVK.vsp E | 36%nat => PMARVK.op E | 37%nat => PMARVK.ov E
| 38%nat => PMARVK.oec E | 47%nat => PMARVK.vF E | 48%nat => PMARVK.vfl E | _ => 0 end).
Local Ltac cont T SPEC pcb ra K0 Ke :=
lazymatch goal with ST : PMARVK.rvst _ _ _ ?E ?Rc ?Mc ?modelc ?LKc ?crc ?Ac _ _ _ _ _, X : PMARVK.rvc _ _ _ ?E |- srealizes _ _ (@PMSPA.cfg _ ?fx _ _ _ _) _ =>
PMARVK.rvfacts L ar C HI LY HIok E X ST; PMARVK.rvfactsv L ar C HI LY HIok IL ICok ILY E X ST;
pose proof (T fx Rc (mrestrict (ahid Ac modelc) Mc) ltac:(let v := Vof E in exact v)) as PP;
cbn beta iota in PP; L5SAR.feed PP ltac:(PMARVK.rvsc);
let fx1 := fresh "fx" in let R1 := fresh "R" in let M1v := fresh "M" in let MG1 := fresh "MG" in let FRW1 := fresh "FRW" in
let MT1 := fresh "MT" in let KT1 := fresh "KT" in let A1 := fresh "A1" in let A10 := fresh "A10" in let A11 := fresh "A11" in let A12 := fresh "A12" in
destruct PP as (fx1 & R1 & M1v & MG1 & FRW1 & _ & MT1 & KT1 & A1 & A10 & A11 & A12);
assert (M1v = mrestrict (ahid Ac modelc) Mc) by (apply functional_extensionality; exact FRW1); subst M1v;
apply (PMARVC.rv_ro L ar C HI LY HIok E X fx Rc 0xad76c Mc modelc LKc crc Ac _ _ _ 0 (PMARVK.vcat E) fx1 R1 pcb ST MT1
(PMARVK.mid_keep E Rc R1 ltac:(pose proof ST as (_ & ?MD0 & _); assumption) ltac:(PMARVK.kks KT1)));
let model1 := fresh "model" in let ST1 := fresh "ST" in intros model1 ST1 _;
let SP := fresh "SP" in pose proof SPEC as SP; unfold PMA.begin_array_spec, PMA.begin_object_spec, PMSPA.begin_array_spec, PMSPA.begin_object_spec, PMSPA.run_spec in SP;
apply (PMARVG.rv_run L ar C HI HIok pcb 7 _ _ SP E X fx1 R1 Mc model1 LKc crc Ac _ _ _ (PMARVK.vcat E) ra ST1 A1
ltac:(split; [clear; lia| reflexivity]) ltac:(lia));
[ split; [rewrite L5K.rl10; assumption| split; [rewrite L5K.rl11; assumption| rewrite L5K.rl12; assumption]]
| exact (PMARVK.c_INV L ar HI E X)
| ];
let fx2 := fresh "fx" in let R2 := fresh "R" in let M2 := fresh "M" in let model2 := fresh "model" in let LK2 := fresh "LK" in let Ac2 := fresh "Ac" in
let s2 := fresh "s" in let sm2 := fresh "sm" in let e2 := fresh "e" in let cr2 := fresh "cr" in let v2 := fresh "v" in let c2 := fresh "c" in
let ST2 := fresh "ST" in let RP2 := fresh "RP" in let ALT2 := fresh "ALT" in
intros fx2 R2 M2 model2 LK2 Ac2 s2 sm2 e2 cr2 v2 c2 ST2 RP2 ALT2;
clear ST ST1;
PMARVK.rvfacts L ar C HI LY HIok E X ST2;
let MOv := fresh "MOv" in pose proof (PMARVK.rvmore_of L ar C HI LY HIok E X _ _ _ _ _ _ _ _ _ _ _ ST2) as MOv;
let Hv := fresh "Hv" in let Ec := fresh "Ec" in let MO2 := fresh "MO" in let E2 := fresh "E" in let INV2 := fresh "INV" in let PRG2 := fresh "PRG" in
destruct ALT2 as [(Hv & Ec & MO2 & E2)|(Hv & Ec & INV2 & PRG2)];
[
subst c2 e2; rewrite MO2 in MOv;
pose proof (Ke fx2 R2 (mrestrict (ahid Ac2 model2) M2) (fun j : nat => match j with 2%nat => PMARVK.vsp E | 36%nat => PMARVK.op E | 37%nat => PMARVK.ov E
| 38%nat => PMARVK.oec E | 47%nat => PMARVK.vF E | 48%nat => PMARVK.vfl E | 50%nat => v2 | _ => 0 end)) as PP;
cbn beta iota in PP; L5SAR.feed PP ltac:(first [PMARVK.rvsc | lia]);
let fx3 := fresh "fz" in let R3 := fresh "Rz" in let M3v := fresh "Mz" in let MG3 := fresh "MGz" in let FZ3 := fresh "FZz" in
let MT3 := fresh "MTz" in let KT3 := fresh "KTz" in let Z1 := fresh "Zr1" in let Z10 := fresh "Zr10" in let Z11 := fresh "Zr11" in let EX := fresh "EXz" in
destruct PP as (fx3 & R3 & M3v & MG3 & _ & FZ3 & MT3 & KT3 & Z1 & Z10 & Z11 & EX);
apply (PMARVF.rv_fin L ar C HI LY HIok E X fx2 R2 ra M2 model2 LK2 cr2 Ac2 s2 sm2 true v2 (pa_errcat_obj PMA.AD) 0 fx3 R3 M3v ST2 MT3 MG3);
[ let a := fresh "a" in let Ha := fresh "Ha" in let N1 := fresh "N1" in let N2 := fresh "N2" in let N3 := fresh "N3" in
intros a Ha N1 N2 N3; apply FZ3;
first [ exact Ha | (let Y := fresh "Y" in intros Y; first [ (apply N1; clear - Y; lia) | (apply N2; clear - Y; lia) | (apply N3; clear - Y; lia) ]) ]
| decompose [and] EX; assumption
| left; reflexivity
| exact Z1 | exact Z10 | exact Z11
| apply (PMARVK.mid_keep E R2 R3); [pose proof ST2 as (_ & ?MD0 & _); assumption| PMARVK.kks KT3]
| left; split; [lia|]; split; [reflexivity|]; split; reflexivity ]
|
subst v2 c2; let IM := fresh "IM" in pose proof INV2 as (IM & _); rewrite IM in MOv;
pose proof (K0 fx2 R2 (mrestrict (ahid Ac2 model2) M2) ltac:(let v := Vof E in exact v)) as PP;
cbn beta iota in PP; L5SAR.feed PP ltac:(PMARVK.rvsc);
let fx3 := fresh "fz" in let R3 := fresh "Rz" in let M3v := fresh "Mz" in let MG3 := fresh "MGz" in let FZ3 := fresh "FZz" in
let MT3 := fresh "MTz" in let KT3 := fresh "KTz" in let Z1 := fresh "Zr1" in let Z10 := fresh "Zr10" in let Z11 := fresh "Zr11" in
destruct PP as (fx3 & R3 & M3v & MG3 & _ & FZ3 & MT3 & KT3 & Z1 & Z10 & Z11 & _);
apply (PMARVF.rv_fin L ar C HI LY HIok E X fx2 R2 ra M2 model2 LK2 cr2 Ac2 s2 sm2 e2 0 (PMARVK.vcat E) 1 fx3 R3 M3v ST2 MT3 MG3);
[ let a := fresh "a" in let Ha := fresh "Ha" in let N1 := fresh "N1" in let N2 := fresh "N2" in let N3 := fresh "N3" in
intros a Ha N1 N2 N3; apply FZ3; [exact Ha| let Y := fresh "Y" in intros Y; apply N1; clear - Y; lia]
| match goal with HO : 6885376 <= PMARVK.op _ <= _, HF : (PMARVK.op _ + 384 <= PMARVK.vF _ \/ PMARVK.vF _ + 512 <= PMARVK.op _) |- _ =>
apply (L5C.u8_at_agree RSEGS (mrestrict (ahid Ac2 model2) M2) M3v); [| clear - HO; lia| clear - HO; lia| exact MOv];
let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; apply FZ3; [clear - Hi HO; lia| clear - Hi HF; lia] end
| right; reflexivity
| exact Z1 | exact Z10 | exact Z11
| apply (PMARVK.mid_keep E R2 R3); [pose proof ST2 as (_ & ?MD0 & _); assumption| PMARVK.kks KT3]
| right; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [exact INV2| exact PRG2] ] ]
end.
Theorem rv_partA : ltac2:(TCodec.tc2 tcn__PmARvA "RN'B'AvOv8vQ2v7r1%6554321'K&;y5'Q7yR0%211%5241'2y8%611%311p061':'1&?%211&>'3'5%2211%711&Cr:r7r6r5r4r3r2&G%118&H%11:&F%11<z&E%11?%A?Q;Q:Q9@?>=<;:86431&I%11<'4&Lr9&Q6&Q0uG%211%42Q>1%7261%62Q>G%:3Q>21u<%811%:2QD1%=2Q11+S3%=2QE1%A3QE31'M&N&@%11R4&Jr<r;+eek<%467321Q=H&Dr>%211%<4;941p0>1p0F1p0Q21p0Q51pRBQJ1p2QI1pR8QN1pDR01pR<R41pJR61pLR<1pR:RC1pR4RE1p>RM1").
Proof. intros E X fx Rc Mc modelc LKc crc Ac t.
intros ST TG R23 R12. unfold PMSRVD.rvA in TG.
destruct TG as [->| ->].
- cont PMARVP2.arvTA_conc BA 0xb0864 0xadd98 PMARVP7.arvA0_conc PMARVP7.arvAe_conc.
- cont PMARVP2.arvTO_conc BO 0xb0ec4 0xad8ec PMARVP7.arvO0_conc PMARVP7.arvOe_conc.
Qed.
End WithHeap.
End SCFG_1.
End PMARVA.
